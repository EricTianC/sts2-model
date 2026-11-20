#!/usr/bin/env python3
"""
Cross-language `.NET 9` <-> Lean 4 differential tester for Slay the Spire 2 logic model.

Generates randomized and fixed edge-case vectors across 15 test families:
  1. RNG_SEQ       (SplitMix64 + Xoshiro256** bit-exact stream & IEEE-754 double bits)
  2. RNG_SHUFFLE   (UnstableShuffle Fisher-Yates child-RNG permutation)
  3. DMG_PIPE      (Hook.ModifyDamageInternal: Strength, Weak, Vulnerable, PaperPhrog, LateMul, Cap)
  4. BLK_PIPE      (Hook.ModifyBlock: Dexterity, Frail, Powered vs Unpowered)
  5. CREATURE_DMG  (CreatureCmd.Damage: Block, Intangible cap+AfterOsty, DieForYou Osty + Overkill)
  6. POWER_STACK   (PowerCmd.Apply: Single/Counter, Clamp +/-999999999, AllowNegative, Artifact)
  7. CARD_COST     (CardEnergyCost local Absolute/Relative + Hook delta + ExcessEnergyWithStars)
  8. RARITY_ODDS   (CardRarityOdds Float32 bit-exact sequences & pity offset reset/clamp)
  9. MOD_SORT      (ModHelper ordinal subscriber registration sort & deduplication)
 10. QUEUE_SET     (Multiplayer ActionQueueSet concurrent queues, pause/choice/resume/cancel)
 11. TIMELINE_SEEK (Multi-player combat replay, FNV-1a 64-bit state checksum, & keyframe seek)
 12. TRACE_JSON    (Versioned external trace JSON codec, 64-bit string seeds/checksums, & interop)
 13. TURN_LIFECYCLE (Round hooks, power durations, damage reactions, and orb passives)
 14. TIER2_EFFECTS (Layered card, potion, and monster effect execution and table lookup)
 15. TIER2_CARD    (Runtime operands, actual card payment and piles, and combat-local modifiers)
 16. EXPEDITION    (Explicit two-act route, rewards, and combat persistence)

Run via: `uv run python scripts/run_diff_test.py`
"""
from __future__ import annotations

import json
import pathlib
import random
import subprocess
import tempfile
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_BIN = ROOT / ".lake" / "build" / "bin" / "sts2sim"
CS_DLL = ROOT / "DiffTest" / "Sts2Oracle" / "bin" / "Debug" / "net9.0" / "Sts2Oracle.dll"


def generate_vectors(seed: int = 20260401) -> list[str]:
    rng = random.Random(seed)
    rows: list[str] = []

    # 1. RNG_SEQ (edge seeds: 0, 1, max uint64, powers of 2, + random) - 60 vectors
    edge_seeds = [0, 1, 2, 42, (1 << 63), (1 << 64) - 1, 0xDEADBEEFCAFEBABE]
    for s in edge_seeds:
        rows.append(f"RNG_SEQ\t{s}\t12")
    for _ in range(53):
        s = rng.randrange(0, 1 << 64)
        cnt = rng.randint(1, 15)
        rows.append(f"RNG_SEQ\t{s}\t{cnt}")

    # 2. RNG_SHUFFLE (empty, singleton, 2-elem, 10-elem, 40-elem) - 65 vectors
    for n in [0, 1, 2, 3, 5, 10, 20]:
        xs = ",".join(str(i * 3 - 5) for i in range(n))
        rows.append(f"RNG_SHUFFLE\t{n + 100}\t{xs}")
    for _ in range(58):
        s = rng.randrange(0, 1 << 64)
        n = rng.randint(2, 30)
        xs = ",".join(str(rng.randint(-50, 50)) for _ in range(n))
        rows.append(f"RNG_SHUFFLE\t{s}\t{xs}")

    # 3. DMG_PIPE (powered/unpowered/move/non-move, neg strength, phrog, late mul, cap) - 100 vectors
    dmg_edges = [
        (6, 8, 3, 1, 1, 1, 100, -1),    # Move+Str+Weak+Vuln+Phrog
        (6, 12, 3, 1, 1, 1, 200, 10),   # Move+Unpowered -> unpowered bypasses everything + cap
        (0, 8, -5, 1, 0, 0, 100, -1),   # negative clamps at 0
        (10, 8, 2, 1, 0, 1, 150, 12),   # capped at 12
        (100, 8, 50, 1, 1, 0, 200, 0),  # capped at 0
        (7, 0, 5, 1, 0, 1, 100, -1),    # non-Move -> IsPoweredAttack=false
    ]
    for b, m, st, v, ph, w, lm, cp in dmg_edges:
        rows.append(f"DMG_PIPE\t{b}\t{m}\t{st}\t{v}\t{ph}\t{w}\t{lm}\t{cp}")
    for _ in range(94):
        b = rng.choice([0, 1, 3, 6, 8, 12, 25, 99])
        m = rng.choice([0, 2, 4, 8, 10, 12, 14])
        st = rng.randint(-10, 15)
        v = rng.randint(0, 1)
        ph = rng.randint(0, 1)
        w = rng.randint(0, 1)
        lm = rng.choice([50, 75, 100, 125, 150, 200])
        cp = rng.choice([-1, -1, -1, 0, 1, 10, 30])
        rows.append(f"DMG_PIPE\t{b}\t{m}\t{st}\t{v}\t{ph}\t{w}\t{lm}\t{cp}")

    # 4. BLK_PIPE - 60 vectors
    for m in [0, 4, 8, 12]:
        rows.append(f"BLK_PIPE\t8\t{m}\t3\t1")
        rows.append(f"BLK_PIPE\t2\t{m}\t-5\t1")
    for _ in range(52):
        b = rng.randint(0, 30)
        m = rng.choice([0, 4, 8, 12])
        dx = rng.randint(-8, 12)
        fr = rng.randint(0, 1)
        rows.append(f"BLK_PIPE\t{b}\t{m}\t{dx}\t{fr}")

    # 5. CREATURE_DMG (Block, Unblockable, Osty DieForYou, Overkill spill, Intangible, dead target) - 100 vectors
    cdmg_edges = [
        (0, 10, 5, 8, 15, 0),    # Dead target
        (80, 10, 0, 8, 25, 1),   # Intangible caps ModifyDamage at 1 -> 1 blocked, 0 hp loss
        (80, 5, 10, 8, 20, 0),   # 20-5=15 unblocked -> Osty 10 dies, overkill 5 hits owner -> 75 HP
        (80, 5, 10, 8, 20, 1),   # Intangible + Osty: cap=1 -> blocked by 5 block -> 0 unblocked
        (80, 5, 10, 12, 20, 0),  # Unpowered ignores Osty -> hits owner after 5 block -> 65 HP
        (80, 5, 10, 10, 20, 0),  # Move + Unblockable (8|2=10): skips 5 blk, Osty takes 10, 10 spills to owner
    ]
    for a, b, c, m, r, i in cdmg_edges:
        rows.append(f"CREATURE_DMG\t{a}\t{b}\t{c}\t{m}\t{r}\t{i}")
    for _ in range(94):
        thp = rng.choice([0, 1, 5, 20, 50, 80])
        tblk = rng.choice([0, 3, 10, 25])
        osty = rng.choice([0, 0, 5, 12, 30])
        mask = rng.choice([8, 10, 12, 14, 2, 4, 0])
        raw = rng.choice([0, 1, 4, 15, 35, 120])
        intang = rng.randint(0, 1)
        rows.append(f"CREATURE_DMG\t{thp}\t{tblk}\t{osty}\t{mask}\t{raw}\t{intang}")

    # 6. POWER_STACK (clamp, zero removal, single stack, AllowNegative, Artifact) - 80 vectors
    pstack_edges = [
        (0, 5, 0, 0, 1, 1),            # Artifact blocks visible debuff -> 0, removed=1, art=0
        (0, 5, 0, 0, 2, 0),            # Buff ignores Artifact -> 5, art=2
        (999999990, 50, 0, 0, 0, 0),   # Clamps at 999999999
        (3, -3, 0, 1, 0, 0),           # AllowNegative reaches 0 -> removed=1
        (3, -5, 0, 1, 0, 0),           # AllowNegative reaches -2 -> kept
        (1, 5, 1, 0, 0, 0),            # Single stack stays 1
        (0, 5, 1, 0, 0, 0),            # New Single applied with 5 -> clamped to 1
    ]
    for e, ap, sg, an, ar, db in pstack_edges:
        rows.append(f"POWER_STACK\t{e}\t{ap}\t{sg}\t{an}\t{ar}\t{db}")
    for _ in range(73):
        ex = rng.choice([0, 0, 1, 3, -4, 999999995, -999999995])
        ap = rng.choice([0, 1, 3, -3, -5, 50])
        sg = rng.randint(0, 1)
        an = rng.randint(0, 1)
        ar = rng.choice([0, 0, 1, 3])
        db = rng.randint(0, 1)
        rows.append(f"POWER_STACK\t{ex}\t{ap}\t{sg}\t{an}\t{ar}\t{db}")

    # 7. CARD_COST - 80 vectors
    cost_edges = [
        (-1, 0, 3, 4, 0, 0, 0, 1, 0),  # Uncosted (-1) stays -1
        (2, 1, 4, 0, 0, 1, 0, 0, 0),   # X-cost pays current energy 4
        (3, 0, 1, 4, 0, 0, 0, 1, 0),   # Excess energy (2) paid with 4 stars -> playable!
        (3, 0, 1, 3, 0, 0, 0, 1, 0),   # Only 3 stars -> unplayable!
        (2, 0, 2, 2, 1, 2, -1, 1, 0),  # Relative -1 + starCost 1
        (1, 0, 1, 0, 0, 0, 0, 0, -5),  # Hook delta -5 clamps to 0
    ]
    for row in cost_edges:
        rows.append("CARD_COST\t" + "\t".join(str(x) for x in row))
    for _ in range(74):
        bc = rng.choice([-1, 0, 1, 2, 3, 4])
        cx = 1 if (bc == 0 and rng.random() < 0.25) else 0
        en = rng.randint(0, 6)
        st = rng.randint(0, 6)
        sc = rng.choice([0, 0, 1, 2, 3])
        mt = rng.choice([0, 1, 2])
        ma = rng.randint(-2, 3)
        ex = rng.randint(0, 1)
        hd = rng.randint(-2, 2)
        rows.append(f"CARD_COST\t{bc}\t{cx}\t{en}\t{st}\t{sc}\t{mt}\t{ma}\t{ex}\t{hd}")

    # 8. RARITY_ODDS (Float32 bit-exact verification across all 7 types, scarcity 0/1) - 80 vectors
    for tcode in range(7):
        for scar in [0, 1]:
            rows.append(f"RARITY_ODDS\t{1000 + tcode * 10 + scar}\t{scar}\t{tcode}\t25")
    for _ in range(66):
        s = rng.randrange(0, 1 << 64)
        scar = rng.randint(0, 1)
        tc = rng.randint(0, 6)
        nr = rng.randint(1, 40)
        rows.append(f"RARITY_ODDS\t{s}\t{scar}\t{tc}\t{nr}")

    # 9. MOD_SORT (ordinal comparison, case sensitivity, duplicates, empty) - 45 vectors
    mod_edges = [
        "",
        "mod_a",
        "zeta,Alpha,beta,alpha,Zeta,mod_a,mod_a",
        "com.b,com.A,com.1,com.a",
    ]
    for m in mod_edges:
        rows.append(f"MOD_SORT\t{m}")
    alphabet = ["alpha", "Beta", "gamma_1", "gamma_2", "Delta", "mod.core", "mod.ui", "Zeta", "a9", "A9"]
    for _ in range(41):
        picks = [rng.choice(alphabet) for _ in range(rng.randint(1, 10))]
        rows.append("MOD_SORT\t" + ",".join(picks))

    # 10. QUEUE_SET (concurrent ActionQueueSet pause, early resume, cancel, combat end) - 60 vectors
    q_edges = [
        "1,2\tENQ,1,2,1,1;ENQ,2,2,1,1;PICK;PAUSE,0,1;ENQ,1,2,1,1;PICK;POP,1;RESUME,0;PICK;POP,3;PICK",
        "1,2\tENQ,1,2,1,1;EXEC,0;RESUME,0;PAUSE,0,0;PICK;POP,1;PICK",
        "1,2\tENQ,1,2,1,1;ENQ,2,1,0,0;ENQ,1,3,1,0;CANCELPD;PICK;CEND;ENQ,1,2,1,1;CSTART;PICK",
        "1,2,3\tENQ,3,2,1,1;ENQ,1,2,1,1;PPAUSED,1;PICK;PPAUSED,0;PICK;POP,1;PICK",
    ]
    for qe in q_edges:
        rows.append(f"QUEUE_SET\t{qe}")
    for _ in range(56):
        pids = "1,2" if rng.random() < 0.7 else "1,2,3"
        num_p = len(pids.split(","))
        ops: list[str] = []
        est_max_id = 0
        for _ in range(rng.randint(5, 18)):
            kind = rng.choice(["ENQ", "ENQ", "ENQ", "PICK", "EXEC", "PAUSE", "RESUME", "POP", "CANCELPD", "CEND", "CSTART", "PPAUSED"])
            if kind == "ENQ":
                pid = rng.randint(1, num_p)
                tc = rng.choice([1, 2, 2, 3, 4])
                pd = rng.randint(0, 1)
                ip = rng.randint(0, 1)
                ops.append(f"ENQ,{pid},{tc},{pd},{ip}")
                est_max_id += 1
            elif kind == "PICK":
                ops.append("PICK")
            elif kind == "EXEC":
                aid = rng.randint(0, max(0, est_max_id - 1))
                ops.append(f"EXEC,{aid}")
            elif kind == "PAUSE":
                aid = rng.randint(0, max(0, est_max_id - 1))
                cpc = rng.randint(0, 1)
                ops.append(f"PAUSE,{aid},{cpc}")
            elif kind == "RESUME":
                aid = rng.randint(0, max(0, est_max_id - 1))
                ops.append(f"RESUME,{aid}")
                est_max_id += 1
            elif kind == "POP":
                aid = rng.randint(0, max(0, est_max_id - 1))
                ops.append(f"POP,{aid}")
            elif kind == "PPAUSED":
                ops.append(f"PPAUSED,{rng.randint(0, 1)}")
            else:
                ops.append(kind)
        rows.append(f"QUEUE_SET\t{pids}\t{';'.join(ops)}")

    # 11. TIMELINE_SEEK (multiplayer combat replay, keyframe seek, & FNV-1a 64-bit checksum) - 60 vectors
    tl_edges = [
        "42\t34\t1\tP1_TWIN;P2_STRIKEP;P1_BASH",
        "42\t34\t2\tP1_BASH;P1_TWIN;P2_STRIKEP",
        "99\t65\t2\tP1_FPOT;P2_DEF;END_ROUND;P1_BASH;P2_UPPER;END_ROUND;P1_STRIKE",
        "777\t120\t3\tP2_UPPER;P1_TWIN;END_ROUND;P1_STRIKE;P2_STRIKEP;END_ROUND;P2_DEF;P1_BASH",
    ]
    for te in tl_edges:
        rows.append(f"TIMELINE_SEEK\t{te}")
    act_pool = ["P1_BASH", "P1_STRIKE", "P1_TWIN", "P1_FPOT", "P2_DEF", "P2_STRIKEP", "P2_UPPER", "END_ROUND"]
    for _ in range(56):
        seed = rng.randrange(0, 1 << 64)
        ehp = rng.choice([12, 25, 34, 55, 80, 120])
        stride = rng.randint(1, 5)
        n_acts = rng.randint(1, 12)
        seq = [rng.choice(act_pool) for _ in range(n_acts)]
        rows.append(f"TIMELINE_SEEK\t{seed}\t{ehp}\t{stride}\t{';'.join(seq)}")

    # 12. TRACE_JSON (External Trace JSON Wire Protocol interop, 64-bit seeds, mixed events) - 60 vectors
    def mk_wire_card(inst_id: int, entry: str, owner_id: int, cost: int, upg: int = 0) -> dict:
        ctype = "power" if entry in ("INFLAME", "FOOTWORK") else ("skill" if entry in ("DEFEND_IRONCLAD", "SHRUG_IT_OFF") else "attack")
        return {
            "instanceId": inst_id,
            "modelEntry": entry,
            "ownerId": owner_id,
            "cardType": ctype,
            "rarity": "common",
            "targetType": "self" if ctype in ("power", "skill") else "anyEnemy",
            "baseCost": cost,
            "upgradeLevel": upg,
            "gainsBlock": entry in ("DEFEND_IRONCLAD", "SHRUG_IT_OFF", "IRON_WAVE"),
        }

    def mk_wire_bundle(
        run_seed: int,
        rng_seed: int,
        enemy_entry: str,
        enemy_hp: int,
        enemy_blk: int,
        enemy_pows: list[dict],
        p1_potions: list[str | None],
        events: list[dict],
        stride: int = 2,
        include_combat: bool = True,
        gold: int = 99,
    ) -> dict:
        init_state: dict = {
            "run": {
                "runSeed": str(run_seed),
                "currentActIndex": 0,
                "ascensionLevel": 5,
                "gold": gold,
                "totalFloors": 1,
                "currentRoom": "monster" if include_combat else "shop",
            },
            "playerIds": [1, 2],
            "nextActionId": 0,
            "nextHookId": 0,
            "nextChecksumId": 0,
            "isInCombat": include_combat,
        }
        if include_combat:
            move_id = "INCANT" if enemy_entry == "CULTIST" else "SLAM"
            init_state["combat"] = {
                "combatId": 1,
                "roundNumber": 1,
                "currentSide": "player",
                "isInProgress": True,
                "isEnding": False,
                "nextInstanceId": 500,
                "rng": {"counter": 0, "seed": str(rng_seed)},
                "allies": [
                    {"id": 101, "modelEntry": "IRONCLAD", "modelCategory": "CHARACTER", "side": "player", "playerId": 1, "currentHp": 80, "maxHp": 80, "block": 0, "powers": []},
                    {"id": 102, "modelEntry": "SILENT", "modelCategory": "CHARACTER", "side": "player", "playerId": 2, "currentHp": 70, "maxHp": 70, "block": 0, "powers": []},
                ],
                "enemies": [
                    {"id": 200, "modelEntry": enemy_entry, "modelCategory": "MONSTER", "side": "enemy", "currentHp": enemy_hp, "maxHp": enemy_hp, "block": enemy_blk, "powers": enemy_pows, "monsterMoveId": move_id}
                ],
                "players": [
                    {
                        "playerId": 1, "creatureId": 101, "characterEntry": "IRONCLAD", "energy": 5, "baseMaxEnergy": 3, "stars": 0, "turnNumber": 1,
                        "hand": [
                            mk_wire_card(1001, "BASH", 1, 2),
                            mk_wire_card(1002, "POMMEL_STRIKE", 1, 1),
                            mk_wire_card(1003, "INFLAME", 1, 1),
                            mk_wire_card(1004, "IRON_WAVE", 1, 1),
                        ],
                        "draw": [mk_wire_card(1010, "STRIKE_IRONCLAD", 1, 1), mk_wire_card(1011, "CLEAVE", 1, 1)],
                        "discard": [mk_wire_card(1020, "TWIN_STRIKE", 1, 1)],
                        "potions": [{"modelEntry": p} for p in p1_potions],
                    },
                    {
                        "playerId": 2, "creatureId": 102, "characterEntry": "SILENT", "energy": 5, "baseMaxEnergy": 3, "stars": 0, "turnNumber": 1,
                        "hand": [
                            mk_wire_card(2001, "TWIN_STRIKE", 2, 1),
                            mk_wire_card(2002, "SHRUG_IT_OFF", 2, 1),
                            mk_wire_card(2003, "UPPERCUT", 2, 2),
                            mk_wire_card(2004, "STRIKE_IRONCLAD", 2, 1, 1),
                        ],
                        "draw": [mk_wire_card(2010, "NEUTRALIZE", 2, 0)],
                        "discard": [mk_wire_card(2020, "DEFEND_IRONCLAD", 2, 1)],
                        "potions": [],
                    },
                ],
            }
        return {
            "schemaVersion": 1,
            "viewerPlayerId": 1,
            "keyframeStride": stride,
            "initialState": init_state,
            "events": events,
            "expectedChecksums": [],
        }

    # Edge 1: Co-op Guardian multi-round with potions, powers, draw, opaqueStep
    tj_edge_1 = mk_wire_bundle(
        run_seed=(1 << 63) + 777,
        rng_seed=42,
        enemy_entry="COOP_GUARDIAN",
        enemy_hp=60,
        enemy_blk=5,
        enemy_pows=[{"instanceId": 10, "modelEntry": "ARTIFACT_POWER", "powerType": "buff", "stackType": "counter", "allowNegative": False, "amount": 1}],
        p1_potions=["STRENGTH_POTION", "FIRE_POTION"],
        events=[
            {"seqIdx": 0, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "usePotion", "slotIdx": 0, "targetId": None}}},
            {"seqIdx": 1, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "playCard", "cardId": 1001, "targetId": 200}}},
            {"seqIdx": 2, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2001, "targetId": 200}}},
            {"seqIdx": 3, "actorPlayerId": 1, "kind": "endRoundAndRunEnemies"},
            {"seqIdx": 4, "actorPlayerId": 1, "kind": "opaqueStep", "opaque": {"label": "RELIC", "hpDeltas": [{"id": 200, "delta": -4}], "powerDeltas": [{"creatureId": 200, "category": "POWER", "entry": "VULNERABLE_POWER", "delta": 2}], "energyDeltas": [{"id": 1, "delta": 1}]}},
        ],
        stride=2,
    )
    # Edge 2: Non-combat RunSync chain + max uint64 runSeed (> 2^53)
    tj_edge_2 = mk_wire_bundle(
        run_seed=(1 << 64) - 1,
        rng_seed=1,
        enemy_entry="COOP_GUARDIAN",
        enemy_hp=10,
        enemy_blk=0,
        enemy_pows=[],
        p1_potions=[],
        include_combat=False,
        gold=150,
        events=[
            {"seqIdx": 0, "actorPlayerId": 1, "kind": "runSync", "runSync": {"type": "mapMove", "row": 1, "col": 2, "pointType": "monster", "roomType": "monster"}},
            {"seqIdx": 1, "actorPlayerId": 1, "kind": "runSync", "runSync": {"type": "eventChoice", "optionKey": "TAKE_GOLD", "goldDelta": 75, "hpDelta": -5}},
            {"seqIdx": 2, "actorPlayerId": 1, "kind": "runSync", "runSync": {"type": "merchantBuy", "cardModel": {"category": "CARD", "entry": "BASH"}, "goldCost": 60}},
            {"seqIdx": 3, "actorPlayerId": 1, "kind": "runSync", "runSync": {"type": "rewardPick", "goldGain": 25}},
            {"seqIdx": 4, "actorPlayerId": 1, "kind": "runSync", "runSync": {"type": "actAdvance"}},
        ],
        stride=1,
    )
    # Edge 3: Cultist AI multi-round + Shrug/Pommel draw + Swift Potion
    tj_edge_3 = mk_wire_bundle(
        run_seed=98765432101234567,
        rng_seed=999,
        enemy_entry="CULTIST",
        enemy_hp=52,
        enemy_blk=0,
        enemy_pows=[],
        p1_potions=["SWIFT_POTION", "HEAL_POTION"],
        events=[
            {"seqIdx": 0, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "usePotion", "slotIdx": 0, "targetId": None}}},
            {"seqIdx": 1, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2002, "targetId": None}}},
            {"seqIdx": 2, "actorPlayerId": 1, "kind": "endRoundAndRunEnemies"},
            {"seqIdx": 3, "actorPlayerId": 1, "kind": "endRoundAndRunEnemies"},
        ],
        stride=2,
    )
    # Edge 4: Artifact + Power card removal + Hook action
    tj_edge_4 = mk_wire_bundle(
        run_seed=1234567890123456789,
        rng_seed=777,
        enemy_entry="COOP_GUARDIAN",
        enemy_hp=40,
        enemy_blk=10,
        enemy_pows=[{"instanceId": 20, "modelEntry": "ARTIFACT_POWER", "powerType": "buff", "stackType": "counter", "allowNegative": False, "amount": 2}],
        p1_potions=["FEAR_POTION"],
        events=[
            {"seqIdx": 0, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "hookAction", "playerId": 1, "hookId": 5}},
            {"seqIdx": 1, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "playCard", "cardId": 1003, "targetId": None}}},
            {"seqIdx": 2, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "usePotion", "slotIdx": 0, "targetId": 200}}},
            {"seqIdx": 3, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2003, "targetId": 200}}},
        ],
        stride=1,
    )
    for b in (tj_edge_1, tj_edge_2, tj_edge_3, tj_edge_4):
        rows.append("TRACE_JSON\t" + json.dumps(b, separators=(",", ":")))

    wire_event_templates = [
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "playCard", "cardId": 1001, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "playCard", "cardId": 1002, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "playCard", "cardId": 1003, "targetId": None}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "playCard", "cardId": 1004, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2001, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2002, "targetId": None}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2003, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 2, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 2, "payload": {"type": "playCard", "cardId": 2004, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "usePotion", "slotIdx": 0, "targetId": 200}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "combat", "combat": {"eventType": "gameAction", "playerId": 1, "payload": {"type": "discardPotion", "slotIdx": 1}}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "endRoundAndRunEnemies"},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "opaqueStep", "opaque": {"label": "RAND", "hpDeltas": [{"id": 200, "delta": -3}], "blockDeltas": [{"id": 101, "delta": 4}], "energyDeltas": [{"id": 1, "delta": 1}], "starsDeltas": [{"id": 2, "delta": 2}]}},
        lambda idx: {"seqIdx": idx, "actorPlayerId": 1, "kind": "runSync", "runSync": {"type": "rewardPick", "goldGain": 15}},
    ]
    for _ in range(56):
        rseed = rng.randrange(1 << 54, 1 << 64)  # Always test 64-bit string precision (> 2^53)
        cseed = rng.randrange(0, 1 << 64)
        enemy = rng.choice(["COOP_GUARDIAN", "CULTIST"])
        ehp = rng.choice([24, 34, 55, 80, 110])
        eblk = rng.choice([0, 0, 5, 10])
        art_amt = rng.choice([0, 0, 1, 2])
        pows = [{"instanceId": 15, "modelEntry": "ARTIFACT_POWER", "powerType": "buff", "stackType": "counter", "allowNegative": False, "amount": art_amt}] if art_amt > 0 else []
        pots = rng.sample(["FIRE_POTION", "BLOCK_POTION", "STRENGTH_POTION", "ENERGY_POTION", "FEAR_POTION"], k=2)
        stride = rng.randint(1, 4)
        n_ev = rng.randint(1, 8)
        evs = [rng.choice(wire_event_templates)(idx) for idx in range(n_ev)]
        b = mk_wire_bundle(rseed, cseed, enemy, ehp, eblk, pows, pots, evs, stride=stride)
        rows.append("TRACE_JSON\t" + json.dumps(b, separators=(",", ":")))

    rows.extend(vector for vector, _ in FIXED_VECTORS)
    return rows


Expected = str | dict[str, int | str]


def lifecycle_vectors() -> list[tuple[str, Expected]]:
    rows: list[tuple[str, Expected]] = []

    def add(expected: str, *, mode=0, p_hp=80, p_block=0, p_powers="", orbs="",
            e_hp=40, e_block=0, e_powers="", actions="") -> None:
        fields = ("TURN_LIFECYCLE", mode, p_hp, p_block, p_powers, orbs,
                  e_hp, e_block, e_powers, actions)
        rows.append(("\t".join(map(str, fields)), expected))

    def rounds(n: int) -> str:
        return ";".join(["END_ROUND"] * n)

    # 10 duration cases: PowerCmd applies a skip to newly inflicted player debuffs
    # on the enemy turn, but stacking does not reapply the skip.
    for initial, hp_by_round in (("", (75, 68)), ("VULNERABLE_POWER:1", (73, 66))):
        for n, hp in enumerate(hp_by_round, 1):
            add(f"{hp},0,3,VULNERABLE_POWER:1:0|40,0,1,-|-", mode=1,
                p_powers=initial, actions=rounds(n))
    for initial in ("", "WEAK_POWER:1,FRAIL_POWER:1"):
        for n in (1, 2):
            add("80,0,3,WEAK_POWER:1:0;FRAIL_POWER:1:0|40,0,1,-|-", mode=3,
                p_powers=initial, actions=rounds(n))
    add("80,0,3,-|40,0,1,VULNERABLE_POWER:1:0|-", actions="P_VULN:2;END_ROUND")
    # PowerModel.GetTypeForAmount treats removing a debuff as a buff.
    add("80,0,3,-|40,0,1,VULNERABLE_POWER:1:0;ARTIFACT_POWER:1:0|-",
        e_powers="VULNERABLE_POWER:2,ARTIFACT_POWER:1", actions="P_VULN:-1")

    # 8 Poison cases: PoisonPower.Trigger bypasses block and only decrements on survival.
    # The headless damage path retains the power in the lethal state's snapshot.
    poison = "POISON_POWER:3"
    retained_block = poison + ",BARRICADE_POWER:1"
    add("80,0,3,POISON_POWER:3:0|40,0,1,-|-", p_powers=poison)
    add("80,0,3,-|40,0,1,POISON_POWER:3:0|-", e_powers=poison)
    for n, p_hp, e_hp, amount in ((1, 77, 37, 2), (2, 75, 35, 1)):
        powers = f"POISON_POWER:{amount}:0;BARRICADE_POWER:1:0"
        add(f"{p_hp},5,3,{powers}|40,0,1,-|-",
            p_block=5, p_powers=retained_block, actions=rounds(n))
        add(f"80,0,3,-|{e_hp},5,1,{powers}|-",
            e_block=5, e_powers=retained_block, actions=rounds(n))
    add("0,0,3,POISON_POWER:3:0|40,0,0,-|-", p_hp=3, p_powers=poison, actions=rounds(1))
    add("80,0,3,-|0,0,0,POISON_POWER:3:0|-", mode=1, e_hp=3, e_powers=poison, actions=rounds(1))

    # 8 Doom cases: DoomPower.BeforeSideTurnEnd executes after the attack, at HP <=
    # stacks. CreatureCmd.Kill removes ordinary powers without consuming block.
    doom = "DOOM_POWER:10:0;BARRICADE_POWER:1:0"
    for e_hp, final_enemy, vuln_skip in (
        (9, "0,7,0,-", 1), (10, "0,7,0,-", 1),
        (11, f"11,7,1,{doom}", 0), (12, f"12,7,1,{doom}", 0),
    ):
        setup = dict(e_hp=e_hp, e_block=7, e_powers="DOOM_POWER:10,BARRICADE_POWER:1")
        add(f"80,0,3,-|{e_hp},7,1,{doom}|-", **setup)
        add(f"75,0,3,VULNERABLE_POWER:1:{vuln_skip}|{final_enemy}|-",
            **setup, mode=1, actions=rounds(1))

    # 8 Thorns cases: BeforeDamageReceived retaliates against powered attacks only,
    # and its Unpowered damage does not bypass block.
    thorns = "THORNS_POWER:4"
    for block, struck_hp in ((0, 76), (3, 79), (4, 80)):
        add(f"{struck_hp},0,3,-|34,0,1,THORNS_POWER:4:0|-",
            p_block=block, e_powers=thorns, actions="P_STRIKE")
        add(f"80,{block},3,-|34,0,1,THORNS_POWER:4:0|-",
            p_block=block, e_powers=thorns, actions="P_UNPOW")
    # The headless damage core cancels a hit from a dealer killed by the reaction;
    # that does not cancel the rest of the current effect program.
    add("0,0,3,-|40,0,0,THORNS_POWER:4:0|-", p_hp=3, e_powers=thorns, actions="P_STRIKE")
    add("80,0,3,THORNS_POWER:4:0;VULNERABLE_POWER:1:1|0,0,0,-|-",
        mode=1, p_powers=thorns, e_hp=4, actions=rounds(1))

    # 8 Plating cases: end-of-own-turn block is Unpowered; own-turn-start decay
    # skips round 1. The headless fixture starts at the first player action.
    for n, hp, powers in (
        (0, 80, "PLATING_POWER:3:0;DEXTERITY_POWER:5:0;FRAIL_POWER:1:0"),
        (1, 78, "PLATING_POWER:2:0;DEXTERITY_POWER:5:0;VULNERABLE_POWER:1:0"),
        (2, 73, "PLATING_POWER:1:0;DEXTERITY_POWER:5:0;VULNERABLE_POWER:1:0"),
        (3, 67, "DEXTERITY_POWER:5:0;VULNERABLE_POWER:1:0"),
    ):
        add(f"{hp},0,3,{powers}|40,0,1,-|-", mode=1,
            p_powers="PLATING_POWER:3,DEXTERITY_POWER:5,FRAIL_POWER:1", actions=rounds(n))
    for n, block, amount in ((0, 0, 3), (1, 3, 3), (2, 2, 2), (3, 1, 1)):
        add(f"80,0,3,-|40,{block},1,PLATING_POWER:{amount}:0|-",
            e_powers="PLATING_POWER:3", actions=rounds(n))

    # 6 Ritual cases: RitualPower.AfterApplied only marks a new enemy application.
    for n, hp, powers in (
        (0, 80, "-"),
        (1, 80, "RITUAL_POWER:2:0"),
        (2, 76, "RITUAL_POWER:2:0;STRENGTH_POWER:2:0"),
        (3, 70, "RITUAL_POWER:2:0;STRENGTH_POWER:4:0"),
    ):
        add(f"{hp},0,3,-|40,0,1,{powers}|-", mode=2, actions=rounds(n))
    for n, hp, strength in ((1, 80, 3), (2, 73, 6)):
        add(f"{hp},0,3,-|40,0,1,RITUAL_POWER:3:0;STRENGTH_POWER:{strength}:0|-",
            mode=2, e_powers="RITUAL_POWER:1", actions=rounds(n))

    # 12 orb cases: Dark accumulates into base evoke; Plasma ignores Focus and
    # cannot trigger after a lethal player-end passive prevents a new round.
    add("80,0,3,-|40,0,1,-|dark:6:6", orbs="dark")
    add("80,0,3,-|40,0,1,-|dark:6:12", orbs="dark", actions=rounds(1))
    add("80,0,3,FOCUS_POWER:2:0|40,0,1,-|dark:3:20",
        orbs="dark:3:10", p_powers="FOCUS_POWER:2", actions=rounds(2))
    add("80,0,3,FOCUS_POWER:-9:0|40,0,1,-|dark:6:6",
        orbs="dark", p_powers="FOCUS_POWER:-9", actions=rounds(2))
    add("80,0,3,-|40,0,1,-|plasma:1:2", orbs="plasma")
    add("80,0,4,FOCUS_POWER:2:0|40,0,1,-|plasma:1:2",
        orbs="plasma", p_powers="FOCUS_POWER:2", actions=rounds(2))
    add("80,0,6,FOCUS_POWER:-9:0|40,0,1,-|plasma:3:9",
        orbs="plasma:3:9", p_powers="FOCUS_POWER:-9", actions=rounds(1))
    add("80,0,3,FOCUS_POWER:2:0|39,0,1,-|lightning:3:8",
        orbs="lightning", p_powers="FOCUS_POWER:2", e_block=4, actions=rounds(1))
    add("79,0,3,FOCUS_POWER:2:0;VULNERABLE_POWER:1:0|40,0,1,-|frost:2:5",
        mode=1, orbs="frost", p_powers="FOCUS_POWER:2", actions=rounds(1))
    add("80,0,3,-|33,0,1,-|glass:2:8", orbs="glass", actions=rounds(2))
    add("80,0,3,FOCUS_POWER:-4:0|40,0,1,-|glass:4:8",
        orbs="glass", p_powers="FOCUS_POWER:-4", actions=rounds(1))
    add("80,2,3,-|0,0,0,-|plasma:1:2;dark:6:12;frost:2:5;lightning:3:8;glass:3:8",
        mode=1, orbs="plasma,dark,frost,lightning,glass", e_hp=3, actions=rounds(1))
    return rows


def tier2_vectors() -> list[tuple[str, Expected]]:
    rows: list[tuple[str, Expected]] = []

    def add(kind: str, entry: str, expected: dict[str, int | str], *, found: bool = True,
            param=0, asc=0, p_strength=0, e_hp=80, e_block=0, p_powers="", e_powers="") -> None:
        fields = ("TIER2_EFFECTS", kind, entry, param, asc, p_strength, e_hp, e_block,
                  p_powers, e_powers)
        rows.append(("\t".join(map(str, fields)), {**expected, "found": f"found={int(found)}"}))

    # 40 cards: canonical and upgraded OnPlay effects; the fixture does not pay
    # costs or move the played card. Empty choices use the first eligible card.
    strikes = ",".join(["STRIKE_IRONCLAD"] * 5)
    dagger_hand = ",".join(["STRIKE_IRONCLAD"] * 4 + ["DEFEND_IRONCLAD"])
    sword_hand = strikes + ",SOVEREIGN_BLADE"
    debris_hand = strikes + ",DEBRIS"
    dex_frail = "DEXTERITY_POWER:2,FRAIL_POWER:1"
    card_cases = (
        ("SUCKER_PUNCH", {}, (
            dict(e_hp=72, e_powers="WEAK_POWER:1:0", energy=5),
            dict(e_hp=70, e_powers="WEAK_POWER:2:0", energy=5),
        )),
        ("ASTRAL_PULSE", dict(e_block=9), (
            dict(e_hp=77, e_block=0, stars=2), dict(e_hp=73, e_block=0, stars=2),
        )),
        ("ACROBATICS", {}, (
            dict(hand_count=7, draw_count=7, discard_count=3),
            dict(hand_count=8, draw_count=6, discard_count=3),
        )),
        ("ADRENALINE", {}, (
            dict(energy=6, hand_count=7, draw_count=8),
            dict(energy=7, hand_count=7, draw_count=8),
        )),
        ("AFTERLIFE", {}, (dict(allies=2), dict(allies=2))),
        ("BALL_LIGHTNING", dict(p_strength=2, e_powers="THORNS_POWER:3"), (
            dict(p_hp=67, e_hp=71, orbs=1), dict(p_hp=67, e_hp=68, orbs=1),
        )),
        ("ASSASSINATE", dict(p_strength=2, e_block=4, e_powers="VULNERABLE_POWER:1"), (
            dict(e_hp=66, e_block=0, e_powers="VULNERABLE_POWER:2:0"),
            dict(e_hp=62, e_block=0, e_powers="VULNERABLE_POWER:3:0"),
        )),
        # Bloodletting.cs: explicit Unblockable | Unpowered | Move overrides the
        # dynamic variable for damage; DaggerThrow.cs: attack, then draw, then discard.
        ("BLOODLETTING", dict(p_strength=2), (
            dict(p_hp=67, energy=7), dict(p_hp=67, energy=8),
        )),
        ("BULWARK", {}, (
            dict(p_block=12, hand=sword_hand), dict(p_block=15, hand=sword_hand),
        )),
        ("BURNING_PACT", {}, (
            dict(hand_count=6, draw_count=8, exhaust_count=1),
            dict(hand_count=7, draw_count=7, exhaust_count=1),
        )),
        ("COLLISION_COURSE", {}, (
            dict(e_hp=70, hand=debris_hand), dict(e_hp=66, hand=debris_hand),
        )),
        ("CONSUMING_SHADOW", {}, (
            dict(orbs=2, p_powers="CONSUMING_SHADOW_POWER:1:0"),
            dict(orbs=3, p_powers="CONSUMING_SHADOW_POWER:1:0"),
        )),
        ("DASH", dict(p_powers=dex_frail), (
            dict(p_block=9, e_hp=70), dict(p_block=11, e_hp=67),
        )),
        ("DEADLY_POISON", dict(e_powers="POISON_POWER:2"), (
            dict(e_powers="POISON_POWER:7:0"), dict(e_powers="POISON_POWER:9:0"),
        )),
        ("DAGGER_THROW", {}, (
            dict(e_hp=71, hand=dagger_hand, draw_count=9, discard_count=3),
            dict(e_hp=68, hand=dagger_hand, draw_count=9, discard_count=3),
        )),
        ("FIGHT_ME", {}, (
            dict(e_hp=70, p_powers="STRENGTH_POWER:3:0", e_powers="STRENGTH_POWER:1:0"),
            dict(e_hp=68, p_powers="STRENGTH_POWER:4:0", e_powers="STRENGTH_POWER:1:0"),
        )),
        ("FRIENDSHIP", dict(p_strength=1), (
            dict(p_powers="STRENGTH_POWER:-1:0;FRIENDSHIP_POWER:1:0"),
            dict(p_powers="FRIENDSHIP_POWER:1:0"),
        )),
        ("NOT_YET", {}, (dict(p_hp=80), dict(p_hp=80))),
        ("SHADOW_STEP", {}, (
            dict(hand="-", hand_count=0, discard_count=7, p_powers="SHADOW_STEP_POWER:1:0"),
            dict(hand="-", hand_count=0, discard_count=7, p_powers="SHADOW_STEP_POWER:1:0"),
        )),
        ("RICOCHET", {}, (dict(e_hp=68), dict(e_hp=65))),
    )
    for entry, setup, upgrades in card_cases:
        for upgrade, expected in enumerate(upgrades):
            add("CARD", entry, expected, **setup, param=upgrade)

    # 16 potions: OnUse values, with powered-stat and existing-stack fixtures.
    potion_cases = (
        ("BLOCK_POTION", dict(p_powers=dex_frail), dict(p_block=12)),
        ("FIRE_POTION", dict(p_strength=2, p_powers="WEAK_POWER:2", e_hp=10, e_block=7,
                             e_powers="VULNERABLE_POWER:2,THORNS_POWER:3"),
         dict(p_hp=70, e_hp=0, e_block=0, in_progress=0)),
        ("SHIP_IN_A_BOTTLE", dict(p_powers=dex_frail),
         dict(p_block=10, p_powers="DEXTERITY_POWER:2:0;FRAIL_POWER:1:0;BLOCK_NEXT_TURN_POWER:10:0")),
        ("FYSH_OIL", dict(p_strength=-1), dict(p_powers="DEXTERITY_POWER:1:0")),
        ("HEART_OF_IRON", dict(p_powers="PLATING_POWER:2"), dict(p_powers="PLATING_POWER:9:0")),
        ("LIQUID_BRONZE", {}, dict(p_powers="THORNS_POWER:3:0")),
        ("KINGS_COURAGE", {}, dict(hand=sword_hand)),
        ("BONE_BREW", {}, dict(allies=2)),
        ("POTION_OF_BINDING", dict(e_powers="ARTIFACT_POWER:1"), dict(e_powers="VULNERABLE_POWER:1:0")),
        ("POISON_POTION", dict(e_powers="POISON_POWER:2"), dict(e_powers="POISON_POWER:8:0")),
        ("STAR_POTION", dict(param=7), dict(stars=5)),
        ("ENERGY_POTION", {}, dict(energy=7)),
        ("SWIFT_POTION", {}, dict(hand_count=8, draw_count=7)),
        # ShrinkPower's real stack type is dynamic; this row checks lookup and
        # parity without presenting the extractor's static amount as vanilla.
        ("BEETLE_JUICE", {}, dict(e_hp=80, in_progress=1)),
        ("POTION_OF_DOOM", dict(e_hp=20), dict(e_hp=20, e_powers="DOOM_POWER:33:0", in_progress=1)),
        ("MAZALETHS_GIFT", {}, dict(p_powers="RITUAL_POWER:1:0")),
    )
    for entry, setup, expected in potion_cases:
        add("POTION", entry, expected, **setup)

    # 20 monsters: fixed action parameters and last performed move, not initial HP
    # scaling. DeadlyEnemies is A9, while ToughEnemies is A8.
    for asc, hp in enumerate((60, 60, 60, 60, 60, 60, 60, 60, 60, 59, 59)):
        add("MONSTER", "ASSASSIN_RUBY_RAIDER", dict(p_hp=hp, move="KILLSHOT_MOVE"), param=1, asc=asc)
    for asc, hp, block in ((8, 63, 7), (9, 62, 8)):
        add("MONSTER", "BOWLBUG_EGG", dict(p_hp=hp, e_block=block, move="BITE_MOVE"),
            param=1, asc=asc, e_block=99)
    for asc, hp, block, strength in ((7, 51, 7, 1), (8, 51, 8, 1), (9, 49, 8, 2)):
        add("MONSTER", "SEAPUNK",
            dict(p_hp=hp, e_block=block, e_powers=f"STRENGTH_POWER:{strength}:0", move="BUBBLE_BURP_MOVE"),
            param=3, asc=asc)
    add("MONSTER", "CALCIFIED_CULTIST",
        dict(p_hp=61, e_powers="RITUAL_POWER:2:0;STRENGTH_POWER:2:0", move="DARK_STRIKE_MOVE"), param=2)
    # Model-specific RNG fixture: seed 424242's first two-way roll is 1,
    # picking LASH from the source branch order (THWACK, LASH).
    add("MONSTER", "SLITHERING_STRANGLER", dict(move="LASH", e_block=0), param=2)
    add("MONSTER", "SHRINKER_BEETLE", dict(p_hp=70, move="SHRINKER_MOVE"), param=1)
    add("MONSTER", "BIG_DUMMY", dict(p_hp=70, energy=3, draw_count=5, move="NOTHING", in_progress=1))

    # 4 absent Tier-2 rows: a missing monster still advances a round (but has no
    # move, unlike BigDummy), and a missing potion can still be supplied by Tier-1.
    add("CARD", "SHIV", dict(p_hp=70, energy=5, e_hp=80, hand=strikes, in_progress=1), found=False)
    add("POTION", "POWER_POTION", dict(p_hp=70, energy=5, e_hp=80, hand=strikes, in_progress=1), found=False)
    add("MONSTER", "VANTOM", dict(p_hp=70, energy=3, draw_count=5, move="", in_progress=1), found=False)
    add("POTION", "HEAL_POTION", dict(p_hp=80, e_hp=1, in_progress=1), found=False, e_hp=0)
    return rows


def tier2_card_vectors() -> list[tuple[str, Expected]]:
    rows: list[tuple[str, Expected]] = []
    # Canonical constructor / OnUpgrade metadata from reference/sts2 card classes.
    # The fixture passes it to both runtimes instead of reading expected values from the IR.
    metadata = {
        "CAPACITOR": ("power", "S", (1, 1), (0, 0)),
        "BULK_UP": ("power", "S", (2, 2), (0, 0)),
        "MODDED": ("skill", "S", (0, 0), (0, 0)),
        "BODY_SLAM": ("attack", "E", (1, 0), (0, 0)),
        "STACK": ("skill", "S", (1, 1), (0, 0)),
        "MIMIC": ("skill", "A", (1, 1), (1, 0)),
        "DEMONIC_SHIELD": ("skill", "A", (0, 0), (1, 0)),
        "ENTRENCH": ("skill", "S", (2, 1), (0, 0)),
        "DOUBLE_ENERGY": ("skill", "S", (1, 0), (1, 1)),
        "BUBBLE_BUBBLE": ("skill", "E", (1, 1), (0, 0)),
        "DISMANTLE": ("attack", "E", (1, 1), (0, 0)),
        "IMPATIENCE": ("skill", "S", (0, 0), (0, 0)),
        "FIGHT_ME": ("attack", "E", (2, 2), (0, 0)),
    }

    def add(entry: str, up: int, *, mode: str, energy: int = 5, p_block: int = 0,
            a_block: int = 0, discard: int = 0, filler: str = "-", capacity: int = 3,
            orbs: str = "-", p_powers: str = "-", a_powers: str = "-", e_powers: str = "-",
            player_hp: int = 70, enemy_hp: int = 80, final_energy: int | None = None,
            final_p_block: int | None = None, final_a_block: int | None = None,
            final_capacity: int | None = None, final_orbs: str | None = None,
            final_p_powers: str | None = None, final_a_powers: str | None = None,
            final_e_powers: str | None = None, drawn: int = 0, cost_delta: int = 0,
            ok: int = 1) -> None:
        kind, target, costs, exhausts = metadata[entry]
        cost, exhaust = costs[up], exhausts[up]
        fields = ("TIER2_CARD", mode, entry, up, cost, kind, target, exhaust, energy, p_block, a_block,
                  discard, filler, capacity, orbs, p_powers, a_powers, e_powers)

        # CardModel result piles and CardPileCmd draw contract; exact instance IDs and order.
        initial_hand = [f"999:{cost}"]
        if entry == "MODDED":
            initial_hand.append(f"998:{cost}")
        if filler != "-":
            initial_hand.append("1001:1")
        initial_draw = [f"{cid}:1" for cid in range(1011, 1018)]
        initial_discard = [f"{cid}:2" for cid in range(1021, 1021 + discard)]
        hand, draw, disc = initial_hand.copy(), initial_draw.copy(), initial_discard.copy()
        exh: list[str] = []
        play: list[str] = []
        if ok:
            played = f"999:{cost + cost_delta}"
            hand = hand[1:] + draw[:drawn]
            draw = draw[drawn:]
            if mode == "EFFECT":
                play.append(played)
            elif exhaust:
                exh.append(played)
            elif kind != "power":
                disc.append(played)
        after_energy = energy - (cost if ok and mode != "EFFECT" else 0)
        if mode == "ROUND":
            # End turn discards the remaining hand; the next turn draws five.
            disc.extend(hand)
            hand, draw = draw[:5], draw[5:]
            after_energy = 3
        elif mode == "NEXT":
            # The first combat was won with a real Strike; a fresh fight
            # clones the original deck in the scenario's fixed arrangement.
            hand, draw, disc = initial_hand, initial_draw, initial_discard
            after_energy = 3

        def powers(given: str, expected: str | None) -> str:
            if expected is not None:
                return expected
            return "-" if given == "-" else ";".join(f"{power}:0" for power in given.split(","))

        player = (player_hp, p_block if final_p_block is None else final_p_block,
                  after_energy if final_energy is None else final_energy,
                  capacity if final_capacity is None else final_capacity)
        ally = (70, a_block if final_a_block is None else final_a_block)
        projection = (str(ok), ",".join(map(str, player)), ",".join(map(str, ally)), f"{enemy_hp},0",
                      powers(p_powers, final_p_powers), powers(a_powers, final_a_powers),
                      powers(e_powers, final_e_powers), orbs if final_orbs is None else final_orbs,
                      *(",".join(pile) or "-" for pile in (hand, draw, disc, exh, play)))
        rows.append(("\t".join(map(str, fields)), "|".join(projection)))

    for mode in ("EFFECT", "PLAY"):
        for up in (0, 1):
            # OrbCmd caps at ten; RemoveCapacity removes occupied excess from
            # the tail, not by evoking it. In particular frost gives no block.
            add("CAPACITOR", up, mode=mode, final_capacity=(5, 6)[up])
            add("CAPACITOR", up, mode=mode, capacity=9, final_capacity=10)
            add("CAPACITOR", up, mode=mode, capacity=10, final_capacity=10)
            bulk_powers = f"STRENGTH_POWER:{(2, 3)[up]}:0;DEXTERITY_POWER:{(2, 3)[up]}:0"
            add("BULK_UP", up, mode=mode, capacity=2, orbs="lightning,frost",
                final_capacity=1, final_orbs="lightning", final_p_powers=bulk_powers)
            add("BULK_UP", up, mode=mode, capacity=2, orbs="lightning",
                final_capacity=1, final_p_powers=bulk_powers)
            add("BULK_UP", up, mode=mode, capacity=0, final_capacity=0, final_p_powers=bulk_powers)
            add("MODDED", up, mode=mode, final_capacity=4, drawn=(1, 2)[up], cost_delta=1)
            add("MODDED", up, mode=mode, capacity=10, final_capacity=10, drawn=(1, 2)[up], cost_delta=1)

            # CalculatedVar reads the current source quantity; Power hooks
            # then modify powered damage or block, not the observed operand.
            add("BODY_SLAM", up, mode=mode, p_block=7, a_block=13,
                p_powers="STRENGTH_POWER:2", enemy_hp=71)
            add("BODY_SLAM", up, mode=mode, a_block=13, enemy_hp=80)
            add("STACK", up, mode=mode, final_p_block=(0, 3)[up])
            add("STACK", up, mode=mode, discard=2, final_p_block=(2, 5)[up])
            add("MIMIC", up, mode=mode, p_block=3, a_block=7,
                p_powers="DEXTERITY_POWER:2,FRAIL_POWER:1", a_powers="DEXTERITY_POWER:9", final_p_block=9)
            add("MIMIC", up, mode=mode, p_block=3, final_p_block=3)
            # DemonicShield's first command is a one-HP loss, bypassing block and
            # Strength/Weak. Its second command uses the owner's block/dexterity,
            # but Frail belongs to the target: 7 + truncate((5 + 2) * .75) = 12.
            add("DEMONIC_SHIELD", up, mode=mode, p_block=5, a_block=7,
                p_powers="STRENGTH_POWER:5,WEAK_POWER:1,DEXTERITY_POWER:2",
                a_powers="DEXTERITY_POWER:9,FRAIL_POWER:1", player_hp=69, final_a_block=12)
            add("DEMONIC_SHIELD", up, mode=mode, a_block=7, player_hp=69, final_a_block=7)
            add("ENTRENCH", up, mode=mode, p_block=7, p_powers="DEXTERITY_POWER:8,FRAIL_POWER:1",
                final_p_block=14)

            add("DOUBLE_ENERGY", up, mode=mode, final_energy=(8, 10)[up] if mode == "PLAY" else 10)
            add("BUBBLE_BUBBLE", up, mode=mode, p_powers="POISON_POWER:2")
            add("BUBBLE_BUBBLE", up, mode=mode, e_powers="POISON_POWER:2",
                final_e_powers=f"POISON_POWER:{(11, 14)[up]}:0")
            # Artifact is only consumed if the conditional Apply is reached.
            add("BUBBLE_BUBBLE", up, mode=mode, e_powers="ARTIFACT_POWER:1")
            add("BUBBLE_BUBBLE", up, mode=mode, e_powers="POISON_POWER:2,ARTIFACT_POWER:1",
                final_e_powers="POISON_POWER:2:0")
            add("DISMANTLE", up, mode=mode, p_powers="VULNERABLE_POWER:1", enemy_hp=(72, 70)[up])
            add("DISMANTLE", up, mode=mode, e_powers="VULNERABLE_POWER:1", enemy_hp=(56, 50)[up])
            add("IMPATIENCE", up, mode=mode, drawn=(2, 3)[up])
            add("IMPATIENCE", up, mode=mode, filler="skill", discard=2, drawn=(2, 3)[up])
            add("IMPATIENCE", up, mode=mode, filler="attack", drawn=0)
            add("FIGHT_ME", up, mode=mode, enemy_hp=(70, 68)[up],
                final_p_powers=f"STRENGTH_POWER:{(3, 4)[up]}:0", final_e_powers="STRENGTH_POWER:1:0")

    # Zero-energy and exact-payment boundaries, and explicit combat duration.
    add("BODY_SLAM", 0, mode="PLAY", energy=0, p_block=7, ok=0)
    add("BODY_SLAM", 1, mode="PLAY", energy=0, p_block=7, enemy_hp=73)
    add("DOUBLE_ENERGY", 0, mode="PLAY", energy=1, final_energy=0)
    add("DOUBLE_ENERGY", 1, mode="PLAY", energy=0, final_energy=0)
    for up in (0, 1):
        add("MODDED", up, mode="ROUND", p_block=4, final_p_block=0, final_capacity=4,
            drawn=(1, 2)[up], cost_delta=1)
    add("MODDED", 0, mode="NEXT", filler="attack", p_block=4, a_block=7,
        orbs="frost", p_powers="DEXTERITY_POWER:2", a_powers="FRAIL_POWER:1",
        drawn=1, cost_delta=1, final_p_block=0, final_a_block=0, final_capacity=3, final_orbs="-",
        final_p_powers="-", final_a_powers="-")
    return rows


FIXED_VECTORS = lifecycle_vectors() + tier2_vectors() + tier2_card_vectors() + [
    ("EXPEDITION", "99,5,111,1,1,1,1|53,75,0,3,3,3,5,3,1,1,1,3|1,1,1,5,1,1,1,7,1,1|1,1,1,101,1,1|0,99,0,1"),
]


def matches_expected(output: str, expected: Expected) -> bool:
    if isinstance(expected, str):
        return output == expected
    try:
        player, enemy, p_powers, e_powers, hand, found = output.split("|")
        player_keys = ("p_hp", "p_block", "energy", "stars", "hand_count", "draw_count",
                       "discard_count", "exhaust_count", "orbs", "allies")
        enemy_keys = ("e_hp", "e_block", "move", "in_progress")
        actual = dict(zip(player_keys, player.split(","), strict=True))
        actual.update(zip(enemy_keys, enemy.split(","), strict=True))
    except ValueError:
        return False
    actual.update(p_powers=p_powers, e_powers=e_powers, hand=hand, found=found)
    return all(actual[key] == str(value) for key, value in expected.items())


def main() -> int:
    if not LEAN_BIN.exists():
        raise SystemExit(f"Lean binary not found: {LEAN_BIN} (run `lake build` first)")
    if not CS_DLL.exists():
        raise SystemExit(f"C# oracle not found: {CS_DLL} (run `dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj` first)")

    work_root = ROOT / ".agent_works"
    work_root.mkdir(exist_ok=True)
    vectors = generate_vectors()
    expected_by_vector = dict(FIXED_VECTORS)
    with tempfile.TemporaryDirectory(dir=work_root, prefix="diff-") as tmpdir:
        work_dir = pathlib.Path(tmpdir)
        tsv_path = work_dir / "vectors.tsv"
        tsv_path.write_text("\n".join(vectors) + "\n", encoding="utf-8")
        lean_proc = subprocess.run([str(LEAN_BIN), "--diff", tsv_path], capture_output=True, text=True, check=True)
        cs_proc = subprocess.run(["dotnet", str(CS_DLL), "--diff", tsv_path], capture_output=True, text=True, check=True)

        # MOD_SORT on "" emits an empty line; preserve the 1:1 correspondence.
        lean_raw = lean_proc.stdout.splitlines()
        cs_raw = cs_proc.stdout.splitlines()
        if len(lean_raw) != len(vectors) or len(cs_raw) != len(vectors):
            print(f"LINE COUNT MISMATCH: vectors={len(vectors)}, lean={len(lean_raw)}, csharp={len(cs_raw)}")
            return 1

        family_counts: Counter[str] = Counter()
        mismatches = 0
        for idx, (vec, l_out, c_out) in enumerate(zip(vectors, lean_raw, cs_raw)):
            fam = vec.split("\t", 1)[0]
            family_counts[fam] += 1
            expected = expected_by_vector.get(vec)
            unexpected = [] if expected is None else [
                side for side, out in (("Lean", l_out), (".NET", c_out)) if not matches_expected(out, expected)
            ]
            if l_out != c_out or unexpected:
                mismatches += 1
                if mismatches <= 15 or unexpected:
                    print(f"[MISMATCH #{idx} {fam}] input={vec!r}\n  Lean: {l_out!r}\n  .NET: {c_out!r}")
                    if expected is not None:
                        print(f"  Expected: {expected!r}")
                    if unexpected:
                        print(f"  Failed expectation: {', '.join(unexpected)}")

        print("Differential test summary (.NET 9 Sts2Oracle vs Lean 4 sts2sim):")
        for fam, cnt in sorted(family_counts.items()):
            print(f"  {fam:14s}: {cnt} vectors")
        print(f"Total vectors: {len(vectors)}, mismatches: {mismatches}")
        if mismatches != 0:
            return 1

        # Bi-directional C# <-> Lean JSON trace file handoff verification
        cs_trace = work_dir / "cs_export.json"
        lean_trace = work_dir / "lean_export.json"
        subprocess.run(["dotnet", str(CS_DLL), "--export-sample-trace", cs_trace], capture_output=True, text=True, check=True)
        lean_inspect = subprocess.run([str(LEAN_BIN), "--inspect", cs_trace, "--verify", "--viewer", "2"], capture_output=True, text=True, check=True)
        if "ChecksumsVerified=true" not in lean_inspect.stdout:
            print(f"Bi-directional C# -> Lean verification failed:\n{lean_inspect.stdout}\n{lean_inspect.stderr}")
            return 1
        subprocess.run([str(LEAN_BIN), "--export-sample-trace", lean_trace], capture_output=True, text=True, check=True)
        cs_verify = subprocess.run(["dotnet", str(CS_DLL), "--verify-trace", lean_trace], capture_output=True, text=True, check=True)
        if "VERIFIED_OK" not in cs_verify.stdout:
            print(f"Bi-directional Lean -> C# verification failed:\n{cs_verify.stdout}\n{cs_verify.stderr}")
            return 1

    print("Bi-directional C# <-> Lean JSON trace handoff: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

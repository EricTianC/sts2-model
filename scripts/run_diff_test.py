#!/usr/bin/env python3
"""
Cross-language `.NET 9` <-> Lean 4 differential tester for Slay the Spire 2 logic model.

Generates 850 randomized and adversarial edge-case test vectors across 12 test families:
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

Run via: `uv run python scripts/run_diff_test.py`
"""
from __future__ import annotations

import json
import os
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

    return rows


def main() -> int:
    if not LEAN_BIN.exists():
        raise SystemExit(f"Lean binary not found: {LEAN_BIN} (run `lake build` first)")
    if not CS_DLL.exists():
        raise SystemExit(f"C# oracle not found: {CS_DLL} (run `dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj` first)")

    vectors = generate_vectors()
    with tempfile.NamedTemporaryFile("w", suffix=".tsv", delete=False, encoding="utf-8") as f:
        tsv_path = f.name
        f.write("\n".join(vectors) + "\n")

    try:
        lean_proc = subprocess.run([str(LEAN_BIN), "--diff", tsv_path], capture_output=True, text=True, check=True)
        cs_proc = subprocess.run(["dotnet", str(CS_DLL), "--diff", tsv_path], capture_output=True, text=True, check=True)
    finally:
        os.unlink(tsv_path)

    lean_lines = [ln.strip() for ln in lean_proc.stdout.splitlines() if ln.strip() != "" or len(vectors) == 0]
    # Note: MOD_SORT on "" emits an empty line, so splitlines(keepends=False) preserves line count 1:1
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
        if l_out != c_out:
            mismatches += 1
            if mismatches <= 15:
                print(f"[MISMATCH #{idx} {fam}] input={vec!r}\n  Lean: {l_out!r}\n  .NET: {c_out!r}")

    print("Differential test summary (.NET 9 Sts2Oracle vs Lean 4 sts2sim):")
    for fam, cnt in sorted(family_counts.items()):
        print(f"  {fam:14s}: {cnt} vectors")
    print(f"Total vectors: {len(vectors)}, mismatches: {mismatches}")
    if mismatches != 0:
        return 1

    # Bi-directional C# <-> Lean JSON trace file handoff verification
    with tempfile.TemporaryDirectory() as tmpdir:
        cs_trace = os.path.join(tmpdir, "cs_export.json")
        lean_trace = os.path.join(tmpdir, "lean_export.json")
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

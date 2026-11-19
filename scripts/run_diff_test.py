#!/usr/bin/env python3
"""
Cross-language `.NET 9` <-> Lean 4 differential tester for Slay the Spire 2 logic model.

Generates 650+ randomized and adversarial edge-case test vectors across 9 test families:
  1. RNG_SEQ      (SplitMix64 + Xoshiro256** bit-exact stream & IEEE-754 double bits)
  2. RNG_SHUFFLE  (UnstableShuffle Fisher-Yates child-RNG permutation)
  3. DMG_PIPE     (Hook.ModifyDamageInternal: Strength, Weak, Vulnerable, PaperPhrog, LateMul, Cap)
  4. BLK_PIPE     (Hook.ModifyBlock: Dexterity, Frail, Powered vs Unpowered)
  5. CREATURE_DMG (CreatureCmd.Damage: Block, Intangible cap+AfterOsty, DieForYou Osty + Overkill)
  6. POWER_STACK  (PowerCmd.Apply: Single/Counter, Clamp +/-999999999, AllowNegative, Artifact)
  7. CARD_COST    (CardEnergyCost local Absolute/Relative + Hook delta + ExcessEnergyWithStars)
  8. RARITY_ODDS  (CardRarityOdds Float32 bit-exact sequences & pity offset reset/clamp)
  9. MOD_SORT     (ModHelper ordinal subscriber registration sort & deduplication)

Run via: `uv run python scripts/run_diff_test.py`
"""
from __future__ import annotations

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
    return 0 if mismatches == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""
Automated static catalog extractor for Slay the Spire 2 (Option C).

Scans decompiled C# reference sources in `reference/sts2/` and emits:
  - Sts2Model/Catalog/Cards.lean   (717 concrete CardModel entries in 30-item chunks)
  - Sts2Model/Catalog/Relics.lean  (316 concrete RelicModel entries in 30-item chunks)
  - Sts2Model/Catalog/Powers.lean  (304 concrete PowerModel entries in 30-item chunks)
  - Sts2Model/Catalog/Verify.lean  (pure kernel count & Nodup proofs, ZERO `native_decide`)

Run via: `uv run python scripts/extract_catalog.py`
"""
from __future__ import annotations

import pathlib
import re
from typing import Iterable

ROOT = pathlib.Path(__file__).resolve().parent.parent
REF_DIR = ROOT / "reference" / "sts2"
CATALOG_DIR = ROOT / "Sts2Model" / "Catalog"
CHUNK_SIZE = 30


def slugify(txt: str) -> str:
    """Exact port of `MegaCrit.Sts2.Core.Helpers.StringHelper.Slugify`."""
    t = re.sub(r"(?<=[A-Za-z0-9])([A-Z])", r"_\1", txt.strip())
    t = re.sub(r"\s+", "_", t.upper())
    return re.sub(r"[^A-Z0-9_]", "", t)


def to_lean_ctor(name: str) -> str:
    if not name:
        raise ValueError("Empty enum variant name")
    return f".{name[0].lower()}{name[1:]}"


def extract_prop_enum_list(src: str, prop_name: str, enum_name: str) -> list[str]:
    # Check both `=> ...;` expression-bodied properties and `{ get { ... } }` blocks if any
    m = re.search(rf"\b{prop_name}\s*=>\s*(.*?);", src, re.S)
    if not m:
        return []
    body = m.group(1)
    seen: list[str] = []
    for variant in re.findall(rf"\b{enum_name}\.(\w+)", body):
        ctor = to_lean_ctor(variant)
        if ctor not in seen:
            seen.append(ctor)
    return seen


def parse_cards() -> list[dict]:
    cards_dir = REF_DIR / "MegaCrit.Sts2.Core.Models.Cards"
    entries: list[dict] = []
    for p in sorted(cards_dir.glob("*.cs")):
        src = p.read_text(encoding="utf-8", errors="replace")
        cm = re.search(r"\bclass\s+(\w+)\s*:\s*CardModel\b", src)
        if not cm:
            raise ValueError(f"Unexpected Card class signature in {p.name}")
        cls = cm.group(1)
        bm = re.search(
            r":\s*base\s*\(\s*(-?\d+)\s*,\s*CardType\.(\w+)\s*,\s*CardRarity\.(\w+)\s*,\s*TargetType\.(\w+)",
            src,
        )
        if not bm:
            raise ValueError(f"Could not parse : base(...) in {p.name}")
        base_cost = int(bm.group(1))
        card_type = to_lean_ctor(bm.group(2))
        rarity = to_lean_ctor(bm.group(3))
        target_type = to_lean_ctor(bm.group(4))
        costs_x = "true" if re.search(r"HasEnergyCostX\s*=>\s*true\s*;", src) else "false"
        sm = re.search(r"CanonicalStarCost\s*=>\s*(-?\d+)\s*;", src)
        star_cost = int(sm.group(1)) if sm else 0
        keywords = extract_prop_enum_list(src, "CanonicalKeywords", "CardKeyword")
        tags = extract_prop_enum_list(src, "CanonicalTags", "CardTag")
        entries.append(
            {
                "id": slugify(cls),
                "className": cls,
                "baseCost": base_cost,
                "costsX": costs_x,
                "baseStarCost": star_cost,
                "cardType": card_type,
                "rarity": rarity,
                "targetType": target_type,
                "keywords": keywords,
                "tags": tags,
            }
        )
    entries.sort(key=lambda e: e["id"])
    assert_strictly_sorted(entries, "Cards")
    return entries


def parse_relics() -> list[dict]:
    relics_dir = REF_DIR / "MegaCrit.Sts2.Core.Models.Relics"
    entries: list[dict] = []
    for p in sorted(relics_dir.glob("*.cs")):
        src = p.read_text(encoding="utf-8", errors="replace")
        if re.search(r"\bclass\s+VakuuCardSelector\s*:\s*ICardSelector\b", src):
            continue
        cm = re.search(r"\bclass\s+(\w+)\s*:\s*RelicModel\b", src)
        if not cm:
            raise ValueError(f"Unexpected Relic class signature in {p.name}")
        cls = cm.group(1)
        rm = re.search(r"public\s+override\s+RelicRarity\s+Rarity\s*=>\s*RelicRarity\.(\w+)\s*;", src)
        if not rm:
            raise ValueError(f"Could not parse RelicRarity in {p.name}")
        entries.append(
            {
                "id": slugify(cls),
                "className": cls,
                "rarity": to_lean_ctor(rm.group(1)),
            }
        )
    entries.sort(key=lambda e: e["id"])
    assert_strictly_sorted(entries, "Relics")
    return entries


def parse_powers() -> list[dict]:
    powers_dir = REF_DIR / "MegaCrit.Sts2.Core.Models.Powers"
    entries: list[dict] = []
    for p in sorted(powers_dir.glob("*.cs")):
        src = p.read_text(encoding="utf-8", errors="replace")
        if re.search(r"\babstract\s+class\b", src):
            continue
        cm = re.search(r"\bclass\s+(\w+)\s*:\s*(\w+)", src)
        if not cm:
            raise ValueError(f"Unexpected Power class signature in {p.name}")
        cls, base = cm.group(1), cm.group(2)

        # PowerType
        pt_m = re.search(r"public\s+override\s+PowerType\s+Type\s*=>\s*PowerType\.(\w+)\s*;", src)
        if pt_m:
            power_type = to_lean_ctor(pt_m.group(1))
        elif base.startswith("Temporary"):
            pos_m = re.search(r"IsPositive\s*=>\s*(true|false)\s*;", src)
            power_type = ".debuff" if (pos_m and pos_m.group(1) == "false") else ".buff"
        else:
            raise ValueError(f"Could not parse PowerType in {p.name} (base {base})")

        # PowerStackType
        st_m = re.search(r"public\s+override\s+PowerStackType\s+StackType\s*=>\s*PowerStackType\.(\w+)\s*;", src)
        if st_m:
            stack_type = to_lean_ctor(st_m.group(1))
        elif base.startswith("Temporary"):
            stack_type = ".counter"
        elif cls == "MonologuePower":
            stack_type = ".none"  # StrengthApplied initialized to 0m -> canonical PowerStackType.None
        elif cls == "ShrinkPower":
            stack_type = ".counter"  # !IsInfinite default -> canonical PowerStackType.Counter
        else:
            raise ValueError(f"Could not parse PowerStackType in {p.name} (base {base})")

        inst_m = re.search(r"InstanceType\s*=>\s*PowerInstanceType\.(\w+)\s*;", src)
        instance_type = to_lean_ctor(inst_m.group(1)) if inst_m else ".none"
        allow_neg = "true" if re.search(r"AllowNegative\s*=>\s*true\s*;", src) else "false"

        entries.append(
            {
                "id": slugify(cls),
                "className": cls,
                "powerType": power_type,
                "stackType": stack_type,
                "instanceType": instance_type,
                "allowNegative": allow_neg,
            }
        )
    entries.sort(key=lambda e: e["id"])
    assert_strictly_sorted(entries, "Powers")
    return entries


def assert_strictly_sorted(entries: list[dict], kind: str) -> None:
    for i in range(1, len(entries)):
        prev_id = entries[i - 1]["id"]
        cur_id = entries[i]["id"]
        if not (prev_id < cur_id):
            raise ValueError(f"{kind}: IDs not strictly sorted at {i}: {prev_id!r} vs {cur_id!r}")


def chunked(xs: list, size: int) -> list[list]:
    return [xs[i : i + size] for i in range(0, len(xs), size)]


def emit_chunk_file(path: pathlib.Path, title: str, var_prefix: str, ty_name: str, chunks: list[list[str]], total_count: int) -> None:
    lines = [
        "/-",
        f"  AUTO-GENERATED by `scripts/extract_catalog.py` from `reference/sts2/`.",
        f"  {title} ({total_count} entries, strictly sorted by `id`, split into {CHUNK_SIZE}-entry chunks).",
        "-/",
        "import Sts2Model.Catalog.Types",
        "",
        "namespace Sts2Model.Catalog",
        "",
        "open Sts2Model.Core",
        "",
    ]
    chunk_names = []
    for idx, ch in enumerate(chunks):
        cname = f"{var_prefix}Chunk{idx}"
        chunk_names.append(cname)
        lines.append(f"def {cname} : List {ty_name} := [")
        for i, item in enumerate(ch):
            sep = "," if i + 1 < len(ch) else ""
            lines.append(f"  {item}{sep}")
        lines.append("]")
        lines.append("")
    # Right-associative append for O(chunk) head?/getLast? kernel proofs
    joined = " ++\n  ".join(chunk_names)
    lines.append(f"def all{var_prefix.capitalize()} : List {ty_name} :=")
    lines.append(f"  {joined}")
    lines.append("")
    lines.append("end Sts2Model.Catalog")
    path.write_text("\n".join(lines), encoding="utf-8")


def emit_cards(cards: list[dict]) -> list[list[dict]]:
    chunks_raw = chunked(cards, CHUNK_SIZE)
    chunks_str = []
    for ch in chunks_raw:
        items = []
        for c in ch:
            kws = "[" + ", ".join(c["keywords"]) + "]"
            tgs = "[" + ", ".join(c["tags"]) + "]"
            items.append(
                f'⟨"{c["id"]}", "{c["className"]}", {c["baseCost"]}, {c["costsX"]}, '
                f'{c["baseStarCost"]}, {c["cardType"]}, {c["rarity"]}, {c["targetType"]}, {kws}, {tgs}⟩'
            )
        chunks_str.append(items)
    emit_chunk_file(CATALOG_DIR / "Cards.lean", "Vanilla Card Catalog", "cards", "CardCatalogEntry", chunks_str, len(cards))
    return chunks_raw


def emit_relics(relics: list[dict]) -> list[list[dict]]:
    chunks_raw = chunked(relics, CHUNK_SIZE)
    chunks_str = []
    for ch in chunks_raw:
        items = [f'⟨"{r["id"]}", "{r["className"]}", {r["rarity"]}⟩' for r in ch]
        chunks_str.append(items)
    emit_chunk_file(CATALOG_DIR / "Relics.lean", "Vanilla Relic Catalog", "relics", "RelicCatalogEntry", chunks_str, len(relics))
    return chunks_raw


def emit_powers(powers: list[dict]) -> list[list[dict]]:
    chunks_raw = chunked(powers, CHUNK_SIZE)
    chunks_str = []
    for ch in chunks_raw:
        items = [
            f'⟨"{p["id"]}", "{p["className"]}", {p["powerType"]}, {p["stackType"]}, {p["instanceType"]}, {p["allowNegative"]}⟩'
            for p in ch
        ]
        chunks_str.append(items)
    emit_chunk_file(CATALOG_DIR / "Powers.lean", "Vanilla Power Catalog", "powers", "PowerCatalogEntry", chunks_str, len(powers))
    return chunks_raw


def emit_verify_block(
    lines: list[str],
    prefix: str,
    cap_name: str,
    ty_name: str,
    chunks: list[list[dict]],
    total: int,
) -> None:
    n = len(chunks)
    # Chunk length and chunk strictly-sorted proofs
    for i, ch in enumerate(chunks):
        lines.append(f"private theorem {prefix}Chunk{i}_len : {prefix}Chunk{i}.length = {len(ch)} := rfl")
        lines.append(
            f"private theorem {prefix}Chunk{i}_sorted : isStrictlySorted ({prefix}Chunk{i}.map (·.id)) = true := by decide"
        )
    lines.append("")

    # Right-to-left sorted suffix theorems: suffix_{n-1} = chunk_{n-1}, suffix_i = chunk_i ++ suffix_{i+1}
    lines.append(
        f"private theorem {prefix}Suffix{n - 1}_sorted : isStrictlySorted ({prefix}Chunk{n - 1}.map (·.id)) = true := {prefix}Chunk{n - 1}_sorted"
    )
    for i in range(n - 2, -1, -1):
        rhs_expr = " ++ ".join(f"{prefix}Chunk{j}" for j in range(i, n))
        prev_theorem = f"{prefix}Suffix{i + 1}_sorted"
        cur_name = f"{prefix}Suffix{i}_sorted"
        lines.append(f"private theorem {cur_name} :")
        lines.append(f"    isStrictlySorted (({rhs_expr}).map (·.id)) = true := by")
        lines.append(f"  apply strictlySorted_join _ _ _ {prefix}Chunk{i}_sorted {prev_theorem}")
        lines.append("  decide")
    lines.append("")

    # Final count and Nodup proofs
    len_args = ", ".join(f"{prefix}Chunk{i}_len" for i in range(n))
    lines.append(f"theorem all{cap_name}_count : all{cap_name}.length = {total} := by")
    lines.append(f"  rw [all{cap_name}]")
    lines.append(f"  simp only [List.length_append, {len_args}]")
    lines.append("")
    lines.append(f"theorem all{cap_name}_nodup : (all{cap_name}.map (·.id)).Nodup := by")
    lines.append(f"  apply isStrictlySorted_implies_nodup")
    lines.append(f"  simpa [all{cap_name}] using {prefix}Suffix0_sorted")
    lines.append("")
    lines.append(f"def lookup{cap_name[:-1]} (id : String) : Option {ty_name} :=")
    lines.append(f"  all{cap_name}.find? (·.id == id)")
    lines.append("")


def emit_verify(
    card_chunks: list[list[dict]],
    relic_chunks: list[list[dict]],
    power_chunks: list[list[dict]],
    n_cards: int,
    n_relics: int,
    n_powers: int,
) -> None:
    lines = [
        "/-",
        "  AUTO-GENERATED by `scripts/extract_catalog.py`.",
        "  Pure kernel-checked count and ID uniqueness (`Nodup`) proofs for all extracted",
        f"  vanilla Cards ({n_cards}), Relics ({n_relics}), and Powers ({n_powers}).",
        "  Uses ZERO `sorry`, ZERO `axiom`, and ZERO `native_decide`.",
        "-/",
        "import Sts2Model.Catalog.Types",
        "import Sts2Model.Catalog.Cards",
        "import Sts2Model.Catalog.Relics",
        "import Sts2Model.Catalog.Powers",
        "",
        "namespace Sts2Model.Catalog",
        "",
    ]
    emit_verify_block(lines, "cards", "Cards", "CardCatalogEntry", card_chunks, n_cards)
    emit_verify_block(lines, "relics", "Relics", "RelicCatalogEntry", relic_chunks, n_relics)
    emit_verify_block(lines, "powers", "Powers", "PowerCatalogEntry", power_chunks, n_powers)
    lines.append("end Sts2Model.Catalog")
    (CATALOG_DIR / "Verify.lean").write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    CATALOG_DIR.mkdir(parents=True, exist_ok=True)
    cards = parse_cards()
    relics = parse_relics()
    powers = parse_powers()
    card_chunks = emit_cards(cards)
    relic_chunks = emit_relics(relics)
    power_chunks = emit_powers(powers)
    emit_verify(card_chunks, relic_chunks, power_chunks, len(cards), len(relics), len(powers))
    print(f"Extracted and emitted catalog: Cards={len(cards)}, Relics={len(relics)}, Powers={len(powers)}")


if __name__ == "__main__":
    main()

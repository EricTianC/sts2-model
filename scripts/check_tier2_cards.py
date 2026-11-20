#!/usr/bin/env python3
"""Reconcile the full Tier-2 manifest with the independent card catalog and Lean table."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from extract_catalog import ROOT, parse_cards, to_lean_ctor

MANIFEST = ROOT / "docs/tier2_cards.json"
TABLE = ROOT / "Sts2Model/Sim/Generated/Cards.lean"
SOURCE_DIR = "reference/sts2/MegaCrit.Sts2.Core.Models.Cards/"
TABLE_ENTRY = re.compile(r'^  \{ id := "([A-Z0-9_]+)", baseOps := (.*), upgradedOps := (.*) \},?$', re.M)

# Canonical costs and Exhaust state from the original constructors and OnUpgrade methods.
CONTINUATION = {
    "BODY_SLAM": (1, 0, False, False),
    "BUBBLE_BUBBLE": (1, 1, False, False),
    "BULK_UP": (2, 2, False, False),
    "CAPACITOR": (1, 1, False, False),
    "DEMONIC_SHIELD": (0, 0, True, False),
    "DISMANTLE": (1, 1, False, False),
    "DOUBLE_ENERGY": (1, 0, True, True),
    "ENTRENCH": (2, 1, False, False),
    "FIGHT_ME": (2, 2, False, False),
    "IMPATIENCE": (0, 0, False, False),
    "MIMIC": (1, 1, True, False),
    "MODDED": (0, 0, False, False),
    "STACK": (1, 1, False, False),
}


def index_ordered(rows, label: str) -> dict:
    result = {}
    previous = ""
    for card_id, row in rows:
        if card_id in result:
            raise ValueError(f"{label}: duplicate ID {card_id}")
        if card_id <= previous:
            raise ValueError(f"{label}: {card_id} is not sorted after {previous}")
        result[card_id] = row
        previous = card_id
    return result


def load_manifest(path: Path) -> dict:
    rows = json.loads(path.read_text(encoding="utf-8"))
    return index_ordered(((row["id"], row) for row in rows), str(path))


def load_table(path: Path) -> dict:
    matches = TABLE_ENTRY.findall(path.read_text(encoding="utf-8"))
    if not matches:
        raise ValueError(f"No generated card entries in {path}")
    return index_ordered(((card_id, (base, upgraded)) for card_id, base, upgraded in matches), str(path))


def check_ids(expected: set[str], actual: set[str], label: str) -> None:
    if expected != actual:
        raise ValueError(f"{label}: missing {sorted(expected - actual)}; extra {sorted(actual - expected)}")


def lean_list(ops: list[str]) -> str:
    return "[ " + ", ".join(ops) + " ]" if ops else "[]"


def check_manifest(rows: dict, table: dict) -> None:
    catalog = {row["id"]: row for row in parse_cards()}
    check_ids(set(catalog), set(rows), "Independent catalog vs. manifest")
    generated = set()
    for card_id, row in rows.items():
        item = catalog[card_id]
        if row["source"] != SOURCE_DIR + item["className"] + ".cs":
            raise ValueError(f"{card_id}: unexpected source {row['source']}")
        metadata = row["metadata"]
        actual = {
            "baseCost": metadata["baseCost"],
            "costsX": "true" if metadata["costsX"] else "false",
            "baseStarCost": metadata["baseStarCost"],
            "cardType": to_lean_ctor(metadata["cardType"]),
            "rarity": to_lean_ctor(metadata["rarity"]),
            "targetType": to_lean_ctor(metadata["targetType"]),
            "keywords": [to_lean_ctor(x) for x in metadata["keywords"]],
            "tags": [to_lean_ctor(x) for x in metadata["tags"]],
        }
        for key, value in actual.items():
            if value != item[key]:
                raise ValueError(f"{card_id}: metadata {key}: catalog {item[key]!r}, manifest {value!r}")
        if row["status"] == "generated":
            if "reason" in row or not (row["baseOps"] or row["upgradedOps"]) or not row["upgradedMetadata"]:
                raise ValueError(f"{card_id}: incomplete or ambiguous generated entry")
            generated.add(card_id)
            program = lean_list(row["baseOps"]), lean_list(row["upgradedOps"])
            if card_id in table and program != table[card_id]:
                raise ValueError(f"{card_id}: manifest programs differ from the generated Lean table")
        elif row["status"] == "skipped":
            reason = row["reason"]
            if (any(key in row for key in ("baseOps", "upgradedOps", "upgradedMetadata"))
                    or not reason["code"] or not reason["detail"]
                    or min(reason["location"]["line"], reason["location"]["column"]) < 1):
                raise ValueError(f"{card_id}: incomplete or ambiguous skipped entry")
        else:
            raise ValueError(f"{card_id}: unknown status {row['status']!r}")
    check_ids(set(table), generated, "Lean table vs. manifest generated IDs")
    print(f"Reconciled {len(rows)} cards: {len(generated)} generated, {len(rows) - len(generated)} skipped.")


def check_continuation(rows: dict) -> None:
    for card_id, expected in CONTINUATION.items():
        row = rows.get(card_id)
        if row is None or row["status"] != "generated":
            raise ValueError(f"Continuation card {card_id} was not generated")
        base = row["metadata"]
        upgraded = row["upgradedMetadata"]
        actual = (base["baseCost"], upgraded["cost"], "Exhaust" in base["keywords"], "Exhaust" in upgraded["keywords"])
        if actual != expected:
            raise ValueError(f"{card_id}: (base cost, upgraded cost, base Exhaust, upgraded Exhaust): expected {expected}, got {actual}")
    rejected = {
        "DUALCAST": "conditional_branch_in_body",
        "PERFECTED_STRIKE": "unsupported_dynamic_var",
        "THE_MAGICIAN": "unsupported_orb_channel",
    }
    for card_id, code in rejected.items():
        row = rows.get(card_id)
        if row is None or row["status"] != "skipped" or row["reason"]["code"] != code:
            raise ValueError(f"{card_id}: expected whole-card rejection for {code}")
    print("Continuation metadata and whole-card rejection controls matched.")


def compare(before: dict, after: dict) -> None:
    for card_id in sorted(before.keys() | after.keys()):
        if card_id not in before:
            print(f"+ {card_id} ({after[card_id]['status']})")
        elif card_id not in after:
            print(f"- {card_id} ({before[card_id]['status']})")
        else:
            old, new = before[card_id], after[card_id]
            for field in sorted(old.keys() | new.keys()):
                if old.get(field) != new.get(field):
                    print(f"~ {card_id} {field}: {old.get(field)!r} -> {new.get(field)!r}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare", type=Path, metavar="PREVIOUS_JSON", help="report changes against an older generated manifest")
    parser.add_argument("--require-generated-from", type=Path, metavar="PREVIOUS_CARDS_LEAN", help="reject lost generated IDs from a baseline Lean table")
    parser.add_argument("--check-continuation", action="store_true", help="enforce the current continuation cards' cost/Exhaust metadata and known rejections")
    args = parser.parse_args()
    try:
        rows = load_manifest(MANIFEST)
        table = load_table(TABLE)
        check_manifest(rows, table)
        if args.require_generated_from:
            baseline = load_table(args.require_generated_from)
            if missing := sorted(baseline.keys() - table.keys()):
                raise ValueError(f"Previously generated cards lost: {missing}")
            print(f"Retained all {len(baseline)} baseline generated IDs.")
        if args.check_continuation:
            check_continuation(rows)
        if args.compare:
            compare(load_manifest(args.compare), rows)
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()

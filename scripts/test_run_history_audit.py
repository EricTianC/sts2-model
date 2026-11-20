"""Test the native history CLI with anonymous fixtures after `lake build sts2sim`."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SIM = ROOT / ".lake" / "build" / "bin" / "sts2sim"
# Adjacent unsigned 64-bit IDs cannot be distinguished after conversion to a float.
PLAYER_1 = (1 << 64) - 2
PLAYER_2 = (1 << 64) - 1
LOCALIZED_TEXT = "UNICODE-LOCALE-ONLY 길 잃은 승객"


def player_stats(player_id, hp, max_hp, gold, **changes):
    return {
        "player_id": player_id,
        "current_hp": hp,
        "max_hp": max_hp,
        "current_gold": gold,
        "damage_taken": 0,
        "hp_healed": 0,
        "max_hp_lost": 0,
        "max_hp_gained": 0,
        "gold_gained": 0,
        "gold_spent": 0,
        "gold_lost": 0,
        "gold_stolen": 0,
        **changes,
    }


def room(kind, model_id, turns=0, **fields):
    return {"room_type": kind, "model_id": model_id, "turns_taken": turns, **fields}


def point(kind, rooms, *players):
    return {"map_point_type": kind, "rooms": rooms, "player_stats": list(players)}


def native_history():
    offered = {"id": "CARD.ANON_PICK", "current_upgrade_level": 1}
    return {
        "schema_version": 9,
        "build_id": "v0.107.1-fixture",
        "win": True,
        "was_abandoned": False,
        "players": [
            {"id": PLAYER_1, "character": "CHARACTER.SILENT"},
            {"id": PLAYER_2, "character": "CHARACTER.DEFECT"},
        ],
        "acts": ["ACT.ANON_ACT_ONE", "ACT.ANON_ACT_TWO"],
        "map_point_history": [
            [
                point(
                    "ancient", [room("event", "EVENT.ANON_START")],
                    player_stats(PLAYER_1, 13, 20, 19, damage_taken=900, gold_gained=900),
                    player_stats(PLAYER_2, 23, 31, 80),
                ),
                point(
                    "unknown", [
                        room("event", "EVENT.ANON_EVENT"),
                        room("monster", "ENCOUNTER.ANON_FIGHT", 4, monster_ids=["MONSTER.ANON"]),
                    ],
                    player_stats(
                        PLAYER_2, 20, 30, 77, damage_taken=4, hp_healed=1, max_hp_lost=2,
                        max_hp_gained=1, gold_gained=4, gold_spent=5, gold_lost=2,
                    ),
                    player_stats(
                        PLAYER_1, 10, 22, 21, damage_taken=5, hp_healed=2, max_hp_lost=1,
                        max_hp_gained=3, gold_gained=12, gold_spent=4, gold_lost=6, gold_stolen=6,
                        card_choices=[
                            {"card": offered, "was_picked": True},
                            {"card": {"id": "CARD.ANON_PASS"}, "was_picked": False},
                        ],
                        cards_gained=[dict(offered)],
                        event_choices=[{"title": LOCALIZED_TEXT}],
                    ),
                ),
            ],
            [
                point(
                    "boss", [room("boss", "ENCOUNTER.ANON_BOSS", 8)],
                    player_stats(PLAYER_1, 11, 21, 22, hp_healed=1, max_hp_lost=1, gold_gained=5, gold_spent=4),
                    player_stats(PLAYER_2, 25, 32, 79, damage_taken=1, hp_healed=6, max_hp_lost=1,
                                 max_hp_gained=3, gold_gained=3, gold_spent=1),
                ),
            ],
        ],
    }


class RunHistoryAuditTest(unittest.TestCase):
    def setUp(self):
        work = ROOT / ".agent_works"
        work.mkdir(exist_ok=True)
        tmp = tempfile.TemporaryDirectory(prefix="run-history-fixture-", dir=work)
        self.addCleanup(tmp.cleanup)
        self.history_path = Path(tmp.name) / f"{PLAYER_1}.run"

    def invoke(self, expected_code):
        result = subprocess.run(
            [str(SIM), "--audit-run-history", str(self.history_path)],
            cwd=ROOT, env={**os.environ, "LC_ALL": "C"}, text=True, encoding="utf-8",
            capture_output=True, check=False,
        )
        self.assertEqual(result.returncode, expected_code, result.stderr or result.stdout)
        for private in (str(PLAYER_1), str(PLAYER_2), LOCALIZED_TEXT):
            self.assertNotIn(private, result.stdout + result.stderr)
        return result

    def audit(self, document, expected_code=0):
        self.history_path.write_text(json.dumps(document), encoding="utf-8")
        return self.invoke(expected_code)

    def test_all_rooms_and_cross_act_ledger(self):
        report = self.audit(native_history()).stdout
        self.assertIn("v0.107.1-fixture, schema 9", report)
        self.assertIn("no map edges or combat replay", report)
        self.assertIn("Player 1: CHARACTER.SILENT", report)
        self.assertIn("Player 2: CHARACTER.DEFECT", report)
        self.assertIn("Act 1: ACT.ANON_ACT_ONE (2 map points)", report)
        self.assertIn("Act 2: ACT.ANON_ACT_TWO (1 map points)", report)
        baseline, act_one, act_two = report.split("(run floor ")[1:]
        self.assertIn("1): map point ancient", baseline)
        self.assertIn("Player 1: HP 13/20, gold 19 (recorded baseline)", baseline)
        self.assertIn("2): map point unknown", act_one)
        self.assertIn("Room 1: event EVENT.ANON_EVENT", act_one)
        self.assertIn("Room 2: monster ENCOUNTER.ANON_FIGHT, 4 turns", act_one)
        self.assertIn("Player 1: HP 10/22, gold 19 -> 21", act_one)
        self.assertIn("Player 2: HP 20/30, gold 80 -> 77", act_one)
        self.assertIn("Card choice: CARD.ANON_PICK (+1) (picked)", act_one)
        self.assertIn("Card choice: CARD.ANON_PASS (not picked)", act_one)
        self.assertEqual(act_one.count("Card gained:"), 1)
        self.assertIn("Card gained: CARD.ANON_PICK (+1)", act_one)
        self.assertIn("Act 2 floor 1", act_one)
        self.assertIn("3): map point boss", act_two)
        self.assertIn("Player 1: HP 11/21, gold 21 -> 22", act_two)
        self.assertIn("Player 2: HP 25/32, gold 77 -> 79", act_two)
        self.assertIn("3 map points; 2 across-point transitions matched", report)
        self.assertIn("only the recorded ledger for this run", report)

    def test_reported_outcomes_are_distinct(self):
        for win, abandoned, outcome in ((True, False, "win"), (False, False, "loss"),
                                        (False, True, "abandoned")):
            with self.subTest(outcome=outcome):
                history = native_history()
                history.update(win=win, was_abandoned=abandoned)
                if not win:
                    history["map_point_history"].pop()  # native history can stop before future acts
                outcomes = [line for line in self.audit(history).stdout.splitlines()
                            if line.startswith("Recorded outcome:")]
                self.assertEqual(outcomes, [f"Recorded outcome: {outcome}"])

    def test_reports_first_tampered_gold(self):
        history = native_history()
        history["map_point_history"][0][1]["player_stats"][1]["current_gold"] += 1
        history["map_point_history"][1][0]["player_stats"][0]["current_gold"] += 1
        mismatch = self.audit(history, 1).stderr
        self.assertIn("Act 1 floor 2 (run floor 2), player 1: current_gold expected 21, actual 22", mismatch)
        self.assertNotIn("Act 2", mismatch)

    def test_signed_arithmetic_is_not_clamped(self):
        history = native_history()
        stats = history["map_point_history"][0][1]["player_stats"][1]
        stats.update(gold_spent=26, current_gold=0)
        mismatch = self.audit(history, 1).stderr
        self.assertIn("current_gold expected -1, actual 0", mismatch)

    def test_schema_and_input_errors(self):
        history = native_history()
        history["schema_version"] = 16
        self.assertIn("unsupported run history schema 16", self.audit(history, 2).stderr)
        history["schema_version"] = 9
        history["map_point_history"][0][1]["player_stats"][1]["player_id"] = PLAYER_2
        self.assertIn("player 2: duplicate player_stats", self.audit(history, 2).stderr)
        history["map_point_history"][0][1]["player_stats"][1]["player_id"] = PLAYER_2 - 2
        self.assertIn("player ID not in the roster", self.audit(history, 2).stderr)
        self.history_path.write_text(f"{{invalid: {PLAYER_2}", encoding="utf-8")
        self.assertIn("invalid JSON", self.invoke(2).stderr)
        self.history_path.unlink()
        self.assertIn("could not read the file", self.invoke(2).stderr)

    def test_model_ids_cannot_be_localized_or_cross_category(self):
        for bad_model in ("EVENT.ANON_EVENT", "ENCOUNTER.Bad\nInjected line"):
            with self.subTest(bad_model=bad_model):
                history = native_history()
                history["map_point_history"][0][1]["rooms"][1]["model_id"] = bad_model
                result = self.audit(history, 2)
                self.assertIn("room 2.model_id: expected a ENCOUNTER model ID", result.stderr)
                self.assertNotIn(bad_model, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Exercise the built schema-16 map audit on anonymous saves."""

import json
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SIM = ROOT / ".lake" / "build" / "bin" / "sts2sim"
WORK = ROOT / ".agent_works"


def fixture():
    start = {"col": 2, "row": 0}
    rest = {"col": 2, "row": 1}
    branch = {"col": 1, "row": 1}
    boss = {"col": 2, "row": 2}
    second = {"col": 2, "row": 3}
    act_map = {
        "width": 3,
        "height": 2,
        "start": {"coord": start, "type": "ancient", "children": [rest, branch]},
        "start_coords": [branch, rest],
        "points": [
            {"coord": rest, "type": "rest_site", "children": [boss]},
            {"coord": branch, "type": "unknown", "children": [boss]},
        ],
        "boss": {"coord": boss, "type": "boss", "children": [second]},
        "second_boss": {"coord": second, "type": "boss"},
    }
    save = {
        "schema_version": 16,
        "current_act_index": 1,
        "acts": [{"saved_map": "not the current act"}, {"saved_map": act_map}],
        "visited_map_coords": [start, rest, boss, second],
        "pre_finished_room": {"is_pre_finished": True},
    }
    return save, act_map


class MapAuditTest(unittest.TestCase):
    def check_audit(self, save, code, text):
        WORK.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=WORK) as tmpdir:
            path = Path(tmpdir) / "anonymous.save"
            path.write_text(json.dumps(save), encoding="utf-8")
            result = subprocess.run(
                [str(SIM), "--audit-act-map", str(path)],
                capture_output=True,
                text=True,
                check=False,
            )
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        self.assertIn(text, result.stdout if code == 0 else result.stderr)
        return result.stdout

    def test_current_act_second_boss_and_prefinished_scope(self):
        save, _ = fixture()
        output = self.check_audit(
            save, 0, "current act index 1): 4 visited coordinates, 3 edges, from (2,0) to (2,3)"
        )
        self.assertIn("Saved room: pre-finished.", output)
        self.assertIn("reward claims and run outcome were not checked", output)

    def test_omitted_route_is_empty_not_start_coords(self):
        save, act_map = fixture()
        del save["visited_map_coords"], save["pre_finished_room"]
        del act_map["second_boss"], act_map["boss"]["children"]
        self.check_audit(save, 0, "0 visited coordinates, 0 edges")

    def test_first_route_coordinate_must_match_start_not_branch(self):
        save, _ = fixture()
        save["visited_map_coords"].pop(0)
        self.check_audit(save, 1, "first visited coordinate (2,1) does not match saved start (2,0)")

    def test_boss_to_second_boss_requires_saved_edge(self):
        save, act_map = fixture()
        del act_map["boss"]["children"]
        self.check_audit(save, 1, "broken edge #3: (2,2) -> (2,3)")

    def test_dangling_child_on_unvisited_branch_is_invalid(self):
        save, act_map = fixture()
        act_map["points"][1]["children"] = [{"col": 0, "row": 1}]
        self.check_audit(save, 2, "dangling child reference (1,1) -> (0,1)")

    def test_special_points_participate_in_uniqueness_check(self):
        save, act_map = fixture()
        act_map["second_boss"]["coord"] = act_map["boss"]["coord"]
        self.check_audit(save, 2, "duplicate map coordinate (2,2)")

    def test_other_schema_is_not_migrated(self):
        self.check_audit({"schema_version": 15}, 2, "unsupported schema_version 15 (expected 16)")


if __name__ == "__main__":
    unittest.main()

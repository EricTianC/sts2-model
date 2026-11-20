"""CLI regression tests using only anonymous synthetic observations."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


VIEWER = Path(__file__).resolve().with_name("view_combat_replay.py")
UNCONFIRMED = "No confirmed play completion snapshot"


def play(sequence):
    return {
        "sequence": sequence, "kind": "GameAction", "player": 1,
        "action": "NetPlayCardAction",
        "payload": {"card": "TEST_CARD", "combatCardIndex": 0, "targetId": 0},
    }


def resume(sequence, old_id):
    return {"sequence": sequence, "kind": "ResumeAction", "player": None, "actionId": old_id}


def checkpoint(number, action_id, *, card="TEST_CARD", index=0, target=0):
    return {
        "id": number,
        "context": f"finished action execution PlayCardAction card: CARD.{card} "
                   f"(ignored runtime marker) index: {index} targetid: {target}",
        "lastExecutedActionId": action_id,
        "creatures": [{"player": 1, "monster": None, "currentHp": 8, "maxHp": 10,
                       "block": 2, "powers": []}],
        "players": [{"player": 1, "character": "TEST_CHARACTER", "turnNumber": 1,
                     "phase": "Play", "energy": 0, "stars": 0, "piles": []}],
    }


def projection(events, checkpoints):
    return {
        "version": "test", "commit": "test", "modelIdHash": 0, "sha256": "0" * 64,
        "exactRoundtrip": False, "nextActionId": 0,
        "start": {"Ascension": 0, "players": [{"player": 1, "character": "TEST_CHARACTER"}]},
        "events": events, "checkpoints": checkpoints,
    }


class ReplayViewerTest(unittest.TestCase):
    def setUp(self):
        work = VIEWER.parent.parent / ".agent_works"
        work.mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(dir=work)
        self.addCleanup(temp.cleanup)
        self.path = Path(temp.name) / "observation.json"

    def view(self, document, *args):
        self.path.write_text(json.dumps(document), encoding="utf-8")
        result = subprocess.run([sys.executable, str(VIEWER), str(self.path), *map(str, args)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_hook_choice_and_resumes_preserve_original_play(self):
        document = projection([
            play(2),
            {"sequence": 4, "kind": "HookAction", "player": 1, "hookId": 0},
            {"sequence": 5, "kind": "PlayerChoice", "player": 1, "choiceId": 0,
             "playerChoice": "Test choice"},
            resume(6, 0),
            resume(9, 2),
        ], [checkpoint(7, 3)])
        play_view = self.view(document, "--event", 2)
        self.assertIn("targetId: 0", play_view)
        self.assertIn("checkpoint #7 (executed actionId 3", play_view)
        resume_view = self.view(document, "--event", 6)
        self.assertIn("old actionId: 0", resume_view)
        self.assertIn("checkpoint #7 (executed actionId 3, play event 2", resume_view)
        choice_view = self.view(document, "--event", 5)
        self.assertIn("choiceId: 0 | playerChoice: Test choice", choice_view)
        self.assertIn("No independent state snapshot", choice_view)
        self.assertNotIn("checkpoint #", choice_view)

    def test_unconfirmed_completion_does_not_hide_observations(self):
        wrong_context = checkpoint(7, 0)
        wrong_context["context"] = "not " + wrong_context["context"]
        cases = {
            "missing action ID": [checkpoint(7, None)],
            "wrong action ID": [checkpoint(7, 1)],
            "wrong card": [checkpoint(7, 0, card="OTHER_CARD")],
            "wrong card index": [checkpoint(7, 0, index=1)],
            "null instead of zero target": [checkpoint(7, 0, target="")],
            "not a completion context": [wrong_context],
            "duplicate action ID": [checkpoint(7, 0), checkpoint(9, 0, index=1)],
            "multiplayer": [checkpoint(7, 0)],
        }
        for label, checkpoints in cases.items():
            with self.subTest(label=label):
                document = projection([play(0)], checkpoints)
                if label == "multiplayer":
                    document["start"]["players"].append({"player": 2, "character": "OTHER_CHARACTER"})
                self.assertIn(UNCONFIRMED, self.view(document, "--event", 0))
                self.assertIn("P1: HP 8/10 block 2", self.view(document, "--checkpoint", 7))

    def test_unknown_kind_stops_numbering_but_not_browsing(self):
        document = projection([
            play(2), {"sequence": 4, "kind": "Unfamiliar", "player": None}, play(8),
        ], [checkpoint(7, 0), checkpoint(9, 1)])
        output = self.view(document)
        self.assertIn("Checkpoint #9", output)
        events = {line.split()[1]: line for line in output.splitlines() if line.startswith("Event ")}
        self.assertIn("checkpoint #7", events["2"])
        self.assertIn("Unfamiliar", events["4"])
        self.assertIn(UNCONFIRMED, events["8"])

    def test_stale_resume_invalidates_chain(self):
        document = projection([play(2), resume(4, 0), resume(6, 0)], [checkpoint(7, 1)])
        self.assertIn(UNCONFIRMED, self.view(document, "--event", 2))
        self.assertIn(UNCONFIRMED, self.view(document, "--event", 4))


if __name__ == "__main__":
    unittest.main()

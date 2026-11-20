#!/usr/bin/env python3
"""Check two recorded Survivor segments against Lean, not a full combat replay."""

import argparse
import hashlib
import itertools
import json
import re
import struct
import subprocess
import sys
import tempfile
from copy import deepcopy
from pathlib import Path

from view_combat_replay import PILES, completion_links, find_id, read_projection, solo_player


ROOT = Path(__file__).resolve().parents[1]
NATIVE_CHOICE = re.compile(r"NetPlayerChoiceResult combat((?: NetCombatCard [0-9]+)+)")
HP_FIELDS = ("currentHp", "maxHp", "block")
POWER_METADATA = {
    "FRAIL_POWER": ("debuff", False),
    "RAVENOUS_POWER": ("buff", False),
    "STRENGTH_POWER": ("buff", True),
}


def expect(where, expected, actual):
    """Report the first differing field, including card positions within piles."""
    if type(expected) is type(actual):
        if isinstance(expected, dict):
            expect(f"{where}.fields", sorted(expected), sorted(actual))
            for key in expected:
                expect(f"{where}.{key}", expected[key], actual[key])
            return
        if isinstance(expected, list):
            expect(f"{where}.length", len(expected), len(actual))
            for i, (left, right) in enumerate(zip(expected, actual)):
                expect(f"{where}[{i}]", left, right)
            return
        if expected == actual:
            return
    raise ValueError(f"{where}: expected {expected!r}, got {actual!r}")


def by_player(records, key, player_id):
    return find_id(records, key, player_id, "player ID")


def native_piles(player):
    return {kind: find_id(player["piles"], "kind", kind, "native pile")["cards"] for kind in PILES}


def native_card(card):
    return {"model": card["model"], "upgrade": card["upgrade"]}


def wire_card(card):
    return {"model": card["modelEntry"], "upgrade": card.get("upgradeLevel", 0)}


def frame_player(frame, player_id):
    return by_player(frame["combat"]["players"], "playerId", player_id)


def pile_ids(player, kind):
    return [card["instanceId"] for card in player[kind]]


def compare_frame(label, checkpoint, frame, player_id):
    combat = frame["combat"]
    observed = by_player(checkpoint["players"], "player", player_id)
    modeled = frame_player(frame, player_id)
    where = f"{label}, checkpoint #{checkpoint['id']} / Lean step {frame['step']}"
    expect(f"{where}.character", observed["character"], modeled["characterEntry"])
    for field in ("energy", "stars", "turnNumber"):
        expect(f"{where}.{field}", observed[field], modeled[field])
    creatures = combat["allies"] + combat["enemies"]
    expect(f"{where}.creatures.length", len(checkpoint["creatures"]), len(creatures))
    for i, (native, wire) in enumerate(zip(checkpoint["creatures"], creatures)):
        name = f"{where}.creatures[{i}]"
        expect(f"{name}.player", native["player"], wire["playerId"])
        if native["monster"] is not None:
            expect(f"{name}.monster", native["monster"], wire["modelEntry"])
        for field in HP_FIELDS:
            expect(f"{name}.{field}", native[field], wire[field])
        expect(f"{name}.powers", sorted([p["model"], p["amount"]] for p in native["powers"]),
               sorted([p["modelEntry"], p["amount"]] for p in wire["powers"]))
    for kind, cards in native_piles(observed).items():
        expect(f"{where}.piles.{kind}", [native_card(c) for c in cards],
               [wire_card(c) for c in modeled[kind.lower()]])


def initial_choice_id(path, observation):
    """Read the byte-aligned CombatReplay header, not the first recorded choice."""
    data = path.read_bytes()
    expect("replay archive digest", observation["sha256"], hashlib.sha256(data).hexdigest())
    pos = 0

    def take(size):
        nonlocal pos
        if size > len(data) - pos:
            raise ValueError("truncated replay header")
        value = data[pos:pos + size]
        pos += size
        return value

    def u32():
        return struct.unpack("<I", take(4))[0]

    expect("replay version", observation["version"], take(u32()).decode("utf-8"))
    expect("replay source commit", observation["commit"], take(u32()).decode("utf-8"))
    expect("replay model ID hash", observation["modelIdHash"], u32())
    expect("solo replay choice cursor count", 1, u32())
    return u32()


def native_play(raw, card_id, model):
    where = f"native event {raw['sequence']}"
    expect(f"{where}.kind", "GameAction", raw["kind"])
    expect(f"{where}.action", "NetPlayCardAction", raw["action"])
    payload = raw["payload"]
    expect(f"{where}.card", model, payload["card"])
    return {"eventType": "gameAction", "playerId": raw["player"],
            "payload": {"type": "playCard", "cardId": card_id, "targetId": payload["targetId"]}}


def native_resume(raw):
    expect(f"native event {raw['sequence']}.kind", "ResumeAction", raw["kind"])
    return {"eventType": "resumeAction", "actionId": raw["actionId"]}


def choice(player_id, choice_id, cards):
    return {"playerId": player_id, "choiceId": choice_id, "cards": cards}


def wire_choice(record):
    return {"eventType": "playerChoice", "playerId": record["playerId"],
            "choiceId": record["choiceId"], "choiceResult": {"type": "cards", "ids": record["cards"]}}


def request(prefix, player_id, next_choice_id, events):
    return {"trace": {**prefix, "events": [
        {"seqIdx": i, "kind": "combat", "combat": combat}
        for i, combat in enumerate(events, 1)
    ]}, "playerId": player_id, "nextChoiceId": next_choice_id}


def observe(directory, label, bundle, *, rejected=None):
    path = directory / f"{label}.json"
    path.write_text(json.dumps(bundle), encoding="utf-8")
    cmd = ["lake", "exe", "sts2sim", "--observe-combat", str(path)]
    result = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    expected_code = 1 if rejected else 0
    if result.returncode != expected_code or (rejected and rejected not in result.stderr):
        detail = result.stderr.strip() or result.stdout.strip()
        raise ValueError(f"{label}: expected Lean exit {expected_code}"
                         f"{f' with {rejected!r}' if rejected else ''}, got {result.returncode}: {detail}")
    if rejected:
        return None
    try:
        frames = json.loads(result.stdout)["frames"]
    except (ValueError, KeyError) as error:
        raise ValueError(f"{label}: invalid Lean observation output: {error}") from error
    expect(f"{label}.steps", [0] + [e["seqIdx"] for e in bundle["trace"]["events"]],
           [frame["step"] for frame in frames])
    return frames


def pending(action_id, player_id, choice_id, candidates, automatic):
    return {"actionId": action_id, "playerId": player_id, "choiceId": choice_id,
            "candidates": candidates, "automatic": automatic}


def check_pause(label, before, paused, player_id, play_card, expected_pending, block):
    start, mid = frame_player(before, player_id), frame_player(paused, player_id)
    expect(f"{label}.pending", [expected_pending], paused["pending"])
    expect(f"{label}.play instance IDs", [play_card], pile_ids(mid, "play"))
    expect(f"{label}.hand instance IDs", expected_pending["candidates"], pile_ids(mid, "hand"))
    expect(f"{label}.discard before resume", pile_ids(start, "discard"), pile_ids(mid, "discard"))
    expect(f"{label}.energy before resume", 0, mid["energy"])
    ally = by_player(paused["combat"]["allies"], "playerId", player_id)
    expect(f"{label}.block before resume", block, ally["block"])


def check_manual(directory, native, prefix, player_id, next_choice_id, checkpoints):
    raw = [find_id(native["events"], "sequence", i, "event") for i in range(6)]
    initial_player = by_player(prefix["initialState"]["combat"]["players"], "playerId", player_id)
    # The archived prefix uses native combat indices as Lean instance IDs. Look
    # them up in the initial state; neither hand position nor choiceId is that ID.
    prefix_ids = {c["instanceId"]: c for pile in PILES[:-1] for c in initial_player[pile.lower()]}
    plays = []
    for event in raw[:4]:
        card = prefix_ids[event["payload"]["combatCardIndex"]]
        plays.append(native_play(event, card["instanceId"], card["modelEntry"]))
    expect("archived first three plays", prefix["events"], request(prefix, player_id, 0, plays[:3])["trace"]["events"])
    survivor_id = plays[-1]["payload"]["cardId"]
    expect("first Survivor play", "SURVIVOR", prefix_ids[survivor_id]["modelEntry"])

    recorded = raw[4]
    expect("native event 4.kind", "PlayerChoice", recorded["kind"])
    match = NATIVE_CHOICE.fullmatch(recorded["playerChoice"])
    if not match:
        raise ValueError(f"native event 4: unrecognized combat choice {recorded['playerChoice']!r}")
    native_indices = [int(i) for i in re.findall(r"NetCombatCard ([0-9]+)", match[1])]
    selected_ids = [prefix_ids[i]["instanceId"] for i in native_indices]
    [selected_id] = selected_ids
    choice_id = recorded["choiceId"]
    expect("Survivor choice matches replay header reservation", next_choice_id, choice_id)
    selection = choice(recorded["player"], choice_id, selected_ids)
    resume = native_resume(raw[5])

    def manual_request(record):
        events = plays + ([] if record is None else [wire_choice(record)]) + [resume]
        return request(prefix, player_id, next_choice_id, events)

    frames = observe(directory, "observed-manual", manual_request(selection))
    for frame, checkpoint in zip(frames[:4], checkpoints[:4]):
        compare_frame("opening prefix", checkpoint, frame, player_id)
    print("Opening prefix #1 → #4: Lean steps 0–3 match observed fields.")
    compare_frame("recorded Survivor", checkpoints[4], frames[6], player_id)
    started = frame_player(frames[3], player_id)
    candidates = [i for i in pile_ids(started, "hand") if i != survivor_id]
    expected_pending = pending(resume["actionId"], player_id, choice_id, candidates, False)
    block = by_player(checkpoints[4]["creatures"], "player", player_id)["block"]
    check_pause("recorded Survivor pause", frames[3], frames[4], player_id, survivor_id, expected_pending, block)
    expect("before native PlayerChoice", [], frames[4]["choices"])
    expect("after native PlayerChoice.pending", [expected_pending], frames[5]["pending"])
    expect("after native PlayerChoice.choices", [selection], frames[5]["choices"])
    expect("PlayerChoice does not resolve combat", frames[4]["combat"], frames[5]["combat"])
    expect("manual resume.pending", [], frames[6]["pending"])
    expect("manual resume.choices", [], frames[6]["choices"])
    modeled = frame_player(frames[6], player_id)
    expect("recorded discard instance IDs", pile_ids(started, "discard") + [selected_id, survivor_id],
           pile_ids(modeled, "discard"))
    expect("recorded hand instance IDs", [i for i in candidates if i != selected_id], pile_ids(modeled, "hand"))
    print(f"Recorded Survivor #4 → #5 (native events 3–5): matched; discarded instance {selected_id}.")

    first_id = candidates[0]
    expect("alternate instance has same model/upgrade", wire_card(prefix_ids[selected_id]), wire_card(prefix_ids[first_id]))
    expect("recorded selection is not first", False, selected_id == first_id)
    alternate = observe(directory, "alternate-instance", manual_request(choice(player_id, choice_id, [first_id])))[6]
    alternate_player = frame_player(alternate, player_id)
    expect("alternate discard instance IDs", pile_ids(started, "discard") + [first_id, survivor_id],
           pile_ids(alternate_player, "discard"))
    expect("alternate hand instance IDs", [i for i in candidates if i != first_id], pile_ids(alternate_player, "hand"))

    out_of_hand = pile_ids(started, "draw")[0]
    invalid = {
        "wrong-player": choice(player_id + 1, choice_id, selected_ids),
        "wrong-choice-id": choice(player_id, choice_id + 1, selected_ids),
        "duplicate": choice(player_id, choice_id, [selected_id, selected_id]),
        "out-of-hand": choice(player_id, choice_id, [out_of_hand]),
        "empty-selection": choice(player_id, choice_id, []),
    }
    for label, record in invalid.items():
        observe(directory, label, manual_request(record), rejected="invalid or unreserved card choice for player")
    observe(directory, "missing-selection", manual_request(None), rejected="missing or invalid card choice for player")
    print(f"Anonymous manual variants: first same-model instance {first_id} selected; invalid and missing choices rejected.")
    return choice_id


def independent_snapshot(prefix, checkpoint, player_id, raw_play, action_id):
    initial = deepcopy(prefix["initialState"])
    combat = initial["combat"]
    player = by_player(combat["players"], "playerId", player_id)
    card_templates = {}
    for pile in PILES[:-1]:
        for card in player[pile.lower()]:
            metadata = {k: v for k, v in card.items() if k != "instanceId"}
            key = (card["modelEntry"], card.get("upgradeLevel", 0))
            expect(f"prefix card metadata {key}", card_templates.setdefault(key, metadata), metadata)
    instance_ids = itertools.count(combat["nextInstanceId"])
    observed = by_player(checkpoint["players"], "player", player_id)
    mapped_index = {}
    native_index = raw_play["payload"]["combatCardIndex"]
    for kind, cards in native_piles(observed).items():
        instances = []
        for card in cards:
            key = (card["model"], card["upgrade"])
            instance_id = next(instance_ids)
            if kind == "Hand" and card["model"] == "SURVIVOR":
                expect("#21 uniquely identifiable Survivor", {}, mapped_index)
                mapped_index[native_index] = instance_id
            instances.append({**card_templates[key], "instanceId": instance_id})
        player[kind.lower()] = instances
    player.update(energy=observed["energy"], stars=observed["stars"], turnNumber=observed["turnNumber"])
    initial_play = player.pop("play")

    # The remaining slug is distinguishable from the other one by max HP.
    creature_templates = {(c["playerId"], c["modelEntry"], c["maxHp"]): c
                          for c in combat["allies"] + combat["enemies"]}
    allies, enemies = [], []
    for creature in checkpoint["creatures"]:
        pid = creature["player"]
        model = observed["character"] if pid == player_id else creature["monster"]
        template = creature_templates[pid, model, creature["maxHp"]]
        powers = []
        for power in creature["powers"]:
            power_type, allow_negative = POWER_METADATA[power["model"]]
            powers.append({"instanceId": next(instance_ids), "modelEntry": power["model"],
                           "amount": power["amount"], "powerType": power_type,
                           "stackType": "counter", "allowNegative": allow_negative})
        wire = {**template, **{field: creature[field] for field in HP_FIELDS}, "powers": powers}
        (allies if pid == player_id else enemies).append(wire)
    rng = checkpoint["runRng"]["Shuffle"]
    combat.update(allies=allies, enemies=enemies, roundNumber=observed["turnNumber"],
                  rng={key: value if key == "counter" else str(value) for key, value in rng.items()},
                  nextInstanceId=next(instance_ids))
    initial["nextActionId"] = action_id
    return {**prefix, "initialState": initial}, initial_play, mapped_index[native_index]


def check_automatic(directory, native, prefix, player_id, choice_id, before, after):
    raw_play = find_id(native["events"], "sequence", 16, "event")
    resume = native_resume(find_id(native["events"], "sequence", 17, "event"))
    snapshot, initial_play, survivor_id = independent_snapshot(prefix, before, player_id, raw_play, resume["actionId"])
    # Native automatic selection emits no choice result/ID. The isolated
    # synchronizer's initial cursor is a fixture input, not a native observation.
    bundle = request(snapshot, player_id, choice_id, [native_play(raw_play, survivor_id, "SURVIVOR"), resume])
    if initial_play:
        bundle["initialPlay"] = initial_play
    frames = observe(directory, "observed-automatic", bundle)
    compare_frame("independent start", before, frames[0], player_id)
    compare_frame("automatic Survivor", after, frames[2], player_id)
    start = frame_player(frames[0], player_id)
    [defend_id] = [i for i in pile_ids(start, "hand") if i != survivor_id]
    expected_pending = pending(resume["actionId"], player_id, choice_id, [defend_id], True)
    block = by_player(after["creatures"], "player", player_id)["block"]
    check_pause("automatic Survivor pause", frames[0], frames[1], player_id, survivor_id, expected_pending, block)
    expect("automatic resume.pending", [], frames[2]["pending"])
    expect("automatic resume.choices", [], frames[2]["choices"])
    expect("automatic discard instance IDs", pile_ids(start, "discard") + [defend_id, survivor_id],
           pile_ids(frame_player(frames[2], player_id), "discard"))
    print("Independent Survivor #21 → #22 (native events 16–17): matched without a PlayerChoice event.")

    queued = [choice(player_id, choice_id, [defend_id]), choice(player_id, choice_id + 1, [pile_ids(start, "draw")[0]])]
    preloaded = observe(directory, "automatic-preserves-choices", {**bundle, "initialChoices": queued})
    for frame, reference in zip(preloaded, frames):
        where = f"preloaded automatic step {frame['step']}"
        expect(f"{where}.choices", queued, frame["choices"])
        expect(f"{where}.pending", reference["pending"], frame["pending"])
        expect(f"{where}.combat", reference["combat"], frame["combat"])

    empty_bundle = deepcopy(bundle)
    empty_player = by_player(empty_bundle["trace"]["initialState"]["combat"]["players"], "playerId", player_id)
    [defend] = [card for card in empty_player["hand"] if card["instanceId"] == defend_id]
    empty_player["hand"].remove(defend)
    empty_player["discard"].append(defend)
    empty = observe(directory, "automatic-empty-hand", empty_bundle)
    expect("empty-hand automatic pause", [{**expected_pending, "candidates": []}], empty[1]["pending"])
    expect("empty-hand automatic resume", [], empty[2]["pending"])
    expect("empty-hand final combat", frames[2]["combat"], empty[2]["combat"])
    print("Anonymous automatic variants: preloaded results preserved; empty hand needs no choice result.")


def check(capture_dir, scratch):
    native = read_projection(capture_dir / "native-observations.json")
    prefix = json.loads((capture_dir / "lean-prefix.json").read_text(encoding="utf-8"))
    player_id = solo_player(native)
    if player_id is None:
        raise ValueError("Survivor fixture requires a single recorded player")
    checkpoints = {i: find_id(native["checkpoints"], "id", i, "checkpoint") for i in (1, 2, 3, 4, 5, 21, 22)}
    links = completion_links(native)
    for event, checkpoint in ((0, 2), (1, 3), (2, 4), (5, 5), (15, 21), (17, 22)):
        link = links.get(event)
        expect(f"native event {event} completion checkpoint", checkpoint, link[0]["id"] if link else None)
    expect("prefix nextActionId", native["nextActionId"], prefix["initialState"]["nextActionId"])
    next_choice_id = initial_choice_id(capture_dir / "latest.mcr", native)
    choice_id = check_manual(scratch, native, prefix, player_id, next_choice_id, [checkpoints[i] for i in range(1, 6)])
    check_automatic(scratch, native, prefix, player_id, choice_id + 1, checkpoints[21], checkpoints[22])
    print("Only the two observed segments were checked; #5 → #21 was not replayed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture_dir", type=Path, metavar="CAPTURE_DIR")
    args = parser.parse_args()
    try:
        scratch = ROOT / ".agent_works"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="observed-survivor-", dir=scratch) as tmp:
            check(args.capture_dir, Path(tmp))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Survivor check failed ({args.capture_dir}): {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

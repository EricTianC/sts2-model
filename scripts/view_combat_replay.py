#!/usr/bin/env python3
"""Browse observations exported by the native STS2 combat replay reader."""

import argparse
import json
import re
from pathlib import Path


NULL = type(None)
PILES = ("Hand", "Draw", "Discard", "Exhaust", "Play")
LAST_OBSERVATION = "Last observation; does not represent post-cleanup state."
MAX_ACTION_ID = (1 << 32) - 1
ENQUEUE_KINDS = ("GameAction", "HookAction")
PLAY_COMPLETION = re.compile(
    r"finished action execution PlayCardAction card: CARD\.([^()\s]+) "
    r"\([^)\r\n]*\) index: ([0-9]+) targetid: ([0-9]*)"
)


def fields(value, path, **required):
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected an object")
    for key, expected in required.items():
        if key not in value:
            raise ValueError(f"{path}.{key}: missing field")
        types = expected if isinstance(expected, tuple) else (expected,)
        if type(value[key]) not in types:  # A JSON boolean is not an integer.
            names = " or ".join(t.__name__ if t is not NULL else "null" for t in types)
            raise ValueError(f"{path}.{key}: expected {names}")


def rows(value, path, *, nonempty=False):
    if nonempty and not value:
        raise ValueError(f"{path}: expected at least one record")
    for i, item in enumerate(value):
        yield item, f"{path}[{i}]"


def ordered_rows(value, path, key, *, nonempty=False):
    previous = -1
    for item, where in rows(value, path, nonempty=nonempty):
        fields(item, where, **{key: int})
        number = item[key]
        if number < 0 or number <= previous:
            raise ValueError(f"{where}.{key}: {number} must be nonnegative and strictly increasing")
        previous = number
        yield item, where


def validate_event(event, where):
    fields(event, where, kind=str, player=(int, NULL))
    for key, kind in (
        ("action", str), ("actionSummary", str), ("actionId", int), ("hookId", int),
        ("gameActionType", str), ("choiceId", int), ("playerChoice", str),
    ):
        if key in event:
            fields(event, where, **{key: (kind, NULL)})
    if event.get("action") == "NetPlayCardAction":
        fields(event, where, payload=dict)
        fields(event["payload"], f"{where}.payload", card=str, combatCardIndex=int,
               targetId=(int, NULL))


def validate_checkpoint(checkpoint, where):
    fields(checkpoint, where, context=str, lastExecutedActionId=(int, NULL),
           creatures=list, players=list)
    for creature, location in rows(checkpoint["creatures"], f"{where}.creatures"):
        fields(creature, location, monster=(str, NULL), player=(int, NULL),
               currentHp=int, maxHp=int, block=int, powers=list)
        for power, at in rows(creature["powers"], f"{location}.powers"):
            fields(power, at, model=str, amount=int)
    for player, location in rows(checkpoint["players"], f"{where}.players", nonempty=True):
        fields(player, location, player=int, character=str, turnNumber=int, phase=str,
               energy=int, stars=int, piles=list)
        for pile, at in rows(player["piles"], f"{location}.piles"):
            fields(pile, at, kind=str, cards=list)
            for card, card_at in rows(pile["cards"], f"{at}.cards"):
                fields(card, card_at, model=(str, NULL), upgrade=int)


def invalid_constant(value):
    raise ValueError(f"invalid JSON constant: {value}")


def read_projection(path):
    document = json.loads(path.read_text(encoding="utf-8"), parse_constant=invalid_constant)
    fields(document, "$", version=str, commit=str, modelIdHash=int, sha256=str,
           exactRoundtrip=bool, nextActionId=int, start=dict, events=list, checkpoints=list)
    if not 0 <= document["nextActionId"] <= MAX_ACTION_ID:
        raise ValueError("$.nextActionId: expected an unsigned 32-bit action ID")
    start = document["start"]
    fields(start, "$.start", Ascension=int, players=list)
    for player, where in rows(start["players"], "$.start.players", nonempty=True):
        fields(player, where, player=int, character=(str, NULL))
    for event, where in ordered_rows(document["events"], "$.events", "sequence"):
        validate_event(event, where)
    for checkpoint, where in ordered_rows(document["checkpoints"], "$.checkpoints", "id",
                                          nonempty=True):
        validate_checkpoint(checkpoint, where)
    return document


def find_id(records, key, number, label):
    for record in records:
        if record[key] == number:
            return record
    raise ValueError(f"{label} {number} not found")


def show_source(document):
    start = document["start"]
    characters = ", ".join(
        f"P{player['player']} {player['character'] if player['character'] is not None else 'unknown'}"
        for player in start["players"]
    )
    print(f"STS2 {document['version']} ({document['commit']}) | {characters} | "
          f"Ascension {start['Ascension']} | {len(document['events'])} events, "
          f"{len(document['checkpoints'])} checkpoints")
    print(f"Source: native replay reader projection | modelIdHash {document['modelIdHash']} | "
          f"capture SHA-256 {document['sha256']}")
    print(f"Exporter-reported exactRoundtrip: {json.dumps(document['exactRoundtrip'])} (not rechecked)")


def checkpoint_heading(checkpoint):
    return f"Checkpoint #{checkpoint['id']} | {checkpoint['context']}"


def player_turn(player):
    return f"P{player['player']} turn {player['turnNumber']} / {player['phase']}"


def health(creature):
    return f"HP {creature['currentHp']}/{creature['maxHp']} block {creature['block']}"


def monster_name(creature):
    return creature["monster"] if creature["monster"] is not None else "unidentified creature"


def show_checkpoint_summary(checkpoint):
    parts = [checkpoint_heading(checkpoint)]
    for player in checkpoint["players"]:
        observed = [
            health(creature) for creature in checkpoint["creatures"]
            if creature["player"] == player["player"]
        ]
        status = ", ".join(observed) if observed else "HP/block not recorded"
        parts.append(f"{player_turn(player)} {status} energy {player['energy']}")
    living = ", ".join(
        f"{monster_name(creature)} {health(creature)}"
        for creature in checkpoint["creatures"]
        if creature["player"] is None and creature["currentHp"] > 0
    )
    parts.append(f"Living non-player creatures: {living or 'none observed'}")
    print(" | ".join(parts))


def show_checkpoint_detail(checkpoint, *, is_last):
    print(checkpoint_heading(checkpoint))
    action_id = checkpoint["lastExecutedActionId"]
    if action_id is not None:
        print(f"  Last executed actionId: {action_id}")
    print("  Creatures (positions in this checkpoint):")
    if not checkpoint["creatures"]:
        print("    none observed")
    for position, creature in enumerate(checkpoint["creatures"], 1):
        player = creature["player"]
        name = monster_name(creature) if player is None else f"P{player}"
        powers = ", ".join(f"{p['model']} {p['amount']}" for p in creature["powers"])
        print(f"    [{position}] {name}: {health(creature)} | powers: {powers or 'none'}")
    for player in checkpoint["players"]:
        print(f"  {player_turn(player)} | {player['character']} | energy {player['energy']} "
              f"stars {player['stars']}")
        recorded = set()
        for pile in player["piles"]:
            recorded.add(pile["kind"])
            cards = ", ".join(
                f"{card['model'] if card['model'] is not None else 'unidentified card'}"
                f"[upgrade={card['upgrade']}]"
                for card in pile["cards"]
            )
            print(f"    {pile['kind']} ({len(pile['cards'])}): {cards or '(empty)'}")
        absent = [kind for kind in PILES if kind not in recorded]
        if absent:
            print(f"    Piles not recorded: {', '.join(absent)}")
    if is_last:
        print(LAST_OBSERVATION)


def candidate_actions(document):
    next_id = document["nextActionId"]
    origins = {}
    chains = {}
    resumes = {}
    unresolved = set()
    for event in document["events"]:
        sequence, kind = event["sequence"], event["kind"]
        if kind == "PlayerChoice":
            continue
        # Do not infer allocations for unfamiliar events or across native ID wrap.
        if next_id > MAX_ACTION_ID:
            break
        if kind in ENQUEUE_KINDS:
            origins[next_id] = sequence
            chains[sequence] = [next_id]
        elif kind == "ResumeAction":
            old = event.get("actionId")
            origin = origins.get(old)
            if origin is not None and chains[origin][-1] == old:
                origins[next_id] = origin
                chains[origin].append(next_id)
                resumes[sequence] = origin
            elif old is not None:
                unresolved.add(old)
        else:
            break
        # Resume allocates even if the old action is not resolvable from this recording.
        next_id += 1
    return chains, resumes, unresolved


def solo_player(document):
    start = document["start"]["players"]
    if len(start) != 1:
        return None
    ordinal = start[0]["player"]
    if any(event["player"] not in (None, ordinal) for event in document["events"]):
        return None
    for checkpoint in document["checkpoints"]:
        players = checkpoint["players"]
        if len(players) != 1 or players[0]["player"] != ordinal:
            return None
        if any(c["player"] not in (None, ordinal) for c in checkpoint["creatures"]):
            return None
    return ordinal


def matches_play(context, payload):
    match = PLAY_COMPLETION.fullmatch(context)
    target = payload["targetId"]
    return match is not None and match.groups() == (
        payload["card"], str(payload["combatCardIndex"]), "" if target is None else str(target)
    )


def completion_links(document):
    player = solo_player(document)
    if player is None:
        return {}
    chains, resumes, unresolved = candidate_actions(document)
    by_action = {}
    for checkpoint in document["checkpoints"]:
        number = checkpoint["lastExecutedActionId"]
        if number is not None:
            by_action[number] = checkpoint if number not in by_action else None
    links = {}
    for event in document["events"]:
        if (event["kind"] != "GameAction" or event.get("action") != "NetPlayCardAction"
                or event["player"] != player):
            continue
        sequence = event["sequence"]
        chain = chains.get(sequence)
        if not chain or unresolved.intersection(chain):
            continue
        # Reject observations at superseded IDs and duplicate observations at the final ID.
        if any(number in by_action for number in chain[:-1]):
            continue
        checkpoint = by_action.get(chain[-1])
        if checkpoint is not None and matches_play(checkpoint["context"], event["payload"]):
            links[sequence] = (checkpoint, sequence)
    for resume, origin in resumes.items():
        if origin in links:
            links[resume] = links[origin]
    return links


def show_event(event, link):
    sequence, kind, player = event["sequence"], event["kind"], event["player"]
    parts = [f"Event {sequence} | {kind} | player: {'not recorded' if player is None else player}"]
    for key in ("action", "gameActionType", "hookId", "actionId", "choiceId", "playerChoice"):
        value = event.get(key)
        if value is not None:
            label = "old actionId" if key == "actionId" and kind == "ResumeAction" else key
            parts.append(f"{label}: {value}")
    if event.get("action") == "NetPlayCardAction":
        payload = event["payload"]
        target = payload["targetId"]
        parts.extend((f"card: {payload['card']}", f"combatCardIndex: {payload['combatCardIndex']}",
                      f"targetId: {'null' if target is None else target}"))
    elif event.get("actionSummary") is not None and event["actionSummary"] != event.get("action"):
        parts.append(event["actionSummary"])
    if kind == "PlayerChoice":
        parts.append("No independent state snapshot")
    elif link is not None:
        checkpoint, origin = link
        number = checkpoint["id"]
        parts.append(f"Associated play completion: checkpoint #{number} "
                     f"(executed actionId {checkpoint['lastExecutedActionId']}, "
                     f"play event {origin}; view with --checkpoint {number})")
    else:
        parts.append("No confirmed play completion snapshot")
    print(" | ".join(parts))


def show_replay(document):
    print("\nObserved checkpoints:")
    for checkpoint in document["checkpoints"]:
        show_checkpoint_summary(checkpoint)
    print(LAST_OBSERVATION)
    print("\nRecorded events:")
    links = completion_links(document)
    for event in document["events"]:
        show_event(event, links.get(event["sequence"]))
    if not document["events"]:
        print("  none recorded")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", metavar="FILE", type=Path, help="native-observations.json projection")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--checkpoint", metavar="ID", type=int, help="show one observed checkpoint")
    selection.add_argument("--event", metavar="SEQ", type=int, help="show one recorded event")
    args = parser.parse_args()
    try:
        document = read_projection(args.file)
        if args.checkpoint is not None:
            checkpoint = find_id(document["checkpoints"], "id", args.checkpoint, "checkpoint")
        elif args.event is not None:
            event = find_id(document["events"], "sequence", args.event, "event")
    except (OSError, ValueError, RecursionError) as error:
        parser.error(f"{args.file}: {error}")

    show_source(document)
    checkpoints = document["checkpoints"]
    if args.checkpoint is not None:
        show_checkpoint_detail(checkpoint, is_last=checkpoint is checkpoints[-1])
    elif args.event is not None:
        show_event(event, completion_links(document).get(event["sequence"]))
    else:
        show_replay(document)


if __name__ == "__main__":
    main()

import Lean.Data.Json
import Std.Data.HashMap

namespace Sts2Sim.RunHistoryAudit

open Lean

private inductive AuditError where
  | input (message : String)
  | ledger (message : String)

private def field (j : Json) (loc key : String) (decode : Json → Except String α) :
    Except AuditError α :=
  ((j.getObjVal? key).bind decode).mapError fun err => .input s!"{loc}.{key}: {err}"

private def fieldD (j : Json) (loc key : String) (fallback : α) (decode : Json → Except String α) :
    Except AuditError α := do
  let obj ← j.getObj?.mapError fun err => .input s!"{loc}: {err}"
  match obj.get? key with
  | none => pure fallback
  | some value => (decode value).mapError fun err => .input s!"{loc}.{key}: {err}"

private def readId (j : Json) : Except String Nat := do
  let id ← j.getNat?
  unless id <= 18446744073709551615 do throw "expected an unsigned 64-bit player ID"
  pure id

private def readInt (j : Json) : Except String Int := do
  let n ← j.getInt?
  unless -2147483648 <= n && n <= 2147483647 do throw "expected a signed 32-bit integer"
  pure n

private def readBuild (j : Json) : Except String String := do
  let build ← j.getStr?
  unless !build.isEmpty && build.all (fun c => c.isAlphanum || c == '.' || c == '-' || c == '_' || c == '+') do
    throw "expected a build identifier"
  pure build

-- Native IDs are ordinal CATEGORY.ENTRY slugs, never localized strings or catalog lookups.
private def readModelId (category : String) (j : Json) : Except String String := do
  let id ← j.getStr?
  let categoryPrefix := category ++ "."
  let entry := id.drop categoryPrefix.length
  unless id.startsWith categoryPrefix && !entry.isEmpty && entry.all (fun c => c.isUpper || c.isDigit || c == '_') do
    throw s!"expected a {category} model ID"
  pure id

private def readKind (allowed : List String) (j : Json) : Except String String := do
  let kind ← j.getStr?
  unless allowed.contains kind do throw "unrecognized native type"
  pure kind

private def readRoomModel (kind : String) : Json → Except String (Option String)
  | .null => pure none
  | j => do
    let category ← match kind with
      | "event" => pure "EVENT"
      | "monster" | "elite" | "boss" => pure "ENCOUNTER"
      | _ => throw "room type does not carry a model ID"
    some <$> readModelId category j

private def renderRoom (j : Json) (loc : String) (roomIndex : Nat) : Except AuditError String := do
  let roomLoc := s!"{loc}, room {roomIndex}"
  let kind ← field j roomLoc "room_type" <| readKind
    ["unassigned", "monster", "elite", "boss", "treasure", "shop", "event", "rest_site", "map"]
  let model ← fieldD j roomLoc "model_id" none (readRoomModel kind)
  let monsters ← fieldD j roomLoc "monster_ids" #[] fun value => do
    (← value.getArr?).mapM (readModelId "MONSTER")
  let turns ← field j roomLoc "turns_taken" Json.getNat?
  let modelSuffix := model.elim "" (fun id => s!" {id}")
  let monsterSuffix := if monsters.isEmpty then "" else s!"; monsters: {String.intercalate ", " monsters.toList}"
  pure s!"  Room {roomIndex}: {kind}{modelSuffix}, {turns} turns{monsterSuffix}"

private def renderCard (card : Json) (loc : String) : Except AuditError String := do
  let id ← field card loc "id" (readModelId "CARD")
  let upgrade ← fieldD card loc "current_upgrade_level" 0 Json.getNat?
  pure (if upgrade == 0 then id else s!"{id} (+{upgrade})")

private structure Balance where
  hp : Int
  maxHp : Int
  gold : Int

private def readBalance (stats : Json) (loc : String) : Except AuditError Balance := do
  let hp ← field stats loc "current_hp" readInt
  let maxHp ← field stats loc "max_hp" readInt
  let gold ← field stats loc "current_gold" readInt
  pure ⟨hp, maxHp, gold⟩

private def advanceBalance (before : Option Balance) (actual : Balance) (stats : Json)
    (loc : String) : Except AuditError Balance := do
  let damage ← field stats loc "damage_taken" readInt
  let healed ← field stats loc "hp_healed" readInt
  let maxLost ← field stats loc "max_hp_lost" readInt
  let maxGained ← field stats loc "max_hp_gained" readInt
  let gained ← field stats loc "gold_gained" readInt
  let spent ← field stats loc "gold_spent" readInt
  let lost ← field stats loc "gold_lost" readInt
  -- The first point supplies the baseline. Thereafter all arithmetic is signed and unclamped.
  -- gold_stolen is not a second debit.
  pure <| before.elim actual fun b =>
    ⟨b.hp + healed - damage, b.maxHp + maxGained - maxLost, b.gold + gained - spent - lost⟩

private def checkBalance (loc : String) (expected actual : Balance) : Except AuditError Unit := do
  let values := [("current_hp", expected.hp, actual.hp), ("max_hp", expected.maxHp, actual.maxHp),
    ("current_gold", expected.gold, actual.gold)]
  for (key, want, observed) in values do
    unless want == observed do throw (.ledger s!"{loc}: {key} expected {want}, actual {observed}")

private def audit (doc : Json) : Except AuditError (Array String) := do
  let schema ← field doc "history" "schema_version" readInt
  unless schema == 9 do throw (.input s!"unsupported run history schema {schema}; expected schema 9")
  let build ← field doc "history" "build_id" readBuild
  let win ← field doc "history" "win" Json.getBool?
  let abandoned ← field doc "history" "was_abandoned" Json.getBool?
  if win && abandoned then throw (.input "history: win and was_abandoned cannot both be true")
  let roster ← field doc "history" "players" Json.getArr?
  if roster.isEmpty then throw (.input "history.players: expected at least one player")
  let acts ← field doc "history" "acts" Json.getArr?
  let history ← field doc "history" "map_point_history" Json.getArr?
  unless history.size <= acts.size do throw (.input "history.map_point_history: more act entries than history.acts")

  let mut report := #[s!"Observed native run history: build {build}, schema {schema}",
    "Scope: recorded map points, rooms and player data; no map edges or combat replay."]
  let mut playerIndex : Std.HashMap Nat Nat := {}
  for i in [:roster.size] do
    let loc := s!"history.players[{i + 1}]"
    let id ← field roster[i]! loc "id" readId
    if playerIndex.contains id then throw (.input s!"{loc}: duplicate player ID")
    playerIndex := playerIndex.insert id i
    let character ← field roster[i]! loc "character" (readModelId "CHARACTER")
    report := report.push s!"Player {i + 1}: {character}"

  let mut balances : Array (Option Balance) := Array.replicate roster.size none
  let mut floor := 0
  for a in [:acts.size] do
    let act ← (readModelId "ACT" acts[a]!).mapError fun err => .input s!"history.acts[{a + 1}]: {err}"
    -- Acts describes the run's lineup; early endings do not have history for later acts.
    let points ← match history[a]? with
      | none => pure #[]
      | some rows => rows.getArr?.mapError fun err => .input s!"history.map_point_history[{a + 1}]: {err}"
    report := report.push s!"Act {a + 1}: {act} ({points.size} map points)"
    for f in [:points.size] do
      floor := floor + 1
      let loc := s!"Act {a + 1} floor {f + 1} (run floor {floor})"
      let point := points[f]!
      let kind ← field point loc "map_point_type" <| readKind
        ["unassigned", "unknown", "shop", "treasure", "rest_site", "monster", "elite", "boss", "ancient"]
      report := report.push s!"{loc}: map point {kind}"
      let rooms ← fieldD point loc "rooms" #[] Json.getArr?
      for r in [:rooms.size] do
        report := report.push (← renderRoom rooms[r]! loc (r + 1))

      let stats ← field point loc "player_stats" Json.getArr?
      let mut byPlayer : Array (Option Json) := Array.replicate roster.size none
      for r in [:stats.size] do
        let row := stats[r]!
        let rowLoc := s!"{loc}.player_stats[{r + 1}]"
        let id ← field row rowLoc "player_id" readId
        let some i := playerIndex.get? id | throw (.input s!"{rowLoc}: player ID not in the roster")
        if byPlayer[i]!.isSome then throw (.input s!"{loc}, player {i + 1}: duplicate player_stats")
        byPlayer := byPlayer.set! i (some row)

      for p in [:roster.size] do
        let playerLoc := s!"{loc}, player {p + 1}"
        let some row := byPlayer[p]! | throw (.input s!"{playerLoc}: missing player_stats")
        let actual ← readBalance row playerLoc
        let before := balances[p]!
        let expected ← advanceBalance before actual row playerLoc
        if before.isSome then checkBalance playerLoc expected actual
        balances := balances.set! p (some expected)
        let goldLine := before.elim s!"{actual.gold} (recorded baseline)" fun b => s!"{b.gold} -> {actual.gold}"
        report := report.push s!"  Player {p + 1}: HP {actual.hp}/{actual.maxHp}, gold {goldLine}"

        let choices ← fieldD row playerLoc "card_choices" #[] Json.getArr?
        for c in [:choices.size] do
          let choice := choices[c]!
          let choiceLoc := s!"{playerLoc}.card_choices[{c + 1}]"
          let card ← field choice choiceLoc "card" pure
          let cardLabel ← renderCard card s!"{choiceLoc}.card"
          let picked ← field choice choiceLoc "was_picked" Json.getBool?
          let status := if picked then "picked" else "not picked"
          report := report.push s!"    Card choice: {cardLabel} ({status})"
        let gains ← fieldD row playerLoc "cards_gained" #[] Json.getArr?
        for c in [:gains.size] do
          let cardLabel ← renderCard gains[c]! s!"{playerLoc}.cards_gained[{c + 1}]"
          report := report.push s!"    Card gained: {cardLabel}"

  let outcome := if win then "win" else if abandoned then "abandoned" else "loss"
  report := report.push s!"Recorded outcome: {outcome}"
  pure <| report.push s!"Ledger: {floor} map points; {floor - 1} across-point transitions matched. This checks only the recorded ledger for this run."

/-- Check a native schema-9 run history, not a combat trace. -/
def run (file : String) : IO UInt32 := do
  let raw ← try IO.FS.readFile file catch _ =>
    IO.eprintln "Run history input error: could not read the file"
    return 2
  -- A path or parser diagnostic can include account data. Report only the validated fields above.
  let parsed := (Json.parse raw).mapError fun _ => AuditError.input "invalid JSON"
  match parsed.bind audit with
  | .error (.input message) =>
    IO.eprintln s!"Run history input error: {message}"
    return 2
  | .error (.ledger message) =>
    IO.eprintln s!"Run history ledger mismatch: {message}"
    return 1
  | .ok report =>
    for line in report do IO.println line
    return 0

end Sts2Sim.RunHistoryAudit

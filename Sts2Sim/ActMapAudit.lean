import Lean.Data.Json
import Sts2Model.Run.Map

namespace Sts2Sim.ActMapAudit

open Lean Sts2Model.Core Sts2Model.Run

private def supportedSchema : Nat := 16

private def field (json : Json) (key : String) (decode : Json → Except String α) : Except String α :=
  ((json.getObjVal? key).bind decode).mapError fun msg => s!"{key}: {msg}"

private def optionalField (json : Json) (key : String) (decode : Json → Except String α) :
    Except String (Option α) :=
  match json.getObjValD key with
  | .null => pure none
  | value => some <$> (decode value).mapError (fun msg => s!"{key}: {msg}")

private def readList (decode : Json → Except String α) (json : Json) : Except String (List α) := do
  let values ← json.getArr?
  let items ← values.mapIdxM fun i value => (decode value).mapError (fun msg => s!"[{i}]: {msg}")
  pure items.toList

private def readCoord (json : Json) : Except String MapCoord := do
  pure ⟨← field json "col" Json.getNat?, ← field json "row" Json.getNat?⟩

-- Native saves use SnakeCaseJsonStringEnumConverter, not the replay wire spelling.
private def readPointType (json : Json) : Except String MapPointType := do
  match ← json.getStr? with
  | "unassigned" => pure .unassigned
  | "unknown" => pure .unknown
  | "shop" => pure .shop
  | "treasure" => pure .treasure
  | "rest_site" => pure .restSite
  | "monster" => pure .monster
  | "elite" => pure .elite
  | "boss" => pure .boss
  | "ancient" => pure .ancient
  | _ => throw "unsupported map point type"

private def readPoint (json : Json) : Except String MapPoint := do
  let coord ← field json "coord" readCoord
  let pointType ← field json "type" readPointType
  let children ← optionalField json "children" (readList readCoord)
  pure { coord, pointType, children := children.getD [] }

-- SerializableActMap stores the ordinary grid points apart from the special points.
private def readMap (json : Json) : Except String ActMap := do
  let width ← field json "width" Json.getNat?
  let mapLength ← field json "height" Json.getNat?
  let start ← field json "start" readPoint
  let boss ← field json "boss" readPoint
  let secondBoss ← optionalField json "second_boss" readPoint
  let points ← field json "points" (readList readPoint)
  let points := match secondBoss with
    | none => points
    | some point => point :: points
  pure { width, mapLength, startPoint := start.coord, bossPoint := boss.coord
         secondBossPoint := secondBoss.map (·.coord), points := start :: boss :: points }

private structure Input where
  actIndex : Nat
  map : ActMap
  visited : List MapCoord
  preFinished : Option Bool

private def readInput (json : Json) : Except String Input := do
  let schema ← field json "schema_version" Json.getNat?
  unless schema == supportedSchema do
    throw s!"unsupported schema_version {schema} (expected {supportedSchema})"
  let actIndex ← field json "current_act_index" Json.getNat?
  let currentAct ← field json "acts" (·.getArrVal? actIndex)
  let map ← (field currentAct "saved_map" readMap).mapError (fun msg => s!"acts[{actIndex}]: {msg}")
  -- saved_map.start_coords lists possible starting branches, not visits.
  let visited ← optionalField json "visited_map_coords" (readList readCoord)
  let preFinished ← optionalField json "pre_finished_room" (fun room => field room "is_pre_finished" Json.getBool?)
  pure { actIndex, map, visited := visited.getD [], preFinished }

private def showCoord (coord : MapCoord) : String := s!"({coord.col},{coord.row})"

private def checkUnique : List MapPoint → Except String Unit
  | [] => pure ()
  | point :: rest => do
      if rest.any (·.coord == point.coord) then
        throw s!"duplicate map coordinate {showCoord point.coord}"
      checkUnique rest

private def checkMap (map : ActMap) : Except String Unit := do
  checkUnique map.points
  for point in map.points do
    for child in point.children do
      if (map.getPoint child).isNone then
        throw s!"dangling child reference {showCoord point.coord} -> {showCoord child}"

private inductive RouteSummary where
  | empty
  | nonempty (first last : MapCoord) (edges : Nat)

private def checkRoute (map : ActMap) (visited : List MapCoord) : Except String RouteSummary := do
  let first :: rest := visited | return .empty
  unless first == map.startPoint do
    throw s!"first visited coordinate {showCoord first} does not match saved start {showCoord map.startPoint}"
  let mut last := first
  let mut edges : Nat := 0
  for next in rest do
    unless map.hasEdge last next do
      throw s!"broken edge #{edges + 1}: {showCoord last} -> {showCoord next}"
    last := next
    edges := edges + 1
  pure (.nonempty first last edges)

private def report (input : Input) (route : RouteSummary) : IO Unit := do
  let summary := match route with
    | .empty => "0 visited coordinates, 0 edges"
    | .nonempty first last edges =>
      s!"{edges + 1} visited coordinates, {edges} edges, from {showCoord first} to {showCoord last}"
  IO.println s!"Act map audit (schema {supportedSchema}, current act index {input.actIndex}): {summary}"
  match input.preFinished with
  | some true => IO.println "Saved room: pre-finished."
  | some false => IO.println "Saved room: not flagged pre-finished."
  | none => pure ()
  IO.println "Audit scope: saved current-act route only; reward claims and run outcome were not checked."

def run (file : String) : IO UInt32 := do
  let raw ← try IO.FS.readFile file catch _ =>
    IO.eprintln "Act map audit: unable to read input file"
    return 2
  match (Json.parse raw).bind readInput with
  | .error msg =>
    IO.eprintln s!"Act map audit: invalid input: {msg}"
    return 2
  | .ok input =>
    let label := s!"Act map audit (current act index {input.actIndex})"
    match checkMap input.map with
    | .error msg =>
      IO.eprintln s!"{label}: invalid saved map: {msg}"
      return 2
    | .ok () =>
      match checkRoute input.map input.visited with
      | .error msg =>
        IO.eprintln s!"{label}: {msg}"
        return 1
      | .ok route =>
        report input route
        return 0

end Sts2Sim.ActMapAudit

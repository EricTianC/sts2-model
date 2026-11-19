/-
  Act Map coordinate graph, placement constraints, and DAG traversal rules.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Map/MapCoord.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Map/MapPoint.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Map/StandardActMap.cs`
-/
import Sts2Model.Core.Enums

namespace Sts2Model.Run

open Sts2Model.Core

/-- `(col, row)` coordinate on the act map grid (`MapCoord.cs`). -/
structure MapCoord where
  col : Nat
  row : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A node on the act map with type and outgoing child edges (`MapPoint.cs`). -/
structure MapPoint where
  coord     : MapCoord
  pointType : MapPointType := .unassigned
  children  : List MapCoord := []
  deriving Repr, DecidableEq, Inhabited

/-- Full Act Map matching `StandardActMap` (row 0 = Starting, rows 1..mapLength-1,
    row mapLength = Boss, optional SecondBoss at mapLength+1). -/
structure ActMap where
  width           : Nat := 7
  mapLength       : Nat := 16
  startPoint      : MapCoord := ⟨3, 0⟩
  bossPoint       : MapCoord := ⟨3, 16⟩
  secondBossPoint : Option MapCoord := none
  points          : List MapPoint := []
  deriving Repr, DecidableEq, Inhabited

namespace ActMap

def getPoint (m : ActMap) (c : MapCoord) : Option MapPoint :=
  m.points.find? (·.coord == c)

def hasEdge (m : ActMap) (u v : MapCoord) : Bool :=
  match m.getPoint u with
  | none   => false
  | some p => p.children.contains v

def maxRow (m : ActMap) : Nat :=
  match m.secondBossPoint with
  | some sb => max m.bossPoint.row sb.row
  | none    => m.bossPoint.row

/-- Every edge goes strictly upward (`u.row < v.row`) — guarantees the map is a DAG! -/
def StrictlyRowIncreasing (m : ActMap) : Prop :=
  ∀ u v, m.hasEdge u v = true → u.row < v.row

/-- `StandardActMap` minimum row restrictions (`_lowestRowByPointType`). -/
def respectsLowestRow (pt : MapPoint) : Bool :=
  match pt.pointType with
  | .restSite => pt.coord.row ≥ 5
  | .elite    => pt.coord.row ≥ 6
  | _         => true

/-- Node types banned from appearing twice in a row along an edge (`_parentMapPointRestrictions`). -/
def cannotRepeatAdjacent : MapPointType → Bool
  | .elite | .restSite | .treasure | .shop => true
  | _ => false

/-- Placement validity matching `StandardActMap.cs` constraints. -/
def ValidPlacement (m : ActMap) : Prop :=
  (∀ pt ∈ m.points, respectsLowestRow pt = true) ∧
  (∀ pt ∈ m.points, ∀ c ∈ pt.children,
    match m.getPoint c with
    | none    => True
    | some cp => cannotRepeatAdjacent pt.pointType = true → pt.pointType ≠ cp.pointType)

/-- Inductive valid path predicate on `ActMap`. -/
inductive ValidPath (m : ActMap) : List MapCoord → Prop where
  | single (u : MapCoord) : ValidPath m [u]
  | step   (u v : MapCoord) (rest : List MapCoord) :
      m.hasEdge u v = true → ValidPath m (v :: rest) → ValidPath m (u :: v :: rest)

/-- Last coordinate of a non-empty list. -/
def lastCoord (default : MapCoord) : List MapCoord → MapCoord
  | []      => default
  | [x]     => x
  | _ :: xs => lastCoord default xs

end ActMap
end Sts2Model.Run

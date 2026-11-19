/-
  Monster Move State Machine modeling `MonsterState`, `MoveState`, `ConditionalBranchState`,
  `RandomBranchState`, and acyclic well-formedness guaranteeing termination on `MoveState`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.MonsterMoves.MonsterMoveStateMachine/*.cs`
-/
import Sts2Model.Core.Rng
import Sts2Model.Model.State

namespace Sts2Model.Combat

open Sts2Model.Core
open Sts2Model.Model

abbrev StateId := String

/-- Monster state node kinds. Ref: `Core.MonsterMoves.MonsterMoveStateMachine/*.cs`. -/
inductive MonsterStateKind where
  | move (followUpId : StateId) (canTransitionAway : Bool := true) (mustPerformOnce : Bool := false)
  | conditionalBranch (branches : List (CombatState → Creature → Bool × StateId)) (fallbackId : StateId)
  | randomBranch (weightedTargets : List (StateId × Nat))

/-- Named node in a monster move state machine. -/
structure MonsterNode where
  id                : StateId
  kind              : MonsterStateKind
  shouldAppearInLogs : Bool := true

/-- Deterministic monster state machine matching `MonsterMoveStateMachine.cs`. -/
structure MonsterStateMachine where
  initialStateId     : StateId
  currentStateId     : StateId
  performedFirstMove : Bool := false
  nodes              : StateId → Option MonsterNode
  stateLog           : List StateId := []

namespace MonsterStateMachine

def selectWeightedTarget (targets : List (StateId × Nat)) (roll : Nat) : StateId :=
  let rec go (rem : Nat) : List (StateId × Nat) → StateId
    | [] => ""
    | [(sid, _)] => sid
    | (sid, w) :: rest =>
        if rem < w then sid else go (rem - w) rest
  go roll targets

/-- Evaluate one transition step out of a branch or move node. -/
def stepTransition (sm : MonsterStateMachine) (cs : CombatState) (owner : Creature)
    (node : MonsterNode) (rng : Rng) : StateId × Rng :=
  match node.kind with
  | .move followUp _ _ =>
      let nextId := if followUp == "" then sm.initialStateId else followUp
      (nextId, rng)
  | .conditionalBranch branches fallbackId =>
      let rec pick : List (CombatState → Creature → Bool × StateId) → StateId
        | [] => fallbackId
        | fn :: rest =>
            let (cond, tid) := fn cs owner
            if cond then tid else pick rest
      (pick branches, rng)
  | .randomBranch targets =>
      let totalW := targets.foldl (fun acc (_, w) => acc + w) 0
      if totalW == 0 then
        (sm.initialStateId, rng)
      else
        let (roll, rng') := rng.nextInt totalW
        (selectWeightedTarget targets roll, rng')

def isMoveNode (n : MonsterNode) : Bool :=
  match n.kind with
  | .move _ _ _ => true
  | _ => false

/-- Fuel-bounded traversal matching `MonsterMoveStateMachine.FindNextMoveState` (`do ... while (!IsMove)`). -/
def rollMoveFuel (fuel : Nat) (sm : MonsterStateMachine) (cs : CombatState)
    (owner : Creature) (rng : Rng) : Option (StateId × MonsterStateMachine × Rng) :=
  match sm.nodes sm.currentStateId with
  | none => none
  | some cur =>
      let canLeave := match cur.kind with
        | .move _ cta _ => cta && sm.performedFirstMove
        | _ => true
      if !canLeave && isMoveNode cur then
        some (cur.id, sm, rng)
      else
        let rec loop (k : Nat) (curId : StateId) (r : Rng) : Option (StateId × Rng) :=
          match k with
          | 0 => none
          | k' + 1 =>
              match sm.nodes curId with
              | none => none
              | some n =>
                  let (nextId, r') := sm.stepTransition cs owner n r
                  let targetId := if nextId == "" then sm.initialStateId else nextId
                  match sm.nodes targetId with
                  | none => none
                  | some targetNode =>
                      if isMoveNode targetNode then
                        some (targetId, r')
                      else
                        loop k' targetId r'
        match loop fuel sm.currentStateId rng with
        | none => none
        | some (finalMoveId, r') =>
            let sm' :=
              { sm with
                currentStateId := finalMoveId
              , stateLog := sm.stateLog ++ [finalMoveId] }
            some (finalMoveId, sm', r')

/-- Acyclic well-formedness predicate:
    every non-move node exists with bounded integer rank `rank : StateId → Nat`,
    every transition from a move or branch points to an existing node,
    and every transition into a non-move node strictly decreases `rank`. -/
structure WellFormed (sm : MonsterStateMachine) (rank : StateId → Nat) : Prop where
  allTargetsExist : ∀ sid node, sm.nodes sid = some node →
    ∀ cs owner rng,
      let (nid, _) := sm.stepTransition cs owner node rng
      let tid := if nid == "" then sm.initialStateId else nid
      ∃ targetNode, sm.nodes tid = some targetNode
  branchDecreases : ∀ sid node, sm.nodes sid = some node →
    ∀ cs owner rng,
      let (nid, _) := sm.stepTransition cs owner node rng
      let tid := if nid == "" then sm.initialStateId else nid
      ∀ targetNode, sm.nodes tid = some targetNode →
        isMoveNode targetNode = false →
        isMoveNode node = false →
        rank tid < rank sid
  moveTargetsHaveBoundedRank : ∀ sid node, sm.nodes sid = some node →
    isMoveNode node = true →
    ∀ cs owner rng,
      let (nid, _) := sm.stepTransition cs owner node rng
      let tid := if nid == "" then sm.initialStateId else nid
      ∃ targetNode, sm.nodes tid = some targetNode

end MonsterStateMachine
end Sts2Model.Combat

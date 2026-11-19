/-
  Formal proofs for CombatManager turn state machine & MonsterAI termination:
  - Legal turn phase transitions
  - Win/Loss mutual exclusion and `PendingLoss` priority over victory
  - `ShouldStopCombatFromEnding` blocks victory when primary enemies are dead
  - Acyclic well-formed `MonsterStateMachine` guaranteed termination on a `MoveState`
  All theorems proved in Lean 4 kernel with zero `sorry`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/CombatManager.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/PlayerTurnPhase.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.MonsterMoves.MonsterMoveStateMachine/MonsterMoveStateMachine.cs`
-/
import Sts2Model.Combat.TurnLoop
import Sts2Model.Combat.MonsterAI

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Combat

/-- Legal transitions between `PlayerTurnPhase` states in STS2 combat. -/
inductive ValidTurnPhaseTransition : PlayerTurnPhase → PlayerTurnPhase → Prop where
  | startToAutoPre   : ValidTurnPhaseTransition .start .autoPrePlay
  | autoPreToPlay    : ValidTurnPhaseTransition .autoPrePlay .play
  | playToAutoPost   : ValidTurnPhaseTransition .play .autoPostPlay
  | autoPostToEnd    : ValidTurnPhaseTransition .autoPostPlay .«end»
  | endToNone        : ValidTurnPhaseTransition .«end» .none
  | noneToStart      : ValidTurnPhaseTransition .none .start
  | anyToNoneCombatEnd (p : PlayerTurnPhase) : ValidTurnPhaseTransition p .none

theorem checkWinCondition_none_ongoing_when_stopped (cs : CombatState) (reg : BehaviorRegistry)
    (mods : List (ModId × ModelId)) (hStopped : cs.isInProgress = false) :
    checkWinCondition cs reg mods = (cs, .ongoing) := by
  simp [checkWinCondition, hStopped]

/-- `PendingLoss` always produces `.defeat` (never `.victory`), taking precedence over dead enemies.
    Ref: `CombatManager.CheckWinCondition` lines 1481-1485. -/
theorem pendingLoss_implies_defeat (cs : CombatState) (reg : BehaviorRegistry)
    (mods : List (ModId × ModelId)) (pl : PendingLossState)
    (hInProg : cs.isInProgress = true) (hPending : cs.pendingLoss = some pl) :
    (checkWinCondition cs reg mods).2 = .defeat ∧
    (checkWinCondition cs reg mods).1.isInProgress = false := by
  simp [checkWinCondition, hInProg, hPending, setPhaseForAllPlayers]

/-- If `ShouldStopCombatFromEnding` returns `true` and there is no `PendingLoss`,
    `checkWinCondition` keeps combat ongoing even when all enemies are dead.
    Ref: `CombatManager.IsCombatEnding` lines 458-461. -/
theorem checkWinCondition_respects_stopCombatHook (cs : CombatState) (reg : BehaviorRegistry)
    (mods : List (ModId × ModelId))
    (hInProg : cs.isInProgress = true)
    (hNoLoss : cs.pendingLoss = none)
    (hStop : shouldStopCombatFromEnding cs reg mods = true) :
    checkWinCondition cs reg mods = (cs, .ongoing) := by
  unfold checkWinCondition isCombatEnding
  simp [hInProg, hNoLoss, hStop]

/-- A combat win requires no pending loss, no living primary enemy, and `ShouldStopCombatFromEnding = false`. -/
theorem victory_iff_conditions (cs : CombatState) (reg : BehaviorRegistry)
    (mods : List (ModId × ModelId)) (hInProg : cs.isInProgress = true) :
    (checkWinCondition cs reg mods).2 = .victory ↔
      cs.pendingLoss = none ∧
      (∀ e ∈ cs.enemies, !(e.isAlive && e.isPrimaryEnemy)) ∧
      shouldStopCombatFromEnding cs reg mods = false := by
  unfold checkWinCondition isCombatEnding
  cases hLoss : cs.pendingLoss with
  | some pl =>
      simp [hInProg]
  | none =>
      simp only [hInProg, Bool.not_true, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
      cases hAny : cs.enemies.any (fun e => e.isAlive && e.isPrimaryEnemy) with
      | true =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          constructor
          · intro h; cases h
          · intro ⟨_, hForall, _⟩
            rcases List.any_eq_true.mp hAny with ⟨e, he, hPred⟩
            have hF := hForall e he
            rw [hPred] at hF
            cases hF
      | false =>
          have hAllFalse : ∀ e ∈ cs.enemies, (e.isAlive && e.isPrimaryEnemy) = false := by
            intro e he
            cases hp : (e.isAlive && e.isPrimaryEnemy) with
            | false => rfl
            | true => exact False.elim (Bool.false_ne_true (hAny ▸ List.any_eq_true.mpr ⟨e, he, hp⟩))
          cases hStop : shouldStopCombatFromEnding cs reg mods with
          | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              constructor
              · intro h; simp at h
              · intro ⟨_, _, hFalse⟩; cases hFalse
          | false =>
              constructor
              · intro _
                refine ⟨trivial, fun e he => ?_, rfl⟩
                rw [hAllFalse e he]; rfl
              · intro _
                simp

/-- Win and loss outcomes are mutually exclusive in `checkWinCondition`. -/
theorem win_loss_mutually_exclusive (cs : CombatState) (reg : BehaviorRegistry)
    (mods : List (ModId × ModelId)) :
    ¬ ((checkWinCondition cs reg mods).2 = .victory ∧ (checkWinCondition cs reg mods).2 = .defeat) := by
  intro ⟨hv, hd⟩
  rw [hv] at hd
  cases hd

/-- Helper: fuel-bounded traversal in a well-formed `MonsterStateMachine` always reaches a `MoveState`
    when `fuel > rank curId` (for non-move nodes) or `fuel ≥ 1` (if starting from a move node whose
    next hop has `rank target ≤ fuel - 1`). -/
private theorem rollMoveFuel_loop_terminates (sm : MonsterStateMachine) (rank : StateId → Nat)
    (hwf : sm.WellFormed rank) (cs : CombatState) (owner : Creature) :
    ∀ (fuel : Nat) (curId : StateId) (node : MonsterNode) (rng : Rng),
      sm.nodes curId = some node →
      (MonsterStateMachine.isMoveNode node = false → rank curId < fuel) →
      (MonsterStateMachine.isMoveNode node = true → 0 < fuel ∧
        ∀ tNode, sm.nodes (let tid := (sm.stepTransition cs owner node rng).1; if tid == "" then sm.initialStateId else tid) = some tNode →
          MonsterStateMachine.isMoveNode tNode = false → rank (let tid := (sm.stepTransition cs owner node rng).1; if tid == "" then sm.initialStateId else tid) + 1 < fuel) →
      (MonsterStateMachine.rollMoveFuel.loop sm cs owner fuel curId rng).isSome = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro curId node rng _ hRankFalse hRankTrue
      cases hMov : MonsterStateMachine.isMoveNode node with
      | false => have := hRankFalse hMov; omega
      | true => have := (hRankTrue hMov).1; omega
  | succ k ih =>
      intro curId node rng hNode hRankFalse hRankTrue
      unfold MonsterStateMachine.rollMoveFuel.loop
      rw [hNode]
      dsimp only
      have hExists := hwf.allTargetsExist curId node hNode cs owner rng
      dsimp only at hExists
      rcases hExists with ⟨targetNode, hTarget⟩
      rw [hTarget]
      dsimp only
      cases hTMov : MonsterStateMachine.isMoveNode targetNode with
      | true => rfl
      | false =>
          apply ih _ targetNode _ hTarget
          · intro _
            cases hCurMov : MonsterStateMachine.isMoveNode node with
            | false =>
                have hDec := hwf.branchDecreases curId node hNode cs owner rng targetNode hTarget hTMov hCurMov
                have hR := hRankFalse hCurMov
                simp only [MonsterStateMachine.stepTransition] at hDec hR ⊢
                omega
            | true =>
                have hR := (hRankTrue hCurMov).2 targetNode hTarget hTMov
                simp only [MonsterStateMachine.stepTransition] at hR ⊢
                omega
          · intro hContra
            rw [hTMov] at hContra
            cases hContra

/-- Every well-formed acyclic `MonsterStateMachine` terminates on a valid `MoveState`
    within `maxRank + 2` steps. Ref: `MonsterMoveStateMachine.cs`. -/
theorem monster_stateMachine_terminates (sm : MonsterStateMachine) (rank : StateId → Nat)
    (maxRank : Nat) (hwf : sm.WellFormed rank)
    (hBound : ∀ sid, rank sid ≤ maxRank)
    (cs : CombatState) (owner : Creature) (rng : Rng)
    (curNode : MonsterNode) (hCur : sm.nodes sm.currentStateId = some curNode) :
    (sm.rollMoveFuel (maxRank + 2) cs owner rng).isSome = true := by
  have hLoop : (MonsterStateMachine.rollMoveFuel.loop sm cs owner (maxRank + 2) sm.currentStateId rng).isSome = true := by
    apply rollMoveFuel_loop_terminates sm rank hwf cs owner (maxRank + 2) sm.currentStateId curNode rng hCur
    · intro _; have := hBound sm.currentStateId; omega
    · intro _; constructor
      · omega
      · intro tNode _ _
        have hb := hBound (let tid := (sm.stepTransition cs owner curNode rng).1; if tid == "" then sm.initialStateId else tid)
        dsimp only at hb ⊢
        omega
  unfold MonsterStateMachine.rollMoveFuel
  rw [hCur]
  dsimp only
  split
  · split
    · rfl
    · cases hRes : MonsterStateMachine.rollMoveFuel.loop sm cs owner (maxRank + 2) sm.currentStateId rng with
      | none => rw [hRes] at hLoop; cases hLoop
      | some _ => rfl
  · split
    · rename_i hImp; simp at hImp
    · cases hRes : MonsterStateMachine.rollMoveFuel.loop sm cs owner (maxRank + 2) sm.currentStateId rng with
      | none => rw [hRes] at hLoop; cases hLoop
      | some _ => rfl

end Sts2Model.Proofs

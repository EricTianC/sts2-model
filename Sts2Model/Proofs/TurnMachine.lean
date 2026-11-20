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
open Sts2Model.Command
open Sts2Model.Combat
open Sts2Model.Mechanics

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

/-- Observable per-player orb-queue capacity list in `CombatState`. -/
def playerOrbCapacities (cs : CombatState) : List (PlayerId × Option Nat) :=
  cs.players.map fun p => (p.playerId, p.combatState.map (·.orbQueue.capacity))

private theorem updateCreature_preserves_players (cs : CombatState) (cid : CreatureId) (f : Creature → Creature) :
    (cs.updateCreature cid f).players = cs.players := rfl

private theorem recordHistory_preserves_players (cs : CombatState) (entry : CombatHistoryEntry) :
    (cs.recordHistory entry).players = cs.players := rfl

private theorem updatePlayer_preserves_orbCapacities (cs : CombatState) (pid : PlayerId) (f : Player → Player)
    (hPres : ∀ p, (f p).playerId = p.playerId ∧
      ((f p).combatState.map (·.orbQueue.capacity)) = (p.combatState.map (·.orbQueue.capacity))) :
    playerOrbCapacities (cs.updatePlayer pid f) = playerOrbCapacities cs := by
  unfold playerOrbCapacities CombatState.updatePlayer
  dsimp only
  rw [List.map_map]
  congr 1
  funext p
  dsimp only [Function.comp_def]
  split
  · exact Prod.ext (hPres p).1 (hPres p).2
  · rfl

private theorem gainBlock_preserves_players (cs : CombatState) (reg : BehaviorRegistry)
    (tid : CreatureId) (amt : Dec) (props : ValueProp) (cardSource : Option CardInstance)
    (modSubscribers : List (ModId × ModelId)) :
    (gainBlock cs reg tid amt props cardSource modSubscribers).1.players = cs.players := by
  unfold gainBlock
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

private theorem foldl_recordHistory_players (xs : List DamageResult) (dealerId : Option CreatureId) (st : CombatState) :
    (xs.foldl (fun (acc : CombatState) r => acc.recordHistory (.damageDealt acc.roundNumber dealerId r)) st).players = st.players := by
  induction xs generalizing st with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem damagePreBlockStage_players (cs : CombatState) (reg : BehaviorRegistry)
    (orig : Creature) (oid : CreatureId) (amt modAmt : Dec) (props : ValueProp) (d : Option Creature)
    (card : Option CardInstance) (subs : List (ModId × ModelId)) :
    (damagePreBlockStage cs reg orig oid amt modAmt props d card subs).1.players = cs.players := by
  unfold damagePreBlockStage
  cases (modifyPreBlockDamageTarget cs reg orig amt props d subs).bind cs.findCreature <;> rfl

private theorem damageBlockStage_players (cs1 : CombatState) (bhId : CreatureId)
    (dmgAfterPre : Dec) (props : ValueProp) :
    (damageBlockStage cs1 bhId dmgAfterPre props).1.players = cs1.players := by
  unfold damageBlockStage
  cases cs1.findCreature bhId <;> rfl

private theorem damageUnblockedStage_players (cs2 : CombatState) (reg : BehaviorRegistry)
    (ubId origId : CreatureId) (u0 dmgRem bDec : Dec) (blkB fullB : Bool)
    (props : ValueProp) (d : Option Creature) (card : Option CardInstance) (subs : List (ModId × ModelId)) :
    (damageUnblockedStage cs2 reg ubId origId u0 dmgRem bDec blkB fullB props d card subs).1.players = cs2.players := by
  unfold damageUnblockedStage
  cases cs2.findCreature ubId <;> rfl

private theorem damageOverkillStage_players (cs3 : CombatState) (reg : BehaviorRegistry)
    (ubId origId : CreatureId) (overkill : Nat) (bDec : Dec) (blkB fullB : Bool)
    (props : ValueProp) (d : Option Creature) (card : Option CardInstance) (subs : List (ModId × ModelId)) :
    (damageOverkillStage cs3 reg ubId origId overkill bDec blkB fullB props d card subs).1.players = cs3.players := by
  unfold damageOverkillStage
  split
  · rfl
  · cases cs3.findCreature origId with
    | none => rfl
    | some _ => dsimp only; split <;> rfl

private theorem damageSingleTargetCore_preserves_players (cs : CombatState) (reg : BehaviorRegistry)
    (tid : CreatureId) (amt : Dec) (props : ValueProp) (dealerId : Option CreatureId)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType)
    (modSubscribers : List (ModId × ModelId)) :
    (damageSingleTargetCore cs reg tid amt props dealerId cardSource hookType modSubscribers).1.players = cs.players := by
  have hLive : ∀ s d, (damageSingleTargetCore.damageLiveDealer dealerId s reg tid amt props d cardSource hookType modSubscribers).1.players = s.players := by
    intro s d
    unfold damageSingleTargetCore.damageLiveDealer
    cases s.findCreature tid with
    | none => rfl
    | some originalTarget =>
        dsimp only
        cases originalTarget.isDead with
        | true => rfl
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [foldl_recordHistory_players, damageOverkillStage_players, damageUnblockedStage_players,
              damageBlockStage_players, damagePreBlockStage_players]
  unfold damageSingleTargetCore
  cases dealerId.bind cs.findCreature with
  | none => exact hLive cs none
  | some d =>
      dsimp only
      split
      · rfl
      · exact hLive cs (some d)

private theorem damageSingleTarget_preserves_players (cs : CombatState) (reg : BehaviorRegistry)
    (tid : CreatureId) (amt : Dec) (props : ValueProp) (dealerId : Option CreatureId)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType)
    (modSubscribers : List (ModId × ModelId)) :
    (damageSingleTarget cs reg tid amt props dealerId cardSource hookType modSubscribers).1.players = cs.players := by
  unfold damageSingleTarget
  have hLoop : ∀ (effs : List HookEffect) (acc : CombatState),
      (effs.foldl (fun s eff =>
        match eff with
        | .dealDamage rD rT rA rP => (damageSingleTargetCore s reg rT rA rP rD none ModifyDamageHookType.all modSubscribers).1
        | _ => s) acc).players = acc.players := by
    intro effs
    induction effs with
    | nil => intro acc; rfl
    | cons eff _ ih =>
        intro acc
        dsimp only [List.foldl]
        cases eff with
        | dealDamage rD rT rA rP => rw [ih, damageSingleTargetCore_preserves_players]
        | _ => exact ih acc
  rw [damageSingleTargetCore_preserves_players]
  dsimp only
  cases hD : dealerId.bind cs.findCreature with
  | none =>
      dsimp only
      cases cs.findCreature tid with
      | none => rfl
      | some target =>
          dsimp only
          cases hDead : target.isDead with
          | true => rfl
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hLoop _ cs
  | some d =>
      dsimp only
      by_cases hDDead : d.isDead = true
      · simp [hDDead]
      · have hF : (!!d.isDead) = false := by revert hDDead; cases d.isDead <;> simp
        simp only [hF, Bool.false_eq_true, ↓reduceIte]
        cases cs.findCreature tid with
        | none => rfl
        | some target =>
            dsimp only
            by_cases hTDead : target.isDead = true
            · simp [hTDead]
            · simp only [hTDead, Bool.false_eq_true, ↓reduceIte]
              exact hLoop _ cs

private theorem damage_preserves_players (cs : CombatState) (reg : BehaviorRegistry)
    (tids : List CreatureId) (amt : Dec) (props : ValueProp) (dealerId : Option CreatureId)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType)
    (modSubscribers : List (ModId × ModelId)) :
    (damage cs reg tids amt props dealerId cardSource hookType modSubscribers).1.players = cs.players := by
  unfold damage
  have hFold : ∀ (xs : List CreatureId) (acc : CombatState × List DamageResult),
      (xs.foldl (fun (accState, accRes) tid =>
        let (s', rs) := damageSingleTarget accState reg tid amt props dealerId cardSource hookType modSubscribers
        (s', accRes ++ rs)) acc).1.players = acc.1.players := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons _ _ ih =>
        intro acc
        dsimp only [List.foldl]
        rw [ih, damageSingleTarget_preserves_players]
  exact hFold tids (cs, [])

private theorem triggerOrbPassiveWithFocus_preserves_orbCapacities (cs : CombatState)
    (reg : BehaviorRegistry) (pid : PlayerId) (orb : OrbInstance)
    (modSubscribers : List (ModId × ModelId)) :
    playerOrbCapacities (triggerOrbPassiveWithFocus cs reg pid orb modSubscribers) =
      playerOrbCapacities cs := by
  unfold triggerOrbPassiveWithFocus
  cases cs.isEnding with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases cs.findPlayer pid with
      | none => rfl
      | some player =>
          dsimp only
          cases orb.kind with
          | lightning =>
              dsimp only
              cases cs.hittableEnemies.head? with
              | none => rfl
              | some target =>
                  dsimp only
                  unfold playerOrbCapacities
                  rw [damageSingleTarget_preserves_players]
          | frost =>
              dsimp only
              cases (cs.findCreature player.creatureId |>.map (·.hasPower hibernatePowerModelId) |>.getD false) with
              | false =>
                  simp only [Bool.not_false, ↓reduceIte]
                  unfold playerOrbCapacities
                  rw [gainBlock_preserves_players]
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  have hFold : ∀ (ps : List Player) (acc : CombatState),
                      (ps.foldl (fun s (pl : Player) =>
                        if pl.playerId == pid then s
                        else (gainBlock s reg pl.creatureId (effectivePassiveVal (focusAmountOf cs pid) orb) BlockProps.nonCardUnpowered none modSubscribers).1) acc).players = acc.players := by
                    intro ps
                    induction ps with
                    | nil => intro acc; rfl
                    | cons pl _ ih =>
                        intro acc
                        dsimp only [List.foldl]
                        rw [ih]
                        split
                        · rfl
                        · exact gainBlock_preserves_players _ _ _ _ _ _ _
                  unfold playerOrbCapacities
                  rw [hFold, gainBlock_preserves_players]
          | dark =>
              apply updatePlayer_preserves_orbCapacities
              intro p; cases hCs : p.combatState with
              | none => exact ⟨rfl, by simp [hCs]⟩
              | some _ => exact ⟨rfl, rfl⟩
          | plasma =>
              apply updatePlayer_preserves_orbCapacities
              intro p; cases hCs : p.combatState with
              | none => exact ⟨rfl, by simp [hCs]⟩
              | some _ => exact ⟨rfl, by simp [PlayerCombatState.gainEnergy]⟩
          | glass =>
              dsimp only
              split
              · rfl
              · have hDmg : ∀ (s : CombatState) (ts : List CreatureId),
                    playerOrbCapacities (damage s reg ts (effectivePassiveVal (focusAmountOf cs pid) orb)
                      DamageProps.nonCardUnpowered (some player.creatureId) none ModifyDamageHookType.all modSubscribers).1 =
                    playerOrbCapacities s := fun s ts => by
                  unfold playerOrbCapacities
                  rw [damage_preserves_players]
                rw [hDmg]
                apply updatePlayer_preserves_orbCapacities
                intro p; cases hCs : p.combatState with
                | none => exact ⟨rfl, by simp [hCs]⟩
                | some _ => exact ⟨rfl, rfl⟩
          | custom _ => rfl

/-- Executing turn-end orb passives never modifies any player's orb slot capacity. -/
theorem orb_turn_end_passives_preserve_capacity (cs : CombatState) (reg : BehaviorRegistry)
    (pid : PlayerId) (modSubscribers : List (ModId × ModelId)) :
    playerOrbCapacities (triggerTurnEndOrbs cs reg pid modSubscribers) =
      playerOrbCapacities cs := by
  unfold triggerTurnEndOrbs
  cases hPcs : (cs.findPlayer pid |>.bind (·.combatState)) with
  | none => rfl
  | some pcs =>
      dsimp only
      have hFold : ∀ (os : List OrbInstance) (acc : CombatState),
          playerOrbCapacities (os.foldl (fun s o =>
            if o.kind != .plasma then triggerOrbPassiveWithFocus s reg pid o modSubscribers else s) acc) =
          playerOrbCapacities acc := by
        intro os
        induction os with
        | nil => intro acc; rfl
        | cons o _ ih =>
            intro acc
            dsimp only [List.foldl]
            rw [ih]
            split
            · exact triggerOrbPassiveWithFocus_preserves_orbCapacities acc reg pid o modSubscribers
            · rfl
      exact hFold pcs.orbQueue.orbs cs

/-- `runSideTurnEndLifecycle` is a no-op when combat is no longer in progress. -/
theorem runSideTurnEndLifecycle_noop_when_not_in_progress (cs : CombatState) (reg : BehaviorRegistry)
    (side : CombatSide) (modSubscribers : List (ModId × ModelId))
    (hStopped : cs.isInProgress = false) :
    runSideTurnEndLifecycle cs reg side modSubscribers = (cs, .ongoing) := by
  simp [runSideTurnEndLifecycle, hStopped]

/-- When Ascension value ≥ Base value, `AscensionVal.eval` is monotone in Ascension level. -/
theorem ascensionVal_eval_monotone_when_asc_ge_base (v : AscensionVal) (a b : Nat)
    (hle : a ≤ b) (hAscGe : v.baseVal ≤ v.ascVal) :
    v.eval a ≤ v.eval b := by
  unfold AscensionVal.eval
  by_cases ha : a ≥ v.threshold
  · have hb : b ≥ v.threshold := by omega
    simp [ha, hb]
  · by_cases hb : b ≥ v.threshold
    · simp [ha, hb, hAscGe]
    · simp [ha, hb]

end Sts2Model.Proofs

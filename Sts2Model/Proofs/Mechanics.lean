/-
  Formal proofs for STS2 character mechanics:
  - Orbs: capacity ≤ 10 invariant, Plasma Focus immunity, Glass passive/evoke non-negativity & 2x factor
  - Necrobinder: DieForYou never redirects Unpowered or dead Osty; Doom iff CurrentHp <= Amount
  - Regent: Forge creates SovereignBlade when absent and sets forged flag; loseStars non-underflow
  - Fool: Destroyed arrow cannot be retrieved; distinct melodies per turn ≤ 3
  - Dread: Dominion is always cleared upon entering the act's boss room
  All theorems proved in Lean 4 kernel with zero `sorry`.
-/
import Sts2Model.Mechanics.Orbs
import Sts2Model.Mechanics.Necrobinder
import Sts2Model.Mechanics.Regent
import Sts2Model.Mechanics.Fool
import Sts2Model.Mechanics.Dread
import Sts2Model.Core.Dec

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command
open Sts2Model.Mechanics

-- ============================================================================
-- Defect Orb Invariants
-- ============================================================================

theorem orbQueue_addCapacity_le_max (q : OrbQueue) (amt : Nat) :
    (q.addCapacity amt).capacity ≤ OrbQueue.maxCapacity := by
  simp [OrbQueue.addCapacity, Nat.min_le_left]

theorem orbQueue_removeCapacity_le_max (q : OrbQueue) (amt : Nat) (hLe : q.capacity ≤ OrbQueue.maxCapacity) :
    (q.removeCapacity amt).capacity ≤ OrbQueue.maxCapacity := by
  simp only [OrbQueue.removeCapacity]
  omega

theorem plasma_immune_to_focus (focus : Int) (baseVal : Dec) :
    modifyOrbValue focus .plasma baseVal = baseVal := rfl

theorem effectivePassiveVal_nonneg (focus : Int) (orb : OrbInstance)
    (hPlasma : orb.kind = .plasma → Dec.nonneg orb.basePassive) :
    Dec.nonneg (effectivePassiveVal focus orb) := by
  unfold effectivePassiveVal modifyOrbValue
  cases hK : orb.kind with
  | plasma => exact hPlasma hK
  | _ =>
      dsimp only
      exact Dec.nonneg_maxZero _

theorem glass_evoke_is_double_passive (focus : Int) (orb : OrbInstance) (hK : orb.kind = .glass) :
    effectiveEvokeVal focus orb = Dec.mul (effectivePassiveVal focus orb) (Dec.ofInt 2) := by
  simp [effectiveEvokeVal, hK]

theorem glass_passive_nonneg (orb : OrbInstance) :
    Dec.nonneg (Dec.maxZero (Dec.sub orb.basePassive Dec.one)) :=
  Dec.nonneg_maxZero _

-- ============================================================================
-- Necrobinder (Osty & Doom) Invariants
-- ============================================================================

theorem dieForYou_ignores_unpowered (cs : CombatState) (ctx : ListenerCtx)
    (curTarget : CreatureId) (amt : Dec) (props : ValueProp) (dealer : Option Creature)
    (hUnpowered : props.isPoweredAttack = false) :
    (dieForYouBehavior cs).modifyUnblockedDamageTarget ctx curTarget amt props dealer = curTarget := by
  unfold dieForYouBehavior
  dsimp only
  split
  · rfl
  · split
    · rfl
    · simp [hUnpowered]

theorem dieForYou_ignores_dead_osty (cs : CombatState) (ctx : ListenerCtx)
    (osty : Creature) (hFind : (ctx.ownerId |>.bind cs.findCreature) = some osty)
    (hDead : osty.isDead = true)
    (curTarget : CreatureId) (amt : Dec) (props : ValueProp) (dealer : Option Creature) :
    (dieForYouBehavior cs).modifyUnblockedDamageTarget ctx curTarget amt props dealer = curTarget := by
  unfold dieForYouBehavior
  dsimp only
  rw [hFind]
  dsimp only
  cases osty.petOwnerId |>.bind cs.findPlayer with
  | none => rfl
  | some _ => simp [hDead]

theorem isCreatureDoomed_iff (c : Creature) (p : PowerInstance)
    (hPow : c.getPower doomPowerModelId = some p) :
    isCreatureDoomed c = true ↔ (c.currentHp : Int) ≤ p.amount := by
  simp [isCreatureDoomed, hPow]

-- ============================================================================
-- Regent (Forge & Stars) Invariants
-- ============================================================================

private theorem findPlayer_list_update (ps : List Player) (pid : PlayerId) (f : Player → Player)
    (hf : ∀ x, (f x).playerId = x.playerId) :
    ∀ p, ps.find? (·.playerId == pid) = some p →
      (ps.map (fun x => if x.playerId == pid then f x else x)).find? (·.playerId == pid) = some (f p) := by
  induction ps with
  | nil => intro p h; cases h
  | cons hd tl ih =>
      intro p hFind
      unfold List.find? at hFind
      cases hEq : (hd.playerId == pid) with
      | true =>
          simp only [hEq] at hFind
          cases hFind
          simp only [List.map_cons, hEq, ↓reduceIte, List.find?, hf hd]
      | false =>
          simp only [hEq] at hFind
          have hNe : ((if (hd.playerId == pid) = true then f hd else hd).playerId == pid) = false := by
            simp [hEq]
          simp only [List.map_cons, List.find?, hNe]
          exact ih p hFind

theorem updatePlayer_findPlayer (cs : CombatState) (pid : PlayerId) (f : Player → Player)
    (hf : ∀ x, (f x).playerId = x.playerId) (p : Player)
    (hFind : cs.findPlayer pid = some p) :
    (cs.updatePlayer pid f).findPlayer pid = some (f p) :=
  findPlayer_list_update cs.players pid f hf p hFind

theorem forge_sets_forged_flag (cs : CombatState) (pid : PlayerId) (amount : Dec)
    (player : Player) (pcs : PlayerCombatState)
    (hNotEnd : cs.isEnding = false)
    (hFind : cs.findPlayer pid = some player)
    (hPcs : player.combatState = some pcs)
    (hNoneActive : (getSovereignBlades pcs false).isEmpty = true) :
    ∃ p' pcs', (forgeSovereignBlade cs pid amount).findPlayer pid = some p' ∧
      p'.combatState = some pcs' ∧
      pcs'.sovereignBladeForged = true := by
  unfold forgeSovereignBlade
  simp only [hNotEnd, Bool.false_eq_true, ↓reduceIte, hFind, hPcs, hNoneActive, Bool.not_true,
    CombatState.allocInstanceId]
  have hStep : ∀ (cs' : CombatState) (f : Player → Player) (st' : PlayerCombatState),
      (∀ x, (f x).playerId = x.playerId) →
      (∃ p, cs'.findPlayer pid = some p) →
      (∀ p, (f p).combatState = some st') →
      st'.sovereignBladeForged = true →
      ∃ p' pcs', (cs'.updatePlayer pid f).findPlayer pid = some p' ∧
        p'.combatState = some pcs' ∧ pcs'.sovereignBladeForged = true := by
    intro cs' f st' hf ⟨p0, hp0⟩ hst hforged
    exact ⟨f p0, st', updatePlayer_findPlayer cs' pid f hf p0 hp0, hst p0, hforged⟩
  apply hStep
  · intro _; rfl
  · have hMid : ∀ (cs0 : CombatState) (g : Player → Player),
        (∀ x, (g x).playerId = x.playerId) → cs0.findPlayer pid = some player →
        ∃ p, (cs0.updatePlayer pid g).findPlayer pid = some p := by
      intro cs0 g hg h0
      exact ⟨g player, updatePlayer_findPlayer cs0 pid g hg player h0⟩
    apply hMid
    · intro _; rfl
    · exact hFind
  · intro _; rfl
  · rfl

theorem loseStars_le_available (cs : CombatState) (pid : PlayerId) (amt : Nat)
    (player : Player) (pcs : PlayerCombatState)
    (hFind : cs.findPlayer pid = some player)
    (hPcs : player.combatState = some pcs) :
    (loseStars cs pid amt).2 ≤ pcs.stars := by
  unfold loseStars
  rw [hFind]
  simp only [Option.bind_some, hPcs]
  exact Nat.min_le_left _ _

-- ============================================================================
-- Fool & Dread Invariants
-- ============================================================================

theorem retrieveArrowSlot_destroyed_none (slot : ArrowSlot)
    (hDest : slot.status = .destroyed) :
    retrieveArrowSlot slot = none := by
  simp [retrieveArrowSlot, hDest]

theorem melodiesThisTurn_le_three (cs : CombatState) (pid : PlayerId) :
    melodiesThisTurn cs pid ≤ 3 := by
  unfold melodiesThisTurn
  split <;> split <;> split <;> omega

theorem dreadBeforeRoomEntered_boss_clears_dominion
    (rs : RunState) (cs : CombatState) (cfg : DreadActConfig) :
    let (rs', cs') := dreadBeforeRoomEntered rs cs .boss cfg.bossEncounterId cfg
    rs'.dominion = none ∧ cs'.dominion = none := by
  simp [dreadBeforeRoomEntered]

end Sts2Model.Proofs

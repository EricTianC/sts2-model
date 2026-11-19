/-
  Formal proofs for STS2 damage, block, HP-loss, and Osty redirection pipelines.
  All theorems proved in Lean 4 kernel with zero `sorry`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Hooks/Hook.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/CreatureCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Creatures/Creature.cs`
-/
import Sts2Model.Hook.Pipeline

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

theorem modifyDamageWithListeners_nonneg (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target dealer : Option Creature) (damage : Dec) (props : ValueProp)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType) :
    Dec.nonneg (modifyDamageWithListeners listeners reg target dealer damage props cardSource hookType).1 := by
  unfold modifyDamageWithListeners
  exact Dec.nonneg_maxZero _

theorem modifyDamage_nonneg (cs : CombatState) (reg : BehaviorRegistry)
    (target dealer : Option Creature) (damage : Dec) (props : ValueProp)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType)
    (modSubscribers : List (ModId × ModelId) := []) :
    Dec.nonneg (modifyDamage cs reg target dealer damage props cardSource hookType modSubscribers).1 :=
  modifyDamageWithListeners_nonneg ..

theorem modifyBlockWithListeners_nonneg (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Creature) (block : Dec) (props : ValueProp) (cardSource : Option CardInstance) :
    Dec.nonneg (modifyBlockWithListeners listeners reg target block props cardSource).1 := by
  unfold modifyBlockWithListeners
  exact Dec.nonneg_maxZero _

theorem modifyBlock_nonneg (cs : CombatState) (reg : BehaviorRegistry)
    (target : Creature) (block : Dec) (props : ValueProp) (cardSource : Option CardInstance)
    (modSubscribers : List (ModId × ModelId) := []) :
    Dec.nonneg (modifyBlock cs reg target block props cardSource modSubscribers).1 :=
  modifyBlockWithListeners_nonneg ..

private def capFoldStep (reg : BehaviorRegistry) (target : Option Creature) (props : ValueProp)
    (dealer : Option Creature) (cardSource : Option CardInstance)
    (st : Dec × Dec × List ListenerRef) (ctx : ListenerCtx) : Dec × Dec × List ListenerRef :=
  let (num, minCap, mods) := st
  let cap := (reg ctx.ref.modelId).modifyDamageCap ctx target props dealer cardSource
  if cap < minCap then
    if cap < num then (cap, cap, mods ++ [ctx.ref]) else (num, cap, mods)
  else
    (num, minCap, mods)

private theorem runDamageCap_fold_inv (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (props : ValueProp) (dealer : Option Creature)
    (cardSource : Option CardInstance)
    (num₀ minCap₀ : Dec) (mods₀ : List ListenerRef)
    (hInv : num₀ ≤ minCap₀) :
    let res := listeners.foldl (capFoldStep reg target props dealer cardSource) (num₀, minCap₀, mods₀)
    res.1 ≤ res.2.1 ∧ res.2.1 ≤ minCap₀ ∧
    ∀ ctx ∈ listeners, res.2.1 ≤ (reg ctx.ref.modelId).modifyDamageCap ctx target props dealer cardSource := by
  induction listeners generalizing num₀ minCap₀ mods₀ with
  | nil =>
      refine ⟨hInv, Dec.le_refl minCap₀, ?_⟩
      intro _ hmem
      cases hmem
  | cons hd tl ih =>
      dsimp only [List.foldl_cons, capFoldStep]
      let cap := (reg hd.ref.modelId).modifyDamageCap hd target props dealer cardSource
      split
      · rename_i hlt
        have hcap_le_min : cap ≤ minCap₀ := by
          rw [Dec.lt_iff_not_le] at hlt
          cases Dec.le_total cap minCap₀ with
          | inl h => exact h
          | inr h => exact False.elim (hlt h)
        split
        · rename_i hltNum
          have ihRes := ih cap cap (mods₀ ++ [hd.ref]) (Dec.le_refl cap)
          refine ⟨ihRes.1, Dec.le_trans ihRes.2.1 hcap_le_min, ?_⟩
          intro ctx hmem
          cases List.mem_cons.mp hmem with
          | inl heq => subst heq; exact ihRes.2.1
          | inr htl => exact ihRes.2.2 ctx htl
        · rename_i hltNum
          have hnum_le_cap : num₀ ≤ cap := by
            rw [Dec.lt_iff_not_le] at hltNum
            exact Decidable.of_not_not hltNum
          have ihRes := ih num₀ cap mods₀ hnum_le_cap
          refine ⟨ihRes.1, Dec.le_trans ihRes.2.1 hcap_le_min, ?_⟩
          intro ctx hmem
          cases List.mem_cons.mp hmem with
          | inl heq => subst heq; exact ihRes.2.1
          | inr htl => exact ihRes.2.2 ctx htl
      · rename_i hlt
        have hmin_le_cap : minCap₀ ≤ cap := by
          rw [Dec.lt_iff_not_le] at hlt
          exact Decidable.of_not_not hlt
        have ihRes := ih num₀ minCap₀ mods₀ hInv
        refine ⟨ihRes.1, ihRes.2.1, ?_⟩
        intro ctx hmem
        cases List.mem_cons.mp hmem with
        | inl heq => subst heq; exact Dec.le_trans ihRes.2.1 hmin_le_cap
        | inr htl => exact ihRes.2.2 ctx htl

/-- Every damage cap listener dominates the output of `runDamageCap` whenever `startDmg ≤ Dec.maxDecimal`. -/
theorem damage_cap_dominates (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (startDmg : Dec) (props : ValueProp)
    (dealer : Option Creature) (cardSource : Option CardInstance)
    (hStart : startDmg ≤ Dec.maxDecimal)
    {ctx : ListenerCtx} (hMem : ctx ∈ listeners) :
    (runDamageCap listeners reg target startDmg props dealer cardSource).1 ≤
      (reg ctx.ref.modelId).modifyDamageCap ctx target props dealer cardSource := by
  have hFold := runDamageCap_fold_inv listeners reg target props dealer cardSource
    startDmg Dec.maxDecimal [] hStart
  unfold runDamageCap
  change (listeners.foldl (capFoldStep reg target props dealer cardSource) (startDmg, Dec.maxDecimal, [])).1 ≤ _
  exact Dec.le_trans hFold.1 (hFold.2.2 ctx hMem)

/-- Enchantment additive & multiplicative modifiers are always applied before any listener hook. -/
theorem enchantment_applied_before_listeners (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target dealer : Option Creature) (damage : Dec) (props : ValueProp)
    (card : CardInstance) (ench : EnchantmentInstance)
    (hEnch : card.enchantment = some ench) :
    let preDamage := Dec.mul (Dec.add damage ench.damageAdd) ench.damageMul
    (modifyDamageWithListeners listeners reg target dealer damage props (some card) ModifyDamageHookType.all).1 =
      (let (a1, _) := runDamageAdditive listeners reg target preDamage props dealer (some card)
       let (a2, _) := runDamageMultiplicative listeners reg target a1 props dealer (some card)
       let (a3, _) := runDamageMultiplicativeLate listeners reg target a2 props dealer (some card)
       let (a4, _) := runDamageCap listeners reg target a3 props dealer (some card)
       Dec.maxZero a4) := by
  simp [modifyDamageWithListeners, ModifyDamageHookType.all, hEnch]

/-- Unpowered damage (`props.unpowered = true`) is immune to Strength, Vulnerable, Weak, and Vajra. -/
theorem unpowered_ignores_powered_damage_modifiers (cs : CombatState) (ctx : ListenerCtx)
    (target dealer : Option Creature) (dmg : Dec) (props : ValueProp) (card : Option CardInstance)
    (hUnpowered : props.unpowered = true) :
    strengthBehavior.modifyDamageAdditive ctx target dmg props dealer card = Dec.zero ∧
    vajraBehavior.modifyDamageAdditive ctx target dmg props dealer card = Dec.zero ∧
    (vulnerableBehavior cs).modifyDamageMultiplicative ctx target dmg props dealer card = Dec.one ∧
    weakBehavior.modifyDamageMultiplicative ctx target dmg props dealer card = Dec.one := by
  have hp : props.isPoweredAttack = false := by
    simp [ValueProp.isPoweredAttack, hUnpowered]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [strengthBehavior, hp]; split <;> simp
  · simp only [vajraBehavior, hp]; split <;> simp
  · simp only [vulnerableBehavior, hp]; split <;> simp
  · simp only [weakBehavior, hp]; split <;> simp

/-- Unpowered block (`props.unpowered = true`) is immune to Dexterity and Frail. -/
theorem unpowered_ignores_powered_block_modifiers (ctx : ListenerCtx)
    (target : Creature) (blk : Dec) (props : ValueProp) (card : Option CardInstance)
    (hUnpowered : props.unpowered = true) :
    dexterityBehavior.modifyBlockAdditive ctx target blk props card = Dec.zero ∧
    frailBehavior.modifyBlockMultiplicative ctx target blk props card = Dec.one := by
  have hp : props.isPoweredCardOrMonsterMoveBlock = false := by
    simp [ValueProp.isPoweredCardOrMonsterMoveBlock, hUnpowered]
  constructor
  · simp only [dexterityBehavior, hp]; split <;> simp
  · simp only [frailBehavior, hp]; split <;> simp

/-- Unblockable damage (`props.unblockable = true`) completely bypasses creature Block. -/
theorem unblockable_bypasses_block (c : Creature) (amt : Dec) (props : ValueProp)
    (hUnb : props.unblockable = true) :
    (c.damageBlockInternal amt props).2 = Dec.zero ∧
    (c.damageBlockInternal amt props).1.block = c.block := by
  simp [Creature.damageBlockInternal, hUnb, Dec.truncate, Dec.zero, Dec.pow10]

/-- Integer truncation exactness for `Dec.ofNat`. -/
theorem truncate_ofNat (n : Nat) : (Dec.ofNat n).truncate = (n : Int) := by
  unfold Dec.ofNat Dec.truncate
  have hp : Dec.pow10 0 = 1 := by decide
  rw [hp]
  exact Int.tdiv_one (n : Int)

private theorem clamp_ofNat_statCap (n : Nat) (hBound : n ≤ Creature.statCap) :
    Dec.clamp (Dec.ofNat n) Dec.zero (Dec.ofNat Creature.statCap) = Dec.ofNat n := by
  have hpow : Dec.pow10 0 = 1 := by decide
  unfold Dec.clamp
  have h1 : ¬ Dec.ofNat n < Dec.zero := by
    change ¬ ((n : Int) * Dec.pow10 0 < 0 * Dec.pow10 0)
    rw [hpow]; omega
  have h2 : ¬ Dec.ofNat Creature.statCap < Dec.ofNat n := by
    change ¬ ((Creature.statCap : Int) * Dec.pow10 0 < (n : Int) * Dec.pow10 0)
    rw [hpow]; omega
  simp [h1, h2]

private theorem loseHpInternal_ofNat (c : Creature) (rem : Nat) (props : ValueProp)
    (hAlive : 0 < c.currentHp) (hBound : rem ≤ Creature.statCap) :
    let (c', res) := c.loseHpInternal (Dec.ofNat rem) props
    res.unblockedDamage + res.overkillDamage = rem ∧
    c.currentHp - c'.currentHp = res.unblockedDamage := by
  have hpow : Dec.pow10 0 = 1 := by decide
  simp +zetaDelta [Creature.loseHpInternal, clamp_ofNat_statCap rem hBound]
  rw [truncate_ofNat, Int.max_eq_right (Int.natCast_nonneg rem), Int.toNat_natCast]
  split
  · rename_i hkill
    have hle : c.currentHp ≤ rem := by
      have h2 := hkill.2
      change (c.currentHp : Int) * Dec.pow10 0 ≤ (rem : Int) * Dec.pow10 0 at h2
      rw [hpow] at h2
      omega
    omega
  · rename_i hkill
    simp only [not_and] at hkill
    have hnot := hkill hAlive
    change ¬ ((c.currentHp : Int) * Dec.pow10 0 ≤ (rem : Int) * Dec.pow10 0) at hnot
    rw [hpow] at hnot
    simp only [Int.mul_one] at hnot
    omega

/-- Conservation of integer damage across Block absorption, HP loss, and Overkill damage
    for a living creature (`CreatureCmd.Damage` skips already-dead targets). -/
theorem damage_block_hp_conservation (c : Creature) (dmg : Nat) (props : ValueProp)
    (hAlive : c.isAlive = true) (hBound : dmg ≤ Creature.statCap) :
    let (cAfterBlk, blockedDec) := c.damageBlockInternal (Dec.ofNat dmg) props
    let blocked := blockedDec.toNat
    let rem := dmg - blocked
    let (cFinal, res) := cAfterBlk.loseHpInternal (Dec.ofNat rem) props
    blocked + res.unblockedDamage + res.overkillDamage = dmg ∧
    c.block - cAfterBlk.block = blocked ∧
    cAfterBlk.currentHp - cFinal.currentHp = res.unblockedDamage := by
  have hPos : 0 < c.currentHp := by
    unfold Creature.isAlive at hAlive
    exact of_decide_eq_true hAlive
  by_cases hUnb : props.unblockable = true
  · have hcBlk : c.damageBlockInternal (Dec.ofNat dmg) props = (c, Dec.zero) := by
      simp [Creature.damageBlockInternal, hUnb, Dec.truncate, Dec.zero, Dec.pow10]
    rw [hcBlk]
    dsimp only
    have htoNat : Dec.zero.toNat = 0 := by decide
    rw [htoNat, Nat.sub_zero]
    have hl := loseHpInternal_ofNat c dmg props hPos hBound
    dsimp only at hl
    omega
  · have hUnbF : props.unblockable = false := by
      cases h : props.unblockable <;> simp_all
    have hpow : Dec.pow10 0 = 1 := by decide
    have hmin : Dec.min (Dec.ofNat c.block) (Dec.ofNat dmg) = Dec.ofNat (Nat.min c.block dmg) := by
      unfold Dec.min
      by_cases hcb : c.block ≤ dmg
      · have hdec : Dec.ofNat c.block ≤ Dec.ofNat dmg := by
          change (c.block : Int) * Dec.pow10 0 ≤ (dmg : Int) * Dec.pow10 0
          rw [hpow]; omega
        simp [hdec, Nat.min_eq_left hcb]
      · have hndec : ¬ Dec.ofNat c.block ≤ Dec.ofNat dmg := by
          change ¬ ((c.block : Int) * Dec.pow10 0 ≤ (dmg : Int) * Dec.pow10 0)
          rw [hpow]; omega
        have hlt : dmg ≤ c.block := by omega
        simp [hndec, Nat.min_eq_right hlt]
    let blkUsed := Nat.min c.block dmg
    have htoNat : (Dec.ofNat blkUsed).toNat = blkUsed := by
      unfold Dec.toNat Dec.maxZero
      have hnot : ¬ (Dec.ofNat blkUsed).mantissa < 0 := by
        change ¬ ((blkUsed : Int) < 0); omega
      simp [hnot, truncate_ofNat]
    have hBlkStep : c.damageBlockInternal (Dec.ofNat dmg) props =
        ({ c with block := c.block - blkUsed }, Dec.ofNat blkUsed) := by
      have hmin' : Dec.min (Dec.ofNat c.block) (Dec.ofNat dmg) = Dec.ofNat blkUsed := hmin
      have hle : blkUsed ≤ c.block := Nat.min_le_left _ _
      simp only [Creature.damageBlockInternal, hUnbF, Bool.false_eq_true, ↓reduceIte, hmin', truncate_ofNat]
      have hint : Int.toNat (max 0 (blkUsed : Int)) = blkUsed := by omega
      rw [hint, Nat.min_eq_right hle]
    rw [hBlkStep]
    dsimp only
    rw [htoNat]
    have hremBound : dmg - blkUsed ≤ Creature.statCap := by omega
    have hl := loseHpInternal_ofNat { c with block := c.block - blkUsed } (dmg - blkUsed) props hPos hremBound
    dsimp only at hl
    have hblkLeDmg : blkUsed ≤ dmg := Nat.min_le_right _ _
    have hblkLeC : blkUsed ≤ c.block := Nat.min_le_left _ _
    omega

/-- Osty unblocked damage redirection + overkill spill-over conserves total unblocked damage
    when both Osty and the Necrobinder owner are alive. Ref: `CreatureCmd.cs` lines 169-189. -/
theorem osty_redirection_conservation (osty owner : Creature) (unblocked : Nat)
    (hOstyAlive : osty.isAlive = true) (hOwnerAlive : owner.isAlive = true)
    (hBound : unblocked ≤ Creature.statCap) :
    let (osty', res1) := osty.loseHpInternal (Dec.ofNat unblocked) DamageProps.monsterMove
    let (owner', res2) := owner.loseHpInternal (Dec.ofNat res1.overkillDamage) DamageProps.monsterMove
    res1.unblockedDamage + res2.unblockedDamage + res2.overkillDamage = unblocked ∧
    osty.currentHp - osty'.currentHp = res1.unblockedDamage ∧
    owner.currentHp - owner'.currentHp = res2.unblockedDamage := by
  have hOstyPos : 0 < osty.currentHp := of_decide_eq_true (by simpa [Creature.isAlive] using hOstyAlive)
  have hOwnerPos : 0 < owner.currentHp := of_decide_eq_true (by simpa [Creature.isAlive] using hOwnerAlive)
  have h1 := loseHpInternal_ofNat osty unblocked DamageProps.monsterMove hOstyPos hBound
  dsimp only at h1
  have hovBound : (osty.loseHpInternal (Dec.ofNat unblocked) DamageProps.monsterMove).2.overkillDamage ≤ Creature.statCap := by
    omega
  have h2 := loseHpInternal_ofNat owner
    (osty.loseHpInternal (Dec.ofNat unblocked) DamageProps.monsterMove).2.overkillDamage
    DamageProps.monsterMove hOwnerPos hovBound
  dsimp only at h2
  dsimp only
  omega

end Sts2Model.Proofs

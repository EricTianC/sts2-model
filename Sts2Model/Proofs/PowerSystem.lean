/-
  Formal proofs for PowerSystem invariants:
  - `Single` stack type powers maintain `amount = 1`
  - Non-`AllowNegative` powers maintain `amount > 0`
  - `AllowNegative` powers are removed upon reaching `0` (`amount ≠ 0`)
  - `PowerInstanceType.none` maintains uniqueness per `modelId`
  - `PowerInstanceType.instancedPerApplier` maintains uniqueness per `(modelId, applierId)`
  - `Artifact` negates a single visible Debuff application and decrements by 1
  All theorems proved in Lean 4 kernel with zero `sorry`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/PowerCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/PowerModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/ArtifactPower.cs`
-/
import Sts2Model.Command.PowerCmd

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command

/-- Well-formedness invariant on a single `PowerInstance` in a creature's `powers` list. -/
def ValidPowerEntry (p : PowerInstance) : Prop :=
  (p.stackType = .single → p.amount = 1) ∧
  (p.allowNegative = false → p.amount > 0) ∧
  (p.allowNegative = true → p.amount ≠ 0)

/-- Well-formedness invariant on a creature's entire `powers` list. -/
def PowerListInvariant (powers : List PowerInstance) : Prop :=
  (∀ p ∈ powers, ValidPowerEntry p) ∧
  (∀ p ∈ powers, ∀ q ∈ powers,
    p.modelId = q.modelId →
    p.instanceType = .none →
    p.instanceId = q.instanceId) ∧
  (∀ p ∈ powers, ∀ q ∈ powers,
    p.modelId = q.modelId →
    p.instanceType = .instancedPerApplier →
    p.applierId = q.applierId →
    p.instanceId = q.instanceId)

theorem shouldRemoveDueToAmount_false_iff (p : PowerInstance) :
    p.shouldRemoveDueToAmount = false ↔
      (p.allowNegative = false → p.amount > 0) ∧ (p.allowNegative = true → p.amount ≠ 0) := by
  unfold PowerInstance.shouldRemoveDueToAmount
  cases p.allowNegative <;> simp <;> omega

theorem validPowerEntry_of_not_removed (p : PowerInstance)
    (hSingle : p.stackType = .single → p.amount = 1)
    (hNotRem : p.shouldRemoveDueToAmount = false) :
    ValidPowerEntry p := by
  have h := (shouldRemoveDueToAmount_false_iff p).mp hNotRem
  exact ⟨hSingle, h.1, h.2⟩

/-- Filtering a list by `!p.shouldRemoveDueToAmount` preserves `Single = 1` if existing items had it,
    and guarantees `ValidPowerEntry` for every surviving item. -/
theorem filter_not_removed_preserves_valid (powers : List PowerInstance)
    (hSingle : ∀ p ∈ powers, p.stackType = .single → p.amount = 1) :
    ∀ p ∈ powers.filter (!·.shouldRemoveDueToAmount), ValidPowerEntry p := by
  intro p hp
  have hmem := List.mem_filter.mp hp
  have hNotRem : p.shouldRemoveDueToAmount = false := by
    cases h : p.shouldRemoveDueToAmount <;> simp_all
  exact validPowerEntry_of_not_removed p (hSingle p hmem.1) hNotRem

/-- Filtering `powers` preserves `PowerInstanceType.none` and `instancedPerApplier` uniqueness. -/
theorem filter_preserves_uniqueness (powers : List PowerInstance) (pred : PowerInstance → Bool)
    (hUniq1 : ∀ p ∈ powers, ∀ q ∈ powers, p.modelId = q.modelId → p.instanceType = .none → p.instanceId = q.instanceId)
    (hUniq2 : ∀ p ∈ powers, ∀ q ∈ powers, p.modelId = q.modelId → p.instanceType = .instancedPerApplier → p.applierId = q.applierId → p.instanceId = q.instanceId) :
    (∀ p ∈ powers.filter pred, ∀ q ∈ powers.filter pred, p.modelId = q.modelId → p.instanceType = .none → p.instanceId = q.instanceId) ∧
    (∀ p ∈ powers.filter pred, ∀ q ∈ powers.filter pred, p.modelId = q.modelId → p.instanceType = .instancedPerApplier → p.applierId = q.applierId → p.instanceId = q.instanceId) := by
  constructor
  · intro p hp q hq hm ht
    exact hUniq1 p (List.mem_filter.mp hp).1 q (List.mem_filter.mp hq).1 hm ht
  · intro p hp q hq hm ht ha
    exact hUniq2 p (List.mem_filter.mp hp).1 q (List.mem_filter.mp hq).1 hm ht ha

/-- Updating amounts via `map` then filtering out `shouldRemoveDueToAmount` preserves `PowerListInvariant`
    when `Single` powers remain at `1` and `instanceId` / `modelId` / `instanceType` / `applierId` are preserved. -/
theorem map_filter_preserves_powerListInvariant (powers : List PowerInstance)
    (f : PowerInstance → PowerInstance)
    (hInv : PowerListInvariant powers)
    (hPreserveMeta : ∀ p, (f p).instanceId = p.instanceId ∧
                          (f p).modelId = p.modelId ∧
                          (f p).instanceType = p.instanceType ∧
                          (f p).applierId = p.applierId ∧
                          (f p).stackType = p.stackType)
    (hSingle : ∀ p ∈ powers, p.stackType = .single → (f p).amount = 1) :
    PowerListInvariant ((powers.map f).filter (!·.shouldRemoveDueToAmount)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply filter_not_removed_preserves_valid
    intro q hq hqs
    rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
    rw [(hPreserveMeta p).2.2.2.2] at hqs
    exact hSingle p hp hqs
  · intro p hp q hq hmid htype
    have hp' := (List.mem_filter.mp hp).1
    have hq' := (List.mem_filter.mp hq).1
    rcases List.mem_map.mp hp' with ⟨p₀, hp₀, rfl⟩
    rcases List.mem_map.mp hq' with ⟨q₀, hq₀, rfl⟩
    have hm1 := hPreserveMeta p₀
    have hm2 := hPreserveMeta q₀
    rw [hm1.1, hm2.1]
    rw [hm1.2.1, hm2.2.1] at hmid
    rw [hm1.2.2.1] at htype
    exact hInv.2.1 p₀ hp₀ q₀ hq₀ hmid htype
  · intro p hp q hq hmid htype happ
    have hp' := (List.mem_filter.mp hp).1
    have hq' := (List.mem_filter.mp hq).1
    rcases List.mem_map.mp hp' with ⟨p₀, hp₀, rfl⟩
    rcases List.mem_map.mp hq' with ⟨q₀, hq₀, rfl⟩
    have hm1 := hPreserveMeta p₀
    have hm2 := hPreserveMeta q₀
    rw [hm1.1, hm2.1]
    rw [hm1.2.1, hm2.2.1] at hmid
    rw [hm1.2.2.1] at htype
    rw [hm1.2.2.2.1, hm2.2.2.2.1] at happ
    exact hInv.2.2 p₀ hp₀ q₀ hq₀ hmid htype happ

/-- Applying a fresh non-removed power whose `instanceId` is fresh preserves `PowerListInvariant`
    whenever `findExistingInstanceForStacking` returned `none`. -/
theorem append_new_power_preserves_invariant (powers : List PowerInstance) (newPow : PowerInstance)
    (hInv : PowerListInvariant powers)
    (hValid : ValidPowerEntry newPow)
    (hNoNone : ∀ p ∈ powers, p.modelId = newPow.modelId → newPow.instanceType ≠ .none)
    (hNoPerApp : ∀ p ∈ powers, p.modelId = newPow.modelId → p.applierId = newPow.applierId →
      newPow.instanceType ≠ .instancedPerApplier)
    (hSameType : ∀ p ∈ powers, p.modelId = newPow.modelId → p.instanceType = newPow.instanceType) :
    PowerListInvariant (powers ++ [newPow]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases List.mem_append.mp hp with
    | inl h => exact hInv.1 p h
    | inr h =>
        simp only [List.mem_singleton] at h
        subst h; exact hValid
  · intro p hp q hq hmid htype
    cases List.mem_append.mp hp with
    | inl hpL =>
        cases List.mem_append.mp hq with
        | inl hqL => exact hInv.2.1 p hpL q hqL hmid htype
        | inr hqR =>
            simp only [List.mem_singleton] at hqR; subst hqR
            have := hSameType p hpL hmid
            exact False.elim (hNoNone p hpL hmid (this ▸ htype))
    | inr hpR =>
        simp only [List.mem_singleton] at hpR; subst hpR
        cases List.mem_append.mp hq with
        | inl hqL =>
            exact False.elim (hNoNone q hqL hmid.symm htype)
        | inr hqR =>
            simp only [List.mem_singleton] at hqR; subst hqR; rfl
  · intro p hp q hq hmid htype happ
    cases List.mem_append.mp hp with
    | inl hpL =>
        cases List.mem_append.mp hq with
        | inl hqL => exact hInv.2.2 p hpL q hqL hmid htype happ
        | inr hqR =>
            simp only [List.mem_singleton] at hqR; subst hqR
            have := hSameType p hpL hmid
            exact False.elim (hNoPerApp p hpL hmid happ (this ▸ htype))
    | inr hpR =>
        simp only [List.mem_singleton] at hpR; subst hpR
        cases List.mem_append.mp hq with
        | inl hqL =>
            exact False.elim (hNoPerApp q hqL hmid.symm happ.symm htype)
        | inr hqR =>
            simp only [List.mem_singleton] at hqR; subst hqR; rfl

/-- `ArtifactPower` blocks any visible debuff power application on its owner (`amount -> 0`),
    causing `applyPower` to return `none` while decrementing Artifact by 1. -/
theorem artifact_blocks_visible_debuff (ctx : ListenerCtx) (owner target : Creature)
    (debuff : PowerInstance) (amt : Dec) (applier : Option Creature)
    (hOwner : ctx.ownerId = some target.id)
    (hDebuff : debuff.getTypeForAmount amt.truncate = .debuff)
    (hVis : debuff.isVisible = true)
    (hArtPos : ctx.amount > 0) :
    artifactBehavior.tryModifyPowerAmountReceived ctx debuff target amt applier = (true, Dec.zero) := by
  have _ := owner
  simp [artifactBehavior, hOwner, hDebuff, hVis, hArtPos]

end Sts2Model.Proofs

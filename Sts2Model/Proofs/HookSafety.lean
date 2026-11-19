/-
  Formal proofs for Hook snapshot safety, ModHelper pool freeze monotonicity,
  mod hook load-order independence, and additive/multiplicative mod composition laws.
  All theorems proved in Lean 4 kernel with zero `sorry`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/CombatState.cs` (`IterateHookListeners`)
  - `reference/sts2/MegaCrit.Sts2.Core.Modding/ModHelper.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Hooks/Hook.cs`
-/
import Sts2Model.Hook.Pipeline

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

/-- Traced execution of `runSnapshotHooks`: records every `ListenerRef` whose `step` actually fired. -/
def runSnapshotHooksTraced (snapshot : List ListenerRef) (cs : CombatState)
    (step : CombatState → ListenerRef → CombatState) : CombatState × List ListenerRef :=
  snapshot.foldl (fun (acc, fired) ref =>
    if containsListener acc ref then (step acc ref, fired ++ [ref]) else (acc, fired)) (cs, [])

theorem runSnapshotHooksTraced_fst_eq (snapshot : List ListenerRef) (cs : CombatState)
    (step : CombatState → ListenerRef → CombatState) :
    (runSnapshotHooksTraced snapshot cs step).1 = runSnapshotHooks snapshot cs step := by
  unfold runSnapshotHooksTraced runSnapshotHooks
  suffices h : ∀ (l : List ListenerRef) (s : CombatState) (f : List ListenerRef),
      (l.foldl (fun (acc, fired) ref =>
        if containsListener acc ref then (step acc ref, fired ++ [ref]) else (acc, fired)) (s, f)).1 =
      l.foldl (fun acc ref => if containsListener acc ref then step acc ref else acc) s from
    h snapshot cs []
  intro l
  induction l with
  | nil => intro s f; rfl
  | cons hd tl ih =>
      intro s f
      simp only [List.foldl_cons]
      split <;> exact ih ..

private theorem runSnapshotHooksTraced_subset_aux (l : List ListenerRef) (s : CombatState) (f : List ListenerRef)
    (step : CombatState → ListenerRef → CombatState)
    (r : ListenerRef) (hrNotInL : r ∉ l) (hrNotInF : r ∉ f) :
    r ∉ (l.foldl (fun (acc, fired) ref =>
      if containsListener acc ref then (step acc ref, fired ++ [ref]) else (acc, fired)) (s, f)).2 := by
  induction l generalizing s f with
  | nil => exact hrNotInF
  | cons hd tl ih =>
      simp only [List.mem_cons, not_or] at hrNotInL
      simp only [List.foldl_cons]
      split
      · apply ih _ _ hrNotInL.2
        simp [List.mem_append, hrNotInF, hrNotInL.1]
      · exact ih _ _ hrNotInL.2 hrNotInF

/-- Any listener not present in the captured snapshot (e.g. added dynamically mid-dispatch)
    never fires during that snapshot pass, preventing self-triggering infinite loops. -/
theorem snapshot_ignores_newly_added_listeners (snapshot : List ListenerRef) (cs : CombatState)
    (step : CombatState → ListenerRef → CombatState) {r : ListenerRef} (hNotIn : r ∉ snapshot) :
    r ∉ (runSnapshotHooksTraced snapshot cs step).2 :=
  runSnapshotHooksTraced_subset_aux snapshot cs [] step r hNotIn (by simp)

/-- If a listener has already been removed from `cs` (`containsListener cs r = false`),
    then dispatching `runSnapshotHooks [r] cs step` skips `step` completely. -/
theorem snapshot_skips_removed_listeners (cs : CombatState)
    (step : CombatState → ListenerRef → CombatState) {r : ListenerRef}
    (hRemoved : containsListener cs r = false) :
    runSnapshotHooks [r] cs step = cs := by
  simp [runSnapshotHooks, hRemoved]

/-- At any step of `runSnapshotHooks`, if `r` is currently dead in `cs`,
    `r` is skipped without calling `step`. -/
theorem snapshot_cons_skips_dead (r : ListenerRef) (rest : List ListenerRef) (cs : CombatState)
    (step : CombatState → ListenerRef → CombatState)
    (hDead : containsListener cs r = false) :
    runSnapshotHooks (r :: rest) cs step = runSnapshotHooks rest cs step := by
  simp [runSnapshotHooks, hDead]

-- ============================================================================
-- ModHelper Pool Freezing & Deterministic Ordinal Subscriber Order
-- ============================================================================

private theorem upsertEntry_finds (entries : List ModPoolEntry) (e : ModPoolEntry) :
    ModPoolRegistry.findEntry ⟨ModPoolRegistry.upsertEntry entries e⟩ e.poolKey = some e := by
  unfold ModPoolRegistry.findEntry ModPoolRegistry.upsertEntry
  split
  · rename_i hAny
    induction entries with
    | nil => simp at hAny
    | cons hd tl ih =>
        simp only [List.any_cons, Bool.or_eq_true] at hAny
        simp only [List.map_cons, List.find?_cons]
        by_cases heq : (hd.poolKey == e.poolKey) = true
        · simp [heq]
        · have htl : tl.any (·.poolKey == e.poolKey) = true := by
            cases hAny with
            | inl h => contradiction
            | inr h => exact h
          simp only [heq, ↓reduceIte, Bool.false_eq_true]
          exact ih htl
  · rename_i hNotAny
    have hnone : ∀ x ∈ entries, (x.poolKey == e.poolKey) = false := by
      intro x hx
      cases h : (x.poolKey == e.poolKey) with
      | false => rfl
      | true => exact False.elim (hNotAny (List.any_eq_true.mpr ⟨x, hx, h⟩))
    induction entries with
    | nil => simp
    | cons hd tl ih =>
        simp only [List.cons_append, List.find?_cons]
        have hhd : (hd.poolKey == e.poolKey) = false := hnone hd (by simp)
        rw [hhd]
        exact ih (fun htl => hNotAny (by simp [htl])) (fun x hx => hnone x (by simp [hx]))

private theorem find?_key_eq {α : Type} (p : α → Bool) (xs : List α) (x : α)
    (h : xs.find? p = some x) : p x = true := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
      simp only [List.find?_cons] at h
      cases hp : p hd with
      | true => rw [hp] at h; cases h; exact hp
      | false => rw [hp] at h; exact ih h

/-- Once `concatModelsFromMods` freezes a pool, `isPoolFrozen` becomes `true` and every
    subsequent `addModelToPool` returns `.error`. -/
theorem modHelper_pool_freeze_monotonic (reg : ModPoolRegistry) (poolKey : String)
    (basePool : List ModelId) (newModel : ModelId) :
    let (reg', _) := reg.concatModelsFromMods poolKey basePool
    reg'.isPoolFrozen poolKey = true ∧
    ∃ err, reg'.addModelToPool poolKey newModel = .error err := by
  unfold ModPoolRegistry.concatModelsFromMods
  cases hfind : reg.findEntry poolKey with
  | some e =>
      dsimp only
      have hek : e.poolKey = poolKey := by
        have hp := find?_key_eq (fun x : ModPoolEntry => x.poolKey == poolKey) reg.entries e hfind
        exact beq_iff_eq.mp hp
      have hF : ModPoolRegistry.findEntry ⟨ModPoolRegistry.upsertEntry reg.entries { e with isFrozen := true }⟩ poolKey =
          some { e with isFrozen := true } := by
        rw [← hek]
        exact upsertEntry_finds reg.entries { e with isFrozen := true }
      refine ⟨?_, ?_⟩
      · unfold ModPoolRegistry.isPoolFrozen
        rw [hF]; rfl
      · refine ⟨s!"Tried to add model {newModel} to pool {poolKey}, but it's too late!", ?_⟩
        unfold ModPoolRegistry.addModelToPool
        rw [hF]; rfl
  | none =>
      dsimp only
      have hF : ModPoolRegistry.findEntry ⟨ModPoolRegistry.upsertEntry reg.entries ⟨poolKey, true, []⟩⟩ poolKey =
          some ⟨poolKey, true, []⟩ :=
        upsertEntry_finds reg.entries ⟨poolKey, true, []⟩
      refine ⟨?_, ?_⟩
      · unfold ModPoolRegistry.isPoolFrozen
        rw [hF]; rfl
      · refine ⟨s!"Tried to add model {newModel} to pool {poolKey}, but it's too late!", ?_⟩
        unfold ModPoolRegistry.addModelToPool
        rw [hF]; rfl

private theorem str_cmp_swap (a b : String) :
    String.compare a b = (String.compare b a).swap :=
  @Std.OrientedOrd.eq_swap String _ _ a b

private theorem str_cmp_eq_iff (a b : String) :
    String.compare a b = .eq ↔ a = b := by
  constructor
  · intro h
    change compare a b = .eq at h
    exact @Std.LawfulEqCmp.eq_of_compare String _ _ a b h
  · intro h
    subst h
    change compare a a = .eq
    exact @Std.ReflCmp.compare_self String _ _ a

private theorem str_cmp_lt_gt {a b : String} (h : String.compare a b = .lt) :
    String.compare b a = .gt := by
  have hs := str_cmp_swap a b
  rw [h] at hs
  cases hba : String.compare b a with
  | lt => rw [hba] at hs; cases hs
  | eq => rw [hba] at hs; cases hs
  | gt => rfl

private theorem str_cmp_gt_lt {a b : String} (h : String.compare a b = .gt) :
    String.compare b a = .lt := by
  have hs := str_cmp_swap a b
  rw [h] at hs
  cases hba : String.compare b a with
  | lt => rfl
  | eq => rw [hba] at hs; cases hs
  | gt => rw [hba] at hs; cases hs

private theorem str_cmp_ne_eq {a b : String} (hne : a ≠ b) :
    String.compare a b ≠ .eq := by
  intro h
  exact hne ((str_cmp_eq_iff a b).mp h)

private theorem insertSubscriberSorted_comm (s₁ s₂ : ModHookSubscriber) (xs : List ModHookSubscriber)
    (hne : s₁.id ≠ s₂.id) :
    insertSubscriberSorted s₁ (insertSubscriberSorted s₂ xs) =
    insertSubscriberSorted s₂ (insertSubscriberSorted s₁ xs) := by
  have h12b : (s₁.id == s₂.id) = false := beq_false_of_ne hne
  have h21b : (s₂.id == s₁.id) = false := beq_false_of_ne hne.symm
  induction xs with
  | nil =>
      simp only [insertSubscriberSorted, h12b, h21b, Bool.false_eq_true, ↓reduceIte]
      cases hcmp : String.compare s₁.id s₂.id with
      | lt =>
          have hgt := str_cmp_lt_gt hcmp
          simp [hgt]
      | eq => exact False.elim (str_cmp_ne_eq hne hcmp)
      | gt =>
          have hlt := str_cmp_gt_lt hcmp
          simp [hlt]
  | cons hd tl ih =>
      by_cases heq1 : s₁.id = hd.id
      · have hne2 : s₂.id ≠ hd.id := fun h => hne (heq1.trans h.symm)
        have hb1 : (s₁.id == hd.id) = true := beq_iff_eq.mpr heq1
        have hb2 : (s₂.id == hd.id) = false := beq_false_of_ne hne2
        simp only [insertSubscriberSorted, hb1, hb2, Bool.false_eq_true, ↓reduceIte]
        cases hcmp2 : String.compare s₂.id hd.id with
        | lt =>
            have h12gt : String.compare s₁.id s₂.id = .gt := by
              rw [heq1]; exact str_cmp_lt_gt hcmp2
            simp [insertSubscriberSorted, h12b, h12gt, hb1]
        | eq => exact False.elim (str_cmp_ne_eq hne2 hcmp2)
        | gt =>
            simp [insertSubscriberSorted, hb1]
      · by_cases heq2 : s₂.id = hd.id
        · have hb1 : (s₁.id == hd.id) = false := beq_false_of_ne heq1
          have hb2 : (s₂.id == hd.id) = true := beq_iff_eq.mpr heq2
          simp only [insertSubscriberSorted, hb1, hb2, Bool.false_eq_true, ↓reduceIte]
          cases hcmp1 : String.compare s₁.id hd.id with
          | lt =>
              have h21gt : String.compare s₂.id s₁.id = .gt := by
                rw [heq2]; exact str_cmp_lt_gt hcmp1
              simp [insertSubscriberSorted, h21b, h21gt, hb2]
          | eq => exact False.elim (str_cmp_ne_eq heq1 hcmp1)
          | gt =>
              simp [insertSubscriberSorted, hb2]
        · have hb1 : (s₁.id == hd.id) = false := beq_false_of_ne heq1
          have hb2 : (s₂.id == hd.id) = false := beq_false_of_ne heq2
          simp only [insertSubscriberSorted, hb1, hb2, Bool.false_eq_true, ↓reduceIte]
          cases hcmp1 : String.compare s₁.id hd.id <;> cases hcmp2 : String.compare s₂.id hd.id
          · -- both lt
            simp only [beq_self_eq_true, ↓reduceIte]
            cases h12 : String.compare s₁.id s₂.id with
            | lt =>
                have h21 := str_cmp_lt_gt h12
                simp [insertSubscriberSorted, h12b, h21b, h12, h21, hb2, hcmp2]
            | eq => exact False.elim (str_cmp_ne_eq hne h12)
            | gt =>
                have h21 := str_cmp_gt_lt h12
                simp [insertSubscriberSorted, h12b, h21b, h12, h21, hb1, hcmp1]
          · exact False.elim (str_cmp_ne_eq heq2 hcmp2)
          · -- s₁ < hd < s₂
            have h21 : String.compare s₂.id s₁.id = .gt := by
              have hle1 : (compare s₁.id hd.id).isLE = true := by
                change (String.compare s₁.id hd.id).isLE = true; rw [hcmp1]; rfl
              have hle2 : (compare hd.id s₂.id).isLE = true := by
                change (String.compare hd.id s₂.id).isLE = true
                rw [str_cmp_gt_lt hcmp2]; rfl
              have h12le : (compare s₁.id s₂.id).isLE = true := Std.TransOrd.isLE_trans hle1 hle2
              have h12lt : String.compare s₁.id s₂.id = .lt := by
                cases h : String.compare s₁.id s₂.id with
                | lt => rfl
                | eq => exact False.elim (str_cmp_ne_eq hne h)
                | gt => change (String.compare s₁.id s₂.id).isLE = true at h12le; rw [h] at h12le; cases h12le
              exact str_cmp_lt_gt h12lt
            simp [insertSubscriberSorted, h21b, hb1, hb2, hcmp1, hcmp2, h21]
          · exact False.elim (str_cmp_ne_eq heq1 hcmp1)
          · exact False.elim (str_cmp_ne_eq heq1 hcmp1)
          · exact False.elim (str_cmp_ne_eq heq1 hcmp1)
          · -- hd < s₁, s₂ < hd
            have h12 : String.compare s₁.id s₂.id = .gt := by
              have hle2 : (compare s₂.id hd.id).isLE = true := by
                change (String.compare s₂.id hd.id).isLE = true; rw [hcmp2]; rfl
              have hle1 : (compare hd.id s₁.id).isLE = true := by
                change (String.compare hd.id s₁.id).isLE = true
                rw [str_cmp_gt_lt hcmp1]; rfl
              have h21le : (compare s₂.id s₁.id).isLE = true := Std.TransOrd.isLE_trans hle2 hle1
              have h21lt : String.compare s₂.id s₁.id = .lt := by
                cases h : String.compare s₂.id s₁.id with
                | lt => rfl
                | eq => exact False.elim (str_cmp_ne_eq hne.symm h)
                | gt => change (String.compare s₂.id s₁.id).isLE = true at h21le; rw [h] at h21le; cases h21le
              exact str_cmp_lt_gt h21lt
            simp [insertSubscriberSorted, h12b, hb1, hb2, hcmp1, hcmp2, h12]
          · exact False.elim (str_cmp_ne_eq heq2 hcmp2)
          · -- hd < s₁, hd < s₂
            simp [insertSubscriberSorted, hb1, hb2, hcmp1, hcmp2]
            rw [ih]

private theorem any_id_insertSubscriberSorted_of_true (xs : List ModHookSubscriber) (s : ModHookSubscriber)
    (target : ModId) (h : xs.any (·.id == target) = true) :
    (insertSubscriberSorted s xs).any (·.id == target) = true := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
      simp only [List.any_cons, Bool.or_eq_true] at h
      unfold insertSubscriberSorted
      split
      · simp only [List.any_cons, Bool.or_eq_true]; exact h
      · split
        · simp only [List.any_cons, Bool.or_eq_true]; right; exact h
        · simp only [List.any_cons, Bool.or_eq_true]
          cases h with
          | inl hl => left; exact hl
          | inr hr => right; exact ih hr

private theorem any_id_insertSubscriberSorted_of_false (xs : List ModHookSubscriber) (s : ModHookSubscriber)
    (target : ModId) (hne : s.id ≠ target) (h : xs.any (·.id == target) = false) :
    (insertSubscriberSorted s xs).any (·.id == target) = false := by
  have hs : (s.id == target) = false := beq_false_of_ne hne
  induction xs with
  | nil => simp [insertSubscriberSorted, hs]
  | cons hd tl ih =>
      simp only [List.any_cons] at h
      have hhd : (hd.id == target) = false := by
        cases hh : (hd.id == target) <;> rw [hh] at h <;> first | rfl | cases h
      have htl : (tl.any (·.id == target)) = false := by
        rw [hhd, Bool.false_or] at h; exact h
      unfold insertSubscriberSorted
      split
      · simp [List.any_cons, hhd, htl]
      · split
        · simp [List.any_cons, hs, hhd, htl]
        · simp [List.any_cons, hhd, ih htl]

/-- ModHelper hook subscription is independent of mod load order for distinct mod IDs.
    Ref: `ModHelper.cs :: SubscribeForCombatStateHooks`. -/
theorem modHelper_combat_sort_order_independent (reg : ModHookRegistry)
    (id₁ id₂ : ModId) (m₁ m₂ : List ModelId) (hne : id₁ ≠ id₂) :
    (reg.subscribeCombatHooks id₁ m₁).subscribeCombatHooks id₂ m₂ =
    (reg.subscribeCombatHooks id₂ m₂).subscribeCombatHooks id₁ m₁ := by
  unfold ModHookRegistry.subscribeCombatHooks
  cases h1 : reg.combatSubscribers.any (·.id == id₁) <;>
  cases h2 : reg.combatSubscribers.any (·.id == id₂)
  · have h1' := any_id_insertSubscriberSorted_of_false reg.combatSubscribers ⟨id₂, m₂⟩ id₁ hne.symm h1
    have h2' := any_id_insertSubscriberSorted_of_false reg.combatSubscribers ⟨id₁, m₁⟩ id₂ hne h2
    simp only [Bool.false_eq_true, ↓reduceIte, h1', h2']
    congr 1
    exact (insertSubscriberSorted_comm ⟨id₁, m₁⟩ ⟨id₂, m₂⟩ reg.combatSubscribers hne).symm
  · have h2' := any_id_insertSubscriberSorted_of_true reg.combatSubscribers ⟨id₁, m₁⟩ id₂ h2
    simp only [h1, h2', Bool.false_eq_true, ↓reduceIte]
  · have h1' := any_id_insertSubscriberSorted_of_true reg.combatSubscribers ⟨id₂, m₂⟩ id₁ h1
    simp only [h2, h1', Bool.false_eq_true, ↓reduceIte]
  · simp only [h1, h2, ↓reduceIte]

theorem modHelper_run_sort_order_independent (reg : ModHookRegistry)
    (id₁ id₂ : ModId) (m₁ m₂ : List ModelId) (hne : id₁ ≠ id₂) :
    (reg.subscribeRunHooks id₁ m₁).subscribeRunHooks id₂ m₂ =
    (reg.subscribeRunHooks id₂ m₂).subscribeRunHooks id₁ m₁ := by
  unfold ModHookRegistry.subscribeRunHooks
  cases h1 : reg.runSubscribers.any (·.id == id₁) <;>
  cases h2 : reg.runSubscribers.any (·.id == id₂)
  · have h1' := any_id_insertSubscriberSorted_of_false reg.runSubscribers ⟨id₂, m₂⟩ id₁ hne.symm h1
    have h2' := any_id_insertSubscriberSorted_of_false reg.runSubscribers ⟨id₁, m₁⟩ id₂ hne h2
    simp only [Bool.false_eq_true, ↓reduceIte, h1', h2']
    congr 1
    exact (insertSubscriberSorted_comm ⟨id₁, m₁⟩ ⟨id₂, m₂⟩ reg.runSubscribers hne).symm
  · have h2' := any_id_insertSubscriberSorted_of_true reg.runSubscribers ⟨id₁, m₁⟩ id₂ h2
    simp only [h1, h2', Bool.false_eq_true, ↓reduceIte]
  · have h1' := any_id_insertSubscriberSorted_of_true reg.runSubscribers ⟨id₂, m₂⟩ id₁ h1
    simp only [h2, h1', Bool.false_eq_true, ↓reduceIte]
  · simp only [h1, h2, ↓reduceIte]

-- ============================================================================
-- Mod Hook Composition Laws (Additive / Multiplicative / Mixed Counterexample)
-- ============================================================================

/-- Pure additive modifiers from two mods commute up to exact rational value `Dec.eqVal`. -/
theorem mod_additive_hooks_commute (base d₁ d₂ : Dec) :
    Dec.eqVal (Dec.add (Dec.add base d₁) d₂) (Dec.add (Dec.add base d₂) d₁) := by
  have h1 : Dec.eqVal (Dec.add (Dec.add base d₁) d₂) (Dec.add base (Dec.add d₁ d₂)) :=
    Dec.add_assoc_eqVal base d₁ d₂
  have h2 : Dec.eqVal (Dec.add base (Dec.add d₁ d₂)) (Dec.add base (Dec.add d₂ d₁)) :=
    Dec.eqVal_add_compat (Dec.eqVal_refl base) (Dec.add_comm_eqVal d₁ d₂)
  have h3 : Dec.eqVal (Dec.add base (Dec.add d₂ d₁)) (Dec.add (Dec.add base d₂) d₁) :=
    Dec.eqVal_symm (Dec.add_assoc_eqVal base d₂ d₁)
  exact Dec.eqVal_trans h1 (Dec.eqVal_trans h2 h3)

/-- Pure multiplicative modifiers from two mods commute up to exact rational value `Dec.eqVal`. -/
theorem mod_multiplicative_hooks_commute (base m₁ m₂ : Dec) :
    Dec.eqVal (Dec.mul (Dec.mul base m₁) m₂) (Dec.mul (Dec.mul base m₂) m₁) := by
  have h1 : Dec.eqVal (Dec.mul (Dec.mul base m₁) m₂) (Dec.mul base (Dec.mul m₁ m₂)) :=
    Dec.mul_assoc_eqVal base m₁ m₂
  have h2 : Dec.eqVal (Dec.mul base (Dec.mul m₁ m₂)) (Dec.mul base (Dec.mul m₂ m₁)) :=
    Dec.eqVal_mul_compat (Dec.eqVal_refl base) (Dec.mul_comm_eqVal m₁ m₂)
  have h3 : Dec.eqVal (Dec.mul base (Dec.mul m₂ m₁)) (Dec.mul (Dec.mul base m₂) m₁) :=
    Dec.eqVal_symm (Dec.mul_assoc_eqVal base m₂ m₁)
  exact Dec.eqVal_trans h1 (Dec.eqVal_trans h2 h3)

/-- Mixing an additive modifier (+3) and a multiplicative modifier (x1.5) is NOT commutative:
    `(6 + 3) * 1.5 = 13.5` while `6 * 1.5 + 3 = 12`, showing why STS2 strictly splits
    `ModifyDamageAdditive` and `ModifyDamageMultiplicative` into separate passes. -/
theorem mod_mixed_add_mul_noncommutative :
    let base := Dec.ofInt 6
    let addMod := Dec.ofInt 3
    let mulMod := Dec.ofScaled 15 1
    ¬ Dec.eqVal (Dec.mul (Dec.add base addMod) mulMod)
                (Dec.add (Dec.mul base mulMod) addMod) := by
  decide

end Sts2Model.Proofs

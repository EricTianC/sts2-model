/-
  Formal proofs of CardPile disjointness, total card conservation under moves/shuffles,
  Deck vs combat pile isolation, CanPlay resource sufficiency, and Canonical immutability.
  All theorems proved in Lean 4 kernel with zero `sorry`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Cards/CardPile.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/CardPileCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/CardModel.cs`
-/
import Sts2Model.Command.CardCmd

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command

/-- All 5 combat piles contain pairwise disjoint card instance IDs with no duplicates. -/
def CombatPileInvariant (p : PlayerPiles) : Prop :=
  (p.allCards.map (·.instanceId)).Nodup

theorem removeCardById_none {cid : CardInstanceId} {xs : List CardInstance}
    (h : (removeCardById cid xs).1 = none) :
    (removeCardById cid xs).2 = xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
      unfold removeCardById at h ⊢
      split at h
      · cases h
      · rename_i hne
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rw [ih h]

theorem removeCardById_some_perm {cid : CardInstanceId} {xs : List CardInstance} {c : CardInstance}
    (h : (removeCardById cid xs).1 = some c) :
    xs.Perm (c :: (removeCardById cid xs).2) ∧ c.instanceId = cid := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
      unfold removeCardById at h ⊢
      split at h
      · rename_i heq
        simp only [heq, ↓reduceIte]
        cases h
        exact ⟨List.Perm.refl _, beq_iff_eq.mp heq⟩
      · rename_i hne
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        have ih' := ih h
        refine ⟨?_, ih'.2⟩
        exact (ih'.1.cons hd).trans (List.Perm.swap c hd _)

theorem removeCardById_some_length {cid : CardInstanceId} {xs : List CardInstance} {c : CardInstance}
    (h : (removeCardById cid xs).1 = some c) :
    (removeCardById cid xs).2.length + 1 = xs.length := by
  have hp := (removeCardById_some_perm h).1.length_eq
  simp only [List.length_cons] at hp
  omega

theorem insertIntoPileList_perm (pos : CardPilePosition) (c : CardInstance) (xs : List CardInstance) :
    (insertIntoPileList pos c xs).Perm (c :: xs) := by
  cases pos with
  | top => exact List.Perm.refl _
  | none => exact List.perm_append_singleton c xs
  | bottom => exact List.perm_append_singleton c xs
  | random => exact List.perm_append_singleton c xs

theorem insertIntoPileList_length (pos : CardPilePosition) (c : CardInstance) (xs : List CardInstance) :
    (insertIntoPileList pos c xs).length = xs.length + 1 := by
  cases pos <;> simp [insertIntoPileList]

private theorem setPile_getPile_perm (p : PlayerPiles) (pt : PileType) (cs : List CardInstance)
    (hCombat : pt.isCombatPile = true) :
    (p.setPile pt cs).allCards.Perm (cs ++ (p.setPile pt []).allCards) := by
  cases pt <;> try cases hCombat
  · -- draw
    simp only [PlayerPiles.setPile, PlayerPiles.allCards]
    have h1 : (p.hand ++ cs ++ p.discard ++ p.exhaust ++ p.play).Perm
              ((p.hand ++ cs) ++ (p.discard ++ p.exhaust ++ p.play)) := by
      simp only [List.append_assoc]; exact List.Perm.refl _
    have h2 : ((p.hand ++ cs) ++ (p.discard ++ p.exhaust ++ p.play)).Perm
              ((cs ++ p.hand) ++ (p.discard ++ p.exhaust ++ p.play)) :=
      List.Perm.append_right _ List.perm_append_comm
    have h3 : ((cs ++ p.hand) ++ (p.discard ++ p.exhaust ++ p.play)).Perm
              (cs ++ (p.hand ++ [] ++ p.discard ++ p.exhaust ++ p.play)) := by
      simp only [List.append_nil, List.append_assoc]; exact List.Perm.refl _
    exact h1.trans (h2.trans h3)
  · -- hand
    simp only [PlayerPiles.setPile, PlayerPiles.allCards, List.nil_append, List.append_assoc]
    exact List.Perm.refl _
  · -- discard
    simp only [PlayerPiles.setPile, PlayerPiles.allCards]
    have h1 : (p.hand ++ p.draw ++ cs ++ p.exhaust ++ p.play).Perm
              ((p.hand ++ p.draw ++ cs) ++ (p.exhaust ++ p.play)) := by
      simp only [List.append_assoc]; exact List.Perm.refl _
    have h2 : ((p.hand ++ p.draw ++ cs) ++ (p.exhaust ++ p.play)).Perm
              ((cs ++ (p.hand ++ p.draw)) ++ (p.exhaust ++ p.play)) := by
      apply List.Perm.append_right
      simpa only [List.append_assoc] using (List.perm_append_comm : ((p.hand ++ p.draw) ++ cs).Perm (cs ++ (p.hand ++ p.draw)))
    have h3 : ((cs ++ (p.hand ++ p.draw)) ++ (p.exhaust ++ p.play)).Perm
              (cs ++ (p.hand ++ p.draw ++ [] ++ p.exhaust ++ p.play)) := by
      simp only [List.append_nil, List.append_assoc]; exact List.Perm.refl _
    exact h1.trans (h2.trans h3)
  · -- exhaust
    simp only [PlayerPiles.setPile, PlayerPiles.allCards]
    have h1 : (p.hand ++ p.draw ++ p.discard ++ cs ++ p.play).Perm
              ((p.hand ++ p.draw ++ p.discard ++ cs) ++ p.play) := by
      simp only [List.append_assoc]; exact List.Perm.refl _
    have h2 : ((p.hand ++ p.draw ++ p.discard ++ cs) ++ p.play).Perm
              ((cs ++ (p.hand ++ p.draw ++ p.discard)) ++ p.play) := by
      apply List.Perm.append_right
      simpa only [List.append_assoc] using (List.perm_append_comm : ((p.hand ++ p.draw ++ p.discard) ++ cs).Perm (cs ++ (p.hand ++ p.draw ++ p.discard)))
    have h3 : ((cs ++ (p.hand ++ p.draw ++ p.discard)) ++ p.play).Perm
              (cs ++ (p.hand ++ p.draw ++ p.discard ++ [] ++ p.play)) := by
      simp only [List.append_nil, List.append_assoc]; exact List.Perm.refl _
    exact h1.trans (h2.trans h3)
  · -- play
    simp only [PlayerPiles.setPile, PlayerPiles.allCards]
    have h1 : (p.hand ++ p.draw ++ p.discard ++ p.exhaust ++ cs).Perm
              (cs ++ (p.hand ++ p.draw ++ p.discard ++ p.exhaust)) :=
      List.perm_append_comm
    simpa [List.append_nil, List.append_assoc] using h1

private theorem allCards_perm_of_setPile (p : PlayerPiles) (pt : PileType)
    (hCombat : pt.isCombatPile = true) :
    p.allCards.Perm (p.getPile pt ++ (p.setPile pt []).allCards) := by
  have h := setPile_getPile_perm p pt (p.getPile pt) hCombat
  have hid : p.setPile pt (p.getPile pt) = p := by
    cases pt <;> first | rfl | cases hCombat
  rw [hid] at h
  exact h

private theorem setPile_setPile_empty (p : PlayerPiles) (pt : PileType) (cs : List CardInstance) :
    (p.setPile pt cs).setPile pt [] = p.setPile pt [] := by
  cases pt <;> rfl

/-- Moving a card between combat piles preserves `totalCount`.
    Ref: `CardPileCmd.Add` + `RemoveFromCurrentPile`. -/
theorem moveCard_totalCount (piles : PlayerPiles) (cid : CardInstanceId) (destPile : PileType)
    (pos : CardPilePosition) (tr : CardInstance → CardInstance)
    (hDest : destPile.isCombatPile = true)
    (hFound : (moveCard piles cid destPile pos tr).2.isSome = true) :
    (moveCard piles cid destPile pos tr).1.totalCount = piles.totalCount := by
  unfold moveCard at hFound ⊢
  cases hFind : piles.findPileOf cid with
  | none => rw [hFind] at hFound
  | some srcPile =>
      rw [hFind] at hFound
      dsimp only at hFound ⊢
      cases hRem : (removeCardById cid (piles.getPile srcPile)).1 with
      | none => rw [hRem] at hFound
      | some card =>
          dsimp only
          have hSrcCombat : srcPile.isCombatPile = true := by
            unfold PlayerPiles.findPileOf at hFind
            split at hFind
            · cases hFind; rfl
            · split at hFind
              · cases hFind; rfl
              · split at hFind
                · cases hFind; rfl
                · split at hFind
                  · cases hFind; rfl
                  · split at hFind
                    · cases hFind; rfl
                    · cases hFind
          have hCond : (destPile == .none || destPile == .deck) = false := by
            cases destPile <;> first | rfl | cases hDest
          rw [hCond]
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hpSrc := (allCards_perm_of_setPile piles srcPile hSrcCombat).length_eq
          have hp1 := (setPile_getPile_perm piles srcPile (removeCardById cid (piles.getPile srcPile)).2 hSrcCombat).length_eq
          have hpDst := (allCards_perm_of_setPile (piles.setPile srcPile (removeCardById cid (piles.getPile srcPile)).2) destPile hDest).length_eq
          have hp2 := (setPile_getPile_perm (piles.setPile srcPile (removeCardById cid (piles.getPile srcPile)).2) destPile (insertIntoPileList pos (tr card) ((piles.setPile srcPile (removeCardById cid (piles.getPile srcPile)).2).getPile destPile)) hDest).length_eq
          have hRemLen := removeCardById_some_length hRem
          have hInsLen := insertIntoPileList_length pos (tr card) ((piles.setPile srcPile (removeCardById cid (piles.getPile srcPile)).2).getPile destPile)
          have hTotal : ∀ q : PlayerPiles, q.totalCount = q.allCards.length := by
            intro q; simp [PlayerPiles.totalCount, PlayerPiles.allCards, List.length_append, Nat.add_assoc]
          rw [hTotal, hTotal]
          simp only [List.length_append] at hpSrc hp1 hpDst hp2
          omega

/-- Moving a card between combat piles with an ID-preserving transform preserves `CombatPileInvariant`. -/
theorem moveCard_preserves_invariant (piles : PlayerPiles) (cid : CardInstanceId) (destPile : PileType)
    (pos : CardPilePosition) (tr : CardInstance → CardInstance)
    (hId : ∀ c, (tr c).instanceId = c.instanceId)
    (hDest : destPile.isCombatPile = true)
    (hInv : CombatPileInvariant piles) :
    CombatPileInvariant (moveCard piles cid destPile pos tr).1 := by
  unfold CombatPileInvariant at *
  unfold moveCard
  cases hFind : piles.findPileOf cid with
  | none => exact hInv
  | some srcPile =>
      dsimp only
      cases hRem : (removeCardById cid (piles.getPile srcPile)).1 with
      | none => exact hInv
      | some card =>
          dsimp only
          have hSrcCombat : srcPile.isCombatPile = true := by
            unfold PlayerPiles.findPileOf at hFind
            split at hFind
            · cases hFind; rfl
            · split at hFind
              · cases hFind; rfl
              · split at hFind
                · cases hFind; rfl
                · split at hFind
                  · cases hFind; rfl
                  · split at hFind
                    · cases hFind; rfl
                    · cases hFind
          have hCond : (destPile == .none || destPile == .deck) = false := by
            cases destPile <;> first | rfl | cases hDest
          rw [hCond]
          simp only [Bool.false_eq_true, ↓reduceIte]
          let piles1 := piles.setPile srcPile (removeCardById cid (piles.getPile srcPile)).2
          let dstList := insertIntoPileList pos (tr card) (piles1.getPile destPile)
          have hpSrc := allCards_perm_of_setPile piles srcPile hSrcCombat
          have hp1 := setPile_getPile_perm piles srcPile (removeCardById cid (piles.getPile srcPile)).2 hSrcCombat
          have hpRem := (removeCardById_some_perm hRem).1
          -- piles.allCards ~ card :: piles1.allCards
          have hCardPiles1 : piles.allCards.Perm (card :: piles1.allCards) := by
            have ha := hpSrc.trans (List.Perm.append_right _ hpRem)
            have hb : (card :: (removeCardById cid (piles.getPile srcPile)).2 ++ (piles.setPile srcPile []).allCards).Perm
                      (card :: piles1.allCards) := by
              change (card :: ((removeCardById cid (piles.getPile srcPile)).2 ++ (piles.setPile srcPile []).allCards)).Perm (card :: piles1.allCards)
              exact List.Perm.cons card hp1.symm
            exact ha.trans hb
          have hpDst := allCards_perm_of_setPile piles1 destPile hDest
          have hp2 := setPile_getPile_perm piles1 destPile dstList hDest
          have hInsPerm := insertIntoPileList_perm pos (tr card) (piles1.getPile destPile)
          have hpOut : (piles1.setPile destPile dstList).allCards.Perm (tr card :: piles1.allCards) := by
            have hA := hp2.trans (List.Perm.append_right _ hInsPerm)
            have hB : ((tr card :: piles1.getPile destPile) ++ (piles1.setPile destPile []).allCards).Perm
                      (tr card :: piles1.allCards) :=
              List.Perm.cons (tr card) hpDst.symm
            exact hA.trans hB
          have hIdsIn : (piles.allCards.map (·.instanceId)).Perm (card.instanceId :: piles1.allCards.map (·.instanceId)) :=
            hCardPiles1.map (·.instanceId)
          have hIdsOut : ((piles1.setPile destPile dstList).allCards.map (·.instanceId)).Perm
              ((tr card).instanceId :: piles1.allCards.map (·.instanceId)) :=
            hpOut.map (·.instanceId)
          rw [hId card] at hIdsOut
          have hNodupMid : (card.instanceId :: piles1.allCards.map (·.instanceId)).Nodup :=
            hIdsIn.nodup_iff.mp hInv
          exact hIdsOut.nodup_iff.mpr hNodupMid

/-- Shuffling discard into draw preserves total combat card count and `CombatPileInvariant`.
    Ref: `CardPileCmd.Shuffle`. -/
theorem shuffleDiscardIntoDraw_totalCount (piles : PlayerPiles) (rng : Rng) (stable : Bool := false) :
    (shuffleDiscardIntoDraw piles rng stable).1.totalCount = piles.totalCount := by
  cases stable <;> simp [shuffleDiscardIntoDraw, PlayerPiles.totalCount, Rng.unstableShuffle_length] <;> omega

theorem shuffleDiscardIntoDraw_preserves_invariant (piles : PlayerPiles) (rng : Rng)
    (hInv : CombatPileInvariant piles) :
    CombatPileInvariant (shuffleDiscardIntoDraw piles rng).1 := by
  unfold CombatPileInvariant shuffleDiscardIntoDraw PlayerPiles.allCards at *
  dsimp only
  have hShuf := Rng.unstableShuffle_perm (piles.draw ++ piles.discard) rng
  have hAllPerm :
      (piles.hand ++ (Rng.unstableShuffle (piles.draw ++ piles.discard) rng).1 ++ [] ++ piles.exhaust ++ piles.play).Perm
      (piles.hand ++ piles.draw ++ piles.discard ++ piles.exhaust ++ piles.play) := by
    have hMid := List.Perm.append_right (piles.exhaust ++ piles.play) hShuf
    have hLeft := List.Perm.append_left piles.hand hMid
    simpa only [List.append_nil, List.append_assoc] using hLeft
  exact (hAllPerm.map (·.instanceId)).nodup_iff.mpr hInv

/-- `cloneDeckForCombat` produces combat piles from `player.deck` without mutating `player.deck`
    (out-of-combat deck isolation). Ref: `PileType.Deck`. -/
theorem cloneDeckForCombat_preserves_deck (player : Player) (baseId : Nat) :
    (cloneDeckForCombat player baseId).1.draw.length = player.deck.length ∧
    (cloneDeckForCombat player baseId).1.hand = [] ∧
    (cloneDeckForCombat player baseId).1.discard = [] ∧
    (cloneDeckForCombat player baseId).1.exhaust = [] ∧
    (cloneDeckForCombat player baseId).1.play = [] := by
  unfold cloneDeckForCombat
  suffices h : ∀ (xs : List CardInstance) (acc : List CardInstance) (idC : Nat),
      (xs.foldl (fun (a, i) dc => (a ++ [{ dc with instanceId := i, isCanonical := false }], i + 1)) (acc, idC)).1.length =
      acc.length + xs.length by
    simpa using h player.deck [] baseId
  intro xs
  induction xs with
  | nil => intro acc idC; simp
  | cons hd tl ih =>
      intro acc idC
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.length_append]
      omega

/-- If `canPlay` succeeds, `checkResourcesFor` guarantees `energy` and `stars` never underflow.
    Ref: `CardModel.CanPlay` & `CardModel.SpendResources`. -/
theorem canPlay_implies_sufficient_resources (cs : CombatState) (reg : BehaviorRegistry)
    (pid : PlayerId) (card : CardInstance) (autoPlay : AutoPlayType)
    (modSubscribers : List (ModId × ModelId))
    (player : Player) (pcs : PlayerCombatState)
    (hFind : cs.findPlayer pid = some player)
    (hPcs : player.combatState = some pcs)
    (hCan : (canPlay cs reg pid card autoPlay modSubscribers).1 = true) :
    let eCost : Int :=
      if card.energyCost.costsX then (pcs.energy : Int)
      else effectiveEnergyCost cs reg card modSubscribers
    let sCost : Int := effectiveStarCost pcs card
    let excessWithStars := shouldPayExcessEnergyCostWithStars cs reg player modSubscribers
    let (eReq, sReq, _) := pcs.checkResourcesFor eCost sCost excessWithStars
    eReq ≤ pcs.energy ∧ sReq ≤ pcs.stars := by
  unfold canPlay at hCan
  rw [hFind] at hCan
  dsimp only at hCan
  rw [hPcs] at hCan
  dsimp only at hCan
  unfold UnplayableReason.isPlayable UnplayableReason.none at hCan
  have heq := beq_iff_eq.mp hCan
  dsimp only at heq ⊢
  injection heq with _ _ _ hE hS _
  simp only [PlayerCombatState.checkResourcesFor] at hE hS ⊢
  constructor
  · exact Nat.le_of_not_gt (fun h => by rw [decide_eq_true h] at hE; cases hE)
  · exact Nat.le_of_not_gt (fun h => by rw [decide_eq_true h] at hS; cases hS)

/-- `CanonicalModel` can never be marked mutable; cloning via `.toMutable` produces a distinct `MutableModel`
    preserving `modelId`. Ref: `AbstractModel.IsCanonical` / `ToMutable`. -/
theorem canonicalModel_toMutable_preserves_id {α : Type} (c : CanonicalModel α) :
    c.isCanonical = true ∧
    c.isMutable = false ∧
    c.toMutable.isMutable = true ∧
    c.toMutable.isCanonical = false ∧
    c.toMutable.modelId = c.modelId := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Sts2Model.Proofs

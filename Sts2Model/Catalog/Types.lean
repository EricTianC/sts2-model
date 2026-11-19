/-
  Static Catalog Entry Structures & Sorted-Chunk Kernel Verification Helpers.
  Enables pure kernel verification (no `native_decide`, no `sorry`) of all
  vanilla Card (717), Relic (316), and Power (304) definitions extracted from `reference/sts2/`.
-/
import Sts2Model.Core.Enums

namespace Sts2Model.Catalog

open Sts2Model.Core

/-- Static canonical metadata for a vanilla Card parsed from `MegaCrit.Sts2.Core.Models.Cards/*.cs`. -/
structure CardCatalogEntry where
  id           : String
  className    : String
  baseCost     : Int
  costsX       : Bool
  baseStarCost : Int
  cardType     : CardType
  rarity       : CardRarity
  targetType   : TargetType
  keywords     : List CardKeyword
  tags         : List CardTag
  deriving Repr, DecidableEq, Inhabited

/-- Static canonical metadata for a vanilla Relic parsed from `MegaCrit.Sts2.Core.Models.Relics/*.cs`. -/
structure RelicCatalogEntry where
  id        : String
  className : String
  rarity    : RelicRarity
  deriving Repr, DecidableEq, Inhabited

/-- Static canonical metadata for a vanilla Power parsed from `MegaCrit.Sts2.Core.Models.Powers/*.cs`. -/
structure PowerCatalogEntry where
  id            : String
  className     : String
  powerType     : PowerType
  stackType     : PowerStackType
  instanceType  : PowerInstanceType
  allowNegative : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Strictly ascending ordering predicate on `List String` using `String.lt`. -/
def isStrictlySorted : List String → Bool
  | []           => true
  | [_]          => true
  | a :: b :: xs => decide (a < b) && isStrictlySorted (b :: xs)

theorem isStrictlySorted_cons_lt :
    ∀ (a : String) (xs : List String), isStrictlySorted (a :: xs) = true → ∀ x ∈ xs, a < x
  | _, [] => fun _ _ h => nomatch h
  | _, b :: tl => fun h x hx => by
      simp only [isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
      cases hx with
      | head => exact h.1
      | tail _ hmem => exact Std.lt_trans h.1 (isStrictlySorted_cons_lt b tl h.2 x hmem)

theorem isStrictlySorted_implies_nodup :
    ∀ xs : List String, isStrictlySorted xs = true → xs.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: xs => fun h => by
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        exact Std.lt_irrefl (isStrictlySorted_cons_lt a xs h a hmem)
      · exact isStrictlySorted_implies_nodup xs (by
          cases xs with
          | nil => rfl
          | cons b tl =>
              simp only [isStrictlySorted, Bool.and_eq_true] at h
              exact h.2)

theorem isStrictlySorted_append :
    ∀ (xs ys : List String),
      isStrictlySorted xs = true →
      isStrictlySorted ys = true →
      (∀ a b, xs.getLast? = some a → ys.head? = some b → a < b) →
      isStrictlySorted (xs ++ ys) = true
  | [], _ => fun _ hy _ => hy
  | [_], [] => fun hx _ _ => hx
  | [a], b :: _ => fun _ hy hlink => by
      simp only [List.singleton_append, isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hlink a b rfl rfl, hy⟩
  | a :: a2 :: as, ys => fun hx hy hlink => by
      simp only [isStrictlySorted, Bool.and_eq_true] at hx
      simp only [List.cons_append, isStrictlySorted, Bool.and_eq_true]
      refine ⟨hx.1, isStrictlySorted_append (a2 :: as) ys hx.2 hy ?_⟩
      intro x y hxLast hyHead
      exact hlink x y (by simpa [List.getLast?] using hxLast) hyHead

theorem strictlySorted_join {α : Type} (xs ys : List α) (f : α → String)
    (hx : isStrictlySorted (xs.map f) = true)
    (hy : isStrictlySorted (ys.map f) = true)
    (hb : (match (xs.map f).getLast?, (ys.map f).head? with
           | some a, some b => decide (a < b)
           | _, _ => true) = true) :
    isStrictlySorted ((xs ++ ys).map f) = true := by
  rw [List.map_append]
  apply isStrictlySorted_append (xs.map f) (ys.map f) hx hy
  intro a b ha hb'
  rw [ha, hb'] at hb
  exact of_decide_eq_true hb

end Sts2Model.Catalog

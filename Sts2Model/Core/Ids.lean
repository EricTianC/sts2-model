/-
  Model identifiers, runtime entity IDs, deterministic ordering, and Canonical vs Mutable
  model type-level separation.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Models/ModelId.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/AbstractModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Models/DeterministicModelComparer.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/CombatId.cs`
-/

namespace Sts2Model.Core

/-- Categories of models registered in `ModelDb`.
    Ref: `ModelId.SlugifyCategory` and `ModelDb.cs`. -/
inductive ModelCategory where
  | none
  | card
  | relic
  | power
  | potion
  | enchantment
  | affliction
  | orb
  | monster
  | character
  | act
  | event
  | ancientEvent
  | encounter
  | modifier
  | badge
  | cardPool
  | potionPool
  | relicPool
  | dominion
  | runModel
  | custom (slug : String)
  deriving Repr, DecidableEq, Inhabited

def ModelCategory.slug : ModelCategory → String
  | .none         => "NONE"
  | .card         => "CARD"
  | .relic        => "RELIC"
  | .power        => "POWER"
  | .potion       => "POTION"
  | .enchantment  => "ENCHANTMENT"
  | .affliction   => "AFFLICTION"
  | .orb          => "ORB"
  | .monster      => "MONSTER"
  | .character    => "CHARACTER"
  | .act          => "ACT"
  | .event        => "EVENT"
  | .ancientEvent => "ANCIENT_EVENT"
  | .encounter    => "ENCOUNTER"
  | .modifier     => "MODIFIER"
  | .badge        => "BADGE"
  | .cardPool     => "CARD_POOL"
  | .potionPool   => "POTION_POOL"
  | .relicPool    => "RELIC_POOL"
  | .dominion     => "DOMINION"
  | .runModel     => "RUN"
  | .custom s     => s

/-- Deterministic sorting ID matching `ModelIdSerializationCache.GetNetIdForCategory`. -/
def ModelCategory.sortingId : ModelCategory → Nat
  | .none         => 0
  | .act          => 1
  | .affliction   => 2
  | .ancientEvent => 3
  | .badge        => 4
  | .card         => 5
  | .cardPool     => 6
  | .character    => 7
  | .dominion     => 8
  | .enchantment  => 9
  | .encounter    => 10
  | .event        => 11
  | .modifier     => 12
  | .monster      => 13
  | .orb          => 14
  | .potion       => 15
  | .potionPool   => 16
  | .power        => 17
  | .relic        => 18
  | .relicPool    => 19
  | .runModel     => 20
  | .custom _     => 99

/-- Model identifier `(Category, Entry)`. Ref: `Core.Models/ModelId.cs`. -/
structure ModelId where
  category : String
  entry : String
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace ModelId

def none : ModelId := ⟨"NONE", "NONE"⟩

def mkCard (entry : String) : ModelId := ⟨"CARD", entry⟩
def mkRelic (entry : String) : ModelId := ⟨"RELIC", entry⟩
def mkPower (entry : String) : ModelId := ⟨"POWER", entry⟩
def mkPotion (entry : String) : ModelId := ⟨"POTION", entry⟩
def mkEnchantment (entry : String) : ModelId := ⟨"ENCHANTMENT", entry⟩
def mkAffliction (entry : String) : ModelId := ⟨"AFFLICTION", entry⟩
def mkOrb (entry : String) : ModelId := ⟨"ORB", entry⟩
def mkMonster (entry : String) : ModelId := ⟨"MONSTER", entry⟩
def mkCharacter (entry : String) : ModelId := ⟨"CHARACTER", entry⟩
def mkModifier (entry : String) : ModelId := ⟨"MODIFIER", entry⟩
def mkBadge (entry : String) : ModelId := ⟨"BADGE", entry⟩
def mkDominion (entry : String) : ModelId := ⟨"DOMINION", entry⟩

def toString (m : ModelId) : String :=
  m.category ++ "." ++ m.entry

instance : ToString ModelId := ⟨toString⟩

/-- Ordinal comparison matching `ModelId.Compare(a, b)` in `ModelId.cs`. -/
def compare (a b : ModelId) : Ordering :=
  match String.compare a.category b.category with
  | .eq => String.compare a.entry b.entry
  | ord => ord

instance : Ord ModelId := ⟨compare⟩

end ModelId

/-- Runtime entity identifiers for determinism across multiplayer peers. -/
abbrev CreatureId := Nat
abbrev PlayerId := Nat
abbrev CardInstanceId := Nat
abbrev PowerInstanceId := Nat
abbrev OrbInstanceId := Nat
abbrev CombatId := Nat
abbrev ModId := String

/-- Mutability marker mirroring `AbstractModel.IsMutable` / `IsCanonical`. -/
inductive ModelMutability where
  | canonical
  | mutable
  deriving Repr, DecidableEq, Inhabited

/-- Type-level wrapper ensuring `ModelDb` canonical templates cannot be mutated directly.
    Ref: `AbstractModel.AssertCanonical` / `AssertMutable` / `ToMutable`. -/
structure ModelRef (m : ModelMutability) (α : Type) where
  modelId : ModelId
  payload : α
  deriving Repr, DecidableEq

abbrev CanonicalModel (α : Type) := ModelRef .canonical α
abbrev MutableModel (α : Type) := ModelRef .mutable α

def CanonicalModel.toMutable {α : Type} (c : CanonicalModel α) : MutableModel α :=
  ⟨c.modelId, c.payload⟩

def ModelRef.isCanonical {m : ModelMutability} {α : Type} (_ : ModelRef m α) : Bool :=
  match m with
  | .canonical => true
  | .mutable   => false

def ModelRef.isMutable {m : ModelMutability} {α : Type} (_ : ModelRef m α) : Bool :=
  match m with
  | .canonical => false
  | .mutable   => true

end Sts2Model.Core

/-
  Orb instance and OrbQueue model (Lightning, Frost, Dark, Plasma, Glass).
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Orbs/OrbQueue.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/OrbModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Orbs/*.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums

namespace Sts2Model.Model

open Sts2Model.Core

/-- Mutable orb instance channeled in a player's `OrbQueue`.
    Ref: `Core.Models/OrbModel.cs` & `Core.Models.Orbs/*.cs`. -/
structure OrbInstance where
  instanceId : OrbInstanceId
  modelId    : ModelId
  kind       : OrbKind
  basePassive : Dec
  baseEvoke   : Dec
  deriving Repr, DecidableEq, Inhabited

namespace OrbInstance

def mkDefault (id : OrbInstanceId) : OrbKind → OrbInstance
  | .lightning => ⟨id, ModelId.mkOrb "LIGHTNING_ORB", .lightning, Dec.ofInt 3, Dec.ofInt 8⟩
  | .frost     => ⟨id, ModelId.mkOrb "FROST_ORB", .frost, Dec.ofInt 2, Dec.ofInt 5⟩
  | .dark      => ⟨id, ModelId.mkOrb "DARK_ORB", .dark, Dec.ofInt 6, Dec.ofInt 6⟩
  | .plasma    => ⟨id, ModelId.mkOrb "PLASMA_ORB", .plasma, Dec.ofInt 1, Dec.ofInt 2⟩
  | .glass     => ⟨id, ModelId.mkOrb "GLASS_ORB", .glass, Dec.ofInt 4, Dec.ofInt 8⟩
  | .custom s  => ⟨id, ModelId.mkOrb s, .custom s, Dec.zero, Dec.zero⟩

end OrbInstance

/-- Player orb queue with `maxCapacity = 10`.
    Ref: `Core.Entities.Orbs/OrbQueue.cs`. -/
structure OrbQueue where
  capacity : Nat := 0
  orbs     : List OrbInstance := []
  deriving Repr, DecidableEq, Inhabited

namespace OrbQueue

def maxCapacity : Nat := 10

def clear (_ : OrbQueue) : OrbQueue :=
  { capacity := 0, orbs := [] }

def addCapacity (q : OrbQueue) (amount : Nat) : OrbQueue :=
  { q with capacity := min maxCapacity (q.capacity + amount) }

def removeCapacity (q : OrbQueue) (amount : Nat) : OrbQueue :=
  let newCap := q.capacity - amount
  { capacity := newCap, orbs := q.orbs.take newCap }

def isFull (q : OrbQueue) : Bool :=
  q.orbs.length ≥ q.capacity

def tryEnqueue (q : OrbQueue) (orb : OrbInstance) : OrbQueue × Bool :=
  if q.capacity == 0 || q.orbs.length ≥ q.capacity then
    (q, false)
  else
    ({ q with orbs := q.orbs ++ [orb] }, true)

def dequeueFront (q : OrbQueue) : OrbQueue × Option OrbInstance :=
  match q.orbs with
  | [] => (q, none)
  | o :: os => ({ q with orbs := os }, some o)

def popLast (q : OrbQueue) : OrbQueue × Option OrbInstance :=
  match q.orbs.reverse with
  | [] => (q, none)
  | o :: revRest => ({ q with orbs := revRest.reverse }, some o)

end OrbQueue
end Sts2Model.Model

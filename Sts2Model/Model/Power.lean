/-
  Power model instance and stacking / sign / removal rules.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Models/PowerModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Powers/*.cs`
-/
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums

namespace Sts2Model.Model

open Sts2Model.Core

/-- Mutable power instance attached to a creature.
    Ref: `Core.Models/PowerModel.cs`. -/
structure PowerInstance where
  instanceId            : PowerInstanceId
  modelId               : ModelId
  ownerId               : CreatureId
  applierId             : Option CreatureId := none
  targetId              : Option CreatureId := none
  powerType             : PowerType := .buff
  stackType             : PowerStackType := .counter
  instanceType          : PowerInstanceType := .none
  allowNegative         : Bool := false
  isVisible             : Bool := true
  scaleInMultiplayer    : Bool := false
  amount                : Int := 0
  amountOnTurnStart     : Int := 0
  skipNextDurationTick  : Bool := false
  ownerIsSecondaryEnemy : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace PowerInstance

def maxAmountBound : Int := 999999999

/-- Ref: `PowerModel.SetAmount` clamp `[-999999999, 999999999]`. -/
@[inline] def clampAmount (a : Int) : Int :=
  max (-maxAmountBound) (min maxAmountBound a)

/-- Ref: `PowerModel.GetTypeForAmount(decimal customAmount)`. -/
def getTypeForAmount (p : PowerInstance) (amt : Int) : PowerType :=
  if p.stackType == .counter && p.allowNegative && amt < 0 then
    .debuff
  else if !p.allowNegative && p.powerType == .debuff && amt < 0 then
    .buff
  else
    p.powerType

def typeForCurrentAmount (p : PowerInstance) : PowerType :=
  p.getTypeForAmount p.amount

/-- Ref: `PowerModel.ShouldRemoveDueToAmount()`. -/
def shouldRemoveDueToAmount (p : PowerInstance) : Bool :=
  if p.allowNegative then
    p.amount == 0
  else
    p.amount ≤ 0

end PowerInstance
end Sts2Model.Model

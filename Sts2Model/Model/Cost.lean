/-
  Card energy cost model, local cost modifiers, expiration rules, and temporary card costs.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Cards/CardEnergyCost.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Cards/LocalCostModifier.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Cards/TemporaryCardCost.cs`
-/
import Sts2Model.Core.Enums

namespace Sts2Model.Model

open Sts2Model.Core

/-- A single local modifier to a card's cost.
    Ref: `Core.Entities.Cards/LocalCostModifier.cs`. -/
structure LocalCostModifier where
  amount       : Int
  costType     : LocalCostType
  expiration   : LocalCostModifierExpiration
  isReduceOnly : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace LocalCostModifier

/-- Ref: `LocalCostModifier.Modify(int currentCost)`. -/
def modify (m : LocalCostModifier) (currentCost : Int) : Int :=
  match m.costType with
  | .absolute => if m.isReduceOnly then min currentCost m.amount else m.amount
  | .relative => if m.isReduceOnly then min currentCost (currentCost + m.amount) else currentCost + m.amount
  | .none     => currentCost

end LocalCostModifier

/-- Temporary card cost (used for energy or star temporary sets).
    Ref: `Core.Entities.Cards/TemporaryCardCost.cs`. -/
structure TemporaryCardCost where
  cost                   : Nat
  clearsWhenTurnEnds     : Bool
  clearsWhenCardIsPlayed : Bool
  deriving Repr, DecidableEq, Inhabited

namespace TemporaryCardCost

def untilPlayed (cost : Int) : TemporaryCardCost :=
  { cost := Int.toNat (max cost 0), clearsWhenTurnEnds := false, clearsWhenCardIsPlayed := true }

def thisTurn (cost : Int) : TemporaryCardCost :=
  { cost := Int.toNat (max cost 0), clearsWhenTurnEnds := true, clearsWhenCardIsPlayed := true }

def thisCombat (cost : Int) : TemporaryCardCost :=
  { cost := Int.toNat (max cost 0), clearsWhenTurnEnds := false, clearsWhenCardIsPlayed := false }

end TemporaryCardCost

/-- Encapsulates energy cost, X-cost capture, upgrades, and local cost modifiers.
    Ref: `Core.Entities.Cards/CardEnergyCost.cs`. -/
structure CardEnergyCost where
  canonical       : Int
  baseCost        : Int
  costsX          : Bool := false
  capturedXValue  : Nat := 0
  wasJustUpgraded : Bool := false
  localModifiers  : List LocalCostModifier := []
  deriving Repr, DecidableEq, Inhabited

namespace CardEnergyCost

def mkCanonical (canonicalCost : Int) (costsX : Bool := false) : CardEnergyCost :=
  let c := if costsX then 0 else canonicalCost
  { canonical := c, baseCost := c, costsX := costsX }

/-- Evaluate cost applying local modifiers (and optionally a precomputed global hook modifier).
    Ref: `CardEnergyCost.GetWithModifiers(CostModifiers modifiers)`. -/
def getWithModifiers (e : CardEnergyCost) (isCanonical : Bool)
    (modifiers : CostModifiers := CostModifiers.all)
    (globalAdjust : Int → Int := id) : Int :=
  if isCanonical || e.baseCost < 0 || e.costsX then
    e.baseCost
  else
    let afterLocal :=
      if modifiers.includeLocal then
        e.localModifiers.foldl (fun acc m => m.modify acc) e.baseCost
      else
        e.baseCost
    let afterGlobal :=
      if modifiers.includeGlobal then
        globalAdjust afterLocal
      else
        afterLocal
    max 0 afterGlobal

/-- Ref: `CardEnergyCost.GetAmountToSpend()`. -/
def getAmountToSpend (e : CardEnergyCost) (playerEnergy : Nat)
    (isCanonical : Bool := false) (globalAdjust : Int → Int := id) : Nat :=
  if e.costsX then
    playerEnergy
  else
    Int.toNat (max 0 (e.getWithModifiers isCanonical CostModifiers.all globalAdjust))

/-- Ref: `CardEnergyCost.GetResolved()`. -/
def getResolved (e : CardEnergyCost) (isCanonical : Bool := false)
    (globalAdjust : Int → Int := id) : Nat :=
  if e.costsX then
    e.capturedXValue
  else
    Int.toNat (max 0 (e.getWithModifiers isCanonical CostModifiers.all globalAdjust))

/-- Add a local modifier. Ref: `CardEnergyCost.Set*` / `Add*`. -/
def addModifier (e : CardEnergyCost) (m : LocalCostModifier) : CardEnergyCost :=
  { e with localModifiers := e.localModifiers ++ [m] }

def setUntilPlayed (e : CardEnergyCost) (cost : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if cost == 0 && e.canonical < 0 then e
  else e.addModifier ⟨cost, .absolute, LocalCostModifierExpiration.onlyWhenPlayed, reduceOnly⟩

def setThisTurnOrUntilPlayed (e : CardEnergyCost) (cost : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if cost == 0 && e.canonical < 0 then e
  else e.addModifier ⟨cost, .absolute, LocalCostModifierExpiration.endOfTurnOrWhenPlayed, reduceOnly⟩

def setThisTurn (e : CardEnergyCost) (cost : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if cost == 0 && e.canonical < 0 then e
  else e.addModifier ⟨cost, .absolute, LocalCostModifierExpiration.onlyEndOfTurn, reduceOnly⟩

def setThisCombat (e : CardEnergyCost) (cost : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if cost == 0 && e.canonical < 0 then e
  else e.addModifier ⟨cost, .absolute, LocalCostModifierExpiration.endOfCombat, reduceOnly⟩

def addUntilPlayed (e : CardEnergyCost) (amount : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if amount == 0 then e
  else e.addModifier ⟨amount, .relative, LocalCostModifierExpiration.onlyWhenPlayed, reduceOnly⟩

def addThisTurnOrUntilPlayed (e : CardEnergyCost) (amount : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if amount == 0 then e
  else e.addModifier ⟨amount, .relative, LocalCostModifierExpiration.endOfTurnOrWhenPlayed, reduceOnly⟩

def addThisTurn (e : CardEnergyCost) (amount : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if amount == 0 then e
  else e.addModifier ⟨amount, .relative, LocalCostModifierExpiration.onlyEndOfTurn, reduceOnly⟩

def addThisCombat (e : CardEnergyCost) (amount : Int) (reduceOnly : Bool := false) : CardEnergyCost :=
  if amount == 0 then e
  else e.addModifier ⟨amount, .relative, LocalCostModifierExpiration.endOfCombat, reduceOnly⟩

/-- Ref: `CardEnergyCost.EndOfTurnCleanup()`. -/
def endOfTurnCleanup (e : CardEnergyCost) : CardEnergyCost × Bool :=
  let kept := e.localModifiers.filter (fun m => !m.expiration.endOfTurn)
  let changed := kept.length != e.localModifiers.length
  ({ e with localModifiers := kept }, changed)

/-- Ref: `CardEnergyCost.AfterCardPlayedCleanup()`. -/
def afterCardPlayedCleanup (e : CardEnergyCost) : CardEnergyCost × Bool :=
  let kept := e.localModifiers.filter (fun m => !m.expiration.whenPlayed)
  let changed := kept.length != e.localModifiers.length
  ({ e with localModifiers := kept }, changed)

/-- Ref: `CardEnergyCost.UpgradeBy(int addend)`. -/
def upgradeBy (e : CardEnergyCost) (addend : Int) : CardEnergyCost :=
  if e.costsX || addend == 0 then
    e
  else
    let oldBase := e.baseCost
    let newBase := max (oldBase + addend) 0
    let updatedMods :=
      if newBase < oldBase then
        e.localModifiers.map fun m =>
          if m.costType == .absolute && m.amount > newBase then
            { m with amount := newBase }
          else
            m
      else
        e.localModifiers
    { e with baseCost := newBase, wasJustUpgraded := true, localModifiers := updatedMods }

end CardEnergyCost
end Sts2Model.Model

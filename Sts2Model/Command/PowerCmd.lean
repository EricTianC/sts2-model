/-
  Power application, stacking (`None` / `Instanced` / `InstancedPerApplier`),
  Artifact debuff negation, `AllowNegative`, and zero/non-positive removal.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/PowerCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/PowerModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/ArtifactPower.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Enums
import Sts2Model.Model.State
import Sts2Model.Hook.Pipeline

namespace Sts2Model.Command

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

/-- Locate an existing power instance to stack onto, matching `PowerCmd.FindExistingInstanceForStacking`.
    Ref: `Core.Commands/PowerCmd.cs` lines 169-178. -/
def findExistingInstanceForStacking (basePower : PowerInstance) (target : Creature)
    (applierId : Option CreatureId) : Option PowerInstance :=
  match basePower.instanceType with
  | .instanced => none
  | .instancedPerApplier =>
      target.powers.find? fun p => p.modelId == basePower.modelId && p.applierId == applierId
  | .none =>
      target.powers.find? fun p => p.modelId == basePower.modelId

/-- Decrement a power by 1 and remove it if `shouldRemoveDueToAmount`.
    Ref: `PowerCmd.Decrement` & `PowerCmd.ModifyAmount`. -/
def decrementPowerById (cs : CombatState) (targetId : CreatureId) (instId : PowerInstanceId) : CombatState :=
  cs.updateCreature targetId fun c =>
    let updated := c.powers.map fun p =>
      if p.instanceId == instId then
        { p with amount := PowerInstance.clampAmount (p.amount - 1) }
      else p
    { c with powers := updated.filter (!·.shouldRemoveDueToAmount) }

/-- Decrement all Artifact stacks triggered during `ModifyPowerAmountReceived` (`ArtifactPower.cs` line 40). -/
private def consumeTriggeredModifiers (cs : CombatState) (mods : List ListenerRef) : CombatState :=
  mods.foldl (fun acc ref =>
    match ref with
    | .power ownerId instId mid =>
        if mid == ModelId.mkPower "ARTIFACT_POWER" then
          decrementPowerById acc ownerId instId
        else acc
    | _ => acc) cs

/-- Modify an existing power's amount, clamping and auto-removing when `shouldRemoveDueToAmount` holds.
    Ref: `PowerCmd.ModifyAmount`. -/
def modifyPowerAmount (cs : CombatState) (reg : BehaviorRegistry)
    (targetId : CreatureId) (instId : PowerInstanceId) (offset : Dec)
    (applierId : Option CreatureId := none)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × Int :=
  if cs.isEnding then (cs, 0)
  else
    match cs.findCreature targetId with
    | none => (cs, 0)
    | some target =>
        match target.powers.find? (·.instanceId == instId) with
        | none => (cs, 0)
        | some pow =>
            let applier := applierId.bind cs.findCreature
            let (offset1, _) :=
              match applier with
              | some a =>
                  if cs.containsCreature a.id then
                    modifyPowerAmountGiven cs reg pow (some a) offset target modSubscribers
                  else (offset, [])
              | none => (offset, [])
            let (offset2, recvMods) :=
              modifyPowerAmountReceived cs reg pow target offset1 applier modSubscribers
            let cs1 := consumeTriggeredModifiers cs recvMods
            let deltaInt :=
              if pow.stackType == .single then 0 else offset2.truncate
            let newAmount := PowerInstance.clampAmount (pow.amount + deltaInt)
            let updatedPow := { pow with amount := newAmount }
            let cs2 := cs1.updateCreature targetId fun c =>
              let mapped := c.powers.map fun p => if p.instanceId == instId then updatedPow else p
              { c with powers := mapped.filter (!·.shouldRemoveDueToAmount) }
            let cs3 := cs2.recordHistory (.powerReceived cs2.roundNumber pow.modelId targetId deltaInt)
            (cs3, newAmount)

/-- Apply a power template `template` to `targetId` with raw `amount`.
    Handles stacking, `Single` stack type (`amount := 1`), `ModifyPowerAmountGiven`/`Received`,
    Artifact consumption, `AllowNegative`, and removal if final amount fails invariant.
    Ref: `PowerCmd.Apply`. -/
def applyPower (cs : CombatState) (reg : BehaviorRegistry)
    (template : PowerInstance) (targetId : CreatureId) (amount : Dec)
    (applierId : Option CreatureId := none)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × Option PowerInstance :=
  if cs.isEnding || Dec.eqVal amount Dec.zero then (cs, none)
  else
    match cs.findCreature targetId with
    | none => (cs, none)
    | some target =>
        if !target.isHittableFlag then (cs, none)
        else
          match findExistingInstanceForStacking template target applierId with
          | some existing =>
              let (cs', newAmt) := modifyPowerAmount cs reg targetId existing.instanceId amount applierId modSubscribers
              if newAmt == 0 then (cs', none)
              else (cs', cs'.findCreature targetId |>.bind (·.powers.find? (·.instanceId == existing.instanceId)))
          | none =>
              let (newInstId, csAlloc) := cs.allocInstanceId
              let applier := applierId.bind csAlloc.findCreature
              let (amt1, _) :=
                match applier with
                | some a =>
                    if csAlloc.containsCreature a.id then
                      modifyPowerAmountGiven csAlloc reg template (some a) amount target modSubscribers
                    else (amount, [])
                | none => (amount, [])
              let (amt2, recvMods) :=
                modifyPowerAmountReceived csAlloc reg template target amt1 applier modSubscribers
              let cs1 := consumeTriggeredModifiers csAlloc recvMods
              let rawInt := if template.stackType == .single then
                  if amt2.truncate == 0 then 0 else 1
                else amt2.truncate
              let clamped := PowerInstance.clampAmount rawInt
              let newPow : PowerInstance :=
                { template with
                  instanceId := newInstId
                , ownerId := targetId
                , applierId := applierId
                , amount := clamped
                , skipNextDurationTick :=
                    (target.side == .player && cs1.currentSide == .enemy && template.powerType == .debuff) ||
                    (target.side == .enemy && cs1.currentSide == .enemy && template.modelId == ModelId.mkPower "RITUAL_POWER") }
              if newPow.shouldRemoveDueToAmount then
                (cs1, none)
              else
                let cs2 := cs1.updateCreature targetId fun c => { c with powers := c.powers ++ [newPow] }
                let cs3 := cs2.recordHistory (.powerReceived cs2.roundNumber newPow.modelId targetId clamped)
                (cs3, some newPow)

/-- Remove a specific power instance from a creature. Ref: `PowerCmd.Remove`. -/
def removePower (cs : CombatState) (targetId : CreatureId) (instId : PowerInstanceId) : CombatState :=
  cs.updateCreature targetId fun c =>
    { c with powers := c.powers.filter (·.instanceId != instId) }

/-- Remove all instances matching `powerModelId` from `targetId`. Ref: `PowerCmd.Remove<T>`. -/
def removePowerByModel (cs : CombatState) (targetId : CreatureId) (powerModelId : ModelId) : CombatState :=
  cs.updateCreature targetId fun c =>
    { c with powers := c.powers.filter (·.modelId != powerModelId) }

/-- Clear `skipNextDurationTick` without decrementing (`RitualPower` / `TickDownDuration`). -/
def clearSkipDurationTick (cs : CombatState) (targetId : CreatureId) (instId : PowerInstanceId) : CombatState :=
  cs.updateCreature targetId fun c =>
    { c with powers := c.powers.map fun q =>
        if q.instanceId == instId then { q with skipNextDurationTick := false } else q }

/-- Tick down a duration-based power (`Vulnerable`, `Weak`, `Frail`), respecting `SkipNextDurationTick`.
    Ref: `PowerCmd.TickDownDuration`. -/
def tickDownDuration (cs : CombatState) (targetId : CreatureId) (instId : PowerInstanceId) : CombatState :=
  match cs.findCreature targetId |>.bind (·.powers.find? (·.instanceId == instId)) with
  | none => cs
  | some p =>
      if p.skipNextDurationTick then
        clearSkipDurationTick cs targetId instId
      else
        decrementPowerById cs targetId instId

end Sts2Model.Command

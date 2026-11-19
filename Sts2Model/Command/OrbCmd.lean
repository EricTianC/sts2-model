/-
  Orb channeling, evoking, capacity management, and passive triggering.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/OrbCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Orbs/*.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Model.State
import Sts2Model.Command.CreatureCmd

namespace Sts2Model.Command

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

/-- Add orb slots up to `OrbQueue.maxCapacity = 10`. Ref: `OrbCmd.AddSlots`. -/
def addOrbSlots (cs : CombatState) (pid : PlayerId) (amount : Nat) : CombatState :=
  if cs.isEnding then cs
  else cs.updatePlayer pid fun p =>
    match p.combatState with
    | none => p
    | some pcs => { p with combatState := some { pcs with orbQueue := pcs.orbQueue.addCapacity amount } }

/-- Remove orb slots from the back. Ref: `OrbCmd.RemoveSlots`. -/
def removeOrbSlots (cs : CombatState) (pid : PlayerId) (amount : Nat) : CombatState :=
  if cs.isEnding then cs
  else cs.updatePlayer pid fun p =>
    match p.combatState with
    | none => p
    | some pcs => { p with combatState := some { pcs with orbQueue := pcs.orbQueue.removeCapacity amount } }

/-- Apply passive effect of a single orb (Lightning, Frost, Dark, Plasma, Glass). -/
def triggerOrbPassive (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (orb : OrbInstance) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if cs.isEnding then cs
  else match cs.findPlayer pid with
    | none => cs
    | some player =>
        match orb.kind with
        | .lightning =>
            match cs.hittableEnemies.head? with
            | none => cs
            | some target =>
                (damageSingleTarget cs reg target.id orb.basePassive DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
        | .frost =>
            (gainBlock cs reg player.creatureId orb.basePassive BlockProps.nonCardUnpowered none modSubscribers).1
        | .dark =>
            cs.updatePlayer pid fun p =>
              match p.combatState with
              | none => p
              | some pcs =>
                  let orbs' := pcs.orbQueue.orbs.map fun o =>
                    if o.instanceId == orb.instanceId then { o with baseEvoke := Dec.add o.baseEvoke o.basePassive }
                    else o
                  { p with combatState := some { pcs with orbQueue := { pcs.orbQueue with orbs := orbs' } } }
        | .plasma =>
            cs.updatePlayer pid fun p =>
              match p.combatState with
              | none => p
              | some pcs => { p with combatState := some (pcs.gainEnergy orb.basePassive.toNat) }
        | .glass =>
            let targets := cs.hittableEnemies.map (·.id)
            let csDmg := (damage cs reg targets orb.basePassive DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
            csDmg.updatePlayer pid fun p =>
              match p.combatState with
              | none => p
              | some pcs =>
                  let orbs' := pcs.orbQueue.orbs.map fun o =>
                    if o.instanceId == orb.instanceId then
                      { o with basePassive := Dec.maxZero (Dec.sub o.basePassive Dec.one) }
                    else o
                  { p with combatState := some { pcs with orbQueue := { pcs.orbQueue with orbs := orbs' } } }
        | .custom _ => cs

/-- Apply evoke effect of an orb. Ref: `OrbCmd.Evoke` & `Core.Models.Orbs/*.cs`. -/
def applyOrbEvoke (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (orb : OrbInstance) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  match cs.findPlayer pid with
  | none => cs
  | some player =>
      match orb.kind with
      | .lightning =>
          match cs.hittableEnemies.head? with
          | none => cs
          | some target =>
              (damageSingleTarget cs reg target.id orb.baseEvoke DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
      | .frost =>
          (gainBlock cs reg player.creatureId orb.baseEvoke BlockProps.nonCardUnpowered none modSubscribers).1
      | .dark =>
          let lowestEnemy := cs.hittableEnemies.foldl (fun best cur =>
            match best with
            | none => some cur
            | some b => if cur.currentHp < b.currentHp then some cur else some b) none
          match lowestEnemy with
          | none => cs
          | some target =>
              (damageSingleTarget cs reg target.id orb.baseEvoke DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
      | .plasma =>
          cs.updatePlayer pid fun p =>
            match p.combatState with
            | none => p
            | some pcs => { p with combatState := some (pcs.gainEnergy orb.baseEvoke.toNat) }
      | .glass =>
          let targets := cs.hittableEnemies.map (·.id)
          let evokeAmt := Dec.mul orb.basePassive (Dec.ofInt 2)
          (damage cs reg targets evokeAmt DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
      | .custom _ => cs

/-- Evoke the front orb in `OrbQueue`. Ref: `OrbCmd.EvokeNext`. -/
def evokeNextOrb (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (dequeue : Bool := true) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if cs.isEnding then cs
  else match cs.findPlayer pid |>.bind (·.combatState) with
    | none => cs
    | some pcs =>
        match pcs.orbQueue.orbs.head? with
        | none => cs
        | some frontOrb =>
            let cs1 :=
              if dequeue then
                cs.updatePlayer pid fun p =>
                  match p.combatState with
                  | none => p
                  | some st =>
                      let (q', _) := st.orbQueue.dequeueFront
                      { p with combatState := some { st with orbQueue := q' } }
              else cs
            applyOrbEvoke cs1 reg pid frontOrb modSubscribers

/-- Channel an orb, evoking the front orb first if `OrbQueue` is full.
    Ref: `OrbCmd.Channel`. -/
def channelOrb (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (kind : OrbKind) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if cs.isEnding then cs
  else match cs.findPlayer pid with
    | none => cs
    | some player =>
        match player.combatState with
        | none => cs
        | some pcs =>
            let cs0 :=
              if player.baseOrbSlots == 0 && pcs.orbQueue.capacity == 0 then
                addOrbSlots cs pid 1
              else cs
            let cs1 :=
              match cs0.findPlayer pid |>.bind (·.combatState) with
              | some pcsNow =>
                  if pcsNow.orbQueue.isFull then evokeNextOrb cs0 reg pid true modSubscribers
                  else cs0
              | none => cs0
            let (oid, cs2) := cs1.allocInstanceId
            let orb := OrbInstance.mkDefault oid kind
            cs2.updatePlayer pid fun p =>
              match p.combatState with
              | none => p
              | some st =>
                  let (q', _) := st.orbQueue.tryEnqueue orb
                  { p with combatState := some { st with orbQueue := q' } }

end Sts2Model.Command

/-
  Defect Orbs system: Focus modification (Plasma immunity), passive/evoke values,
  Glass decay, Dark accumulation, Hibernate Frost sharing, turn-start vs turn-end triggers.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Models/OrbModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Orbs/*.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/FocusPower.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/OrbCmd.cs`
-/
import Sts2Model.Command.OrbCmd

namespace Sts2Model.Mechanics

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command

def focusPowerModelId : ModelId := ModelId.mkPower "FOCUS_POWER"
def hibernatePowerModelId : ModelId := ModelId.mkPower "HIBERNATE_POWER"

/-- Player's total current Focus power amount (`FocusPower`, allows negative). -/
def focusAmountOf (cs : CombatState) (pid : PlayerId) : Int :=
  match cs.findPlayer pid |>.bind (fun p => cs.findCreature p.creatureId) with
  | none => 0
  | some c => c.getPowerAmount focusPowerModelId

/-- Apply Focus to an orb value (`FocusPower.ModifyOrbValue`: `Math.Max(value + Amount, 0m)`).
    Plasma overrides `PassiveVal => 1m` and `EvokeVal => 2m` directly WITHOUT `ModifyOrbValue`. -/
def modifyOrbValue (focus : Int) (kind : OrbKind) (baseVal : Dec) : Dec :=
  match kind with
  | .plasma => baseVal
  | _       => Dec.maxZero (Dec.add baseVal (Dec.ofInt focus))

/-- Effective orb passive value accounting for Focus. -/
def effectivePassiveVal (focus : Int) (orb : OrbInstance) : Dec :=
  modifyOrbValue focus orb.kind orb.basePassive

/-- Effective orb evoke value accounting for Focus:
    - `Lightning`, `Frost`: `ModifyOrbValue(baseEvoke)`
    - `Dark`: accumulated `baseEvoke` (does NOT re-apply Focus on evoke; `DarkOrb.cs` line 25)
    - `Plasma`: `baseEvoke` (2 energy, unaffected by Focus; `PlasmaOrb.cs` line 19)
    - `Glass`: `PassiveVal * 2m` (`GlassOrb.cs` line 23) -/
def effectiveEvokeVal (focus : Int) (orb : OrbInstance) : Dec :=
  match orb.kind with
  | .lightning => modifyOrbValue focus .lightning orb.baseEvoke
  | .frost     => modifyOrbValue focus .frost orb.baseEvoke
  | .dark      => orb.baseEvoke
  | .plasma    => orb.baseEvoke
  | .glass     => Dec.mul (effectivePassiveVal focus orb) (Dec.ofInt 2)
  | .custom k  => modifyOrbValue focus (.custom k) orb.baseEvoke

/-- Focus-aware passive trigger matching `LightningOrb`, `FrostOrb` (+`HibernatePower`),
    `DarkOrb` (accumulates `effectivePassiveVal`), `PlasmaOrb`, and `GlassOrb` (decays `-1` min 0). -/
def triggerOrbPassiveWithFocus (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (orb : OrbInstance) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if cs.isEnding then cs
  else
    let focus := focusAmountOf cs pid
    let pVal := effectivePassiveVal focus orb
    match cs.findPlayer pid with
    | none => cs
    | some player =>
        let ownerAlive := cs.findCreature player.creatureId |>.map (·.isAlive) |>.getD false
        let hasHibernate := cs.findCreature player.creatureId |>.map (·.hasPower hibernatePowerModelId) |>.getD false
        match orb.kind with
        | .lightning =>
            match cs.hittableEnemies.head? with
            | none => cs
            | some target =>
                (damageSingleTarget cs reg target.id pVal DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
        | .frost =>
            let cs1 := (gainBlock cs reg player.creatureId pVal BlockProps.nonCardUnpowered none modSubscribers).1
            if !hasHibernate then cs1
            else cs1.players.foldl (fun acc pl =>
              if pl.playerId == pid then acc
              else (gainBlock acc reg pl.creatureId pVal BlockProps.nonCardUnpowered none modSubscribers).1) cs1
        | .dark =>
            let _ := ownerAlive
            cs.updatePlayer pid fun p =>
              match p.combatState with
              | none => p
              | some pcs =>
                  let orbs' := pcs.orbQueue.orbs.map fun o =>
                    if o.instanceId == orb.instanceId then
                      { o with baseEvoke := Dec.add o.baseEvoke pVal }
                    else o
                  { p with combatState := some { pcs with orbQueue := { pcs.orbQueue with orbs := orbs' } } }
        | .plasma =>
            cs.updatePlayer pid fun p =>
              match p.combatState with
              | none => p
              | some pcs => { p with combatState := some (pcs.gainEnergy orb.basePassive.toNat) }
        | .glass =>
            if pVal ≤ Dec.zero then cs
            else
              let targets := cs.hittableEnemies.map (·.id)
              let csDecayed := cs.updatePlayer pid fun p =>
                match p.combatState with
                | none => p
                | some pcs =>
                    let orbs' := pcs.orbQueue.orbs.map fun o =>
                      if o.instanceId == orb.instanceId then
                        { o with basePassive := Dec.maxZero (Dec.sub o.basePassive Dec.one) }
                      else o
                    { p with combatState := some { pcs with orbQueue := { pcs.orbQueue with orbs := orbs' } } }
              (damage csDecayed reg targets pVal DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
        | .custom _ => cs

/-- Focus-aware evoke effect matching all 5 Defect orb classes. -/
def applyOrbEvokeWithFocus (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (orb : OrbInstance) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  let focus := focusAmountOf cs pid
  let eVal := effectiveEvokeVal focus orb
  match cs.findPlayer pid with
  | none => cs
  | some player =>
      let hasHibernate := cs.findCreature player.creatureId |>.map (·.hasPower hibernatePowerModelId) |>.getD false
      match orb.kind with
      | .lightning =>
          match cs.hittableEnemies.head? with
          | none => cs
          | some target =>
              (damageSingleTarget cs reg target.id eVal DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
      | .frost =>
          let cs1 := (gainBlock cs reg player.creatureId eVal BlockProps.nonCardUnpowered none modSubscribers).1
          if !hasHibernate then cs1
          else cs1.players.foldl (fun acc pl =>
            if pl.playerId == pid then acc
            else (gainBlock acc reg pl.creatureId eVal BlockProps.nonCardUnpowered none modSubscribers).1) cs1
      | .dark =>
          let lowestEnemy := cs.hittableEnemies.foldl (fun best cur =>
            match best with
            | none => some cur
            | some b => if cur.currentHp < b.currentHp then some cur else some b) none
          match lowestEnemy with
          | none => cs
          | some target =>
              (damageSingleTarget cs reg target.id eVal DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
      | .plasma =>
          cs.updatePlayer pid fun p =>
            match p.combatState with
            | none => p
            | some pcs => { p with combatState := some (pcs.gainEnergy orb.baseEvoke.toNat) }
      | .glass =>
          if eVal ≤ Dec.zero then cs
          else
            let targets := cs.hittableEnemies.map (·.id)
            (damage cs reg targets eVal DamageProps.nonCardUnpowered (some player.creatureId) none .all modSubscribers).1
      | .custom _ => cs

/-- Plasma orb triggers at `AfterTurnStartOrbTrigger` (`PlasmaOrb.cs` line 21). -/
def triggerTurnStartOrbs (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  match cs.findPlayer pid |>.bind (·.combatState) with
  | none => cs
  | some pcs =>
      pcs.orbQueue.orbs.foldl (fun acc o =>
        if o.kind == .plasma then triggerOrbPassiveWithFocus acc reg pid o modSubscribers else acc) cs

/-- Lightning, Frost, Dark, Glass trigger at `BeforeTurnEndOrbTrigger`. -/
def triggerTurnEndOrbs (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  match cs.findPlayer pid |>.bind (·.combatState) with
  | none => cs
  | some pcs =>
      pcs.orbQueue.orbs.foldl (fun acc o =>
        if o.kind != .plasma then triggerOrbPassiveWithFocus acc reg pid o modSubscribers else acc) cs

end Sts2Model.Mechanics

/-
  Necrobinder mechanics: Osty summoning & revival (`OstyCmd.Summon`),
  `DieForYouPower` damage redirection & dead-Osty untargetability, and `DoomPower` lethal execute.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/OstyCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/DieForYouPower.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/DoomPower.cs`
-/
import Sts2Model.Command.CreatureCmd
import Sts2Model.Command.PowerCmd

namespace Sts2Model.Mechanics

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command

def ostyMonsterModelId : ModelId := ModelId.mkMonster "OSTY"
def dieForYouPowerModelId : ModelId := ModelId.mkPower "DIE_FOR_YOU_POWER"
def doomPowerModelId : ModelId := ModelId.mkPower "DOOM_POWER"

def findOsty (cs : CombatState) (summonerId : PlayerId) : Option Creature :=
  cs.allies.find? fun c => c.modelId == ostyMonsterModelId && c.petOwnerId == some summonerId

/-- `DieForYouPower`: redirects unblocked powered attack damage from `PetOwner` to living Osty,
    and returns `ShouldAllowHitting = false` if target is dead Osty (`DieForYouPower.cs`). -/
def dieForYouBehavior (cs : CombatState) : HookBehavior :=
  { modifyUnblockedDamageTarget := fun ctx curTarget _amt props _dealer =>
      match ctx.ownerId |>.bind cs.findCreature with
      | none => curTarget
      | some osty =>
          match osty.petOwnerId |>.bind cs.findPlayer with
          | none => curTarget
          | some petOwner =>
              if curTarget != petOwner.creatureId then curTarget
              else if osty.isDead then curTarget
              else if !props.isPoweredAttack then curTarget
              else osty.id
  , shouldAllowHitting := fun ctx target =>
      match ctx.ownerId |>.bind cs.findCreature with
      | none => true
      | some osty => if osty.id == target.id then osty.isAlive else true }

/-- `CreatureCmd.GainMaxHp`: adds `amount` to maxHp and heals by the delta gained (`CreatureCmd.cs` line 937). -/
def gainMaxHp (cs : CombatState) (targetId : CreatureId) (amount : Dec) : CombatState :=
  if amount < Dec.zero then cs
  else match cs.findCreature targetId with
    | none => cs
    | some c =>
        let newMax := min (c.maxHp + amount.toNat) Creature.statCap
        let gained := newMax - c.maxHp
        let cs1 := setMaxHp cs targetId (Dec.ofNat newMax)
        heal cs1 targetId (Dec.ofNat gained)

/-- Summon or empower/revive Osty matching `OstyCmd.Summon`:
    1. Alive Osty exists -> `GainMaxHp(osty, amount)`
    2. Dead Osty exists -> revive in place: `SetMaxHp(amount)` + `Heal(amount)`
    3. No Osty exists -> spawn new pet Osty with `DieForYouPower` + `SetMaxHp(amount)` + `Heal(amount)` -/
def summonOsty (cs : CombatState) (reg : BehaviorRegistry) (summonerId : PlayerId) (amount : Dec)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × SummonResult :=
  if Dec.eqVal amount Dec.zero || amount < Dec.zero then
    (cs, { creatureId := (findOsty cs summonerId).map (·.id), amount := Dec.zero })
  else
    match findOsty cs summonerId with
    | some osty =>
        if osty.isAlive then
          let cs' := gainMaxHp cs osty.id amount
          (cs', { creatureId := some osty.id, amount := amount })
        else
          -- Reviving dead Osty: SetMaxHp + Heal
          let hpNat := min amount.toNat Creature.statCap
          let cs1 := cs.updateCreature osty.id fun c =>
            { c with maxHp := hpNat, currentHp := hpNat, isHittableFlag := true }
          let cs2 := cs1.updatePlayer summonerId fun p =>
            match p.combatState with
            | none => p
            | some pcs =>
                let pets' := if pcs.petIds.contains osty.id then pcs.petIds else pcs.petIds ++ [osty.id]
                { p with combatState := some { pcs with petIds := pets' } }
          (cs2, { creatureId := some osty.id, amount := amount })
    | none =>
        let (newCid, cs1) := cs.allocInstanceId
        let hpNat := min amount.toNat Creature.statCap
        let newOsty : Creature :=
          { id := newCid
          , modelId := ostyMonsterModelId
          , side := .player
          , petOwnerId := some summonerId
          , currentHp := hpNat
          , maxHp := hpNat
          , isHittableFlag := true }
        let cs2 := { cs1 with allies := cs1.allies ++ [newOsty] }
        let cs3 := cs2.updatePlayer summonerId fun p =>
          match p.combatState with
          | none => p
          | some pcs => { p with combatState := some { pcs with petIds := pcs.petIds ++ [newCid] } }
        let dieTemplate : PowerInstance :=
          { instanceId := 0
          , modelId := dieForYouPowerModelId
          , ownerId := newCid
          , powerType := .buff
          , stackType := .single }
        let (cs4, _) := applyPower cs3 reg dieTemplate newCid Dec.one none modSubscribers
        (cs4, { creatureId := some newCid, amount := amount })

/-- `DoomPower.IsOwnerDoomed()`: `Owner.CurrentHp <= Amount` (`DoomPower.cs` line 149). -/
def isCreatureDoomed (c : Creature) : Bool :=
  match c.getPower doomPowerModelId with
  | none => false
  | some p => (c.currentHp : Int) ≤ p.amount

/-- Collect all living creatures on `side` that are doomed. Ref: `DoomPower.GetDoomedCreatures`. -/
def getDoomedCreatures (cs : CombatState) (side : CombatSide) : List CreatureId :=
  (cs.getTeammatesOf side).filter (fun c => c.isAlive && isCreatureDoomed c) |>.map (·.id)

/-- Execute `DoomPower.DoomKill` for every doomed living creature on `side`. -/
def triggerSideDoomKill (cs : CombatState) (reg : BehaviorRegistry) (side : CombatSide)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if cs.isEnding then cs
  else
    let doomed := getDoomedCreatures cs side
    doomed.foldl (fun acc cid => (kill acc reg cid false modSubscribers).1) cs

end Sts2Model.Mechanics

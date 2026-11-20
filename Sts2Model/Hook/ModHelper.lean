/-
  Modding registries (`ModHelper`) and unified `HookBehavior` interface for both
  vanilla models and user-authored mods.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Modding/ModHelper.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/AbstractModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/*.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Relics/*.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Model.State
import Sts2Model.Hook.Registry

namespace Sts2Model.Hook

open Sts2Model.Core
open Sts2Model.Model

-- ============================================================================
-- ModHelper Pool Registration & Hook Subscription Registries
-- Ref: `Core.Modding/ModHelper.cs`
-- ============================================================================

structure ModPoolEntry where
  poolKey    : String
  isFrozen   : Bool := false
  modelsToAdd : List ModelId := []
  deriving Repr, DecidableEq, Inhabited

structure ModPoolRegistry where
  entries : List ModPoolEntry := []
  deriving Repr, DecidableEq, Inhabited

namespace ModPoolRegistry

def empty : ModPoolRegistry := ⟨[]⟩

def findEntry (reg : ModPoolRegistry) (poolKey : String) : Option ModPoolEntry :=
  reg.entries.find? (·.poolKey == poolKey)

def isPoolFrozen (reg : ModPoolRegistry) (poolKey : String) : Bool :=
  (reg.findEntry poolKey).map (·.isFrozen) |>.getD false

def upsertEntry (entries : List ModPoolEntry) (e : ModPoolEntry) : List ModPoolEntry :=
  if entries.any (·.poolKey == e.poolKey) then
    entries.map fun cur => if cur.poolKey == e.poolKey then e else cur
  else
    entries ++ [e]

/-- Ref: `ModHelper.AddModelToPool(Type poolType, Type modelType)`.
    Returns `.error` if the pool has already been frozen by `concatModelsFromMods`. -/
def addModelToPool (reg : ModPoolRegistry) (poolKey : String) (modelId : ModelId) :
    Except String ModPoolRegistry :=
  match reg.findEntry poolKey with
  | some e =>
      if e.isFrozen then
        .error s!"Tried to add model {modelId} to pool {poolKey}, but it's too late!"
      else
        let e' := { e with modelsToAdd := e.modelsToAdd ++ [modelId] }
        .ok ⟨upsertEntry reg.entries e'⟩
  | none =>
      let e' : ModPoolEntry := ⟨poolKey, false, [modelId]⟩
      .ok ⟨upsertEntry reg.entries e'⟩

/-- Ref: `ModHelper.ConcatModelsFromMods`. Freezes the pool and appends modded models. -/
def concatModelsFromMods (reg : ModPoolRegistry) (poolKey : String) (basePool : List ModelId) :
    ModPoolRegistry × List ModelId :=
  match reg.findEntry poolKey with
  | some e =>
      let e' := { e with isFrozen := true }
      (⟨upsertEntry reg.entries e'⟩, basePool ++ e.modelsToAdd)
  | none =>
      let e' : ModPoolEntry := ⟨poolKey, true, []⟩
      (⟨upsertEntry reg.entries e'⟩, basePool)

end ModPoolRegistry

/-- Mod subscriber entry sorted deterministically by ordinal `id`.
    Ref: `ModHelper.ModRunHookSubscriber` / `ModCombatHookSubscriber`. -/
structure ModHookSubscriber where
  id     : ModId
  models : List ModelId
  deriving Repr, DecidableEq, Inhabited

/-- Ordered insertion by `String.compare` (`string.CompareOrdinal` in C#). -/
def insertSubscriberSorted (s : ModHookSubscriber) : List ModHookSubscriber → List ModHookSubscriber
  | [] => [s]
  | x :: xs =>
      if s.id == x.id then
        x :: xs
      else if String.compare s.id x.id == .lt then
        s :: x :: xs
      else
        x :: insertSubscriberSorted s xs

structure ModHookRegistry where
  runSubscribers    : List ModHookSubscriber := []
  combatSubscribers : List ModHookSubscriber := []
  deriving Repr, DecidableEq, Inhabited

namespace ModHookRegistry

def empty : ModHookRegistry := ⟨[], []⟩

/-- Ref: `ModHelper.SubscribeForRunStateHooks`. Ignores duplicate `id`, keeps sorted by ordinal `id`. -/
def subscribeRunHooks (reg : ModHookRegistry) (id : ModId) (models : List ModelId) : ModHookRegistry :=
  if reg.runSubscribers.any (·.id == id) then reg
  else { reg with runSubscribers := insertSubscriberSorted ⟨id, models⟩ reg.runSubscribers }

/-- Ref: `ModHelper.SubscribeForCombatStateHooks`. Ignores duplicate `id`, keeps sorted by ordinal `id`. -/
def subscribeCombatHooks (reg : ModHookRegistry) (id : ModId) (models : List ModelId) : ModHookRegistry :=
  if reg.combatSubscribers.any (·.id == id) then reg
  else { reg with combatSubscribers := insertSubscriberSorted ⟨id, models⟩ reg.combatSubscribers }

def flattenRun (reg : ModHookRegistry) : List (ModId × ModelId) :=
  reg.runSubscribers.flatMap fun s => s.models.map (s.id, ·)

def flattenCombat (reg : ModHookRegistry) : List (ModId × ModelId) :=
  reg.combatSubscribers.flatMap fun s => s.models.map (s.id, ·)

end ModHookRegistry

-- ============================================================================
-- Listener Context & Unified HookBehavior Interface
-- ============================================================================

/-- Context bound to a specific listener snapshot item when evaluating hooks. -/
structure ListenerCtx where
  ref       : ListenerRef
  ownerId   : Option CreatureId := none
  playerId  : Option PlayerId := none
  amount    : Int := 0
  deriving Repr, DecidableEq, Inhabited

def resolveListenerCtx (cs : CombatState) (ref : ListenerRef) : ListenerCtx :=
  match ref with
  | .power ownerId instId _ =>
      let amt := match cs.findCreature ownerId with
        | some c => (c.powers.find? (·.instanceId == instId)).map (·.amount) |>.getD 0
        | none => 0
      { ref := ref, ownerId := some ownerId, amount := amt }
  | .monster cid _ =>
      { ref := ref, ownerId := some cid }
  | .relic pid _ =>
      let player := cs.findPlayer pid
      let cnt := player.bind (fun p => (p.relics.find? (·.modelId == ref.modelId)).map (·.counter)) |>.getD 0
      { ref := ref, ownerId := player.map (·.creatureId), playerId := some pid, amount := cnt }
  | .potion pid _ _ =>
      let player := cs.findPlayer pid
      { ref := ref, ownerId := player.map (·.creatureId), playerId := some pid }
  | .orb pid _ _ =>
      let player := cs.findPlayer pid
      { ref := ref, ownerId := player.map (·.creatureId), playerId := some pid }
  | .card pid _ _ =>
      let player := cs.findPlayer pid
      { ref := ref, ownerId := player.map (·.creatureId), playerId := some pid }
  | .affliction pid _ _ =>
      let player := cs.findPlayer pid
      { ref := ref, ownerId := player.map (·.creatureId), playerId := some pid }
  | .enchantment pid _ _ =>
      let player := cs.findPlayer pid
      { ref := ref, ownerId := player.map (·.creatureId), playerId := some pid }
  | _ => { ref := ref }

/-- Pure effect values emitted by `HookBehavior` turn-lifecycle & reactive damage callbacks. -/
inductive HookEffect where
  | tickDownDuration (ownerId : CreatureId) (instId : PowerInstanceId)
  | clearSkipDurationTick (ownerId : CreatureId) (instId : PowerInstanceId)
  | decrementPower (ownerId : CreatureId) (instId : PowerInstanceId)
  | modifyPowerAmount (ownerId : CreatureId) (instId : PowerInstanceId) (delta : Int)
  | applyPowerById (targetId : CreatureId) (powerId : ModelId) (amount : Int) (powerType : PowerType := .buff) (allowNegative : Bool := false)
  | dealDamage (dealerId : Option CreatureId) (targetId : CreatureId) (amount : Dec) (props : ValueProp)
  | gainBlock (targetId : CreatureId) (amount : Dec) (props : ValueProp)
  | doomKillSide (side : CombatSide)
  deriving Repr, DecidableEq

/-- Abstract model hook implementation matching virtual methods on `AbstractModel`. -/
structure HookBehavior where
  modifyDamageAdditive :
    ListenerCtx → Option Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ _ _ _ _ => Dec.zero
  modifyDamageMultiplicative :
    ListenerCtx → Option Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ _ _ _ _ => Dec.one
  modifyDamageMultiplicativeLate :
    ListenerCtx → Option Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ _ _ _ _ => Dec.one
  modifyDamageCap :
    ListenerCtx → Option Creature → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ _ _ _ => Dec.maxDecimal
  modifyBlockAdditive :
    ListenerCtx → Creature → Dec → ValueProp → Option CardInstance → Dec :=
    fun _ _ _ _ _ => Dec.zero
  modifyBlockMultiplicative :
    ListenerCtx → Creature → Dec → ValueProp → Option CardInstance → Dec :=
    fun _ _ _ _ _ => Dec.one
  modifyHpLostBeforeOsty :
    ListenerCtx → Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ amt _ _ _ => amt
  modifyHpLostBeforeOstyLate :
    ListenerCtx → Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ amt _ _ _ => amt
  modifyHpLostAfterOsty :
    ListenerCtx → Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ amt _ _ _ => amt
  modifyHpLostAfterOstyLate :
    ListenerCtx → Creature → Dec → ValueProp → Option Creature → Option CardInstance → Dec :=
    fun _ _ amt _ _ _ => amt
  modifyPreBlockDamageTarget :
    ListenerCtx → Creature → Option CreatureId → Dec → ValueProp → Option Creature → Option CreatureId :=
    fun _ _ cur _ _ _ => cur
  modifyUnblockedDamageTarget :
    ListenerCtx → CreatureId → Dec → ValueProp → Option Creature → CreatureId :=
    fun _ cur _ _ _ => cur
  modifyEnergyCostInCombat :
    ListenerCtx → CardInstance → Dec → Dec :=
    fun _ _ c => c
  modifyEnergyCostInCombatLate :
    ListenerCtx → CardInstance → Dec → Dec :=
    fun _ _ c => c
  modifyPowerAmountGivenAdditive :
    ListenerCtx → PowerInstance → Option Creature → Dec → Creature → Dec :=
    fun _ _ _ _ _ => Dec.zero
  modifyPowerAmountGivenMultiplicative :
    ListenerCtx → PowerInstance → Option Creature → Dec → Creature → Dec :=
    fun _ _ _ _ _ => Dec.one
  tryModifyPowerAmountReceived :
    ListenerCtx → PowerInstance → Creature → Dec → Option Creature → Bool × Dec :=
    fun _ _ _ amt _ => (false, amt)
  shouldPlay : ListenerCtx → CardInstance → AutoPlayType → Bool := fun _ _ _ => true
  shouldDie : ListenerCtx → Creature → Bool := fun _ _ => true
  shouldDieLate : ListenerCtx → Creature → Bool := fun _ _ => true
  shouldClearBlock : ListenerCtx → Creature → Bool := fun _ _ => true
  shouldDraw : ListenerCtx → Player → Bool → Bool := fun _ _ _ => true
  shouldEtherealTrigger : ListenerCtx → CardInstance → Bool := fun _ _ => true
  shouldFlush : ListenerCtx → Player → Bool := fun _ _ => true
  shouldStopCombatFromEnding : ListenerCtx → Bool := fun _ => false
  shouldTakeExtraTurnEarly : ListenerCtx → Player → Bool := fun _ _ => false
  shouldTakeExtraTurn : ListenerCtx → Player → Bool := fun _ _ => false
  shouldPayExcessEnergyCostWithStars : ListenerCtx → Player → Bool := fun _ _ => false
  shouldAllowHitting : ListenerCtx → Creature → Bool := fun _ _ => true
  shouldPlayerResetEnergy : ListenerCtx → Player → Bool := fun _ _ => true
  shouldCreatureBeRemovedFromCombatAfterDeath : ListenerCtx → Creature → Bool := fun _ _ => true
  shouldPowerBeRemovedOnDeath : ListenerCtx → PowerInstance → Bool := fun _ _ => true
  afterSideTurnStart : ListenerCtx → CombatState → CombatSide → List CreatureId → List HookEffect :=
    fun _ _ _ _ => []
  beforeSideTurnEnd : ListenerCtx → CombatState → CombatSide → List CreatureId → List HookEffect :=
    fun _ _ _ _ => []
  afterSideTurnEnd : ListenerCtx → CombatState → CombatSide → List CreatureId → List HookEffect :=
    fun _ _ _ _ => []
  beforeDamageReceived : ListenerCtx → CombatState → Creature → Dec → ValueProp → Option Creature → List HookEffect :=
    fun _ _ _ _ _ _ => []

def HookBehavior.neutral : HookBehavior := {}

abbrev BehaviorRegistry := ModelId → HookBehavior

-- ============================================================================
-- Built-in Vanilla Hook Behaviors (Powers & Relics)
-- ============================================================================

def strengthBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyDamageAdditive := fun ctx _ _ props dealer _ =>
      match dealer, ctx.ownerId with
      | some d, some oid =>
          if d.id == oid && props.isPoweredAttack then Dec.ofInt ctx.amount else Dec.zero
      | _, _ => Dec.zero }

def dexterityBehavior (cs : CombatState) : HookBehavior :=
  { HookBehavior.neutral with
    modifyBlockAdditive := fun ctx target _ props card =>
      let recipient := match card with
        | none => some target.id
        | some c => (cs.findPlayer c.ownerId).map (·.creatureId)
      if recipient.isSome && recipient == ctx.ownerId && props.isPoweredCardOrMonsterMoveBlock then
        Dec.ofInt ctx.amount else Dec.zero }

def vulnerableBehavior (cs : CombatState) : HookBehavior :=
  { HookBehavior.neutral with
    modifyDamageMultiplicative := fun ctx target _ props dealer _ =>
      match target, ctx.ownerId with
      | some t, some oid =>
          if t.id == oid && props.isPoweredAttack then
            let baseMul := Dec.ofScaled 15 1 -- 1.5m
            let hasPaperPhrog := match dealer.bind (·.playerId.bind cs.findPlayer) with
              | some p => p.relics.any fun r => !r.isMelted && r.modelId == ModelId.mkRelic "PAPER_PHROG"
              | none   => false
            if hasPaperPhrog then Dec.ofScaled 175 2 else baseMul
          else Dec.one
      | _, _ => Dec.one
    afterSideTurnEnd := fun ctx _ side _ =>
      if side == .enemy then
        match ctx.ref with
        | .power oid instId _ => [.tickDownDuration oid instId]
        | _ => []
      else [] }

def weakBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyDamageMultiplicative := fun ctx _ _ props dealer _ =>
      match dealer, ctx.ownerId with
      | some d, some oid =>
          if d.id == oid && props.isPoweredAttack then Dec.ofScaled 75 2 else Dec.one
      | _, _ => Dec.one
    afterSideTurnEnd := fun ctx _ side _ =>
      if side == .enemy then
        match ctx.ref with
        | .power oid instId _ => [.tickDownDuration oid instId]
        | _ => []
      else [] }

def frailBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyBlockMultiplicative := fun ctx target _ props _ =>
      match ctx.ownerId with
      | some oid =>
          if target.id == oid && props.isPoweredCardOrMonsterMoveBlock then Dec.ofScaled 75 2 else Dec.one
      | none => Dec.one
    afterSideTurnEnd := fun ctx _ side _ =>
      if side == .enemy then
        match ctx.ref with
        | .power oid instId _ => [.tickDownDuration oid instId]
        | _ => []
      else [] }

def intangibleBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyDamageCap := fun ctx target _ _ _ =>
      match target, ctx.ownerId with
      | some t, some oid => if t.id == oid then Dec.one else Dec.maxDecimal
      | _, _ => Dec.maxDecimal
    modifyHpLostAfterOsty := fun ctx target amt _ _ _ =>
      match ctx.ownerId with
      | some oid => if target.id == oid && Dec.one ≤ amt then Dec.one else amt
      | none => amt
    afterSideTurnEnd := fun ctx _ side _ =>
      if side == .enemy then
        match ctx.ref with
        | .power oid instId _ => [.decrementPower oid instId]
        | _ => []
      else [] }

def artifactBehavior : HookBehavior :=
  { HookBehavior.neutral with
    tryModifyPowerAmountReceived := fun ctx pow target amt _ =>
      match ctx.ownerId with
      | some oid =>
          if target.id == oid &&
             pow.getTypeForAmount amt.truncate == .debuff &&
             pow.isVisible &&
             ctx.amount > 0 then
            (true, Dec.zero)
          else (false, amt)
      | none => (false, amt) }

def barricadeBehavior : HookBehavior :=
  { HookBehavior.neutral with
    shouldClearBlock := fun ctx c =>
      match ctx.ownerId with
      | some oid => c.id != oid
      | none => true }

def vajraBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyDamageAdditive := fun ctx _ _ props dealer _ =>
      match dealer, ctx.ownerId with
      | some d, some oid =>
          if d.id == oid && props.isPoweredAttack then Dec.one else Dec.zero
      | _, _ => Dec.zero }

def poisonBehavior : HookBehavior :=
  { HookBehavior.neutral with
    afterSideTurnStart := fun ctx _ _ participants =>
      match ctx.ref with
      | .power oid instId _ =>
          if participants.contains oid && ctx.amount > 0 then
            [ .dealDamage none oid (Dec.ofInt ctx.amount) DamageProps.nonCardHpLoss
            , .decrementPower oid instId ]
          else []
      | _ => [] }

def doomBehavior : HookBehavior :=
  { HookBehavior.neutral with
    beforeSideTurnEnd := fun _ _ side _ =>
      if side == .enemy then [.doomKillSide .enemy] else [] }

def thornsBehavior : HookBehavior :=
  { HookBehavior.neutral with
    beforeDamageReceived := fun ctx _ target _ props dealer =>
      match ctx.ownerId, dealer with
      | some oid, some d =>
          if target.id == oid && props.isPoweredAttack && ctx.amount > 0 then
            [.dealDamage (some oid) d.id (Dec.ofInt ctx.amount) DamageProps.nonCardUnpowered]
          else []
      | _, _ => [] }

def platingBehavior : HookBehavior :=
  { HookBehavior.neutral with
    beforeSideTurnEnd := fun ctx _ _ participants =>
      match ctx.ownerId with
      | some oid =>
          if participants.contains oid && ctx.amount > 0 then
            [.gainBlock oid (Dec.ofInt ctx.amount) BlockProps.nonCardUnpowered]
          else []
      | none => []
    afterSideTurnStart := fun ctx cs _ participants =>
      match ctx.ref with
      | .power oid instId _ =>
          if !participants.contains oid then []
          else
            match cs.findCreature oid with
            | none => []
            | some owner =>
                let skipPlayerTurn1 :=
                  match (owner.playerId.bind cs.findPlayer).bind (·.combatState) with
                  | some pcs => pcs.turnNumber == 1
                  | none     => false
                let skipEnemyRound1 := owner.side == .enemy && cs.roundNumber == 1
                if skipPlayerTurn1 || skipEnemyRound1 then []
                else
                  let decr : Int :=
                    if owner.side == .enemy then -(max 1 cs.players.length : Int) else -1
                  [.modifyPowerAmount oid instId decr]
      | _ => [] }

def ritualBehavior : HookBehavior :=
  { HookBehavior.neutral with
    afterSideTurnEnd := fun ctx cs _ participants =>
      match ctx.ref with
      | .power oid instId _ =>
          if !participants.contains oid then []
          else
            let skipped :=
              (cs.findCreature oid |>.bind (·.powers.find? (·.instanceId == instId))).map
                (·.skipNextDurationTick) |>.getD false
            if skipped then [.clearSkipDurationTick oid instId]
            else if ctx.amount > 0 then
              [.applyPowerById oid (ModelId.mkPower "STRENGTH_POWER") ctx.amount .buff true]
            else []
      | _ => [] }

def builtinBehaviorRegistry (cs : CombatState) : BehaviorRegistry := fun mid =>
  if mid == ModelId.mkPower "STRENGTH_POWER" then strengthBehavior
  else if mid == ModelId.mkPower "DEXTERITY_POWER" then dexterityBehavior cs
  else if mid == ModelId.mkPower "VULNERABLE_POWER" then vulnerableBehavior cs
  else if mid == ModelId.mkPower "WEAK_POWER" then weakBehavior
  else if mid == ModelId.mkPower "FRAIL_POWER" then frailBehavior
  else if mid == ModelId.mkPower "INTANGIBLE_POWER" then intangibleBehavior
  else if mid == ModelId.mkPower "ARTIFACT_POWER" then artifactBehavior
  else if mid == ModelId.mkPower "BARRICADE_POWER" then barricadeBehavior
  else if mid == ModelId.mkPower "POISON_POWER" then poisonBehavior
  else if mid == ModelId.mkPower "DOOM_POWER" then doomBehavior
  else if mid == ModelId.mkPower "THORNS_POWER" then thornsBehavior
  else if mid == ModelId.mkPower "PLATING_POWER" then platingBehavior
  else if mid == ModelId.mkPower "RITUAL_POWER" then ritualBehavior
  else if mid == ModelId.mkRelic "VAJRA" then vajraBehavior
  else HookBehavior.neutral

end Sts2Model.Hook

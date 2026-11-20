/-
  Creature damage, block, heal, max-HP, and kill commands.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/CreatureCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Creatures/Creature.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Enums
import Sts2Model.Model.State
import Sts2Model.Hook.Pipeline

namespace Sts2Model.Command

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

/-- Stage 1 of `damageSingleTargetCore`: PreBlock redirection (Wuppy). -/
def damagePreBlockStage (cs : CombatState) (reg : BehaviorRegistry)
    (originalTarget : Creature) (originalTargetId : CreatureId)
    (amount modifiedAmt : Dec) (props : ValueProp) (dealer : Option Creature)
    (cardSource : Option CardInstance) (modSubscribers : List (ModId × ModelId)) :
    CombatState × Dec × List DamageResult :=
  match (modifyPreBlockDamageTarget cs reg originalTarget amount props dealer modSubscribers).bind cs.findCreature with
  | none => (cs, modifiedAmt, [])
  | some preTarget =>
      let (wAmt, _) :=
        modifyHpLost cs reg originalTarget modifiedAmt props dealer cardSource HpLossHookPhase.wuppyOnly modSubscribers
      let (preTarget', resW) := preTarget.loseHpInternal wAmt props
      let resW' := { resW with
        intendedHpLoss := modifiedAmt.truncate
        originalTargetId := originalTargetId }
      (cs.updateCreature preTarget.id (fun _ => preTarget'), Dec.ofNat resW.overkillDamage, [resW'])

/-- Stage 2 of `damageSingleTargetCore`: Block absorption on target or PetOwner. -/
def damageBlockStage (cs1 : CombatState) (blockHolderId : CreatureId)
    (dmgAfterPre : Dec) (props : ValueProp) :
    CombatState × Dec × Bool × Bool :=
  match cs1.findCreature blockHolderId with
  | none => (cs1, Dec.zero, false, false)
  | some bh =>
      let hadBlock := bh.block > 0
      let (bh', bDec) := bh.damageBlockInternal dmgAfterPre props
      let broken := bh'.block == 0 && bDec > Dec.zero
      let remAfter := Dec.maxZero (Dec.sub dmgAfterPre bDec)
      let fully := !props.unblockable && (bDec > Dec.zero || hadBlock) && remAfter.truncate == 0
      (cs1.updateCreature bh.id (fun _ => bh'), bDec, broken, fully)

/-- Stage 3 of `damageSingleTargetCore`: Unblocked target HP loss (with Osty redirect). -/
def damageUnblockedStage (cs2 : CombatState) (reg : BehaviorRegistry)
    (ubTargetId originalTargetId : CreatureId)
    (unblockedAmt0 dmgRemaining blockedDec : Dec) (blkBroken fullyBlocked : Bool)
    (props : ValueProp) (dealer : Option Creature) (cardSource : Option CardInstance)
    (modSubscribers : List (ModId × ModelId)) :
    CombatState × DamageResult × Nat :=
  match cs2.findCreature ubTargetId with
  | none =>
      let zeroRes : DamageResult :=
        { receiverId := ubTargetId
        , originalTargetId := originalTargetId
        , props := props
        , intendedHpLoss := dmgRemaining.truncate }
      (cs2, zeroRes, 0)
  | some ubTarget =>
      let (ubAmt, _) :=
        modifyHpLost cs2 reg ubTarget unblockedAmt0 props dealer cardSource HpLossHookPhase.afterOstyOnly modSubscribers
      let (ubTarget', resU) := ubTarget.loseHpInternal ubAmt props
      let resU' :=
        if ubTargetId == originalTargetId then
          { resU with
            intendedHpLoss := dmgRemaining.truncate
            originalTargetId := originalTargetId
            blockedDamage := blockedDec.toNat
            wasBlockBroken := blkBroken
            wasFullyBlocked := fullyBlocked }
        else
          { resU with
            intendedHpLoss := dmgRemaining.truncate
            originalTargetId := originalTargetId }
      (cs2.updateCreature ubTargetId (fun _ => ubTarget'), resU', resU.overkillDamage)

/-- Stage 4 of `damageSingleTargetCore`: Overkill spill-over onto original target (`CreatureCmd.cs:183`). -/
def damageOverkillStage (cs3 : CombatState) (reg : BehaviorRegistry)
    (ubTargetId originalTargetId : CreatureId) (overkill : Nat) (blockedDec : Dec)
    (blkBroken fullyBlocked : Bool) (props : ValueProp) (dealer : Option Creature)
    (cardSource : Option CardInstance) (modSubscribers : List (ModId × ModelId)) :
    CombatState × List DamageResult :=
  if ubTargetId == originalTargetId then (cs3, [])
  else
    match cs3.findCreature originalTargetId with
    | none => (cs3, [])
    | some origNow =>
        let (origAmt, _) :=
          modifyHpLost cs3 reg origNow (Dec.ofNat overkill) props dealer cardSource HpLossHookPhase.afterOstyOnly modSubscribers
        if Dec.zero < origAmt then
          let (orig', resO) := origNow.loseHpInternal origAmt props
          let resO' := { resO with
            intendedHpLoss := overkill
            originalTargetId := originalTargetId
            blockedDamage := blockedDec.toNat
            wasBlockBroken := blkBroken
            wasFullyBlocked := fullyBlocked }
          (cs3.updateCreature originalTargetId (fun _ => orig'), [resO'])
        else
          let resZero : DamageResult :=
            { receiverId := originalTargetId
            , originalTargetId := originalTargetId
            , props := props
            , blockedDamage := blockedDec.toNat
            , wasBlockBroken := blkBroken
            , wasFullyBlocked := fullyBlocked }
          (cs3, [resZero])

/-- Internal core of `CreatureCmd.Damage` pipeline over one target without reactive `BeforeDamageReceived` re-entry,
    faithfully reproducing: ModifyDamage -> PreBlockTarget (Wuppy) -> PetOwner Block -> BeforeOsty ->
    UnblockedTarget (Osty) + AfterOsty -> Overkill spill-over to OriginalTarget + AfterOsty.
    Ref: `Core.Commands/CreatureCmd.cs` lines 124-210. -/
def damageSingleTargetCore (cs : CombatState) (reg : BehaviorRegistry)
    (originalTargetId : CreatureId) (amount : Dec) (props : ValueProp)
    (dealerId : Option CreatureId) (cardSource : Option CardInstance)
    (hookType : ModifyDamageHookType := ModifyDamageHookType.all)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × List DamageResult :=
  let dealer := dealerId.bind cs.findCreature
  if let some d := dealer then
    if d.isDead then
      (cs, [⟨originalTargetId, originalTargetId, props, 0, 0, 0, 0, false, false, false⟩])
    else
      damageLiveDealer cs reg originalTargetId amount props dealer cardSource hookType modSubscribers
  else
    damageLiveDealer cs reg originalTargetId amount props none cardSource hookType modSubscribers
where
  damageLiveDealer (cs : CombatState) (reg : BehaviorRegistry)
      (originalTargetId : CreatureId) (amount : Dec) (props : ValueProp)
      (dealer : Option Creature) (cardSource : Option CardInstance)
      (hookType : ModifyDamageHookType) (modSubscribers : List (ModId × ModelId)) :
      CombatState × List DamageResult :=
    match cs.findCreature originalTargetId with
    | none => (cs, [])
    | some originalTarget =>
        if originalTarget.isDead then (cs, [])
        else
          let (modifiedAmt, _) :=
            modifyDamage cs reg (some originalTarget) dealer amount props cardSource hookType modSubscribers
          -- Block belongs to petOwner if target is a pet (CreatureCmd.cs line 143)
          let blockHolderId :=
            (originalTarget.petOwnerId.bind cs.findPlayer).map (·.creatureId)
              |>.getD originalTargetId
          let (cs1, dmgAfterPre, preResults) :=
            damagePreBlockStage cs reg originalTarget originalTargetId amount modifiedAmt props dealer cardSource modSubscribers
          let (cs2, blockedDec, blkBroken, fullyBlocked) :=
            damageBlockStage cs1 blockHolderId dmgAfterPre props
          let dmgRemaining := Dec.maxZero (Dec.sub dmgAfterPre blockedDec)
          let (unblockedAmt0, _) :=
            modifyHpLost cs2 reg originalTarget dmgRemaining props dealer cardSource HpLossHookPhase.beforeOstyOnly modSubscribers
          let ubTargetId :=
            modifyUnblockedDamageTarget cs2 reg originalTargetId unblockedAmt0 props dealer modSubscribers
          let (cs3, ubRes, overkill) :=
            damageUnblockedStage cs2 reg ubTargetId originalTargetId unblockedAmt0 dmgRemaining blockedDec blkBroken fullyBlocked props dealer cardSource modSubscribers
          let (cs4, extraResults) :=
            damageOverkillStage cs3 reg ubTargetId originalTargetId overkill blockedDec blkBroken fullyBlocked props dealer cardSource modSubscribers
          let allRes := preResults ++ [ubRes] ++ extraResults
          let cs5 := allRes.foldl (fun (acc : CombatState) r => acc.recordHistory (.damageDealt acc.roundNumber dealerId r)) cs4
          (cs5, allRes)

/-- Full single-target `CreatureCmd.Damage` entry point: dispatches reactive `BeforeDamageReceived`
    hooks (e.g., `ThornsPower`) once before executing `damageSingleTargetCore`. -/
def damageSingleTarget (cs : CombatState) (reg : BehaviorRegistry)
    (originalTargetId : CreatureId) (amount : Dec) (props : ValueProp)
    (dealerId : Option CreatureId) (cardSource : Option CardInstance)
    (hookType : ModifyDamageHookType := ModifyDamageHookType.all)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × List DamageResult :=
  let csAfterReactive :=
    let dealerOpt := dealerId.bind cs.findCreature
    let dealerAlive := match dealerOpt with | some d => !d.isDead | none => true
    if !dealerAlive then cs
    else
      match cs.findCreature originalTargetId with
      | none => cs
      | some target =>
          if target.isDead then cs
          else
            let effects := collectBeforeDamageReceivedEffects cs reg target amount props dealerOpt modSubscribers
            effects.foldl (fun acc eff =>
              match eff with
              | .dealDamage rDealer rTarget rAmt rProps =>
                  (damageSingleTargetCore acc (reg) rTarget rAmt rProps rDealer none ModifyDamageHookType.all modSubscribers).1
              | _ => acc) cs
  damageSingleTargetCore csAfterReactive reg originalTargetId amount props dealerId cardSource hookType modSubscribers

/-- Damage multiple targets sequentially. Ref: `CreatureCmd.Damage`. -/
def damage (cs : CombatState) (reg : BehaviorRegistry)
    (targetIds : List CreatureId) (amount : Dec) (props : ValueProp)
    (dealerId : Option CreatureId := none) (cardSource : Option CardInstance := none)
    (hookType : ModifyDamageHookType := ModifyDamageHookType.all)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × List DamageResult :=
  targetIds.foldl (fun (accState, accRes) tid =>
    let (s', rs) := damageSingleTarget accState reg tid amount props dealerId cardSource hookType modSubscribers
    (s', accRes ++ rs)) (cs, [])

/-- Ref: `CreatureCmd.GainBlock`. -/
def gainBlock (cs : CombatState) (reg : BehaviorRegistry)
    (targetId : CreatureId) (amount : Dec) (props : ValueProp)
    (cardSource : Option CardInstance := none)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × Dec :=
  if cs.isEnding then (cs, Dec.zero)
  else
    match cs.findCreature targetId with
    | none => (cs, Dec.zero)
    | some c =>
        if c.isDead then (cs, Dec.zero)
        else
          let (modified, _) := modifyBlock cs reg c amount props cardSource modSubscribers
          let c' := c.gainBlockInternal modified
          (cs.updateCreature targetId (fun _ => c'), modified)

/-- Ref: `CreatureCmd.LoseBlock`. -/
def loseBlock (cs : CombatState) (targetId : CreatureId) (amount : Dec) : CombatState :=
  cs.updateCreature targetId (fun c => c.loseBlockInternal amount)

/-- Ref: `CreatureCmd.Heal`. -/
def heal (cs : CombatState) (targetId : CreatureId) (amount : Dec) : CombatState :=
  cs.updateCreature targetId (fun c => c.healInternal amount)

/-- Ref: `CreatureCmd.SetMaxHp`. -/
def setMaxHp (cs : CombatState) (targetId : CreatureId) (amount : Dec) : CombatState :=
  cs.updateCreature targetId (fun c => c.setMaxHpInternal amount)

/-- Ref: `CreatureCmd.Kill`. Respects `Hook.ShouldDie` unless `force = true`. -/
def kill (cs : CombatState) (reg : BehaviorRegistry) (targetId : CreatureId)
    (force : Bool := false) (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × Bool :=
  match cs.findCreature targetId with
  | none => (cs, false)
  | some c =>
      let allowDie := force || (shouldDie cs reg c modSubscribers).1
      if !allowDie then (cs, false)
      else
        let c' := { c with currentHp := 0 }
        let remIds := c'.powers.filter (fun p =>
          (reg p.modelId).shouldPowerBeRemovedOnDeath ⟨.power c'.id p.instanceId p.modelId, some c'.id, none, p.amount⟩ p)
        let keptPowers := c'.powers.filter (fun p => !remIds.any (·.instanceId == p.instanceId))
        (cs.updateCreature targetId (fun _ => { c' with powers := keptPowers }), true)

end Sts2Model.Command

/-
  Headless Effect IR interpreter, potion execution, enemy AI turn loop,
  and step-level causal DamageAttribution capture (zero UI / animation dependencies).
-/
import Sts2Model.Multiplayer.ActionQueueSet
import Sts2Model.Replay.History
import Sts2Model.Command.AttackCommand
import Sts2Model.Command.PowerCmd
import Sts2Model.Command.OrbCmd
import Sts2Model.Mechanics.Regent
import Sts2Model.Mechanics.Necrobinder
import Sts2Model.Mechanics.Fool
import Sts2Model.Combat.MonsterAI
import Sts2Model.Combat.TurnLoop

namespace Sts2Model.Sim

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command
open Sts2Model.Combat
open Sts2Model.Mechanics
open Sts2Model.Multiplayer
open Sts2Model.Replay

/-- Abstract target selector evaluated at effect execution time. -/
inductive EffectTarget where
  | self
  | chosenTarget
  | allEnemies
  | randomEnemy
  | allAllies
  | firstLivingPlayer
  | player (pid : PlayerId)
  | creature (cid : CreatureId)
  deriving Repr, DecidableEq, Inhabited

/-- Explicit state-delta fallback for unmodeled/long-tail cards, relics, or events
    during counterfactual partial replay. -/
structure OpaqueStateDelta where
  label        : String := "opaque"
  hpDeltas     : List (CreatureId × Int) := []
  blockDeltas  : List (CreatureId × Int) := []
  powerDeltas  : List (CreatureId × ModelId × Int) := []
  energyDeltas : List (PlayerId × Int) := []
  starsDeltas  : List (PlayerId × Int) := []
  deriving Repr, DecidableEq, Inhabited

/-- Only operands whose source and affine calculation are statically known. -/
inductive EffectValue where
  | actorBlock (base multiplier : Dec)
  | chosenBlock (base multiplier : Dec)
  | discardCount (base multiplier : Dec)
  deriving Repr, DecidableEq

private def EffectValue.eval (cs : CombatState) (actor : CreatureId) (pid : Option PlayerId)
    (chosen : Option CreatureId) : EffectValue → Dec
  | .actorBlock b m =>
      Dec.add b (Dec.mul m (Dec.ofNat (((cs.findCreature actor).map (·.block)).getD 0)))
  | .chosenBlock b m =>
      Dec.add b (Dec.mul m (Dec.ofNat (((chosen.bind cs.findCreature).map (·.block)).getD 0)))
  | .discardCount b m =>
      let n := ((pid.bind cs.findPlayer).bind (·.combatState)).map (·.piles.discard.length) |>.getD 0
      Dec.add b (Dec.mul m (Dec.ofNat n))

/-- Pure algebraic DSL for card, potion, and monster move effects. -/
inductive EffectOp where
  | dealDamage (target : EffectTarget) (amount : Dec) (hits : Nat := 1) (props : ValueProp := DamageProps.card)
  | gainBlock (target : EffectTarget) (amount : Dec) (props : ValueProp := BlockProps.card)
  | applyPower (target : EffectTarget) (power : PowerInstance) (amount : Dec)
  | removePower (target : EffectTarget) (powerId : ModelId)
  | draw (count : Nat)
  | discardChosen (choiceId : Nat) (count : Nat)
  | discardFromHand (count : Nat)
  | discardAllHand
  | exhaustSelf
  | exhaustChosen (choiceId : Nat) (count : Nat)
  | gainEnergy (amount : Nat)
  | gainStars (amount : Nat)
  | heal (target : EffectTarget) (amount : Dec)
  | channelOrb (kind : OrbKind)
  | evokeOrb (times : Nat := 1)
  | forge (amount : Dec)
  | addCardToPile (card : CardInstance) (pile : PileType) (pos : CardPilePosition := .bottom)
  | addGeneratedCard (cardEntry : String) (cardType : CardType) (cost : Int) (pile : PileType) (count : Nat := 1) (pos : CardPilePosition := .bottom)
  | summonOsty (amount : Dec)
  | shootArrow (target : EffectTarget)
  | dealDamageAsc (target : EffectTarget) (amt : AscensionVal) (hits : Nat := 1) (props : ValueProp := DamageProps.monsterMove)
  | gainBlockAsc (target : EffectTarget) (amt : AscensionVal) (props : ValueProp := BlockProps.monsterMove)
  | applyPowerAsc (target : EffectTarget) (power : PowerInstance) (amt : AscensionVal)
  | addOrbSlots (count : Nat)
  | removeOrbSlots (count : Nat)
  | addPlayedCardCombatCost (amount : Int)
  | dealDamageValue (target : EffectTarget) (amount : EffectValue) (hits : Nat) (props : ValueProp)
  | gainBlockValue (target : EffectTarget) (amount : EffectValue) (props : ValueProp)
  | gainCurrentEnergy
  | applyPowerIfPresent (target : EffectTarget) (power : PowerInstance) (amount : Dec)
  | dealDamageIfPower (target : EffectTarget) (power : ModelId) (amount : Dec)
      (hitsIfPresent hitsOtherwise : Nat) (props : ValueProp)
  | drawIfNoAttacks (count : Nat)
  | applyOpaque (delta : OpaqueStateDelta)
  deriving Repr, DecidableEq

abbrev EffectProgram := List EffectOp

/-- Monster move state machine paired with concrete EffectPrograms per move ID. -/
structure MonsterBlueprint where
  modelId      : ModelId
  stateMachine : MonsterStateMachine
  moveEffects  : StateId → EffectProgram

/-- Closed headless simulation environment (no UI / Godot runtime required). -/
structure EffectEnv where
  behaviorReg      : CombatState → BehaviorRegistry := builtinBehaviorRegistry
  cardEffect       : CardInstance → EffectProgram := fun _ => []
  potionEffect     : ModelId → EffectProgram := fun _ => []
  monsterBlueprint : ModelId → Option MonsterBlueprint := fun _ => none
  knownCardEffect   : CardInstance → Option EffectProgram := fun _ => none
  knownPotionEffect : ModelId → Option EffectProgram := fun _ => none

def applyIntDeltaClamped (cur : Nat) (delta : Int) (maxBound : Nat) : Nat :=
  let raw : Int := (cur : Int) + delta
  min maxBound (Int.toNat (max 0 raw))

/-- Apply an `OpaqueStateDelta` fallback step directly to `CombatState`. -/
def applyOpaqueDelta (cs : CombatState) (d : OpaqueStateDelta) : CombatState :=
  let csHp := d.hpDeltas.foldl (fun acc (cid, delta) =>
    acc.updateCreature cid fun c =>
      { c with currentHp := applyIntDeltaClamped c.currentHp delta c.maxHp }) cs
  let csBlk := d.blockDeltas.foldl (fun acc (cid, delta) =>
    acc.updateCreature cid fun c =>
      { c with block := applyIntDeltaClamped c.block delta Creature.statCap }) csHp
  let csPow := d.powerDeltas.foldl (fun acc (cid, mid, delta) =>
    match acc.findCreature cid with
    | none => acc
    | some c =>
        match c.powers.find? (·.modelId == mid) with
        | some ex =>
            let newAmt := PowerInstance.clampAmount (ex.amount + delta)
            let upd : PowerInstance := { ex with amount := newAmt }
            acc.updateCreature cid fun cr =>
              if upd.shouldRemoveDueToAmount then
                { cr with powers := cr.powers.filter (·.instanceId != ex.instanceId) }
              else
                { cr with powers := cr.powers.map fun p => if p.instanceId == ex.instanceId then upd else p }
        | none =>
            if delta == 0 then acc
            else
              let (newId, acc1) := acc.allocInstanceId
              let pType : PowerType := if delta < 0 then .debuff else .buff
              let newPow : PowerInstance :=
                { instanceId := newId
                , modelId := mid
                , ownerId := cid
                , powerType := pType
                , stackType := .counter
                , allowNegative := delta < 0
                , amount := PowerInstance.clampAmount delta }
              if newPow.shouldRemoveDueToAmount then acc1
              else acc1.updateCreature cid fun cr => { cr with powers := cr.powers ++ [newPow] }) csBlk
  let csEnergy := d.energyDeltas.foldl (fun acc (pid, delta) =>
    acc.updatePlayer pid fun p =>
      match p.combatState with
      | none => p
      | some pcs =>
          { p with combatState := some { pcs with energy := applyIntDeltaClamped pcs.energy delta Creature.statCap } }) csPow
  d.starsDeltas.foldl (fun acc (pid, delta) =>
    acc.updatePlayer pid fun p =>
      match p.combatState with
      | none => p
      | some pcs =>
          { p with combatState := some { pcs with stars := applyIntDeltaClamped pcs.stars delta Creature.statCap } }) csEnergy

def resolveEffectTargets (cs : CombatState) (actorCid : CreatureId)
    (chosenTarget : Option CreatureId) (t : EffectTarget) : List CreatureId × CombatState :=
  match t with
  | .self => ([actorCid], cs)
  | .chosenTarget =>
      match chosenTarget with
      | some tid => ([tid], cs)
      | none => ([], cs)
  | .allEnemies => (cs.hittableEnemies.map (·.id), cs)
  | .randomEnemy =>
      let enemies := cs.hittableEnemies
      match enemies with
      | [] => ([], cs)
      | [x] => ([x.id], cs)
      | xs =>
          let (idx, rng') := cs.rng.nextInt xs.length
          let picked := (xs[idx]?.map (fun c => [c.id])).getD []
          (picked, { cs with rng := rng' })
  | .allAllies => ((cs.allies.filter (·.isAlive)).map (·.id), cs)
  | .firstLivingPlayer =>
      match cs.allies.find? (fun c => c.isAlive && c.isPlayer) with
      | some c => ([c.id], cs)
      | none =>
          match cs.allies.find? (·.isAlive) with
          | some c => ([c.id], cs)
          | none => ([], cs)
  | .player pid =>
      match cs.findPlayer pid with
      | some p => ([p.creatureId], cs)
      | none => ([], cs)
  | .creature cid => ([cid], cs)

def dealerHasPaperPhrog (cs : CombatState) (dealer : Creature) : Bool :=
  match dealer.playerId.bind cs.findPlayer with
  | some p => p.relics.any fun r => !r.isMelted && r.modelId == ModelId.mkRelic "PAPER_PHROG"
  | none   => false

/-- Execute a single damage hit against `tid`, capturing full `DamageAttribution` and history entries. -/
def execSingleHitWithAttribution (env : EffectEnv) (cs : CombatState) (stepIdx : Nat)
    (dealerCid : Option CreatureId) (tid : CreatureId) (amount : Dec) (props : ValueProp)
    (cardSource : Option CardInstance) :
    CombatState × List DamageResult × List CombatHistoryEntryEx × List DamageAttribution :=
  let reg := env.behaviorReg cs
  let dealerOpt := dealerCid.bind cs.findCreature
  let targetOpt := cs.findCreature tid
  match targetOpt with
  | none => (cs, [], [], [])
  | some tBefore =>
      if tBefore.isDead then (cs, [], [], [])
      else
        let dStr := (dealerOpt.map (·.getPowerAmount (ModelId.mkPower "STRENGTH_POWER"))).getD 0
        let dWeak := (dealerOpt.map (·.hasPower (ModelId.mkPower "WEAK_POWER"))).getD false
        let tVuln := tBefore.hasPower (ModelId.mkPower "VULNERABLE_POWER")
        let phrog := (dealerOpt.map (dealerHasPaperPhrog cs)).getD false
        let (modDmg, _) := modifyDamage cs reg (some tBefore) dealerOpt amount props cardSource .all []
        let (csAfter, results) :=
          damageSingleTarget cs reg tid amount props dealerCid cardSource .all []
        let tAfterHp := (csAfter.findCreature tid).map (·.currentHp) |>.getD tBefore.currentHp
        let blkSum := results.foldl (fun acc r => acc + r.blockedDamage) 0
        let unblkSum := results.foldl (fun acc r => acc + r.unblockedDamage) 0
        let overSum := results.foldl (fun acc r => acc + r.overkillDamage) 0
        let attr : DamageAttribution :=
          { round := cs.roundNumber
          , stepIdx := stepIdx
          , dealerId := dealerCid
          , targetId := tid
          , cardModelId := cardSource.map (·.modelId)
          , baseDamage := amount
          , props := props
          , dealerStrength := dStr
          , dealerWeak := dWeak
          , targetVulnerable := tVuln
          , paperPhrog := phrog
          , modifiedDamage := modDmg
          , blockedDamage := blkSum
          , unblockedDamage := unblkSum
          , overkillDamage := overSum
          , targetHpBefore := tBefore.currentHp
          , targetHpAfter := tAfterHp }
        let hist := results.map fun r =>
          .damageReceived cs.roundNumber cs.currentSide r.receiverId dealerCid (cardSource.map (·.modelId)) r
        (csAfter, results, hist, [attr])

private def execDealDamageOp (env : EffectEnv) (cs : CombatState) (actorCid : CreatureId)
    (chosenTarget : Option CreatureId) (cardSource : Option CardInstance) (stepIdx : Nat)
    (choiceStream : ChoiceStream) (tgt : EffectTarget) (amt : Dec) (hits : Nat) (props : ValueProp) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
  let rec hitLoop (rem : Nat) (curCs : CombatState)
      (accRes : List DamageResult) (accHist : List CombatHistoryEntryEx)
      (accAttrs : List DamageAttribution) :
      CombatState × List DamageResult × List CombatHistoryEntryEx × List DamageAttribution :=
    match rem with
    | 0 => (curCs, accRes, accHist, accAttrs)
    | k + 1 =>
        let (cs1, res1, h1, a1) := tids.foldl
          (fun (s, rAcc, hAcc, aAcc) tid =>
            let (s', rs, hs, as_) :=
              execSingleHitWithAttribution env s stepIdx (some actorCid) tid amt props cardSource
            (s', rAcc ++ rs, hAcc ++ hs, aAcc ++ as_))
          (curCs, [], [], [])
        hitLoop k cs1 (accRes ++ res1) (accHist ++ h1) (accAttrs ++ a1)
  let (csFinal, allRes, allHist, allAttrs) := hitLoop hits cs0 [] [] []
  let atkHist := if allRes.isEmpty then [] else [.creatureAttacked cs0.roundNumber cs0.currentSide actorCid allRes]
  (csFinal, atkHist ++ allHist, allAttrs, choiceStream)

private def execGainBlockOp (env : EffectEnv) (cs : CombatState) (actorCid : CreatureId)
    (chosenTarget : Option CreatureId) (cardSource : Option CardInstance)
    (choiceStream : ChoiceStream) (tgt : EffectTarget) (amt : Dec) (props : ValueProp) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
  let (csFinal, hist) := tids.foldl (fun (s, hAcc) tid =>
    let (s', modBlk) := Sts2Model.Command.gainBlock s (env.behaviorReg s) tid amt props cardSource []
    let h := CombatHistoryEntryEx.blockGained s.roundNumber s.currentSide tid modBlk.truncate props
      (cardSource.map (·.instanceId))
    (s', hAcc ++ [h])) (cs0, [])
  (csFinal, hist, [], choiceStream)

private def execApplyPowerOp (env : EffectEnv) (cs : CombatState) (actorCid : CreatureId)
    (chosenTarget : Option CreatureId) (choiceStream : ChoiceStream)
    (tgt : EffectTarget) (template : PowerInstance) (amt : Dec) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
  let (csFinal, hist) := tids.foldl (fun (s, hAcc) tid =>
    let (s', appliedOpt) := Sts2Model.Command.applyPower s (env.behaviorReg s) template tid amt (some actorCid) []
    match appliedOpt with
    | some _ =>
        let h := CombatHistoryEntryEx.powerReceived s.roundNumber s.currentSide template.modelId
          tid (some actorCid) amt.truncate
        (s', hAcc ++ [h])
    | none => (s', hAcc)) (cs0, [])
  (csFinal, hist, [], choiceStream)

private def handIds (cs : CombatState) (pid : PlayerId) : List CardInstanceId :=
  ((cs.findPlayer pid).bind (·.combatState)).map (fun p => p.piles.hand.map (·.instanceId)) |>.getD []

private def discardSelected (cs : CombatState) (pid : PlayerId) (ids : List CardInstanceId) :
    CombatState × List CombatHistoryEntryEx :=
  let next := ids.foldl (fun s cid => Sts2Model.Command.discardCard s pid cid) cs
  (next, ids.map (CombatHistoryEntryEx.cardDiscarded cs.roundNumber cs.currentSide pid))

private def execDrawOp (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId) (count : Nat)
    (stream : ChoiceStream) : CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let (next, drawn) := Sts2Model.Command.drawCards cs reg pid count
  (next, drawn.map (fun c => .cardDrawn next.roundNumber next.currentSide pid c.instanceId false), [], stream)

def execOp (env : EffectEnv) (cs : CombatState) (actorPid : Option PlayerId) (actorCid : CreatureId)
    (chosenTarget : Option CreatureId) (cardSource : Option CardInstance) (stepIdx : Nat)
    (choiceStream : ChoiceStream) (op : EffectOp) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let reg := env.behaviorReg cs
  match op with
  | .dealDamage tgt amt hits props =>
      execDealDamageOp env cs actorCid chosenTarget cardSource stepIdx choiceStream tgt amt hits props
  | .gainBlock tgt amt props =>
      execGainBlockOp env cs actorCid chosenTarget cardSource choiceStream tgt amt props
  | .applyPower tgt template amt =>
      execApplyPowerOp env cs actorCid chosenTarget choiceStream tgt template amt
  | .removePower tgt pid =>
      let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
      let csFinal := tids.foldl (fun s tid => Sts2Model.Command.removePowerByModel s tid pid) cs0
      (csFinal, [], [], choiceStream)
  | .draw count =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid => execDrawOp cs reg pid count choiceStream
  | .discardChosen choiceId count =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let (chosenOpt, stream') := PlayerChoiceSynchronizer.consumeFromStream pid choiceId choiceStream
          let candidateIds : List CardInstanceId :=
            match chosenOpt with
            | some (.cards ids) => ids.take count
            | _ =>
                let hand := ((cs.findPlayer pid).bind (·.combatState)).map (·.piles.hand) |>.getD []
                let selfId := cardSource.map (·.instanceId)
                ((hand.filter fun c => some c.instanceId != selfId).take count).map (·.instanceId)
          let (csFinal, hist) := candidateIds.foldl (fun (s, hAcc) cid =>
            let s' := Sts2Model.Command.discardCard s pid cid
            let h := CombatHistoryEntryEx.cardDiscarded s'.roundNumber s'.currentSide pid cid
            (s', hAcc ++ [h])) (cs, [])
          (csFinal, hist, [], stream')
  | .discardFromHand count =>
      match actorPid with
      | some pid =>
          let ids := handIds cs pid
          if ids.length ≤ count then
            let (next, hist) := discardSelected cs pid ids
            (next, hist, [], choiceStream)
          else (cs, [], [], choiceStream)
      | none => (cs, [], [], choiceStream)
  | .discardAllHand =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let selfId := cardSource.map (·.instanceId)
          let hand := ((cs.findPlayer pid).bind (·.combatState)).map (·.piles.hand) |>.getD []
          let toDiscard := (hand.filter fun c => some c.instanceId != selfId).map (·.instanceId)
          let (csFinal, hist) := toDiscard.foldl (fun (s, hAcc) cid =>
            let s' := Sts2Model.Command.discardCard s pid cid
            let h := CombatHistoryEntryEx.cardDiscarded s'.roundNumber s'.currentSide pid cid
            (s', hAcc ++ [h])) (cs, [])
          (csFinal, hist, [], choiceStream)
  | .exhaustSelf =>
      match actorPid, cardSource with
      | some pid, some c =>
          let cs' := Sts2Model.Command.exhaustCard cs pid c.instanceId
          let h := CombatHistoryEntryEx.cardExhausted cs'.roundNumber cs'.currentSide pid c.instanceId
          (cs', [h], [], choiceStream)
      | _, _ => (cs, [], [], choiceStream)
  | .exhaustChosen choiceId count =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let (chosenOpt, stream') := PlayerChoiceSynchronizer.consumeFromStream pid choiceId choiceStream
          let candidateIds : List CardInstanceId :=
            match chosenOpt with
            | some (.cards ids) => ids.take count
            | _ =>
                let hand := ((cs.findPlayer pid).bind (·.combatState)).map (·.piles.hand) |>.getD []
                let selfId := cardSource.map (·.instanceId)
                ((hand.filter fun c => some c.instanceId != selfId).take count).map (·.instanceId)
          let (csFinal, hist) := candidateIds.foldl (fun (s, hAcc) cid =>
            let s' := Sts2Model.Command.exhaustCard s pid cid
            let h := CombatHistoryEntryEx.cardExhausted s'.roundNumber s'.currentSide pid cid
            (s', hAcc ++ [h])) (cs, [])
          (csFinal, hist, [], stream')
  | .gainEnergy amt =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let cs' := cs.updatePlayer pid fun p =>
            match p.combatState with
            | none => p
            | some pcs => { p with combatState := some (pcs.gainEnergy amt) }
          (cs', [], [], choiceStream)
  | .gainStars amt =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          (gainStars cs pid amt, [CombatHistoryEntryEx.starsModified cs.roundNumber cs.currentSide pid (amt : Int)], [], choiceStream)
  | .heal tgt amt =>
      let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
      let csFinal := tids.foldl (fun s tid => Sts2Model.Command.heal s tid amt) cs0
      (csFinal, [], [], choiceStream)
  | .channelOrb kind =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let cs' := Sts2Model.Command.channelOrb cs reg pid kind []
          (cs', [CombatHistoryEntryEx.orbChanneled cs'.roundNumber cs'.currentSide pid kind], [], choiceStream)
  | .evokeOrb times =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let rec evLoop (k : Nat) (s : CombatState) : CombatState :=
            match k with
            | 0 => s
            | n + 1 => evLoop n (Sts2Model.Command.evokeNextOrb s (env.behaviorReg s) pid true [])
          (evLoop times cs, [], [], choiceStream)
  | .forge amt =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid => (forgeSovereignBlade cs pid amt, [], [], choiceStream)
  | .addCardToPile card pile pos =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let cs' := cs.updatePlayer pid fun p =>
            match p.combatState with
            | none => p
            | some pcs =>
                let dst := insertIntoPileList pos card (pcs.piles.getPile pile)
                { p with combatState := some { pcs with piles := pcs.piles.setPile pile dst } }
          let h := CombatHistoryEntryEx.cardGenerated cs'.roundNumber cs'.currentSide pid card.instanceId actorPid
          (cs', [h], [], choiceStream)
  | .addGeneratedCard entry ct cost pile count pos =>
      let targetPids : List PlayerId :=
        match actorPid with
        | some pid => [pid]
        | none     => cs.players.map (·.playerId)
      let rec genLoop (rem : Nat) (cur : CombatState) (hAcc : List CombatHistoryEntryEx) :
          CombatState × List CombatHistoryEntryEx :=
        match rem with
        | 0 => (cur, hAcc)
        | k + 1 =>
            let (cur1, hs1) := targetPids.foldl (fun (s, hs) pid =>
              let (newId, s1) := s.allocInstanceId
              let tt : TargetType := match ct with
                | .attack => .anyEnemy
                | .status | .curse => .none
                | _ => .self
              let rar : CardRarity := match ct with
                | .status => .status
                | .curse  => .curse
                | _       => .token
              let newCard : CardInstance :=
                { instanceId := newId
                , modelId := ModelId.mkCard entry
                , ownerId := pid
                , cardType := ct
                , rarity := rar
                , targetType := tt
                , energyCost := CardEnergyCost.mkCanonical cost }
              let s2 := s1.updatePlayer pid fun p =>
                match p.combatState with
                | none => p
                | some pcs =>
                    let dst := insertIntoPileList pos newCard (pcs.piles.getPile pile)
                    { p with combatState := some { pcs with piles := pcs.piles.setPile pile dst } }
              let h := CombatHistoryEntryEx.cardGenerated s2.roundNumber s2.currentSide pid newId actorPid
              (s2, hs ++ [h])) (cur, [])
            genLoop k cur1 (hAcc ++ hs1)
      let (csFinal, allHist) := genLoop count cs []
      (csFinal, allHist, [], choiceStream)
  | .summonOsty amt =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let (cs', res) := Sts2Model.Mechanics.summonOsty cs reg pid amt []
          let h := CombatHistoryEntryEx.summoned cs'.roundNumber cs'.currentSide pid res.amount.truncate
          (cs', [h], [], choiceStream)
  | .shootArrow tgt =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
          match tids.head? with
          | none => (cs0, [], [], choiceStream)
          | some tid =>
              let (cs', slotOpt) := Sts2Model.Mechanics.shootArrowAtTarget cs0 (env.behaviorReg cs0) pid tid []
              match slotOpt with
              | none => (cs', [], [], choiceStream)
              | some slotIdx =>
                  let h := CombatHistoryEntryEx.arrowShot cs'.roundNumber cs'.currentSide pid slotIdx
                  (cs', [h], [], choiceStream)
  | .dealDamageAsc tgt av hits props =>
      execDealDamageOp env cs actorCid chosenTarget cardSource stepIdx choiceStream tgt (Dec.ofInt (av.eval cs.ascensionLevel)) hits props
  | .gainBlockAsc tgt av props =>
      execGainBlockOp env cs actorCid chosenTarget cardSource choiceStream tgt (Dec.ofInt (av.eval cs.ascensionLevel)) props
  | .applyPowerAsc tgt template av =>
      execApplyPowerOp env cs actorCid chosenTarget choiceStream tgt template (Dec.ofInt (av.eval cs.ascensionLevel))
  | .addOrbSlots count =>
      (actorPid.elim cs (fun pid => Sts2Model.Command.addOrbSlots cs pid count), [], [], choiceStream)
  | .removeOrbSlots count =>
      (actorPid.elim cs (fun pid => Sts2Model.Command.removeOrbSlots cs pid count), [], [], choiceStream)
  | .addPlayedCardCombatCost amount =>
      let next := match actorPid, cardSource with
        | some pid, some source => cs.updatePlayer pid fun p =>
            { p with combatState := p.combatState.map fun pcs =>
                let play := pcs.piles.play.map fun c =>
                  if c.instanceId == source.instanceId then { c with energyCost := c.energyCost.addThisCombat amount }
                  else c
                { pcs with piles.play := play } }
        | _, _ => cs
      (next, [], [], choiceStream)
  | .dealDamageValue tgt value hits props =>
      let amt := value.eval cs actorCid actorPid chosenTarget
      execDealDamageOp env cs actorCid chosenTarget cardSource stepIdx choiceStream tgt amt hits props
  | .gainBlockValue tgt value props =>
      let amt := value.eval cs actorCid actorPid chosenTarget
      execGainBlockOp env cs actorCid chosenTarget cardSource choiceStream tgt amt props
  | .gainCurrentEnergy =>
      let next := actorPid.elim cs fun pid => cs.updatePlayer pid fun p =>
        { p with combatState := p.combatState.map fun pcs => pcs.gainEnergy pcs.energy }
      (next, [], [], choiceStream)
  | .applyPowerIfPresent tgt power amt =>
      let (tids, state) := resolveEffectTargets cs actorCid chosenTarget tgt
      tids.foldl (fun (s, hist, attrs, stream) tid =>
        if (s.findCreature tid).any (·.hasPower power.modelId) then
          let (next, added, _, _) := execApplyPowerOp env s actorCid chosenTarget stream (.creature tid) power amt
          (next, hist ++ added, attrs, stream)
        else (s, hist, attrs, stream)) (state, [], [], choiceStream)
  | .dealDamageIfPower tgt power amt present otherwise props =>
      let (tids, state) := resolveEffectTargets cs actorCid chosenTarget tgt
      let counts := tids.map fun tid => (tid, if (state.findCreature tid).any (·.hasPower power) then present else otherwise)
      counts.foldl (fun (s, hist, attrs, stream) (tid, hits) =>
        let (next, added, damage, _) := execDealDamageOp env s actorCid chosenTarget cardSource
          stepIdx stream (.creature tid) amt hits props
        (next, hist ++ added, attrs ++ damage, stream)) (state, [], [], choiceStream)
  | .drawIfNoAttacks count =>
      match actorPid with
      | some pid =>
          if ((cs.findPlayer pid).bind (·.combatState)).any (fun pcs => !pcs.piles.hand.any (·.cardType == .attack)) then
            execDrawOp cs reg pid count choiceStream
          else (cs, [], [], choiceStream)
      | none => (cs, [], [], choiceStream)
  | .applyOpaque delta =>
      (applyOpaqueDelta cs delta, [], [], choiceStream)

/-- Execute a full `EffectProgram` deterministically against `CombatState`. -/
def execEffectProgram (env : EffectEnv) (cs : CombatState) (actorPid : Option PlayerId)
    (actorCid : CreatureId) (chosenTarget : Option CreatureId) (cardSource : Option CardInstance)
    (stepIdx : Nat) (choiceStream : ChoiceStream) (prog : EffectProgram) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  prog.foldl (fun (s, hAcc, aAcc, strm) op =>
    let (s', hs, as_, strm') := execOp env s actorPid actorCid chosenTarget cardSource stepIdx strm op
    (s', hAcc ++ hs, aAcc ++ as_, strm')) (cs, [], [], choiceStream)

/-- Suspended `CardSelectCmd.FromHand`; the resource payment and preceding operations already ran. -/
structure PendingCardChoice where
  play : CardPlay
  source : CardInstance
  actor : CreatureId
  choiceId : Nat
  candidates : List CardInstanceId
  count : Nat
  remaining : EffectProgram
  deriving Repr, DecidableEq

def PendingCardChoice.automatic (p : PendingCardChoice) : Bool :=
  p.candidates.length ≤ p.count

def PendingCardChoice.accepts (p : PendingCardChoice) (cs : CombatState)
    (pid : PlayerId) (id : Nat) (choice : ChoiceResult) : Bool :=
  !p.automatic && pid == p.play.playerId && id == p.choiceId &&
  match choice with
  | .cards ids =>
      let current := handIds cs pid
      ids.length == p.count && ids.eraseDups.length == ids.length &&
        ids.all (fun cid => p.candidates.contains cid && current.contains cid)
  | _ => false

structure HeadlessCardResult where
  combat : CombatState
  accepted : Bool := false
  history : List CombatHistoryEntryEx := []
  attributions : List DamageAttribution := []
  stream : ChoiceStream := []
  outcome : CombatOutcome := .ongoing
  sync : PlayerChoiceSynchronizer := {}
  pending : Option PendingCardChoice := none

private def finishCardPlay (env : EffectEnv) (play : CardPlay) (source : CardInstance)
    (r : HeadlessCardResult) : HeadlessCardResult :=
  let moved := r.combat.updatePlayer play.playerId fun p =>
    match p.combatState with
    | none => p
    | some pcs =>
        let (piles, _) := moveCard pcs.piles play.cardId play.resultPile .bottom CardInstance.afterCardPlayedCleanup
        { p with combatState := some { pcs with piles := piles } }
  let post := CombatHistoryEntryEx.cardPlayFinished moved.roundNumber moved.currentSide play (source.hasKeyword .ethereal) ::
    (if play.resultPile == .exhaust then
      [CombatHistoryEntryEx.cardExhausted moved.roundNumber moved.currentSide play.playerId play.cardId] else [])
  let (checked, outcome) := checkWinCondition (checkAllPlayersDead moved) (env.behaviorReg moved)
  { r with combat := checked, outcome := outcome, history := r.history ++ post, pending := none }

private def runCardProgram (env : EffectEnv) (play : CardPlay) (source : CardInstance)
    (actor : CreatureId) (stepIdx : Nat) (deferAutomatic : Bool) :
    EffectProgram → HeadlessCardResult → HeadlessCardResult
  | [], r => finishCardPlay env play source r
  | .discardFromHand count :: tail, r =>
      let cs := r.combat
      let pid := play.playerId
      if !cs.isInProgress || isCombatEnding cs (env.behaviorReg cs) ||
          !(cs.findCreature actor).any Creature.isAlive then
        runCardProgram env play source actor stepIdx deferAutomatic tail r
      else
        let cs := (tryUndoReadyToEndTurn cs pid).1
        let (sync, id) := r.sync.reserveChoiceId pid
        let ids := handIds cs pid
        if !deferAutomatic && ids.length ≤ count then
          let (next, hist) := discardSelected cs pid ids
          runCardProgram env play source actor stepIdx deferAutomatic tail
            { r with combat := next, sync := sync, history := r.history ++ hist }
        else
          { r with combat := cs, sync := sync, pending := some ⟨play, source, actor, id, ids, count, tail⟩ }
  | op :: tail, r =>
      let (next, hist, attrs, stream) := execOp env r.combat (some play.playerId) actor
        play.targetId (some source) stepIdx r.stream op
      runCardProgram env play source actor stepIdx deferAutomatic tail
        { r with combat := next, history := r.history ++ hist, attributions := r.attributions ++ attrs, stream := stream }

/-- Validate only the result for the reserved player/ID. Automatic selection never consumes a result. -/
def PendingCardChoice.selection (p : PendingCardChoice) (cs : CombatState) (stream : ChoiceStream) :
    Except String (List CardInstanceId × ChoiceStream) := do
  let pid := p.play.playerId
  if p.automatic then
    unless p.candidates.all ((handIds cs pid).contains ·) do throw "automatic discard candidate left hand"
    pure (p.candidates, stream)
  else
    let (result, rest) := PlayerChoiceSynchronizer.consumeFromStream pid p.choiceId stream
    let some (.cards ids) := result | throw s!"missing or invalid card choice for player {pid}, choice {p.choiceId}"
    if !p.accepts cs pid p.choiceId (.cards ids) ||
        rest.any (fun (p', i, _) => p' == pid && i == p.choiceId) then
      throw s!"invalid card choice for player {pid}, choice {p.choiceId}"
    pure (ids, rest)

/-- Resume only the suspended tail, in the original action's resume slot. -/
def resumeCardPlay (env : EffectEnv) (cs : CombatState) (p : PendingCardChoice)
    (stepIdx : Nat) (stream : ChoiceStream) (sync : PlayerChoiceSynchronizer)
    (deferAutomatic : Bool := false) : Except String HeadlessCardResult := do
  let (ids, rest) ← p.selection cs stream
  let (next, hist) := discardSelected cs p.play.playerId ids
  pure (runCardProgram env p.play p.source p.actor stepIdx deferAutomatic p.remaining
    { combat := next, accepted := true, history := hist, stream := rest, sync := sync })

/-- Begin paying and resolving a play. A pending choice leaves the same card in Play.
    Native queue callers defer even automatic choices to the recorded resume slot. -/
def execPlayCardHeadless (env : EffectEnv) (cs : CombatState) (pid : PlayerId)
    (cid : CardInstanceId) (targetId : Option CreatureId) (stepIdx : Nat := 0)
    (choiceStream : ChoiceStream := []) (sync : PlayerChoiceSynchronizer := {})
    (deferAutomatic : Bool := false) : HeadlessCardResult :=
  let rejected : HeadlessCardResult := { combat := cs, stream := choiceStream, sync := sync }
  let reg := env.behaviorReg cs
  match cs.findPlayer pid with
  | none => rejected
  | some player =>
      match player.combatState with
      | none => rejected
      | some pcs =>
          match pcs.piles.hand.find? (·.instanceId == cid) with
          | none => rejected
          | some card =>
              let (ok, _) := Sts2Model.Command.canPlay cs reg pid card .none []
              if !ok then rejected
              else
                let (csSpent, eSpent, sSpent) := Sts2Model.Command.spendResources cs reg pid card []
                let csInPlay := csSpent.updatePlayer pid fun p =>
                  match p.combatState with
                  | none => p
                  | some pSt =>
                      let (piles', _) := Sts2Model.Command.moveCard pSt.piles cid .play .bottom (fun c =>
                        if c.energyCost.costsX then
                          { c with energyCost := { c.energyCost with capturedXValue := eSpent } }
                        else c)
                      { p with
                        combatState := some { pSt with
                          piles := piles'
                          playedTagsThisTurn := pSt.playedTagsThisTurn ++ card.tags } }
                let resultPile := card.defaultResultPile
                let playInfo : CardPlay :=
                  { cardId := cid
                  , playerId := pid
                  , targetId := targetId
                  , resultPile := resultPile
                  , energySpent := eSpent
                  , starsSpent := sSpent }
                let preHist : List CombatHistoryEntryEx :=
                  (if eSpent > 0 then [CombatHistoryEntryEx.energySpent cs.roundNumber cs.currentSide pid eSpent] else []) ++
                  (if sSpent > 0 then [CombatHistoryEntryEx.starsModified cs.roundNumber cs.currentSide pid (-(sSpent : Int))] else []) ++
                  [CombatHistoryEntryEx.cardPlayStarted cs.roundNumber cs.currentSide playInfo]
                let source := if card.energyCost.costsX then
                    { card with energyCost := { card.energyCost with capturedXValue := eSpent } }
                  else card
                runCardProgram env playInfo source player.creatureId stepIdx deferAutomatic (env.cardEffect card)
                  { combat := csInPlay, accepted := true, history := preHist, stream := choiceStream, sync := sync }

/-- Execute using a potion at `slotIdx` headlessly. -/
def execUsePotionHeadless (env : EffectEnv) (cs : CombatState) (pid : PlayerId)
    (slotIdx : Nat) (targetId : Option CreatureId) (stepIdx : Nat := 0)
    (choiceStream : ChoiceStream := []) :
    CombatState × Bool × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream × CombatOutcome :=
  match cs.findPlayer pid with
  | none => (cs, false, [], [], choiceStream, .ongoing)
  | some player =>
      if !cs.isInProgress then (cs, false, [], [], choiceStream, .ongoing)
      else
        match player.potions[slotIdx]? with
        | some (some pot) =>
            let csConsumed := cs.updatePlayer pid fun p =>
              { p with potions := p.potions.zipIdx.map fun (opt, idx) => if idx == slotIdx then none else opt }
            let prog := env.potionEffect pot.modelId
            let (csAfterEff, effHist, attrs, stream') :=
              execEffectProgram env csConsumed (some pid) player.creatureId targetId none stepIdx choiceStream prog
            let potHist := CombatHistoryEntryEx.potionUsed cs.roundNumber cs.currentSide pid pot.modelId targetId
            let (csChecked, outcome) := checkWinCondition (checkAllPlayersDead csAfterEff) (env.behaviorReg csAfterEff) []
            (csChecked, true, [potHist] ++ effHist, attrs, stream', outcome)
        | _ => (cs, false, [], [], choiceStream, .ongoing)

/-- End player turn, roll and execute every living enemy's AI move via `MonsterStateMachine`,
    check win/loss, and begin the next player round if still in progress. -/
def execEnemyTurnHeadless (env : EffectEnv) (cs : CombatState) (stepIdx : Nat := 0)
    (choiceStream : ChoiceStream := []) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream × CombatOutcome :=
  if !cs.isInProgress then (cs, [], [], choiceStream, .ongoing)
  else
    let reg := env.behaviorReg cs
    let (csPlayerEnd, outcome) := runSideTurnEndLifecycle cs reg .player []
    if !csPlayerEnd.isInProgress then (csPlayerEnd, [], [], choiceStream, outcome)
    else
      let csPhase1 := endPlayerTurnPhaseOne csPlayerEnd (env.behaviorReg csPlayerEnd) []
      let csSide := endPlayerTurnPhaseTwo csPhase1 (env.behaviorReg csPhase1) []
      if csSide.currentSide != .enemy || !csSide.isInProgress then
        (csSide, [], [], choiceStream, .ongoing)
      else
        let (csEnemyStart, outcome) := runSideTurnStartLifecycle csSide (env.behaviorReg csSide) .enemy []
        if !csEnemyStart.isInProgress then (csEnemyStart, [], [], choiceStream, outcome)
        else
          let livingEnemyIds := (csEnemyStart.enemies.filter (·.isAlive)).map (·.id)
          let (csAfterMonsters, mHist, mAttrs, stream') :=
            livingEnemyIds.foldl (fun (s, hAcc, aAcc, strm) eid =>
              if !s.isInProgress then (s, hAcc, aAcc, strm)
              else
                match s.findCreature eid with
                | none => (s, hAcc, aAcc, strm)
                | some enemy =>
                    if enemy.isDead then (s, hAcc, aAcc, strm)
                    else
                      let modelId := (enemy.monster.map (·.modelId)).getD enemy.modelId
                      match env.monsterBlueprint modelId with
                      | none => (s, hAcc, aAcc, strm)
                      | some bp =>
                          let baseSm := bp.stateMachine
                          let curStateId :=
                            match enemy.monster with
                            | some mi => if mi.currentMoveId == "" then baseSm.initialStateId else mi.currentMoveId
                            | none => baseSm.initialStateId
                          let pastLog := (enemy.monster.map (·.stateLog)).getD []
                          let runtimeSm : MonsterStateMachine :=
                            { baseSm with
                              currentStateId := curStateId
                            , performedFirstMove := !pastLog.isEmpty
                            , stateLog := pastLog }
                          match MonsterStateMachine.rollMoveFuel 16 runtimeSm s enemy (s.monsterAiRng.getD s.rng) with
                          | none => (s, hAcc, aAcc, strm)
                          | some (moveId, sm', rng') =>
                              let nextLog := if sm'.stateLog.length == pastLog.length then pastLog ++ [moveId] else sm'.stateLog
                              let withRng := if s.monsterAiRng.isSome then { s with monsterAiRng := some rng' }
                                             else { s with rng := rng' }
                              let sRng := withRng.updateCreature eid fun c =>
                                let mi' : MonsterInfo :=
                                  { (c.monster.getD { modelId := modelId }) with
                                    currentMoveId := moveId
                                  , stateLog := nextLog }
                                { c with monster := some mi' }
                              let defaultPlayerCid :=
                                (sRng.allies.find? (fun c => c.isAlive && c.isPlayer)).map (·.id)
                              let (sMoved, moveHist, moveAttrs, strm') :=
                                execEffectProgram env sRng none eid defaultPlayerCid none stepIdx strm (bp.moveEffects moveId)
                              let targets := match defaultPlayerCid with | some cid => [cid] | none => []
                              let moveEntry := CombatHistoryEntryEx.monsterPerformedMove
                                sRng.roundNumber .enemy eid modelId moveId targets
                              (sMoved, hAcc ++ [moveEntry] ++ moveHist, aAcc ++ moveAttrs, strm'))
            (csEnemyStart, [], [], choiceStream)
          let (csChecked, outcome) := checkWinCondition (checkAllPlayersDead csAfterMonsters) (env.behaviorReg csAfterMonsters) []
          if outcome != .ongoing || !csChecked.isInProgress then
            (csChecked, mHist, mAttrs, stream', outcome)
          else
            let (csEnemyEnd, outcome) := runSideTurnEndLifecycle csChecked (env.behaviorReg csChecked) .enemy []
            if !csEnemyEnd.isInProgress then
              (csEnemyEnd, mHist, mAttrs, stream', outcome)
            else
              let csNextRound := endEnemyTurn csEnemyEnd (env.behaviorReg csEnemyEnd) []
              let csReadyPlayers := csNextRound.players.foldl (fun acc p =>
                setupPlayerTurn acc (env.behaviorReg acc) p.playerId 5 []) csNextRound
              let (csPlayerStart, outcome) := runSideTurnStartLifecycle csReadyPlayers (env.behaviorReg csReadyPlayers) .player []
              (csPlayerStart, mHist, mAttrs, stream', outcome)

end Sts2Model.Sim

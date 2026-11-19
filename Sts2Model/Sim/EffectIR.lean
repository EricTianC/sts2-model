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

/-- Pure algebraic DSL for card, potion, and monster move effects. -/
inductive EffectOp where
  | dealDamage (target : EffectTarget) (amount : Dec) (hits : Nat := 1) (props : ValueProp := DamageProps.card)
  | gainBlock (target : EffectTarget) (amount : Dec) (props : ValueProp := BlockProps.card)
  | applyPower (target : EffectTarget) (power : PowerInstance) (amount : Dec)
  | draw (count : Nat)
  | discardChosen (choiceId : Nat) (count : Nat)
  | exhaustSelf
  | gainEnergy (amount : Nat)
  | gainStars (amount : Nat)
  | heal (target : EffectTarget) (amount : Dec)
  | channelOrb (kind : OrbKind)
  | evokeOrb (times : Nat := 1)
  | forge (amount : Dec)
  | addCardToPile (card : CardInstance) (pile : PileType) (pos : CardPilePosition := .bottom)
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

def execOp (env : EffectEnv) (cs : CombatState) (actorPid : Option PlayerId) (actorCid : CreatureId)
    (chosenTarget : Option CreatureId) (cardSource : Option CardInstance) (stepIdx : Nat)
    (choiceStream : ChoiceStream) (op : EffectOp) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let reg := env.behaviorReg cs
  match op with
  | .dealDamage tgt amt hits props =>
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
  | .gainBlock tgt amt props =>
      let (tids, cs0) := resolveEffectTargets cs actorCid chosenTarget tgt
      let (csFinal, hist) := tids.foldl (fun (s, hAcc) tid =>
        let (s', modBlk) := Sts2Model.Command.gainBlock s (env.behaviorReg s) tid amt props cardSource []
        let h := CombatHistoryEntryEx.blockGained s.roundNumber s.currentSide tid modBlk.truncate props
          (cardSource.map (·.instanceId))
        (s', hAcc ++ [h])) (cs0, [])
      (csFinal, hist, [], choiceStream)
  | .applyPower tgt template amt =>
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
  | .draw count =>
      match actorPid with
      | none => (cs, [], [], choiceStream)
      | some pid =>
          let (cs', drawn) := Sts2Model.Command.drawCards cs reg pid count false []
          let hist := drawn.map fun c =>
            CombatHistoryEntryEx.cardDrawn cs'.roundNumber cs'.currentSide pid c.instanceId false
          (cs', hist, [], choiceStream)
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
  | .exhaustSelf =>
      match actorPid, cardSource with
      | some pid, some c =>
          let cs' := Sts2Model.Command.exhaustCard cs pid c.instanceId
          let h := CombatHistoryEntryEx.cardExhausted cs'.roundNumber cs'.currentSide pid c.instanceId
          (cs', [h], [], choiceStream)
      | _, _ => (cs, [], [], choiceStream)
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

/-- Execute playing a card headlessly (`canPlay -> spendResources -> Move Hand->Play -> EffectIR -> ResultPile`). -/
def execPlayCardHeadless (env : EffectEnv) (cs : CombatState) (pid : PlayerId)
    (cid : CardInstanceId) (targetId : Option CreatureId) (stepIdx : Nat := 0)
    (choiceStream : ChoiceStream := []) :
    CombatState × Bool × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  let reg := env.behaviorReg cs
  match cs.findPlayer pid with
  | none => (cs, false, [], [], choiceStream)
  | some player =>
      match player.combatState with
      | none => (cs, false, [], [], choiceStream)
      | some pcs =>
          match pcs.piles.hand.find? (·.instanceId == cid) with
          | none => (cs, false, [], [], choiceStream)
          | some card =>
              let (ok, _) := Sts2Model.Command.canPlay cs reg pid card .none []
              if !ok then (cs, false, [], [], choiceStream)
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
                let prog := env.cardEffect card
                let (csAfterEff, effHist, attrs, stream') :=
                  execEffectProgram env csInPlay (some pid) player.creatureId targetId (some card) stepIdx choiceStream prog
                let csMoved := csAfterEff.updatePlayer pid fun p =>
                  match p.combatState with
                  | none => p
                  | some pSt =>
                      let (piles', _) := Sts2Model.Command.moveCard pSt.piles cid resultPile .bottom CardInstance.afterCardPlayedCleanup
                      { p with combatState := some { pSt with piles := piles' } }
                let wasEthereal := card.hasKeyword .ethereal
                let postHist : List CombatHistoryEntryEx :=
                  [CombatHistoryEntryEx.cardPlayFinished csMoved.roundNumber csMoved.currentSide playInfo wasEthereal] ++
                  (if resultPile == PileType.exhaust then
                    [CombatHistoryEntryEx.cardExhausted csMoved.roundNumber csMoved.currentSide pid cid]
                   else [])
                let (csChecked, _) := checkWinCondition (checkAllPlayersDead csMoved) (env.behaviorReg csMoved) []
                (csChecked, true, preHist ++ effHist ++ postHist, attrs, stream')

/-- Execute using a potion at `slotIdx` headlessly. -/
def execUsePotionHeadless (env : EffectEnv) (cs : CombatState) (pid : PlayerId)
    (slotIdx : Nat) (targetId : Option CreatureId) (stepIdx : Nat := 0)
    (choiceStream : ChoiceStream := []) :
    CombatState × Bool × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  match cs.findPlayer pid with
  | none => (cs, false, [], [], choiceStream)
  | some player =>
      if !cs.isInProgress then (cs, false, [], [], choiceStream)
      else
        match player.potions[slotIdx]? with
        | some (some pot) =>
            let csConsumed := cs.updatePlayer pid fun p =>
              { p with potions := p.potions.zipIdx.map fun (opt, idx) => if idx == slotIdx then none else opt }
            let prog := env.potionEffect pot.modelId
            let (csAfterEff, effHist, attrs, stream') :=
              execEffectProgram env csConsumed (some pid) player.creatureId targetId none stepIdx choiceStream prog
            let potHist := CombatHistoryEntryEx.potionUsed cs.roundNumber cs.currentSide pid pot.modelId targetId
            let (csChecked, _) := checkWinCondition (checkAllPlayersDead csAfterEff) (env.behaviorReg csAfterEff) []
            (csChecked, true, [potHist] ++ effHist, attrs, stream')
        | _ => (cs, false, [], [], choiceStream)

/-- End player turn, roll and execute every living enemy's AI move via `MonsterStateMachine`,
    check win/loss, and begin the next player round if still in progress. -/
def execEnemyTurnHeadless (env : EffectEnv) (cs : CombatState) (stepIdx : Nat := 0)
    (choiceStream : ChoiceStream := []) :
    CombatState × List CombatHistoryEntryEx × List DamageAttribution × ChoiceStream :=
  if !cs.isInProgress then (cs, [], [], choiceStream)
  else
    let reg := env.behaviorReg cs
    let csPhase1 := endPlayerTurnPhaseOne cs reg []
    let csSide := endPlayerTurnPhaseTwo csPhase1 (env.behaviorReg csPhase1) []
    if csSide.currentSide != .enemy || !csSide.isInProgress then
      (csSide, [], [], choiceStream)
    else
      let livingEnemyIds := (csSide.enemies.filter (·.isAlive)).map (·.id)
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
                      match MonsterStateMachine.rollMoveFuel 16 runtimeSm s enemy s.rng with
                      | none => (s, hAcc, aAcc, strm)
                      | some (moveId, sm', rng') =>
                          let nextLog := if sm'.stateLog.length == pastLog.length then pastLog ++ [moveId] else sm'.stateLog
                          let sRng := { s with rng := rng' }.updateCreature eid fun c =>
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
        (csSide, [], [], choiceStream)
      let (csChecked, outcome) := checkWinCondition (checkAllPlayersDead csAfterMonsters) (env.behaviorReg csAfterMonsters) []
      if outcome != .ongoing || !csChecked.isInProgress then
        (csChecked, mHist, mAttrs, stream')
      else
        let csNextRound := endEnemyTurn csChecked (env.behaviorReg csChecked) []
        let csReadyPlayers := csNextRound.players.foldl (fun acc p =>
          setupPlayerTurn acc (env.behaviorReg acc) p.playerId 5 []) csNextRound
        (csReadyPlayers, mHist, mAttrs, stream')

end Sts2Model.Sim

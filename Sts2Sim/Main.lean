/-
  Executable Simulator & `.NET 9` Differential Test Runner (`lake exe sts2sim`).
  Default: executable regression suite. `--diff` runs the .NET reference vectors.
  `--inspect` and `--export-sample-trace` use wire schema v1.
  `--observe-combat` replays scoped observations; native save audits do not simulate.
-/
import Sts2Model
import Sts2Sim.ObservedCombat
import Sts2Sim.RunHistoryAudit
import Sts2Sim.ActMapAudit

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command
open Sts2Model.Combat
open Sts2Model.Multiplayer
open Sts2Model.Sim
open Sts2Model.Replay
open Sts2Model.Mechanics
open Sts2Model.Run
open Sts2Model.Catalog
open Sts2Model.Sim.Generated
open Sts2Model.Examples
open Sts2Model.Examples.ReplayAnalyzer

private def parseUInt64! (s : String) : UInt64 :=
  match s.toNat? with
  | some n => UInt64.ofNat n
  | none   => 0

private def parseInt! (s : String) : Int :=
  match s.toInt? with
  | some n => n
  | none   => 0

private def parseNat! (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none   => 0

private def parseCsvInts (s : String) : List Int :=
  if s.trimAscii.isEmpty then []
  else (s.splitOn ",").map (fun tok => parseInt! tok.trimAscii.toString)

private def parseCsvStrings (s : String) : List String :=
  if s.trimAscii.isEmpty then []
  else (s.splitOn ",").map (fun tok => tok.trimAscii.toString)

private def evalRngSeq (seedStr countStr : String) : String :=
  let seed := parseUInt64! seedStr
  let count := parseNat! countStr
  let rec go (n : Nat) (rng : Rng) (acc : List String) : List String :=
    match n with
    | 0 => acc
    | k + 1 =>
        let (u, rng1) := rng.nextULong
        let (i100, rng2) := rng1.nextInt 100
        let (b, rng3) := rng2.nextBool
        let (d, rng4) := rng3.nextDouble
        let item := s!"{u},{i100},{if b then 1 else 0},{d.toBits}"
        go k rng4 (acc ++ [item])
  String.intercalate ";" (go count (Rng.ofSeed seed) [])

private def evalRngShuffle (seedStr listStr : String) : String :=
  let seed := parseUInt64! seedStr
  let xs := parseCsvInts listStr
  let (out, _) := Rng.unstableShuffle xs (Rng.ofSeed seed)
  String.intercalate "," (out.map toString)

private def evalDmgPipe (fields : List String) : String :=
  let base := parseInt! (fields[1]?.getD "0")
  let mask := parseNat! (fields[2]?.getD "0")
  let str := parseInt! (fields[3]?.getD "0")
  let vuln := parseNat! (fields[4]?.getD "0") == 1
  let phrog := parseNat! (fields[5]?.getD "0") == 1
  let weak := parseNat! (fields[6]?.getD "0") == 1
  let lateMulS2 := parseInt! (fields[7]?.getD "100")
  let capVal := parseInt! (fields[8]?.getD "-1")
  let props := ValueProp.ofBitmask mask
  let dPows : List PowerInstance :=
    (if str != 0 then [{ instanceId := 10, modelId := ModelId.mkPower "STRENGTH_POWER", ownerId := 100, allowNegative := true, amount := str }] else []) ++
    (if weak then [{ instanceId := 11, modelId := ModelId.mkPower "WEAK_POWER", ownerId := 100, powerType := .debuff, amount := 1 }] else []) ++
    (if lateMulS2 != 100 || capVal ≥ 0 then [{ instanceId := 12, modelId := ⟨"DIFF", "DMG_MOD"⟩, ownerId := 200, amount := 1 }] else [])
  let tPows : List PowerInstance :=
    if vuln then [{ instanceId := 20, modelId := ModelId.mkPower "VULNERABLE_POWER", ownerId := 200, powerType := .debuff, amount := 1 }] else []
  let dealer : Creature := { id := 100, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1, currentHp := 80, maxHp := 80, powers := dPows }
  let target : Creature := { id := 200, modelId := ModelId.mkMonster "JAW", side := .enemy, currentHp := 100, maxHp := 100, powers := tPows }
  let relics : List RelicInstance := if phrog then [{ modelId := ModelId.mkRelic "PAPER_PHROG" }] else []
  let player : Player := { playerId := 1, creatureId := 100, characterId := ModelId.mkCharacter "IRONCLAD", relics := relics }
  let cs : CombatState := { allies := [dealer], enemies := [target], players := [player] }
  let modBehavior : HookBehavior :=
    { HookBehavior.neutral with
      modifyDamageMultiplicativeLate := fun _ _ _ pr _ _ =>
        if lateMulS2 != 100 && pr.isPoweredAttack then Dec.ofScaled lateMulS2 2 else Dec.one
      modifyDamageCap := fun _ t _ _ _ =>
        if capVal ≥ 0 && (t.map (·.id)) == some 200 then Dec.ofInt capVal else Dec.maxDecimal }
  let reg : BehaviorRegistry := fun mid =>
    if mid == ⟨"DIFF", "DMG_MOD"⟩ then modBehavior else builtinBehaviorRegistry cs mid
  let (d, _) := modifyDamage cs reg (some target) (some dealer) (Dec.ofInt base) props none
  s!"{d.truncate}|{Dec.format d}"

private def evalBlkPipe (fields : List String) : String :=
  let base := parseInt! (fields[1]?.getD "0")
  let mask := parseNat! (fields[2]?.getD "0")
  let dex := parseInt! (fields[3]?.getD "0")
  let frail := parseNat! (fields[4]?.getD "0") == 1
  let props := ValueProp.ofBitmask mask
  let pows : List PowerInstance :=
    (if dex != 0 then [{ instanceId := 10, modelId := ModelId.mkPower "DEXTERITY_POWER", ownerId := 100, allowNegative := true, amount := dex }] else []) ++
    (if frail then [{ instanceId := 11, modelId := ModelId.mkPower "FRAIL_POWER", ownerId := 100, powerType := .debuff, amount := 1 }] else [])
  let target : Creature := { id := 100, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1, currentHp := 80, maxHp := 80, powers := pows }
  let cs : CombatState := { allies := [target], players := [{ playerId := 1, creatureId := 100, characterId := ModelId.mkCharacter "IRONCLAD" }] }
  let dummyCard : CardInstance :=
    { instanceId := 1, modelId := ModelId.mkCard "DEFEND_IRONCLAD", ownerId := 1, cardType := .skill, rarity := .basic
    , targetType := .self, energyCost := CardEnergyCost.mkCanonical 1, baseBlock := Dec.ofInt base }
  let cardArg := if props.isCardOrMonsterMove then some dummyCard else none
  let (b, _) := modifyBlock cs (builtinBehaviorRegistry cs) target (Dec.ofInt base) props cardArg
  s!"{b.truncate}|{Dec.format b}"

private def evalCreatureDmg (fields : List String) : String :=
  let tHp := parseNat! (fields[1]?.getD "50")
  let tBlk := parseNat! (fields[2]?.getD "0")
  let ostyHp := parseNat! (fields[3]?.getD "0")
  let mask := parseNat! (fields[4]?.getD "8")
  let rawDmg := parseInt! (fields[5]?.getD "0")
  let intang := parseNat! (fields[6]?.getD "0") == 1
  let props := ValueProp.ofBitmask mask
  let tPows : List PowerInstance :=
    if intang then [{ instanceId := 30, modelId := ModelId.mkPower "INTANGIBLE_POWER", ownerId := 100, amount := 1 }] else []
  let target : Creature :=
    { id := 100, modelId := ModelId.mkCharacter "NECROBINDER", side := .player, playerId := some 1
    , currentHp := tHp, maxHp := max tHp 100, block := tBlk, powers := tPows }
  let dealer : Creature := { id := 200, modelId := ModelId.mkMonster "M", side := .enemy, currentHp := 50, maxHp := 50 }
  let allies0 :=
    if ostyHp > 0 then
      let osty : Creature :=
        { id := 101, modelId := ostyMonsterModelId, side := .player, petOwnerId := some 1
        , currentHp := ostyHp, maxHp := max ostyHp 100
        , powers := [{ instanceId := 31, modelId := dieForYouPowerModelId, ownerId := 101, powerType := .buff, stackType := .single, amount := 1 }] }
      [target, osty]
    else [target]
  let player : Player :=
    { playerId := 1, creatureId := 100, characterId := ModelId.mkCharacter "NECROBINDER"
    , combatState := some { petIds := if ostyHp > 0 then [101] else [] } }
  let cs : CombatState := { allies := allies0, enemies := [dealer], players := [player] }
  let reg : BehaviorRegistry := fun mid =>
    if mid == dieForYouPowerModelId then dieForYouBehavior cs else builtinBehaviorRegistry cs mid
  let (cs', resList) := damageSingleTarget cs reg 100 (Dec.ofInt rawDmg) props (some 200) none
  let finalTHp := (cs'.findCreature 100).map (·.currentHp) |>.getD 0
  let finalTBlk := (cs'.findCreature 100).map (·.block) |>.getD 0
  let finalOstyHp := if ostyHp > 0 then (cs'.findCreature 101).map (·.currentHp) |>.getD 0 else 0
  let totalUnblk := resList.foldl (fun acc r => acc + r.unblockedDamage) 0
  let totalBlk := resList.foldl (fun acc r => acc + r.blockedDamage) 0
  let totalOver := resList.foldl (fun acc r => acc + r.overkillDamage) 0
  let tKilled := if resList.any (fun r => r.receiverId == 100 && r.wasTargetKilled) then 1 else 0
  let oKilled := if resList.any (fun r => r.receiverId == 101 && r.wasTargetKilled) then 1 else 0
  s!"{finalTHp},{finalTBlk},{finalOstyHp},{totalUnblk},{totalBlk},{totalOver},{tKilled},{oKilled}"

private def evalPowerStack (fields : List String) : String :=
  let existAmt := parseInt! (fields[1]?.getD "0")
  let applyAmt := parseInt! (fields[2]?.getD "0")
  let isSingle := parseNat! (fields[3]?.getD "0") == 1
  let allowNeg := parseNat! (fields[4]?.getD "0") == 1
  let artAmt := parseNat! (fields[5]?.getD "0")
  let isDebuff := parseNat! (fields[6]?.getD "0") == 1
  let pType := if isDebuff then PowerType.debuff else PowerType.buff
  let sType := if isSingle then PowerStackType.single else PowerStackType.counter
  let tmpl : PowerInstance :=
    { instanceId := 0, modelId := ⟨"DIFF", "TEST_POWER"⟩, ownerId := 100
    , powerType := pType, stackType := sType, allowNegative := allowNeg }
  let initPows : List PowerInstance :=
    (if existAmt != 0 then [{ tmpl with instanceId := 10, amount := existAmt }] else []) ++
    (if artAmt > 0 then [{ instanceId := 11, modelId := ModelId.mkPower "ARTIFACT_POWER", ownerId := 100, powerType := .buff, stackType := .counter, amount := artAmt }] else [])
  let target : Creature := { id := 100, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1, currentHp := 80, maxHp := 80, powers := initPows }
  let applier : Creature := { id := 200, modelId := ModelId.mkMonster "M", side := .enemy, currentHp := 50, maxHp := 50 }
  let cs : CombatState := { allies := [target], enemies := [applier], players := [{ playerId := 1, creatureId := 100, characterId := ModelId.mkCharacter "IRONCLAD" }] }
  let (cs', _) := applyPower cs (builtinBehaviorRegistry cs) tmpl 100 (Dec.ofInt applyAmt) (some 200)
  let tAfter := cs'.findCreature 100
  let pAfter := tAfter.bind (·.getPower ⟨"DIFF", "TEST_POWER"⟩)
  let finalAmt := pAfter.map (·.amount) |>.getD 0
  let removed := if pAfter.isNone then 1 else 0
  let artRem := (tAfter.map (·.getPowerAmount (ModelId.mkPower "ARTIFACT_POWER"))).getD 0
  s!"{finalAmt},{removed},{artRem}"

private def evalCardCost (fields : List String) : String :=
  let baseCost := parseInt! (fields[1]?.getD "1")
  let costsX := parseNat! (fields[2]?.getD "0") == 1
  let energy := parseNat! (fields[3]?.getD "3")
  let stars := parseNat! (fields[4]?.getD "0")
  let starCost := parseInt! (fields[5]?.getD "0")
  let modType := parseNat! (fields[6]?.getD "0")
  let modAmt := parseInt! (fields[7]?.getD "0")
  let excessStars := parseNat! (fields[8]?.getD "0") == 1
  let hookDelta := parseInt! (fields[9]?.getD "0")
  let localMods : List LocalCostModifier :=
    if modType == 1 then [{ amount := modAmt, costType := .absolute, expiration := LocalCostModifierExpiration.endOfCombat }]
    else if modType == 2 then [{ amount := modAmt, costType := .relative, expiration := LocalCostModifierExpiration.endOfCombat }]
    else []
  let eCost : CardEnergyCost := { canonical := baseCost, baseCost := baseCost, costsX := costsX, localModifiers := localMods }
  let card : CardInstance :=
    { instanceId := 50, modelId := ModelId.mkCard "STRIKE_IRONCLAD", ownerId := 1
    , cardType := .attack, rarity := .common, targetType := .anyEnemy
    , energyCost := eCost, baseStarCost := starCost }
  let pcs : PlayerCombatState := { energy := energy, baseMaxEnergy := 3, stars := stars }
  let player : Player := { playerId := 1, creatureId := 100, characterId := ModelId.mkCharacter "REGENT", combatState := some pcs }
  let cHero : Creature := { id := 100, modelId := ModelId.mkCharacter "REGENT", side := .player, playerId := some 1, currentHp := 80, maxHp := 80 }
  let cs : CombatState := { allies := [cHero], players := [player], modifiers := [⟨"DIFF", "COST_MOD"⟩] }
  let costBeh : HookBehavior :=
    { HookBehavior.neutral with
      modifyEnergyCostInCombat := fun _ _ c => Dec.add c (Dec.ofInt hookDelta)
      shouldPayExcessEnergyCostWithStars := fun _ _ => excessStars }
  let reg : BehaviorRegistry := fun mid => if mid == ⟨"DIFF", "COST_MOD"⟩ then costBeh else HookBehavior.neutral
  let eff := if costsX then (energy : Int) else effectiveEnergyCost cs reg card
  let (eReq, sReq, _) := pcs.checkResourcesFor eff starCost excessStars
  let (ok, _) := canPlay cs reg 1 card .none
  s!"{eff},{if ok then 1 else 0},{eReq},{sReq}"

private def evalRarityOdds (fields : List String) : String :=
  let seed := parseUInt64! (fields[1]?.getD "1")
  let scarcity := parseNat! (fields[2]?.getD "0") == 1
  let typeCode := parseNat! (fields[3]?.getD "0")
  let numRolls := parseNat! (fields[4]?.getD "10")
  let ot : CardRarityOddsType := match typeCode with
    | 0 => .regularEncounter
    | 1 => .eliteEncounter
    | 2 => .bossEncounter
    | 3 => .shop
    | 4 => .uniform
    | 5 => .blitz
    | _ => .blitzNeow
  let rec go (k : Nat) (o : CardRarityOddsF32) (r : Rng) (acc : List String) : List String × Float32 :=
    match k with
    | 0 => (acc, o.currentValue)
    | m + 1 =>
        let (rar, o', r') := o.roll ot r
        let ch := match rar with
          | .rare     => "R"
          | .uncommon => "U"
          | _         => "C"
        go m o' r' (acc ++ [ch])
  let (seq, finalOff) := go numRolls { currentValue := (-0.05 : Float32), isScarcity := scarcity } (Rng.ofSeed seed) []
  s!"{String.intercalate "" seq}|{finalOff.toBits}"

private def evalModSort (fields : List String) : String :=
  let ids := parseCsvStrings (fields[1]?.getD "")
  let reg := ids.foldl (fun r id => r.subscribeCombatHooks id []) ModHookRegistry.empty
  String.intercalate "," (reg.combatSubscribers.map (·.id))

private def evalQueueSet (fields : List String) : String :=
  let pids := (parseCsvStrings (fields[1]?.getD "1,2")).map parseNat!
  let opsStr := fields[2]?.getD ""
  let ops := if opsStr.trimAscii.isEmpty then [] else opsStr.splitOn ";"
  let initQs := (ActionQueueSet.init pids).combatStarted
  let (finalQs, picked) := ops.foldl (fun (qs, pAcc) rawOp =>
    let tok := rawOp.trimAscii.toString
    if tok.isEmpty then (qs, pAcc)
    else
      let ps := tok.splitOn ","
      match ps[0]? with
      | some "ENQ" =>
          let pid := parseNat! (ps[1]?.getD "1")
          let tCode := parseNat! (ps[2]?.getD "2")
          let pDriven := parseNat! (ps[3]?.getD "1") == 1
          let isPlay := parseNat! (ps[4]?.getD "1") == 1
          let atp : GameActionType := match tCode with
            | 0 => .none
            | 1 => .combat
            | 2 => .combatPlayPhaseOnly
            | 3 => .nonCombat
            | _ => .any
          let pl : ReplayActionPayload := if isPlay then .playCard 1001 none else .endPlayerTurn true
          ((qs.enqueue pid atp pDriven isPlay pl).1, pAcc)
      | some "PICK" =>
          let (qs1, opt) := qs.getReadyAction
          let aid : Int := match opt with | some a => (a.actionId : Int) | none => -1
          (qs1, pAcc ++ [aid])
      | some "EXEC" =>
          let aid := parseNat! (ps[1]?.getD "0")
          (qs.beginExecuting aid, pAcc)
      | some "PAUSE" =>
          let aid := parseNat! (ps[1]?.getD "0")
          let cpc := parseNat! (ps[2]?.getD "0") == 1
          ((qs.pauseActionForPlayerChoice aid { cancelPlayCardActions := cpc }).1, pAcc)
      | some "RESUME" =>
          let oldId := parseNat! (ps[1]?.getD "0")
          ((qs.resumeAction oldId).1, pAcc)
      | some "POP" =>
          let aid := parseNat! (ps[1]?.getD "0")
          (qs.popAction aid, pAcc)
      | some "CANCELPD" =>
          (qs.startCancellingAllPlayerDrivenCombatActions, pAcc)
      | some "CEND" =>
          (qs.combatEnded, pAcc)
      | some "CSTART" =>
          (qs.combatStarted, pAcc)
      | some "PPAUSED" =>
          let flg := parseNat! (ps[1]?.getD "1") == 1
          let qs1 := if flg then qs.pauseAllPlayerQueues else qs.unpauseAllPlayerQueues
          (qs1, pAcc)
      | _ => (qs, pAcc)) (initQs, [])
  let pickedStr := String.intercalate "," (picked.map toString)
  let remStr := String.intercalate "," (finalQs.queues.map fun q => toString q.actions.length)
  s!"{finalQs.nextActionId}|{pickedStr}|{finalQs.canceledCount}|{remStr}"

private def evalTimelineSeek (fields : List String) : String :=
  let seed := parseUInt64! (fields[1]?.getD "1")
  let enemyHp := max 1 (parseNat! (fields[2]?.getD "50"))
  let stride := max 1 (parseNat! (fields[3]?.getD "2"))
  let actsStr := fields[4]?.getD ""
  let acts := if actsStr.trimAscii.isEmpty then [] else actsStr.splitOn ";"
  let mkC (cid : CardInstanceId) (pid : PlayerId) (entry : String) (cost : Int)
      (ct : CardType := .attack) (tt : TargetType := .anyEnemy) (upg : Nat := 0) : CardInstance :=
    { instanceId := cid, modelId := ModelId.mkCard entry, ownerId := pid
    , cardType := ct, rarity := .common, targetType := tt
    , energyCost := CardEnergyCost.mkCanonical cost, upgradeLevel := upg }
  let p1Hand :=
    [ mkC 1001 1 "BASH" 2
    , mkC 1002 1 "STRIKE_IRONCLAD" 1
    , mkC 1003 1 "TWIN_STRIKE" 1 ]
  let p2Hand :=
    [ mkC 2001 2 "DEFEND_IRONCLAD" 1 .skill .self
    , mkC 2002 2 "STRIKE_IRONCLAD" 1 .attack .anyEnemy 1
    , mkC 2003 2 "UPPERCUT" 2 ]
  let cP1 : Creature := { id := 101, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1, currentHp := 80, maxHp := 80 }
  let cP2 : Creature := { id := 102, modelId := ModelId.mkCharacter "SILENT", side := .player, playerId := some 2, currentHp := 70, maxHp := 70 }
  let cEnemy : Creature :=
    { id := 200, modelId := ModelId.mkMonster "COOP_GUARDIAN", side := .enemy
    , currentHp := enemyHp, maxHp := enemyHp
    , monster := some { modelId := ModelId.mkMonster "COOP_GUARDIAN", currentMoveId := "SLAM" } }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "IRONCLAD"
    , potions := [some { modelId := ModelId.mkPotion "FIRE_POTION" }]
    , combatState := some { energy := 5, baseMaxEnergy := 3, piles := { hand := p1Hand } } }
  let p2 : Player :=
    { playerId := 2, creatureId := 102, characterId := ModelId.mkCharacter "SILENT"
    , combatState := some { energy := 5, baseMaxEnergy := 3, piles := { hand := p2Hand } } }
  let cs : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , allies := [cP1, cP2], enemies := [cEnemy], players := [p1, p2]
    , rng := Rng.ofSeed seed, nextInstanceId := 1000 }
  let initSt : TimelineState :=
    { combat := some cs
    , queueSet := (ActionQueueSet.init [1, 2]).combatStarted
    , choiceSync := PlayerChoiceSynchronizer.init [1, 2] }
  let evs : List TimelineEvent := acts.zipIdx.filterMap fun (rawTok, idx) =>
    let tok := rawTok.trimAscii.toString
    match tok with
    | "P1_BASH" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 1, kind := .combat { eventType := .gameAction, playerId := some 1, payload := some (.playCard 1001 (some 200)) } }
    | "P1_STRIKE" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 1, kind := .combat { eventType := .gameAction, playerId := some 1, payload := some (.playCard 1002 (some 200)) } }
    | "P1_TWIN" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 1, kind := .combat { eventType := .gameAction, playerId := some 1, payload := some (.playCard 1003 (some 200)) } }
    | "P1_FPOT" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 1, kind := .combat { eventType := .gameAction, playerId := some 1, payload := some (.usePotion 0 (some 200)) } }
    | "P2_DEF" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 2, kind := .combat { eventType := .gameAction, playerId := some 2, payload := some (.playCard 2001 none) } }
    | "P2_STRIKEP" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 2, kind := .combat { eventType := .gameAction, playerId := some 2, payload := some (.playCard 2002 (some 200)) } }
    | "P2_UPPER" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 2, kind := .combat { eventType := .gameAction, playerId := some 2, payload := some (.playCard 2003 (some 200)) } }
    | "END_ROUND" => some { seqIdx := idx, roundNumber := 1, actorPlayerId := 1, kind := .endRoundAndRunEnemies }
    | _ => none
  let archive := buildArchive vanillaEffectEnv initSt evs stride 1
  let mid := evs.length / 2
  let s0 := seek vanillaEffectEnv archive 0
  let sMid := seek vanillaEffectEnv archive mid
  let sFin := seek vanillaEffectEnv archive evs.length
  let fullMid := replayEvents vanillaEffectEnv initSt (evs.take mid)
  let fullFin := replayEvents vanillaEffectEnv initSt evs
  let m0 := s0 == initSt && computeStateChecksum s0 == computeStateChecksum initSt
  let mm := sMid == fullMid && computeStateChecksum sMid == computeStateChecksum fullMid
  let mf := sFin == fullFin && computeStateChecksum sFin == computeStateChecksum fullFin
  let csum := computeStateChecksum fullFin
  let (eHp, p1Hp, p2Hp, p1E, p2E) := match fullFin.combat with
    | none => (0, 0, 0, 0, 0)
    | some c =>
        ( (c.findCreature 200).map Creature.currentHp |>.getD 0
        , (c.findCreature 101).map Creature.currentHp |>.getD 0
        , (c.findCreature 102).map Creature.currentHp |>.getD 0
        , ((c.findPlayer 1).bind Player.combatState).map PlayerCombatState.energy |>.getD 0
        , ((c.findPlayer 2).bind Player.combatState).map PlayerCombatState.energy |>.getD 0 )
  s!"{eHp},{p1Hp},{p2Hp},{p1E},{p2E}|{csum}|{if m0 then 1 else 0},{if mm then 1 else 0},{if mf then 1 else 0}"

private def evalTraceJson (fields : List String) : String :=
  let rawJson := fields[1]?.getD ""
  match parseTraceJson rawJson >>= fun b => (decodeArchiveBundle vanillaEffectEnv b).map (fun a => (b, a)) with
  | .error e => s!"ERR:{e}"
  | .ok (bundle, arch) =>
      let n := arch.events.length
      let mid := n / 2
      let s0 := seek vanillaEffectEnv arch 0
      let sMid := seek vanillaEffectEnv arch mid
      let sFin := seek vanillaEffectEnv arch n
      let c0 := computeStateChecksum s0
      let cMid := computeStateChecksum sMid
      let cFin := computeStateChecksum sFin
      let rtOk :=
        let rtJson := serializeTraceJson (encodeArchiveBundle arch bundle.keyframeStride) false
        match parseTraceJson rtJson >>= fun b2 => (decodeArchiveBundle vanillaEffectEnv b2).map (fun a2 => (b2, a2)) with
        | .error _ => false
        | .ok (b2, a2) =>
            let audit := verifyTraceChecksums vanillaEffectEnv a2 b2.expectedChecksums
            audit.allMatched &&
            computeStateChecksum (seek vanillaEffectEnv a2 0) == c0 &&
            computeStateChecksum (seek vanillaEffectEnv a2 mid) == cMid &&
            computeStateChecksum (seek vanillaEffectEnv a2 n) == cFin
      let (eHp, p1Hp, p2Hp, p1E, p2E) := match sFin.combat with
        | none => (0, 0, 0, 0, 0)
        | some c =>
            ( (c.findCreature 200).map Creature.currentHp |>.getD 0
            , (c.findCreature 101).map Creature.currentHp |>.getD 0
            , (c.findCreature 102).map Creature.currentHp |>.getD 0
            , ((c.findPlayer 1).bind Player.combatState).map PlayerCombatState.energy |>.getD 0
            , ((c.findPlayer 2).bind Player.combatState).map PlayerCombatState.energy |>.getD 0 )
      s!"{eHp},{p1Hp},{p2Hp},{p1E},{p2E}|{c0},{cMid},{cFin}|{if rtOk then 1 else 0}"

private def diffPowerTemplate (entry : String) (ownerId : CreatureId := 0) : PowerInstance :=
  match entry with
  | "VULNERABLE_POWER" | "WEAK_POWER" | "FRAIL_POWER" | "POISON_POWER" | "DOOM_POWER" =>
      { instanceId := 0, modelId := ModelId.mkPower entry, ownerId := ownerId
      , powerType := .debuff, stackType := .counter, allowNegative := false, amount := 1 }
  | "STRENGTH_POWER" | "DEXTERITY_POWER" | "FOCUS_POWER" =>
      { instanceId := 0, modelId := ModelId.mkPower entry, ownerId := ownerId
      , powerType := .buff, stackType := .counter, allowNegative := true, amount := 1 }
  | "BARRICADE_POWER" =>
      { instanceId := 0, modelId := ModelId.mkPower entry, ownerId := ownerId
      , powerType := .buff, stackType := .single, allowNegative := false, amount := 1 }
  | _ =>
      { instanceId := 0, modelId := ModelId.mkPower entry, ownerId := ownerId
      , powerType := .buff, stackType := .counter, allowNegative := false, amount := 1 }

private def parseDiffPowerList (s : String) (ownerId : CreatureId) (startInst : Nat) : List PowerInstance :=
  if s.trimAscii.isEmpty then []
  else
    let toks := (s.splitOn ",").map (fun x => x.trimAscii.toString) |>.filter (!·.isEmpty)
    toks.zipIdx.map fun (tok, i) =>
      let ps := tok.splitOn ":"
      let entry := ps[0]?.getD "STRENGTH_POWER"
      let amt := parseInt! (ps[1]?.getD "1")
      { diffPowerTemplate entry ownerId with instanceId := startInst + i, amount := amt }

private def formatDiffPowerList (pows : List PowerInstance) : String :=
  if pows.isEmpty then "-"
  else String.intercalate ";" (pows.map fun p =>
    s!"{p.modelId.entry}:{p.amount}:{if p.skipNextDurationTick then 1 else 0}")

private def orbKindTag : OrbKind → String
  | .lightning => "lightning"
  | .frost     => "frost"
  | .dark      => "dark"
  | .plasma    => "plasma"
  | .glass     => "glass"
  | .custom s  => s

private def parseDiffOrbs (s : String) (startInst : Nat) : List OrbInstance :=
  if s.trimAscii.isEmpty then []
  else
    let toks := (s.splitOn ",").map (fun x => x.trimAscii.toString) |>.filter (!·.isEmpty)
    toks.zipIdx.map fun (tok, i) =>
      let ps := tok.splitOn ":"
      let kdStr := ps[0]?.getD "lightning"
      let kd : OrbKind := match kdStr with
        | "frost"  => .frost
        | "dark"   => .dark
        | "plasma" => .plasma
        | "glass"  => .glass
        | _        => .lightning
      let baseO := OrbInstance.mkDefault (startInst + i) kd
      let pVal := match ps[1]? with | some v => Dec.ofInt (parseInt! v) | none => baseO.basePassive
      let eVal := match ps[2]? with | some v => Dec.ofInt (parseInt! v) | none => baseO.baseEvoke
      { baseO with basePassive := pVal, baseEvoke := eVal }

private def evalTurnLifecycle (fields : List String) : String :=
  let monsterMode := parseNat! (fields[1]?.getD "0")
  let p1Hp := parseNat! (fields[2]?.getD "80")
  let p1Blk := parseNat! (fields[3]?.getD "0")
  let p1Pows := parseDiffPowerList (fields[4]?.getD "") 101 10
  let p1Orbs := parseDiffOrbs (fields[5]?.getD "") 1
  let e1Hp := parseNat! (fields[6]?.getD "40")
  let e1Blk := parseNat! (fields[7]?.getD "0")
  let e1Pows := parseDiffPowerList (fields[8]?.getD "") 200 50
  let actsStr := fields[9]?.getD ""
  let acts := if actsStr.trimAscii.isEmpty then [] else (actsStr.splitOn ";").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let (mEntry, initMove) := match monsterMode with
    | 1 => ("LC_ATK_VULN", "HIT")
    | 2 => ("LC_RITUAL", "BUFF")
    | 3 => ("LC_DEBUFF", "HEX")
    | _ => ("LC_PASS", "NOP")
  let bp : MonsterBlueprint :=
    match monsterMode with
    | 1 =>
        { modelId := ModelId.mkMonster "LC_ATK_VULN"
        , stateMachine := { initialStateId := "HIT", currentStateId := "HIT", nodes := fun sid => if sid == "HIT" then some { id := "HIT", kind := .move "HIT" true false } else none }
        , moveEffects := fun _ => [.dealDamage .allAllies (Dec.ofInt 5) 1 DamageProps.monsterMove, .applyPower .allAllies (mkVulnerablePower 1) (Dec.ofInt 1)] }
    | 2 =>
        { modelId := ModelId.mkMonster "LC_RITUAL"
        , stateMachine :=
            { initialStateId := "BUFF", currentStateId := "BUFF"
            , nodes := fun sid =>
                if sid == "BUFF" then some { id := "BUFF", kind := .move "HIT" true true }
                else if sid == "HIT" then some { id := "HIT", kind := .move "HIT" true false }
                else none }
        , moveEffects := fun mid =>
            if mid == "BUFF" then [.applyPower .self (mkRitualPower 1) (Dec.ofInt 2)]
            else [.dealDamage .allAllies (Dec.ofInt 4) 1 DamageProps.monsterMove] }
    | 3 =>
        { modelId := ModelId.mkMonster "LC_DEBUFF"
        , stateMachine := { initialStateId := "HEX", currentStateId := "HEX", nodes := fun sid => if sid == "HEX" then some { id := "HEX", kind := .move "HEX" true false } else none }
        , moveEffects := fun _ => [.applyPower .allAllies (mkWeakPower 1) (Dec.ofInt 1), .applyPower .allAllies (mkFrailPower 1) (Dec.ofInt 1)] }
    | _ =>
        { modelId := ModelId.mkMonster "LC_PASS"
        , stateMachine := { initialStateId := "NOP", currentStateId := "NOP", nodes := fun sid => if sid == "NOP" then some { id := "NOP", kind := .move "NOP" true false } else none }
        , moveEffects := fun _ => [] }
  let lcEnv : EffectEnv := { tier1EffectEnv with monsterBlueprint := fun mid => if mid.entry == mEntry then some bp else none }
  let drawCards := (List.range 15).map fun i =>
    { instanceId := 1001 + i, modelId := ModelId.mkCard "STRIKE_IRONCLAD", ownerId := 1
    , cardType := .attack, rarity := .basic, targetType := .anyEnemy
    , energyCost := CardEnergyCost.mkCanonical 1 : CardInstance }
  let cP1 : Creature := { id := 101, modelId := ModelId.mkCharacter "DEFECT", side := .player, playerId := some 1, currentHp := p1Hp, maxHp := max 80 p1Hp, block := p1Blk, powers := p1Pows }
  let cE1 : Creature := { id := 200, modelId := ModelId.mkMonster mEntry, side := .enemy, currentHp := e1Hp, maxHp := max 80 e1Hp, block := e1Blk, powers := e1Pows, monster := some { modelId := ModelId.mkMonster mEntry, currentMoveId := initMove } }
  let cap := if p1Orbs.isEmpty then 3 else max 3 p1Orbs.length
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "DEFECT", baseOrbSlots := cap
    , combatState := some { energy := 3, baseMaxEnergy := 3, orbQueue := { capacity := cap, orbs := p1Orbs }, piles := { draw := drawCards } } }
  let cs0 : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , allies := [cP1], enemies := [cE1], players := [p1], rng := Rng.ofSeed 12345, nextInstanceId := 2000 }
  let csFinal := acts.foldl (fun s tok =>
    if !s.isInProgress then s
    else if tok == "P_STRIKE" then
      let (s1, _, _, _) := execEffectProgram lcEnv s (some 1) 101 (some 200) none 0 [] [.dealDamage .chosenTarget (Dec.ofInt 6) 1 DamageProps.card]
      (checkWinCondition (checkAllPlayersDead s1) (lcEnv.behaviorReg s1) []).1
    else if tok == "P_UNPOW" then
      let (s1, _, _, _) := execEffectProgram lcEnv s (some 1) 101 (some 200) none 0 [] [.dealDamage .chosenTarget (Dec.ofInt 6) 1 DamageProps.nonCardUnpowered]
      (checkWinCondition (checkAllPlayersDead s1) (lcEnv.behaviorReg s1) []).1
    else if tok.startsWith "P_VULN:" then
      let amt := parseInt! ((tok.splitOn ":")[1]?.getD "1")
      let (s1, _) := applyPower s (lcEnv.behaviorReg s) (mkVulnerablePower 1) 200 (Dec.ofInt amt) (some 101)
      s1
    else if tok == "END_ROUND" then
      (execEnemyTurnHeadless lcEnv s).1
    else s) cs0
  let cp1 := csFinal.findCreature 101
  let ce1 := csFinal.findCreature 200
  let pp1 := csFinal.findPlayer 1 |>.bind (·.combatState)
  let p1Eng := pp1.map (·.energy) |>.getD 0
  let orbsStr := match (pp1.map (·.orbQueue.orbs)).getD [] with
    | [] => "-"
    | os => String.intercalate ";" (os.map fun (o : OrbInstance) => s!"{orbKindTag o.kind}:{o.basePassive.truncate}:{o.baseEvoke.truncate}")
  s!"{cp1.map (·.currentHp) |>.getD 0},{cp1.map (·.block) |>.getD 0},{p1Eng},{formatDiffPowerList (cp1.map (·.powers) |>.getD [])}|{ce1.map (·.currentHp) |>.getD 0},{ce1.map (·.block) |>.getD 0},{if csFinal.isInProgress then 1 else 0},{formatDiffPowerList (ce1.map (·.powers) |>.getD [])}|{orbsStr}"

private def evalTier2Effects (fields : List String) : String :=
  let kind := fields[1]?.getD "CARD"
  let entry := fields[2]?.getD ""
  let param := parseNat! (fields[3]?.getD "0")
  let asc := parseNat! (fields[4]?.getD "0")
  let pStr := parseInt! (fields[5]?.getD "0")
  let eHp := max 1 (parseNat! (fields[6]?.getD "80"))
  let eBlk := parseNat! (fields[7]?.getD "0")
  let pPowsRaw := parseDiffPowerList (fields[8]?.getD "") 101 10
  let ePows := parseDiffPowerList (fields[9]?.getD "") 200 50
  let pPows := if pStr != 0 then { mkStrengthPower pStr 101 with instanceId := 9 } :: pPowsRaw else pPowsRaw
  let mkSimple (cid : Nat) (e : String) : CardInstance :=
    { instanceId := cid, modelId := ModelId.mkCard e, ownerId := 1
    , cardType := .attack, rarity := .basic, targetType := .anyEnemy
    , energyCost := CardEnergyCost.mkCanonical 1 }
  let initHand := (List.range 5).map fun i => mkSimple (1001 + i) "STRIKE_IRONCLAD"
  let initDraw := (List.range 10).map fun i => mkSimple (1011 + i) "DEFEND_IRONCLAD"
  let initDisc := (List.range 2).map fun i => mkSimple (1021 + i) "BASH"
  let cP1 : Creature := { id := 101, modelId := ModelId.mkCharacter "DEFECT", side := .player, playerId := some 1, currentHp := 70, maxHp := 80, powers := pPows }
  let cE1 : Creature :=
    { id := 200, modelId := ModelId.mkMonster (if kind == "MONSTER" then entry else "BIG_DUMMY"), side := .enemy
    , currentHp := eHp, maxHp := max 120 eHp, block := eBlk, powers := ePows
    , monster := if kind == "MONSTER" then some { modelId := ModelId.mkMonster entry } else none }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "DEFECT", baseOrbSlots := 3
    , combatState := some
        { energy := 5, baseMaxEnergy := 3, stars := 2, turnNumber := 1
        , orbQueue := { capacity := 3 }
        , piles := { hand := initHand, draw := initDraw, discard := initDisc } } }
  let cs0 : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , ascensionLevel := asc, allies := [cP1], enemies := [cE1], players := [p1]
    , rng := Rng.ofSeed 424242, nextInstanceId := 2000 }
  let csFinal :=
    if kind == "CARD" then
      let dummy : CardInstance :=
        { instanceId := 999, modelId := ModelId.mkCard entry, ownerId := 1
        , cardType := .attack, rarity := .common, targetType := .anyEnemy
        , energyCost := CardEnergyCost.mkCanonical 1, upgradeLevel := if param > 0 then 1 else 0 }
      let prog := fullVanillaEffectEnv.cardEffect dummy
      let (cs1, _, _, _) := execEffectProgram fullVanillaEffectEnv cs0 (some 1) 101 (some 200) (some dummy) 0 [] prog
      (checkWinCondition (checkAllPlayersDead cs1) (fullVanillaEffectEnv.behaviorReg cs1) []).1
    else if kind == "POTION" then
      let prog := fullVanillaEffectEnv.potionEffect (ModelId.mkPotion entry)
      let (cs1, _, _, _) := execEffectProgram fullVanillaEffectEnv cs0 (some 1) 101 (some 200) none 0 [] prog
      (checkWinCondition (checkAllPlayersDead cs1) (fullVanillaEffectEnv.behaviorReg cs1) []).1
    else if kind == "MONSTER" then
      let rounds := max 1 (min 5 param)
      (List.range rounds).foldl (fun s _ =>
        if !s.isInProgress then s else (execEnemyTurnHeadless fullVanillaEffectEnv s).1) cs0
    else cs0
  let cp1 := csFinal.findCreature 101
  let ce1 := csFinal.findCreature 200
  let pp1 := csFinal.findPlayer 1 |>.bind (·.combatState)
  let hand := pp1.map (·.piles.hand) |>.getD []
  let draw := pp1.map (·.piles.draw) |>.getD []
  let disc := pp1.map (·.piles.discard) |>.getD []
  let exh := pp1.map (·.piles.exhaust) |>.getD []
  let orbCnt := (pp1.map (·.orbQueue.orbs.length)).getD 0
  let eMove := (ce1.bind (·.monster)).map (·.currentMoveId) |>.getD ""
  let handStr := if hand.isEmpty then "-" else String.intercalate "," (hand.map (·.modelId.entry))
  let found := match kind with
    | "CARD" => allGeneratedCards.any (·.id == entry)
    | "POTION" => allGeneratedPotions.any (·.id == entry)
    | "MONSTER" => allGeneratedMonsters.any (·.id == entry)
    | _ => false
  s!"{cp1.map (·.currentHp) |>.getD 0},{cp1.map (·.block) |>.getD 0},{pp1.map (·.energy) |>.getD 0},{pp1.map (·.stars) |>.getD 0},{hand.length},{draw.length},{disc.length},{exh.length},{orbCnt},{csFinal.allies.length}|{ce1.map (·.currentHp) |>.getD 0},{ce1.map (·.block) |>.getD 0},{eMove},{if csFinal.isInProgress then 1 else 0}|{formatDiffPowerList (cp1.map (·.powers) |>.getD [])}|{formatDiffPowerList (ce1.map (·.powers) |>.getD [])}|{handStr}|found={if found then 1 else 0}"

private def evalTier2Card (fields : List String) : String := Id.run do
  let arg := fun i => fields[i]?.getD "-"
  let num := fun i => parseNat! (arg i)
  let mode := arg 1
  let entry := arg 2
  let ct := match arg 5 with | "attack" => CardType.attack | "power" => .power | _ => .skill
  let (tt, target) := match arg 6 with
    | "A" => (TargetType.anyAlly, 102)
    | "E" => (.anyEnemy, 200)
    | _ => (.self, 101)
  let card : CardInstance :=
    { instanceId := 999, modelId := ModelId.mkCard entry, ownerId := 1
      cardType := ct, rarity := .uncommon, targetType := tt, upgradeLevel := num 3
      keywords := if num 7 == 1 then [.exhaust] else []
      energyCost := CardEnergyCost.mkCanonical (Int.ofNat (num 4)) }
  let basic := fun id entry (ct : CardType) (cost : Int) =>
    { instanceId := id, modelId := ModelId.mkCard entry, ownerId := 1
      cardType := ct, rarity := .basic, targetType := if ct == .attack then .anyEnemy else .self
      energyCost := CardEnergyCost.mkCanonical cost : CardInstance }
  let tail := (if entry == "MODDED" then [{ card with instanceId := 998 }] else []) ++
    (match arg 12 with
      | "skill" => [basic 1001 "DEFEND_IRONCLAD" .skill 1]
      | "attack" => [basic 1001 "STRIKE_IRONCLAD" .attack 1]
      | _ => [])
  let draw := (List.range 7).map (fun i => basic (1011 + i) "DEFEND_IRONCLAD" .skill 1)
  let discard := (List.range (num 11)).map (fun i => basic (1021 + i) "BASH" .attack 2)
  let powers := fun i cid id => if arg i == "-" then [] else parseDiffPowerList (arg i) cid id
  let begin (fresh : Bool) (hp allyHp : Nat) : CombatState :=
    let pc : Creature :=
      { id := 101, modelId := ModelId.mkCharacter "DEFECT", side := .player, playerId := some 1
        currentHp := hp, maxHp := 80, block := if fresh then 0 else num 9
        powers := if fresh then [] else powers 15 101 10 }
    let ally : Creature :=
      { id := 102, modelId := ModelId.mkCharacter "SILENT", side := .player, playerId := some 2
        currentHp := allyHp, maxHp := 80, block := if fresh then 0 else num 10
        powers := if fresh then [] else powers 16 102 30 }
    let m := ModelId.mkMonster (if mode == "ROUND" then "LC_PASS" else "BIG_DUMMY")
    let enemyHp := if mode == "NEXT" && !fresh then 6 else 80
    let enemy : Creature :=
      { id := 200, modelId := m, side := .enemy, currentHp := enemyHp, maxHp := enemyHp
        powers := if fresh then [] else powers 17 200 50
        monster := some { modelId := m, currentMoveId := "PASS" } }
    let player : Player :=
      { playerId := 1, creatureId := 101, characterId := pc.modelId
        combatState := some
          { energy := if fresh then 3 else num 8
            orbQueue :=
              { capacity := if fresh then 3 else num 13
                orbs := if fresh || arg 14 == "-" then [] else parseDiffOrbs (arg 14) 1 }
            piles := { hand := card :: tail, draw := draw, discard := discard } } }
    let other : Player :=
      { playerId := 2, creatureId := 102, characterId := ally.modelId
        combatState := some { energy := 3 } }
    { allies := [pc, ally], enemies := [enemy], players := [player, other]
      rng := Rng.ofSeed 424242, nextInstanceId := 2000 }
  let pass : MonsterBlueprint :=
    { modelId := ModelId.mkMonster "LC_PASS"
      stateMachine :=
        { initialStateId := "PASS", currentStateId := "PASS"
          nodes := fun _ => some {id := "PASS", kind := .move "PASS" true false} }
      moveEffects := fun _ => [] }
  let env := { fullVanillaEffectEnv with monsterBlueprint := fun _ => some pass }
  let cs := begin false 70 70
  let some ops := lookupGeneratedCard entry (num 3 > 0) | return s!"MISSING_GENERATED_CARD:{entry}"
  let (ok, played) := if mode == "EFFECT" then
    let ready := cs.updatePlayer 1 fun p => { p with combatState := p.combatState.map fun pcs =>
      { pcs with piles := { pcs.piles with hand := tail, play := [card] } } }
    (true, (execEffectProgram env ready (some 1) 101 (some target) (some card) 0 [] ops).1)
  else
    let r := execPlayCardHeadless env cs 1 999 (some target)
    (r.accepted && r.pending.isNone, r.combat)
  let value := fun (s : CombatState) id => (s.findCreature id).getD default
  let mut result := played
  if ok && mode == "NEXT" then
    let win := execPlayCardHeadless env played 1 1001 (some 200)
    unless win.outcome == .victory do return "NEXT_DID_NOT_WIN"
    result := begin true (value win.combat 101).currentHp (value win.combat 102).currentHp
  else if ok && mode == "ROUND" then
    result := (execEnemyTurnHeadless env played).1
  let p := (result.findPlayer 1 |>.bind (·.combatState)).getD default
  let me := value result 101
  let ally := value result 102
  let enemy := value result 200
  let joined := fun (xs : List String) => if xs.isEmpty then "-" else String.intercalate "," xs
  let pile := fun (xs : List CardInstance) =>
    joined (xs.map fun c => s!"{c.instanceId}:{c.energyCost.getWithModifiers c.isCanonical}")
  return String.intercalate "|"
    [ if ok then "1" else "0", s!"{me.currentHp},{me.block},{p.energy},{p.orbQueue.capacity}"
    , s!"{ally.currentHp},{ally.block}", s!"{enemy.currentHp},{enemy.block}"
    , formatDiffPowerList me.powers, formatDiffPowerList ally.powers, formatDiffPowerList enemy.powers
    , joined (p.orbQueue.orbs.map (fun o => orbKindTag o.kind))
    , pile p.piles.hand, pile p.piles.draw, pile p.piles.discard, pile p.piles.exhaust, pile p.piles.play ]

private def evalDiffLine (line : String) : String :=
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then ""
  else
    let fields := trimmed.splitOn "\t"
    match fields[0]? with
    | some "RNG_SEQ"        => evalRngSeq (fields[1]?.getD "0") (fields[2]?.getD "0")
    | some "RNG_SHUFFLE"    => evalRngShuffle (fields[1]?.getD "0") (fields[2]?.getD "")
    | some "DMG_PIPE"       => evalDmgPipe fields
    | some "BLK_PIPE"       => evalBlkPipe fields
    | some "CREATURE_DMG"   => evalCreatureDmg fields
    | some "POWER_STACK"    => evalPowerStack fields
    | some "CARD_COST"      => evalCardCost fields
    | some "RARITY_ODDS"    => evalRarityOdds fields
    | some "MOD_SORT"       => evalModSort fields
    | some "QUEUE_SET"      => evalQueueSet fields
    | some "TIMELINE_SEEK"  => evalTimelineSeek fields
    | some "TRACE_JSON"     => evalTraceJson fields
    | some "TURN_LIFECYCLE" => evalTurnLifecycle fields
    | some "TIER2_EFFECTS"  => evalTier2Effects fields
    | some "TIER2_CARD"     => evalTier2Card fields
    | some "EXPEDITION"     => expeditionReferenceProjection
    | _                     => s!"UNKNOWN_OP:{fields[0]?.getD ""}"

private structure InspectOpts where
  seekStep : Option Nat := none
  viewerId : Option PlayerId := none
  doVerify : Bool := false

private def parseInspectOpts (args : List String) (acc : InspectOpts := {}) : Except String InspectOpts :=
  match args with
  | [] => .ok acc
  | "--verify" :: rest => parseInspectOpts rest { acc with doVerify := true }
  | "--seek" :: kStr :: rest =>
      match kStr.toNat? with
      | some k => parseInspectOpts rest { acc with seekStep := some k }
      | none   => .error s!"Invalid --seek step: {kStr}"
  | "--viewer" :: vStr :: rest =>
      match vStr.toNat? with
      | some v => parseInspectOpts rest { acc with viewerId := some v }
      | none   => .error s!"Invalid --viewer playerId: {vStr}"
  | flag :: _ => .error s!"Unknown --inspect option: {flag}"

private def runInspectCommand (tracePath : String) (optArgs : List String) : IO UInt32 := do
  match parseInspectOpts optArgs with
  | .error e =>
      IO.eprintln s!"Error: {e}"
      return 2
  | .ok opts =>
      let raw ← IO.FS.readFile tracePath
      match parseTraceJson raw with
      | .error e =>
          IO.eprintln s!"Trace JSON parse error: {e}"
          return 1
      | .ok bundle =>
          match decodeArchiveBundle fullVanillaEffectEnv bundle with
          | .error e =>
              IO.eprintln s!"Trace bundle decode error: {e}"
              return 1
          | .ok baseArch =>
              let arch := match opts.viewerId with
                | some v => switchViewer baseArch v
                | none   => baseArch
              let mut exitCode : UInt32 := 0
              if opts.doVerify then
                let audit := verifyTraceChecksums fullVanillaEffectEnv arch bundle.expectedChecksums
                IO.println s!"ChecksumsVerified={audit.allMatched} (checked={audit.totalChecked}, mismatches={audit.mismatches.length})"
                if !audit.allMatched then
                  for m in audit.mismatches do
                    IO.eprintln s!"  Checksum mismatch at step #{m.eventIndex}: expected={m.expected}, actual={m.actual}"
                  exitCode := 1
              match opts.seekStep with
              | some k => IO.println (inspectArchiveStep fullVanillaEffectEnv arch k)
              | none   => IO.println (formatTimelineSummary fullVanillaEffectEnv arch)
              return exitCode

private def runRegressionSuite : IO UInt32 := do
  let catalogTests : List (String × Bool) :=
    [ ("catalog_cards_717", allCards.length == 717)
    , ("catalog_relics_316", allRelics.length == 316)
    , ("catalog_powers_304", allPowers.length == 304)
    , ("tier2_cards_373", allGeneratedCards.length == 373)
    , ("tier2_potions_36", allGeneratedPotions.length == 36)
    , ("tier2_monsters_19", allGeneratedMonsters.length == 19) ]
  let suite :=
    allVanillaTests ++ allModTemplateTests ++ catalogTests ++ allTimelineTests ++
      allReplayAnalyzerExampleTests ++ allExpeditionTests
  let mut failed : Nat := 0
  for (name, ok) in suite do
    if ok then
      IO.println s!"[PASS] {name}"
    else
      IO.println s!"[FAIL] {name}"
      failed := failed + 1
  IO.println s!"Summary: {suite.length - failed}/{suite.length} tests passed (failed={failed})"
  return if failed == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--diff", path] =>
      let content ← IO.FS.readFile path
      let lines := content.splitOn "\n"
      for line in lines do
        let t := line.trimAscii.toString
        if !t.isEmpty then
          IO.println (evalDiffLine t)
      return 0
  | ["--timeline-demo"] =>
      IO.println runLateVulnerableDemo
      return 0
  | ["--export-sample-trace", outPath] =>
      IO.FS.writeFile outPath (serializeTraceJson sampleTraceBundle true)
      IO.println s!"Exported sample trace bundle (schemaVersion={traceSchemaVersion}) to {outPath}"
      return 0
  | ["--observe-combat", path] =>
      Sts2Sim.ObservedCombat.run path
  | ["--audit-run-history", path] =>
      Sts2Sim.RunHistoryAudit.run path
  | ["--audit-act-map", path] =>
      Sts2Sim.ActMapAudit.run path
  | "--inspect" :: tracePath :: rest =>
      runInspectCommand tracePath rest
  | _ =>
      runRegressionSuite

/-
  Executable Simulator & `.NET 9` Differential Test Runner (`lake exe sts2sim`).
  Modes:
    1. Default (`lake exe sts2sim`):
       Runs all 49 executable assertions (30 Vanilla + 4 ModTemplates + 3 Catalog + 10 Timeline + 2 ReplayAnalyzerExample), exits 0 iff 100% pass.
    2. Timeline demo (`lake exe sts2sim --timeline-demo`):
       Prints the headless multiplayer timeline reconstruction & downstream analyzer example report.
    3. Export sample JSON trace (`lake exe sts2sim --export-sample-trace <out.json>`):
       Serializes a versioned `WireTraceBundle` (`schemaVersion = 1`) for external/C# consumption.
    4. Inspect / verify external JSON trace (`lake exe sts2sim --inspect <trace.json> [--seek <k>] [--viewer <pid>] [--verify]`):
       Reconstructs timeline state headlessly, switches viewer, and verifies FNV-1a checksums.
    5. Differential oracle mode (`lake exe sts2sim --diff <input.tsv>`):
       Evaluates all 12 deterministic test families row-by-row for comparison with `DiffTest/Sts2Oracle`.
-/
import Sts2Model

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

private def evalDiffLine (line : String) : String :=
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then ""
  else
    let fields := trimmed.splitOn "\t"
    match fields[0]? with
    | some "RNG_SEQ"       => evalRngSeq (fields[1]?.getD "0") (fields[2]?.getD "0")
    | some "RNG_SHUFFLE"   => evalRngShuffle (fields[1]?.getD "0") (fields[2]?.getD "")
    | some "DMG_PIPE"      => evalDmgPipe fields
    | some "BLK_PIPE"      => evalBlkPipe fields
    | some "CREATURE_DMG"  => evalCreatureDmg fields
    | some "POWER_STACK"   => evalPowerStack fields
    | some "CARD_COST"     => evalCardCost fields
    | some "RARITY_ODDS"   => evalRarityOdds fields
    | some "MOD_SORT"      => evalModSort fields
    | some "QUEUE_SET"     => evalQueueSet fields
    | some "TIMELINE_SEEK" => evalTimelineSeek fields
    | some "TRACE_JSON"    => evalTraceJson fields
    | _                    => s!"UNKNOWN_OP:{fields[0]?.getD ""}"

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
          match decodeArchiveBundle vanillaEffectEnv bundle with
          | .error e =>
              IO.eprintln s!"Trace bundle decode error: {e}"
              return 1
          | .ok baseArch =>
              let arch := match opts.viewerId with
                | some v => switchViewer baseArch v
                | none   => baseArch
              let mut exitCode : UInt32 := 0
              if opts.doVerify then
                let audit := verifyTraceChecksums vanillaEffectEnv arch bundle.expectedChecksums
                IO.println s!"ChecksumsVerified={audit.allMatched} (checked={audit.totalChecked}, mismatches={audit.mismatches.length})"
                if !audit.allMatched then
                  for m in audit.mismatches do
                    IO.eprintln s!"  Checksum mismatch at step #{m.eventIndex}: expected={m.expected}, actual={m.actual}"
                  exitCode := 1
              match opts.seekStep with
              | some k => IO.println (inspectArchiveStep vanillaEffectEnv arch k)
              | none   => IO.println (formatTimelineSummary vanillaEffectEnv arch)
              return exitCode

private def runRegressionSuite : IO UInt32 := do
  let catalogTests : List (String × Bool) :=
    [ ("catalog_cards_717", allCards.length == 717)
    , ("catalog_relics_316", allRelics.length == 316)
    , ("catalog_powers_304", allPowers.length == 304) ]
  let suite :=
    allVanillaTests ++ allModTemplateTests ++ catalogTests ++ allTimelineTests ++
      allReplayAnalyzerExampleTests
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
  | "--inspect" :: tracePath :: rest =>
      runInspectCommand tracePath rest
  | _ =>
      runRegressionSuite

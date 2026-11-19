/-
  Executable Simulator & `.NET 9` Differential Test Runner (`lake exe sts2sim`).
  Modes:
    1. Default (`lake exe sts2sim`):
       Runs all 30 VanillaShowcase tests + 4 ModTemplate tests + Catalog checks, exits 0 iff 100% pass.
    2. Differential oracle mode (`lake exe sts2sim --diff <input.tsv>`):
       Evaluates all 9 deterministic test families row-by-row for comparison with `DiffTest/Sts2Oracle`.
-/
import Sts2Model

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command
open Sts2Model.Combat
open Sts2Model.Mechanics
open Sts2Model.Run
open Sts2Model.Catalog
open Sts2Model.Examples

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

private def evalDiffLine (line : String) : String :=
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then ""
  else
    let fields := trimmed.splitOn "\t"
    match fields[0]? with
    | some "RNG_SEQ"      => evalRngSeq (fields[1]?.getD "0") (fields[2]?.getD "0")
    | some "RNG_SHUFFLE"  => evalRngShuffle (fields[1]?.getD "0") (fields[2]?.getD "")
    | some "DMG_PIPE"     => evalDmgPipe fields
    | some "BLK_PIPE"     => evalBlkPipe fields
    | some "CREATURE_DMG" => evalCreatureDmg fields
    | some "POWER_STACK"  => evalPowerStack fields
    | some "CARD_COST"    => evalCardCost fields
    | some "RARITY_ODDS"  => evalRarityOdds fields
    | some "MOD_SORT"     => evalModSort fields
    | _                   => s!"UNKNOWN_OP:{fields[0]?.getD ""}"

private def runRegressionSuite : IO UInt32 := do
  let catalogTests : List (String × Bool) :=
    [ ("catalog_cards_717", allCards.length == 717)
    , ("catalog_relics_316", allRelics.length == 316)
    , ("catalog_powers_304", allPowers.length == 304) ]
  let suite := allVanillaTests ++ allModTemplateTests ++ catalogTests
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
  | _ =>
      runRegressionSuite

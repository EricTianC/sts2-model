/-
  STANDALONE DOWNSTREAM EXAMPLE (Non-Core Reference Project)
  ==========================================================
  This file demonstrates how a third-party Modder or replay-analysis tool can be built
  independently ON TOP OF the public `Sts2Model.Replay.Timeline` & `Sts2Model.Sim.VanillaEffects`
  APIs without embedding application-specific heuristics or solvers into the core STS2 model.

  Included downstream utilities & example formal verification:
  1. Post-mortem missed-Vulnerable causal query over `TimedCombatHistoryEntry` & `DamageAttribution`
  2. Application-specific enemy/team HP diff wrapper built over core `seek` + `forkTimeline`
  3. Bounded depth-limited co-op turn lethality search (`findLethalActionOrder`)
  4. Pure-kernel witness theorem (`late_vulnerable_counterfactual_witness`) and CLI demo
-/
import Sts2Model.Replay.Timeline
import Sts2Model.Sim.VanillaEffects
import Sts2Model.Proofs.ReplayTimeline

namespace Sts2Model.Examples.ReplayAnalyzer

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Command
open Sts2Model.Combat
open Sts2Model.Multiplayer
open Sts2Model.Sim
open Sts2Model.Replay
open Sts2Model.Proofs

-- ============================================================================
-- 1. Example Downstream Query: Missed-Vulnerable Causal Attribution
-- ============================================================================

structure MissedVulnerableHit where
  stepIdx              : Nat
  dealerId             : Option CreatureId
  cardModelId          : Option ModelId
  actualDamage         : Nat
  counterfactualDamage : Nat
  missedDamage         : Nat
  deriving Repr, DecidableEq, Inhabited

structure MissedVulnerableReport where
  round                : Nat
  targetId             : CreatureId
  vulnerableApplied    : Bool
  targetRemainingHp    : Nat
  hitsBeforeVulnerable : List MissedVulnerableHit
  totalMissedDamage    : Nat
  wouldCloseHpGap      : Bool
  deriving Repr, DecidableEq, Inhabited

def vulnerableMultiplier (paperPhrog : Bool) : Dec :=
  if paperPhrog then Dec.ofScaled 175 2 else Dec.ofScaled 15 1

/-- Compute counterfactual integer damage if `VULNERABLE_POWER` had already been active
    during `attr` (preserving Strength, Weak, PaperPhrog, and Unpowered flags). -/
def computeVulnerableCounterfactualDamage (attr : DamageAttribution) : Nat :=
  let actual := attr.modifiedDamage.toNat
  if !attr.props.isPoweredAttack || attr.targetVulnerable then
    actual
  else
    let factor := vulnerableMultiplier attr.paperPhrog
    (Dec.maxZero (Dec.mul attr.modifiedDamage factor)).toNat

/-- Query generic `st.combatHistory : List TimedCombatHistoryEntry` and `st.attributions`
    to find powered attacks on `targetId` in `round` that executed strictly before the
    first `VULNERABLE_POWER` application step. -/
def analyzeMissedVulnerable (st : TimelineState) (round : Nat) (targetId : CreatureId) :
    MissedVulnerableReport :=
  let vulnSteps : List Nat :=
    st.combatHistory.filterMap fun te =>
      match te.entry with
      | .powerReceived r _ mid tid _ amt =>
          if r == round && mid == ModelId.mkPower "VULNERABLE_POWER" && tid == targetId && amt > 0 then
            some te.stepIdx
          else none
      | _ => none
  let firstVulnStep : Option Nat :=
    vulnSteps.foldl (fun acc s =>
      match acc with
      | none   => some s
      | some m => some (min m s)) none
  let vulnApplied := firstVulnStep.isSome
  let candidateAttrs :=
    match firstVulnStep with
    | none => []
    | some vStep =>
        st.attributions.filter fun (a : DamageAttribution) =>
          a.round == round && a.targetId == targetId && a.props.isPoweredAttack &&
          !a.targetVulnerable && a.stepIdx < vStep
  let hits := candidateAttrs.filterMap fun (a : DamageAttribution) =>
    let act := a.modifiedDamage.toNat
    let cf := computeVulnerableCounterfactualDamage a
    let diff := cf - act
    if diff > 0 then
      some { stepIdx := a.stepIdx
           , dealerId := a.dealerId
           , cardModelId := a.cardModelId
           , actualDamage := act
           , counterfactualDamage := cf
           , missedDamage := diff }
    else none
  let totalMissed := hits.foldl (fun acc h => acc + h.missedDamage) 0
  let remHp :=
    match st.combat.bind (·.findCreature targetId) with
    | some c => c.currentHp
    | none   => 0
  { round := round
  , targetId := targetId
  , vulnerableApplied := vulnApplied
  , targetRemainingHp := remHp
  , hitsBeforeVulnerable := hits
  , totalMissedDamage := totalMissed
  , wouldCloseHpGap := vulnApplied && remHp > 0 && totalMissed ≥ remHp }

-- ============================================================================
-- 2. Application-Specific Outcome Projection Over Core `forkTimeline`
-- ============================================================================

structure CounterfactualDiff where
  branchIdx          : Nat
  origEnemyTotalHp   : Nat
  altEnemyTotalHp    : Nat
  enemyHpDelta       : Int
  origAllEnemiesDead : Bool
  altAllEnemiesDead  : Bool
  origTeamTotalHp    : Nat
  altTeamTotalHp     : Nat
  origState          : TimelineState
  altState           : TimelineState
  deriving Repr, DecidableEq

def totalHpOfList (cs : List Creature) : Nat :=
  cs.foldl (fun acc c => acc + c.currentHp) 0

def combatEnemiesTotalHp : Option CombatState → Nat
  | none    => 0
  | some cs => totalHpOfList cs.enemies

def combatAlliesTotalHp : Option CombatState → Nat
  | none    => 0
  | some cs => totalHpOfList cs.allies

def combatAllEnemiesDead : Option CombatState → Bool
  | none    => true
  | some cs => cs.enemies.all (·.isDead)

/-- Seek `archive` to `origEndIdx` and fork via core `forkTimeline` at `branchIdx`
    with alternative suffix `altEvents`, projecting team/enemy HP totals. -/
def branchCounterfactual (env : EffectEnv) (archive : TimelineArchive)
    (branchIdx : Nat) (origEndIdx : Nat) (altEvents : List TimelineEvent) :
    CounterfactualDiff :=
  let origState := seek env archive origEndIdx
  let altState := forkTimeline env archive branchIdx altEvents
  let origE := combatEnemiesTotalHp origState.combat
  let altE := combatEnemiesTotalHp altState.combat
  { branchIdx := branchIdx
  , origEnemyTotalHp := origE
  , altEnemyTotalHp := altE
  , enemyHpDelta := (altE : Int) - (origE : Int)
  , origAllEnemiesDead := combatAllEnemiesDead origState.combat
  , altAllEnemiesDead := combatAllEnemiesDead altState.combat
  , origTeamTotalHp := combatAlliesTotalHp origState.combat
  , altTeamTotalHp := combatAlliesTotalHp altState.combat
  , origState := origState
  , altState := altState }

-- ============================================================================
-- 3. Example Downstream Solver: Bounded Co-op Turn Lethality Search
-- ============================================================================

structure CandidatePlay where
  playerId : PlayerId
  cardId   : CardInstanceId
  targetId : Option CreatureId := none
  deriving Repr, DecidableEq, Inhabited

def allEnemiesDead (cs : CombatState) : Bool :=
  cs.enemies.all (·.isDead)

def removeNth {α : Type} (idx : Nat) : List α → List α
  | [] => []
  | x :: xs =>
      match idx with
      | 0     => xs
      | n + 1 => x :: removeNth n xs

def searchLethalFuel (fuel : Nat) (env : EffectEnv) (cs : CombatState)
    (candidates : List CandidatePlay) (acc : List CandidatePlay) :
    Option (List CandidatePlay × CombatState) :=
  if allEnemiesDead cs then
    some (acc, cs)
  else
    match fuel with
    | 0 => none
    | k + 1 =>
        let rec tryIdx (idx : Nat) : List CandidatePlay → Option (List CandidatePlay × CombatState)
          | [] => none
          | cand :: rest =>
              let (cs', ok, _, _, _) :=
                execPlayCardHeadless env cs cand.playerId cand.cardId cand.targetId acc.length []
              let resOpt :=
                if ok then
                  let rem := removeNth idx candidates
                  searchLethalFuel k env cs' rem (acc ++ [cand])
                else none
              match resOpt with
              | some sol => some sol
              | none => tryIdx (idx + 1) rest
        tryIdx 0 candidates

def findLethalActionOrder (env : EffectEnv) (cs : CombatState)
    (candidates : List CandidatePlay) (maxDepth : Nat := 6) :
    Option (List CandidatePlay × CombatState) :=
  searchLethalFuel maxDepth env cs candidates []

-- ============================================================================
-- 4. Self-Contained Verification Fixture, Kernel Witness Theorem & Demo
-- ============================================================================

def bashCardWitness : CardInstance :=
  { instanceId := 1001, modelId := ModelId.mkCard "BASH", ownerId := 1
  , cardType := .attack, rarity := .basic, targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 2 }

def twinStrikeCardWitness : CardInstance :=
  { instanceId := 2001, modelId := ModelId.mkCard "TWIN_STRIKE", ownerId := 2
  , cardType := .attack, rarity := .common, targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 1 }

def strikePlusCardWitness : CardInstance :=
  { instanceId := 2002, modelId := ModelId.mkCard "STRIKE_IRONCLAD", ownerId := 2
  , cardType := .attack, rarity := .basic, targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 1, upgradeLevel := 1 }

def coopGuardianWitness : Creature :=
  { id := 200, modelId := ModelId.mkMonster "COOP_GUARDIAN", side := .enemy
  , currentHp := 34, maxHp := 34
  , monster := some { modelId := ModelId.mkMonster "COOP_GUARDIAN", currentMoveId := "SLAM" } }

def lateVulnInit : TimelineState :=
  let cP1 : Creature :=
    { id := 101, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1
    , currentHp := 80, maxHp := 80 }
  let cP2 : Creature :=
    { id := 102, modelId := ModelId.mkCharacter "SILENT", side := .player, playerId := some 2
    , currentHp := 70, maxHp := 70 }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "IRONCLAD"
    , combatState := some { energy := 3, piles := { hand := [bashCardWitness] } } }
  let p2 : Player :=
    { playerId := 2, creatureId := 102, characterId := ModelId.mkCharacter "SILENT"
    , combatState := some { energy := 3, piles := { hand := [twinStrikeCardWitness, strikePlusCardWitness] } } }
  let cs : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , allies := [cP1, cP2], enemies := [coopGuardianWitness], players := [p1, p2]
    , rng := Rng.ofSeed 42 }
  { combat := some cs
  , queueSet := (ActionQueueSet.init [1, 2]).combatStarted
  , choiceSync := PlayerChoiceSynchronizer.init [1, 2] }

def mkPlayEv (seqIdx : Nat) (pid : PlayerId) (cid : CardInstanceId) (tid : CreatureId) : TimelineEvent :=
  { seqIdx := seqIdx, actIndex := 0, floor := 1, roundNumber := 1, actorPlayerId := pid
  , kind := .combat { eventType := .gameAction, playerId := some pid, payload := some (.playCard cid (some tid)) } }

/-- Original sequence: P2 attacks BEFORE P1 Bash -> `5+5+9+8 = 27` dmg, Enemy 200 survives at 7 HP. -/
def lateVulnOrigEvents : List TimelineEvent :=
  [ mkPlayEv 0 2 2001 200
  , mkPlayEv 1 2 2002 200
  , mkPlayEv 2 1 1001 200 ]

/-- Counterfactual sequence: P1 Bash FIRST -> `8 + floor(5*1.5)*2 + floor(9*1.5) = 35` dmg, Lethal! -/
def lateVulnAltEvents : List TimelineEvent :=
  [ mkPlayEv 0 1 1001 200
  , mkPlayEv 1 2 2001 200
  , mkPlayEv 2 2 2002 200 ]

def lateVulnOrigArchiveNoKf : TimelineArchive :=
  { initialState := lateVulnInit, events := lateVulnOrigEvents, keyframes := [] }

/-- Example downstream theorem proved in pure Lean 4 kernel (`decide`):
    switching play order to apply `BASH` first flips the outcome from 7 HP survivor to lethal. -/
theorem late_vulnerable_counterfactual_witness :
    let diff := branchCounterfactual vanillaEffectEnv lateVulnOrigArchiveNoKf 0 3 lateVulnAltEvents
    let report := analyzeMissedVulnerable diff.origState 1 200
    diff.origAllEnemiesDead = false ∧
    diff.origEnemyTotalHp = 7 ∧
    diff.altAllEnemiesDead = true ∧
    diff.altEnemyTotalHp = 0 ∧
    report.totalMissedDamage = 8 ∧
    report.wouldCloseHpGap = true := by
  decide

def example_replay_01_late_vulnerable_attribution : Bool :=
  let archive := buildArchive vanillaEffectEnv lateVulnInit lateVulnOrigEvents 1 1
  let diff := branchCounterfactual vanillaEffectEnv archive 0 3 lateVulnAltEvents
  let report := analyzeMissedVulnerable diff.origState 1 200
  report.vulnerableApplied &&
  report.targetRemainingHp == 7 &&
  report.hitsBeforeVulnerable.length == 3 &&
  report.totalMissedDamage == 8 &&
  report.wouldCloseHpGap &&
  !diff.origAllEnemiesDead &&
  diff.origEnemyTotalHp == 7 &&
  diff.altAllEnemiesDead &&
  diff.altEnemyTotalHp == 0 &&
  diff.enemyHpDelta == -7

def example_replay_02_bounded_turn_solver : Bool :=
  match lateVulnInit.combat with
  | none => false
  | some cs =>
      let cands : List CandidatePlay :=
        [ { playerId := 2, cardId := 2001, targetId := some 200 }
        , { playerId := 2, cardId := 2002, targetId := some 200 }
        , { playerId := 1, cardId := 1001, targetId := some 200 } ]
      match findLethalActionOrder vanillaEffectEnv cs cands 4 with
      | none => false
      | some (seq, csFinal) =>
          allEnemiesDead csFinal &&
          (seq.head?.map (·.cardId) == some 1001) &&
          seq.length == 3

def allReplayAnalyzerExampleTests : List (String × Bool) :=
  [ ("example_replay_01_late_vulnerable_attribution", example_replay_01_late_vulnerable_attribution)
  , ("example_replay_02_bounded_turn_solver", example_replay_02_bounded_turn_solver) ]

/-- Human-readable downstream CLI demo demonstrating core timeline reconstruction +
    independent post-mortem analysis, What-If branching via `forkTimeline`, and turn solver. -/
def runLateVulnerableDemo : String :=
  let archive := buildArchive vanillaEffectEnv lateVulnInit lateVulnOrigEvents 1 1
  let summaryP1 := formatTimelineSummary vanillaEffectEnv archive
  let summaryP2 := formatTimelineSummary vanillaEffectEnv (switchViewer archive 2)
  let diff := branchCounterfactual vanillaEffectEnv archive 0 3 lateVulnAltEvents
  let report := analyzeMissedVulnerable diff.origState 1 200
  let hitLines := report.hitsBeforeVulnerable.map fun h =>
    s!"    - Step #{h.stepIdx} Card={h.cardModelId.map (·.entry) |>.getD "?"}: actual={h.actualDamage}, withVuln={h.counterfactualDamage}, missed={h.missedDamage}"
  let solverLine :=
    match lateVulnInit.combat.bind fun cs =>
        findLethalActionOrder vanillaEffectEnv cs
          [ { playerId := 2, cardId := 2001, targetId := some 200 }
          , { playerId := 2, cardId := 2002, targetId := some 200 }
          , { playerId := 1, cardId := 1001, targetId := some 200 } ] 4 with
    | none => "  No lethal sequence found"
    | some (seq, _) =>
        let stepsStr := String.intercalate " -> " (seq.map fun s => s!"P{s.playerId}:card#{s.cardId}")
        s!"  Lethal sequence found: {stepsStr}"
  String.intercalate "\n"
    [ "=== STS2 Headless Multiplayer Timeline Demo (Core Engine + Downstream Analyzer Example) ==="
    , "[1] Timeline Reconstruction (Viewer = Player 1):"
    , summaryP1
    , "[2] Perspective Switch Verification (Viewer = Player 2, same shared checksums):"
    , summaryP2
    , s!"[3] [Downstream Example] Post-Mortem Causal Attribution (Round {report.round}, Target #{report.targetId}):"
    , s!"  VulnerableApplied={report.vulnerableApplied}, RemainingHP={report.targetRemainingHp}, TotalMissedDamage={report.totalMissedDamage}, WouldCloseGap={report.wouldCloseHpGap}"
    , String.intercalate "\n" hitLines
    , "[4] [Downstream Example] Counterfactual Branching (What-If P1 Bash First via Core forkTimeline):"
    , s!"  OrigEnemyHP={diff.origEnemyTotalHp} (Dead={diff.origAllEnemiesDead}) vs AltEnemyHP={diff.altEnemyTotalHp} (Dead={diff.altAllEnemiesDead}), Delta={diff.enemyHpDelta}"
    , "[5] [Downstream Example] Bounded Turn Lethality Solver:"
    , solverLine ]

end Sts2Model.Examples.ReplayAnalyzer
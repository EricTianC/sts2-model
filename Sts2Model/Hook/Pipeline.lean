/-
  Exact Hook pipelines matching `Core.Hooks/Hook.cs`:
  - `ModifyDamage` / `ModifyDamageInternal` (Enchantment -> Additive -> Multiplicative -> MultiplicativeLate -> Cap -> maxZero)
  - `ModifyBlock` (Enchantment -> Additive -> Multiplicative -> maxZero)
  - `ModifyHpLost` (`BeforeOsty` / `BeforeOstyLate` / `AfterOsty` / `AfterOstyLate`, truncated delta tracking)
  - `ModifyEnergyCostInCombat`
  - `ModifyPowerAmountGiven` / `ModifyPowerAmountReceived`
  - `ModifyPreBlockDamageTarget` / `ModifyUnblockedDamageTarget`
  - `Should*` conjunctions / disjunctions
  Reference: `reference/sts2/MegaCrit.Sts2.Core.Hooks/Hook.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Enums
import Sts2Model.Model.State
import Sts2Model.Hook.Registry
import Sts2Model.Hook.ModHelper

namespace Sts2Model.Hook

open Sts2Model.Core
open Sts2Model.Model

/-- Apply additive phase over a list of `HookBehavior` + `ListenerCtx`. -/
def runDamageAdditive (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (startDmg : Dec) (props : ValueProp)
    (dealer : Option Creature) (cardSource : Option CardInstance) :
    Dec × List ListenerRef :=
  listeners.foldl (fun (acc, mods) ctx =>
    let delta := (reg ctx.ref.modelId).modifyDamageAdditive ctx target acc props dealer cardSource
    let acc' := Dec.add acc delta
    let mods' := if !(Dec.eqVal delta Dec.zero) then mods ++ [ctx.ref] else mods
    (acc', mods')) (startDmg, [])

/-- Apply multiplicative phase over a list of `HookBehavior` + `ListenerCtx`. -/
def runDamageMultiplicative (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (startDmg : Dec) (props : ValueProp)
    (dealer : Option Creature) (cardSource : Option CardInstance) :
    Dec × List ListenerRef :=
  listeners.foldl (fun (acc, mods) ctx =>
    let factor := (reg ctx.ref.modelId).modifyDamageMultiplicative ctx target acc props dealer cardSource
    let acc' := Dec.mul acc factor
    let mods' := if !(Dec.eqVal factor Dec.one) then mods ++ [ctx.ref] else mods
    (acc', mods')) (startDmg, [])

/-- Apply late-multiplicative phase over a list of `HookBehavior` + `ListenerCtx`. -/
def runDamageMultiplicativeLate (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (startDmg : Dec) (props : ValueProp)
    (dealer : Option Creature) (cardSource : Option CardInstance) :
    Dec × List ListenerRef :=
  listeners.foldl (fun (acc, mods) ctx =>
    let factor := (reg ctx.ref.modelId).modifyDamageMultiplicativeLate ctx target acc props dealer cardSource
    let acc' := Dec.mul acc factor
    let mods' := if !(Dec.eqVal factor Dec.one) then mods ++ [ctx.ref] else mods
    (acc', mods')) (startDmg, [])

/-- Apply damage cap phase matching `Hook.cs` lines 78-91:
    tracks running `minCap` initialized to `decimal.MaxValue`, updating `num` whenever `cap < minCap && cap < num`. -/
def runDamageCap (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (startDmg : Dec) (props : ValueProp)
    (dealer : Option Creature) (cardSource : Option CardInstance) :
    Dec × List ListenerRef :=
  let (finalDmg, _, mods) := listeners.foldl (fun (num, minCap, mods) ctx =>
    let cap := (reg ctx.ref.modelId).modifyDamageCap ctx target props dealer cardSource
    if cap < minCap then
      if cap < num then
        (cap, cap, mods ++ [ctx.ref])
      else
        (num, cap, mods)
    else
      (num, minCap, mods)) (startDmg, Dec.maxDecimal, [])
  (finalDmg, mods)

/-- Pure list-based `ModifyDamage` pipeline (Enchantment -> Additive -> Multiplicative -> MultiplicativeLate -> Cap -> maxZero).
    Ref: `Hook.ModifyDamage` & `Hook.ModifyDamageInternal`. -/
def modifyDamageWithListeners (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Option Creature) (dealer : Option Creature) (damage : Dec) (props : ValueProp)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType := ModifyDamageHookType.all) :
    Dec × List ListenerRef :=
  let afterEnch :=
    match cardSource.bind (·.enchantment) with
    | none => damage
    | some ench =>
        let d1 := if hookType.additive then Dec.add damage ench.damageAdd else damage
        if hookType.multiplicative then Dec.mul d1 ench.damageMul else d1
  let (afterAdd, mods1) :=
    if hookType.additive then
      runDamageAdditive listeners reg target afterEnch props dealer cardSource
    else (afterEnch, [])
  let (afterMul, mods2) :=
    if hookType.multiplicative then
      runDamageMultiplicative listeners reg target afterAdd props dealer cardSource
    else (afterAdd, [])
  let (afterMulLate, mods3) :=
    if hookType.multiplicative then
      runDamageMultiplicativeLate listeners reg target afterMul props dealer cardSource
    else (afterMul, [])
  let (afterCap, mods4) :=
    if hookType.cap then
      runDamageCap listeners reg target afterMulLate props dealer cardSource
    else (afterMulLate, [])
  (Dec.maxZero afterCap, mods1 ++ mods2 ++ mods3 ++ mods4)

def modifyDamage (cs : CombatState) (reg : BehaviorRegistry)
    (target : Option Creature) (dealer : Option Creature) (damage : Dec) (props : ValueProp)
    (cardSource : Option CardInstance) (hookType : ModifyDamageHookType := ModifyDamageHookType.all)
    (modSubscribers : List (ModId × ModelId) := []) :
    Dec × List ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  modifyDamageWithListeners listeners reg target dealer damage props cardSource hookType

/-- Pure list-based `ModifyBlock` pipeline (Enchantment -> Additive -> Multiplicative -> maxZero).
    Ref: `Hook.ModifyBlock`. -/
def modifyBlockWithListeners (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Creature) (block : Dec) (props : ValueProp) (cardSource : Option CardInstance) :
    Dec × List ListenerRef :=
  let afterEnch :=
    match cardSource.bind (·.enchantment) with
    | none => block
    | some ench =>
        let b1 := Dec.add block ench.blockAdd
        Dec.mul b1 ench.blockMul
  let (afterAdd, mods1) := listeners.foldl (fun (acc, mods) ctx =>
    let delta := (reg ctx.ref.modelId).modifyBlockAdditive ctx target acc props cardSource
    let acc' := Dec.add acc delta
    let mods' := if !(Dec.eqVal delta Dec.zero) then mods ++ [ctx.ref] else mods
    (acc', mods')) (afterEnch, [])
  let (afterMul, mods2) := listeners.foldl (fun (acc, mods) ctx =>
    let factor := (reg ctx.ref.modelId).modifyBlockMultiplicative ctx target acc props cardSource
    let acc' := Dec.mul acc factor
    let mods' := if !(Dec.eqVal factor Dec.one) then mods ++ [ctx.ref] else mods
    (acc', mods')) (afterAdd, [])
  (Dec.maxZero afterMul, mods1 ++ mods2)

def modifyBlock (cs : CombatState) (reg : BehaviorRegistry)
    (target : Creature) (block : Dec) (props : ValueProp) (cardSource : Option CardInstance)
    (modSubscribers : List (ModId × ModelId) := []) :
    Dec × List ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  modifyBlockWithListeners listeners reg target block props cardSource

private def runHpLostPhase (listeners : List ListenerCtx)
    (fn : ListenerCtx → Dec → Dec) (startAmt : Dec) : Dec × List ListenerRef :=
  listeners.foldl (fun (acc, mods) ctx =>
    let next := fn ctx acc
    let mods' := if acc.truncate != next.truncate then mods ++ [ctx.ref] else mods
    (next, mods')) (startAmt, [])

/-- Exact `Hook.ModifyHpLost` matching `Hook.cs` lines 1779-1827. -/
def modifyHpLostWithListeners (listeners : List ListenerCtx) (reg : BehaviorRegistry)
    (target : Creature) (amount : Dec) (props : ValueProp) (dealer : Option Creature)
    (cardSource : Option CardInstance) (phases : HpLossHookPhase) :
    Dec × List ListenerRef :=
  let (afterBefore1, mods1) :=
    if phases.beforeOsty then
      runHpLostPhase listeners (fun ctx d => (reg ctx.ref.modelId).modifyHpLostBeforeOsty ctx target d props dealer cardSource) amount
    else (amount, [])
  let (afterBefore2, mods2) :=
    if phases.beforeOsty then
      runHpLostPhase listeners (fun ctx d => (reg ctx.ref.modelId).modifyHpLostBeforeOstyLate ctx target d props dealer cardSource) afterBefore1
    else (afterBefore1, [])
  let (afterAfter1, mods3) :=
    if phases.afterOsty then
      runHpLostPhase listeners (fun ctx d => (reg ctx.ref.modelId).modifyHpLostAfterOsty ctx target d props dealer cardSource) afterBefore2
    else (afterBefore2, [])
  let (afterAfter2, mods4) :=
    if phases.afterOsty then
      runHpLostPhase listeners (fun ctx d => (reg ctx.ref.modelId).modifyHpLostAfterOstyLate ctx target d props dealer cardSource) afterAfter1
    else (afterAfter1, [])
  (afterAfter2, mods1 ++ mods2 ++ mods3 ++ mods4)

def modifyHpLost (cs : CombatState) (reg : BehaviorRegistry)
    (target : Creature) (amount : Dec) (props : ValueProp) (dealer : Option Creature)
    (cardSource : Option CardInstance) (phases : HpLossHookPhase)
    (modSubscribers : List (ModId × ModelId) := []) :
    Dec × List ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  modifyHpLostWithListeners listeners reg target amount props dealer cardSource phases

/-- Ref: `Hook.ModifyEnergyCostInCombat`. -/
def modifyEnergyCostInCombat (cs : CombatState) (reg : BehaviorRegistry)
    (card : CardInstance) (originalCost : Dec)
    (modSubscribers : List (ModId × ModelId) := []) : Dec :=
  if originalCost < Dec.zero then originalCost
  else
    let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
    let c1 := listeners.foldl (fun acc ctx => (reg ctx.ref.modelId).modifyEnergyCostInCombat ctx card acc) originalCost
    listeners.foldl (fun acc ctx => (reg ctx.ref.modelId).modifyEnergyCostInCombatLate ctx card acc) c1

/-- Ref: `Hook.ModifyPreBlockDamageTarget`. -/
def modifyPreBlockDamageTarget (cs : CombatState) (reg : BehaviorRegistry)
    (originalTarget : Creature) (amount : Dec) (props : ValueProp) (dealer : Option Creature)
    (modSubscribers : List (ModId × ModelId) := []) : Option CreatureId :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  listeners.foldl (fun cur ctx =>
    (reg ctx.ref.modelId).modifyPreBlockDamageTarget ctx originalTarget cur amount props dealer) none

/-- Ref: `Hook.ModifyUnblockedDamageTarget`. -/
def modifyUnblockedDamageTarget (cs : CombatState) (reg : BehaviorRegistry)
    (originalTarget : CreatureId) (amount : Dec) (props : ValueProp) (dealer : Option Creature)
    (modSubscribers : List (ModId × ModelId) := []) : CreatureId :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  listeners.foldl (fun cur ctx =>
    (reg ctx.ref.modelId).modifyUnblockedDamageTarget ctx cur amount props dealer) originalTarget

/-- Ref: `Hook.ModifyPowerAmountGiven`. -/
def modifyPowerAmountGiven (cs : CombatState) (reg : BehaviorRegistry)
    (pow : PowerInstance) (giver : Option Creature) (amount : Dec) (target : Creature)
    (modSubscribers : List (ModId × ModelId) := []) : Dec × List ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  let (a1, mods1) := listeners.foldl (fun (acc, mods) ctx =>
    let delta := (reg ctx.ref.modelId).modifyPowerAmountGivenAdditive ctx pow giver acc target
    (Dec.add acc delta, if !(Dec.eqVal delta Dec.zero) then mods ++ [ctx.ref] else mods)) (amount, [])
  let (a2, mods2) := listeners.foldl (fun (acc, mods) ctx =>
    let factor := (reg ctx.ref.modelId).modifyPowerAmountGivenMultiplicative ctx pow giver acc target
    (Dec.mul acc factor, if !(Dec.eqVal factor Dec.one) then mods ++ [ctx.ref] else mods)) (a1, [])
  (a2, mods1 ++ mods2)

/-- Ref: `Hook.ModifyPowerAmountReceived`. -/
def modifyPowerAmountReceived (cs : CombatState) (reg : BehaviorRegistry)
    (pow : PowerInstance) (target : Creature) (amount : Dec) (giver : Option Creature)
    (modSubscribers : List (ModId × ModelId) := []) : Dec × List ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  listeners.foldl (fun (acc, mods) ctx =>
    let (changed, next) := (reg ctx.ref.modelId).tryModifyPowerAmountReceived ctx pow target acc giver
    if changed then (next, mods ++ [ctx.ref]) else (acc, mods)) (amount, [])

-- ============================================================================
-- Should* Conjunction / Disjunction Evaluators
-- ============================================================================

def evalShouldAll (listeners : List ListenerCtx) (p : ListenerCtx → Bool) :
    Bool × Option ListenerRef :=
  listeners.foldl (fun (ok, preventer) ctx =>
    if !ok then (false, preventer)
    else if !p ctx then (false, some ctx.ref)
    else (true, none)) (true, none)

def evalShouldAny (listeners : List ListenerCtx) (p : ListenerCtx → Bool) :
    Bool × Option ListenerRef :=
  listeners.foldl (fun (hit, src) ctx =>
    if hit then (true, src)
    else if p ctx then (true, some ctx.ref)
    else (false, none)) (false, none)

def shouldPlay (cs : CombatState) (reg : BehaviorRegistry) (card : CardInstance)
    (autoPlay : AutoPlayType := .none) (modSubscribers : List (ModId × ModelId) := []) :
    Bool × Option ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldPlay ctx card autoPlay

def shouldDie (cs : CombatState) (reg : BehaviorRegistry) (c : Creature)
    (modSubscribers : List (ModId × ModelId) := []) : Bool × Option ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  let (ok1, p1) := evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldDie ctx c
  if !ok1 then (false, p1)
  else evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldDieLate ctx c

def shouldClearBlock (cs : CombatState) (reg : BehaviorRegistry) (c : Creature)
    (modSubscribers : List (ModId × ModelId) := []) : Bool × Option ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldClearBlock ctx c

def shouldDraw (cs : CombatState) (reg : BehaviorRegistry) (player : Player) (fromHandDraw : Bool)
    (modSubscribers : List (ModId × ModelId) := []) : Bool × Option ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldDraw ctx player fromHandDraw

def shouldEtherealTrigger (cs : CombatState) (reg : BehaviorRegistry) (card : CardInstance)
    (modSubscribers : List (ModId × ModelId) := []) : Bool :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  (evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldEtherealTrigger ctx card).1

def shouldFlush (cs : CombatState) (reg : BehaviorRegistry) (player : Player)
    (modSubscribers : List (ModId × ModelId) := []) : Bool :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  (evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldFlush ctx player).1

def shouldStopCombatFromEnding (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) : Bool :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  (evalShouldAny listeners fun ctx => (reg ctx.ref.modelId).shouldStopCombatFromEnding ctx).1

def shouldTakeExtraTurn (cs : CombatState) (reg : BehaviorRegistry) (player : Player)
    (modSubscribers : List (ModId × ModelId) := []) : Bool × Option ListenerRef :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  let (ok1, s1) := evalShouldAny listeners fun ctx => (reg ctx.ref.modelId).shouldTakeExtraTurnEarly ctx player
  if ok1 then (true, s1)
  else evalShouldAny listeners fun ctx => (reg ctx.ref.modelId).shouldTakeExtraTurn ctx player

def shouldPayExcessEnergyCostWithStars (cs : CombatState) (reg : BehaviorRegistry) (player : Player)
    (modSubscribers : List (ModId × ModelId) := []) : Bool :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  (evalShouldAny listeners fun ctx => (reg ctx.ref.modelId).shouldPayExcessEnergyCostWithStars ctx player).1

def shouldPlayerResetEnergy (cs : CombatState) (reg : BehaviorRegistry) (player : Player)
    (modSubscribers : List (ModId × ModelId) := []) : Bool :=
  let listeners := (snapshotCombatListeners cs modSubscribers).map (resolveListenerCtx cs)
  (evalShouldAll listeners fun ctx => (reg ctx.ref.modelId).shouldPlayerResetEnergy ctx player).1

end Sts2Model.Hook

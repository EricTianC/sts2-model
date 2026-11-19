/-
  Complete 154-hook catalog, listener reference types, snapshot iteration order,
  and snapshot liveness filtering.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Hooks/Hook.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/CombatState.cs` (`IterateHookListeners`, `Contains`)
  - `reference/sts2/MegaCrit.Sts2.Core.Runs/RunState.cs` (`IterateHookListeners`)
-/
import Sts2Model.Core.Ids
import Sts2Model.Model.State

namespace Sts2Model.Hook

open Sts2Model.Core
open Sts2Model.Model

/-- Five semantic hook patterns in `Core.Hooks/Hook.cs`. -/
inductive HookKind where
  | before
  | after
  | modify
  | should
  | «try»
  deriving Repr, DecidableEq, Inhabited

/-- Catalog entry for a public static method on `Hook`. -/
structure HookCatalogEntry where
  name : String
  kind : HookKind
  deriving Repr, DecidableEq, Inhabited

def beforeHookNames : List String :=
  [ "BeforeAttack", "BeforeBlockGained", "BeforeCardAutoPlayed", "BeforeCardPlayed"
  , "BeforeCardRemoved", "BeforeCombatStart", "BeforeCombatRewardOffered"
  , "BeforeDamageReceived", "BeforeDeath", "BeforeFlush", "BeforeHandDraw"
  , "BeforePotionUsed", "BeforePowerAmountChanged", "BeforeRoomEntered"
  , "BeforeSideTurnStart", "BeforeSideTurnEnd" ]

def afterHookNames : List String :=
  [ "AfterActEntered", "AfterArrowDislodged", "AfterArrowImpaled", "AfterArrowShot"
  , "AfterAttack", "AfterBlockBroken", "AfterBlockCleared", "AfterBlockGained"
  , "AfterCardChangedPiles", "AfterCardDiscarded", "AfterCardDrawn"
  , "AfterCardEnteredCombat", "AfterCardExhausted", "AfterCardGeneratedForCombat"
  , "AfterCardPlayed", "AfterCombatEnd", "AfterCombatVictory"
  , "AfterCreatureAddedToCombat", "AfterCurrentHpChanged", "AfterDamageGiven"
  , "AfterDamageReceived", "AfterDeath", "AfterGoldGained", "AfterDiedToDoom"
  , "AfterEnergyReset", "AfterEnergySpent", "AfterFlush", "AfterForge"
  , "AfterHandEmptied", "AfterItemPurchased", "AfterMapGenerated"
  , "AfterModifyingBlockAmount", "AfterModifyingCardPlayCount"
  , "AfterModifyingCardRewardOptions", "AfterModifyingDamageAmount"
  , "AfterModifyingEnergyGain", "AfterModifyingGoldGained", "AfterModifyingHandDraw"
  , "AfterModifyingHpLostBeforeOsty", "AfterModifyingHpLostAfterOsty"
  , "AfterModifyingOrbPassiveTriggerCount", "AfterModifyingPowerAmountGiven"
  , "AfterModifyingPowerAmountReceived", "AfterModifyingRewards"
  , "AfterOrbChanneled", "AfterOrbEvoked", "AfterOstyRevived"
  , "AfterPlayerTurnStart", "AfterAutoPostPlayPhaseEntered"
  , "AfterAutoPrePlayPhaseEntered", "AfterPotionDiscarded", "AfterPotionProcured"
  , "AfterPotionUsed", "AfterPowerAmountChanged", "AfterPreventingBlockClear"
  , "AfterPreventingDeath", "AfterPreventingDraw", "AfterRestSiteHeal"
  , "AfterRestSiteSmith", "AfterRewardTaken", "AfterRoomEntered", "AfterShuffle"
  , "AfterSideTurnStart", "AfterStarsGained", "AfterStarsSpent", "AfterSummon"
  , "AfterTakingExtraTurn", "AfterSideTurnEnd" ]

def modifyHookNames : List String :=
  [ "ModifyAttackHitCount", "ModifyBlock", "ModifyCardBeingAddedToDeck"
  , "ModifyCardPlayCount", "ModifyCardPlayResultLocation"
  , "ModifyCardRewardAlternatives", "ModifyCardRewardCreationOptions"
  , "ModifyCardRewardUpgradeOdds", "ModifyDamage", "ModifyEnergyCostInCombat"
  , "ModifyKeywordsInCombat", "ModifyEnergyGain", "ModifyGoldGained"
  , "ModifyExtraRestSiteHealText", "ModifyExtraRestSiteMendText"
  , "ModifyGeneratedMap", "ModifyGeneratedMapLate", "ModifyHandDraw"
  , "ModifyHpLost", "ModifyMaxEnergy", "ModifyMerchantCardCreationResults"
  , "ModifyMerchantCardPool", "ModifyMerchantCardRarity", "ModifyMerchantPrice"
  , "ModifyNextEvent", "ModifyOddsIncreaseForUnrolledRoomType"
  , "ModifyOrbPassiveTriggerCount", "ModifyOrbValue", "ModifyPowerAmountGiven"
  , "ModifyPowerAmountReceived", "ModifyRestSiteHealAmount"
  , "ModifyRestSiteOptions", "ModifyRestSiteHealRewards", "ModifyRewards"
  , "ModifyShuffleOrder", "ModifyStarCost", "ModifySummonAmount"
  , "ModifyUnblockedDamageTarget", "ModifyPreBlockDamageTarget"
  , "ModifyUnknownMapPointRoomTypes", "ModifyXValue" ]

def shouldHookNames : List String :=
  [ "ShouldAddToDeck", "ShouldAfflict", "ShouldAllowAncient", "ShouldAllowHitting"
  , "ShouldAllowMerchantCardRemoval", "ShouldAllowSelectingMoreCardRewards"
  , "ShouldAllowTargeting", "ShouldClearBlock"
  , "ShouldCreatureBeRemovedFromCombatAfterDeath", "ShouldDie"
  , "ShouldDisableRemainingRestSiteOptions", "ShouldDraw"
  , "ShouldEtherealTrigger", "ShouldFlush", "ShouldGenerateTreasure"
  , "ShouldGainStars", "ShouldPayExcessEnergyCostWithStars", "ShouldPlay"
  , "ShouldPlayerResetEnergy", "ShouldProceedToNextMapPoint", "ShouldProcurePotion"
  , "ShouldRefillMerchantEntry", "ShouldStopCombatFromEnding"
  , "ShouldTakeExtraTurn", "ShouldForcePotionReward", "ShouldAllowFreeTravel"
  , "ShouldPowerBeRemovedOnDeath" ]

def tryHookNames : List String :=
  [ "TryModifyCardRewardOptions", "TryReplaceDefaultRoomRewards" ]

/-- All 154 public hooks from `reference/sts2/MegaCrit.Sts2.Core.Hooks/Hook.cs`. -/
def allHookEntries : List HookCatalogEntry :=
  beforeHookNames.map (⟨·, .before⟩) ++
  afterHookNames.map (⟨·, .after⟩) ++
  modifyHookNames.map (⟨·, .modify⟩) ++
  shouldHookNames.map (⟨·, .should⟩) ++
  tryHookNames.map (⟨·, .«try»⟩)

theorem hookCatalog_before_count : beforeHookNames.length = 16 := rfl
theorem hookCatalog_after_count  : afterHookNames.length = 68 := rfl
theorem hookCatalog_modify_count : modifyHookNames.length = 41 := rfl
theorem hookCatalog_should_count : shouldHookNames.length = 27 := rfl
theorem hookCatalog_try_count    : tryHookNames.length = 2 := rfl
theorem hookCatalog_total        : allHookEntries.length = 154 := by
  simp [allHookEntries, hookCatalog_before_count, hookCatalog_after_count,
        hookCatalog_modify_count, hookCatalog_should_count, hookCatalog_try_count]

/-- Typed reference to a model listening to hooks in `CombatState` or `RunState`.
    Ref: `CombatState.IterateHookListeners()` and `RunState.IterateHookListeners()`. -/
inductive ListenerRef where
  | power       (ownerId : CreatureId) (instanceId : PowerInstanceId) (modelId : ModelId)
  | monster     (creatureId : CreatureId) (modelId : ModelId)
  | relic       (playerId : PlayerId) (modelId : ModelId)
  | potion      (playerId : PlayerId) (slotIdx : Nat) (modelId : ModelId)
  | orb         (playerId : PlayerId) (instanceId : OrbInstanceId) (modelId : ModelId)
  | card        (playerId : PlayerId) (instanceId : CardInstanceId) (modelId : ModelId)
  | affliction  (playerId : PlayerId) (cardId : CardInstanceId) (modelId : ModelId)
  | enchantment (playerId : PlayerId) (cardId : CardInstanceId) (modelId : ModelId)
  | modifier    (modelId : ModelId)
  | badge       (modelId : ModelId)
  | runModel    (modelId : ModelId)
  | dominion    (modelId : ModelId)
  | modSubscriber (modId : ModId) (modelId : ModelId)
  deriving Repr, DecidableEq, Inhabited

def ListenerRef.modelId : ListenerRef → ModelId
  | .power _ _ mid       => mid
  | .monster _ mid       => mid
  | .relic _ mid         => mid
  | .potion _ _ mid      => mid
  | .orb _ _ mid         => mid
  | .card _ _ mid        => mid
  | .affliction _ _ mid  => mid
  | .enchantment _ _ mid => mid
  | .modifier mid        => mid
  | .badge mid           => mid
  | .runModel mid        => mid
  | .dominion mid        => mid
  | .modSubscriber _ mid => mid

/-- Check whether a listener is still live in `CombatState`, matching `CombatState.Contains(item)`. -/
def containsListener (cs : CombatState) (ref : ListenerRef) : Bool :=
  match ref with
  | .power ownerId instId mid =>
      match cs.findCreature ownerId with
      | some c => c.powers.any fun p => p.instanceId == instId && p.modelId == mid
      | none   => false
  | .monster cid mid =>
      match cs.findCreature cid with
      | some c => c.isMonster && c.modelId == mid
      | none   => false
  | .relic pid mid =>
      match cs.findPlayer pid with
      | some p => p.isActiveForHooks && p.relics.any fun r => !r.isMelted && r.modelId == mid
      | none   => false
  | .potion pid slotIdx mid =>
      match cs.findPlayer pid with
      | some p =>
          if !p.isActiveForHooks then false
          else match p.potions[slotIdx]? with
            | some (some pot) => pot.modelId == mid
            | _ => false
      | none => false
  | .orb pid instId mid =>
      match cs.findPlayer pid with
      | some p =>
          if !p.isActiveForHooks then false
          else match p.combatState with
            | some pcs => pcs.orbQueue.orbs.any fun o => o.instanceId == instId && o.modelId == mid
            | none     => false
      | none => false
  | .card pid instId mid =>
      match cs.findPlayer pid with
      | some p =>
          if !p.isActiveForHooks then false
          else match p.combatState with
            | some pcs => pcs.piles.allCards.any fun c => c.instanceId == instId && c.modelId == mid
            | none     => false
      | none => false
  | .affliction pid cardId mid =>
      match cs.findPlayer pid with
      | some p =>
          if !p.isActiveForHooks then false
          else match p.combatState with
            | some pcs => pcs.piles.allCards.any fun c =>
                c.instanceId == cardId && match c.affliction with | some a => a.modelId == mid | none => false
            | none => false
      | none => false
  | .enchantment pid cardId mid =>
      match cs.findPlayer pid with
      | some p =>
          if !p.isActiveForHooks then false
          else match p.combatState with
            | some pcs => pcs.piles.allCards.any fun c =>
                c.instanceId == cardId && match c.enchantment with | some e => e.modelId == mid | none => false
            | none => false
      | none => false
  | .modifier mid        => cs.modifiers.contains mid
  | .badge mid           => cs.badges.contains mid
  | .runModel mid        => cs.runModels.contains mid
  | .dominion mid        => cs.dominion == some mid
  | .modSubscriber _ _   => true

private def cardListeners (pid : PlayerId) (c : CardInstance) : List ListenerRef :=
  [.card pid c.instanceId c.modelId] ++
  (match c.affliction with | some a => [.affliction pid c.instanceId a.modelId] | none => []) ++
  (match c.enchantment with | some e => [.enchantment pid c.instanceId e.modelId] | none => [])

private def creatureListeners (cs : CombatState) (c : Creature) : List ListenerRef :=
  let pows := c.powers.map fun p => ListenerRef.power c.id p.instanceId p.modelId
  let body :=
    match c.playerId with
    | none => if c.isMonster then [.monster c.id c.modelId] else []
    | some pid =>
        match cs.findPlayer pid with
        | none => []
        | some player =>
            if !player.isActiveForHooks then []
            else
              let rels := (player.relics.filter (!·.isMelted)).map fun r => ListenerRef.relic pid r.modelId
              let pots := (player.potions.zipIdx).filterMap fun (opt, idx) =>
                opt.map fun pot => ListenerRef.potion pid idx pot.modelId
              match player.combatState with
              | none => rels ++ pots
              | some pcs =>
                  let orbs := pcs.orbQueue.orbs.map fun o => ListenerRef.orb pid o.instanceId o.modelId
                  let cards := pcs.piles.allCards.flatMap (cardListeners pid)
                  rels ++ pots ++ orbs ++ cards
  pows ++ body

/-- Exact snapshot order of `CombatState.IterateHookListeners()` plus trailing `ModHelper` combat subscribers.
    Ref: `Core.Combat/CombatState.cs :: IterateHookListeners`. -/
def snapshotCombatListeners (cs : CombatState)
    (modSubscribers : List (ModId × ModelId) := []) : List ListenerRef :=
  let creatureRefs := cs.allCreatures.flatMap (creatureListeners cs)
  let tailRefs :=
    cs.modifiers.map .modifier ++
    cs.badges.map .badge ++
    cs.runModels.map .runModel ++
    (match cs.dominion with | some d => [.dominion d] | none => [])
  let modRefs := modSubscribers.map fun (mid, modelId) => ListenerRef.modSubscriber mid modelId
  creatureRefs ++ tailRefs ++ modRefs

/-- Exact snapshot order of `RunState.IterateHookListeners(childCombatState)`.
    Ref: `Core.Runs/RunState.cs :: IterateHookListeners`. -/
def snapshotRunListeners (rs : RunState)
    (childCombat : Option CombatState := none)
    (modRunSubscribers : List (ModId × ModelId) := [])
    (modCombatSubscribers : List (ModId × ModelId) := []) : List ListenerRef :=
  let deckRefs := rs.players.flatMap fun p =>
    if !p.isActiveForHooks then []
    else p.deck.flatMap fun c =>
      [.card p.playerId c.instanceId c.modelId] ++
      (match c.enchantment with | some e => [.enchantment p.playerId c.instanceId e.modelId] | none => [])
  let runOnlyRefs :=
    match childCombat with
    | some _ => []
    | none =>
        let playerGear := rs.players.flatMap fun p =>
          if !p.isActiveForHooks then []
          else
            let rels := (p.relics.filter (!·.isMelted)).map fun r => ListenerRef.relic p.playerId r.modelId
            let pots := (p.potions.zipIdx).filterMap fun (opt, idx) =>
              opt.map fun pot => ListenerRef.potion p.playerId idx pot.modelId
            rels ++ pots
        playerGear ++
        rs.modifiers.map .modifier ++
        rs.badges.map .badge ++
        rs.runModels.map .runModel ++
        (match rs.dominion with | some d => [.dominion d] | none => [])
  let modRunRefs := modRunSubscribers.map fun (mid, modelId) => ListenerRef.modSubscriber mid modelId
  let combatRefs :=
    match childCombat with
    | some cs => snapshotCombatListeners cs modCombatSubscribers
    | none => []
  deckRefs ++ runOnlyRefs ++ modRunRefs ++ combatRefs

/-- Dispatch a stateful hook over a pre-captured snapshot, checking `containsListener`
    right before executing each listener so models removed mid-dispatch never fire
    and models added mid-dispatch do not trigger within the same snapshot. -/
def runSnapshotHooks (snapshot : List ListenerRef) (cs : CombatState)
    (step : CombatState → ListenerRef → CombatState) : CombatState :=
  snapshot.foldl (fun acc ref => if containsListener acc ref then step acc ref else acc) cs

end Sts2Model.Hook

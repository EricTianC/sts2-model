/-
  Out-of-combat RNG & pity-timer odds (`CardRarityOdds`, `PotionRewardOdds`,
  `UnknownMapPointOdds`) and `RelicGrabBag`.
  Includes BOTH exact `Dec` models (for kernel arithmetic invariants) and bit-exact
  IEEE-754 `Float32` `CardRarityOddsF32` (for `.NET 9` differential testing).
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Odds/CardRarityOdds.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Odds/PotionRewardOdds.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Odds/UnknownMapPointOdds.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Runs/RelicGrabBag.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Enums
import Sts2Model.Core.Ids
import Sts2Model.Core.Rng

namespace Sts2Model.Run

open Sts2Model.Core

-- ============================================================================
-- CardRarityOdds: Exact Dec model (for formal proofs)
-- ============================================================================

structure CardRarityOddsDec where
  offset     : Dec := Dec.ofScaled (-5) 2  -- -0.05
  isScarcity : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace CardRarityOddsDec

def baseOffset : Dec := Dec.ofScaled (-5) 2     -- -0.05
def maxOffset : Dec := Dec.ofScaled 40 2       --  0.40

def rarityGrowth (odds : CardRarityOddsDec) : Dec :=
  if odds.isScarcity then Dec.ofScaled 5 3 else Dec.ofScaled 1 2  -- 0.005 vs 0.01

def baseRareOdds (oddsType : CardRarityOddsType) (isScarcity : Bool) : Dec :=
  match oddsType with
  | .eliteEncounter   => if isScarcity then Dec.ofScaled 50 3 else Dec.ofScaled 100 3
  | .bossEncounter    => Dec.one
  | .shop             => if isScarcity then Dec.ofScaled 45 3 else Dec.ofScaled 90 3
  | .regularEncounter => if isScarcity then Dec.ofScaled 149 4 else Dec.ofScaled 300 4
  | .blitz            => Dec.ofScaled 10 2
  | .blitzNeow        => Dec.ofScaled 5 2
  | .uniform          => Dec.ofScaled 33 2
  | .none             => Dec.zero

def baseUncommonOdds : CardRarityOddsType → Dec
  | .eliteEncounter   => Dec.ofScaled 40 2
  | .bossEncounter    => Dec.zero
  | .shop             => Dec.ofScaled 37 2
  | .regularEncounter => Dec.ofScaled 37 2
  | .blitz            => Dec.ofScaled 50 2
  | .blitzNeow        => Dec.ofScaled 40 2
  | .uniform          => Dec.ofScaled 33 2
  | .none             => Dec.zero

def rollWithoutChangingFutureOdds (odds : CardRarityOddsDec)
    (oddsType : CardRarityOddsType) (curOffset sample : Dec) : CardRarity :=
  let rareThresh := Dec.add (baseRareOdds oddsType odds.isScarcity) curOffset
  let uncThresh := Dec.add (baseUncommonOdds oddsType) rareThresh
  if sample < rareThresh then .rare
  else if sample < uncThresh then .uncommon
  else .common

def rollFromSample (odds : CardRarityOddsDec) (oddsType : CardRarityOddsType) (sample : Dec) :
    CardRarity × CardRarityOddsDec :=
  let curOffset := if oddsType == .bossEncounter then Dec.zero else odds.offset
  let rolled := rollWithoutChangingFutureOdds odds oddsType curOffset sample
  let nextOffset :=
    if rolled == .rare then baseOffset
    else Dec.min (Dec.add odds.offset (rarityGrowth odds)) maxOffset
  (rolled, { odds with offset := nextOffset })

end CardRarityOddsDec

-- ============================================================================
-- CardRarityOdds: IEEE-754 Float32 model matching `CardRarityOdds.cs` for C# DiffTest
-- ============================================================================

structure CardRarityOddsF32 where
  currentValue : Float32 := (-0.05 : Float32)
  isScarcity   : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace CardRarityOddsF32

def nextFloat (rng : Rng) : Float32 × Rng :=
  let (d, rng') := rng.nextDouble
  (d.toFloat32, rng')

def baseRareOdds (t : CardRarityOddsType) (scarcity : Bool) : Float32 :=
  match t with
  | .eliteEncounter   => if scarcity then (0.05 : Float32) else (0.1 : Float32)
  | .bossEncounter    => (1.0 : Float32)
  | .shop             => if scarcity then (0.045 : Float32) else (0.09 : Float32)
  | .regularEncounter => if scarcity then (0.0149 : Float32) else (0.03 : Float32)
  | .blitz            => (0.1 : Float32)
  | .blitzNeow        => (0.05 : Float32)
  | .uniform          => (0.33 : Float32)
  | .none             => (0.0 : Float32)

def baseUncommonOdds : CardRarityOddsType → Float32
  | .eliteEncounter   => (0.4 : Float32)
  | .bossEncounter    => (0.0 : Float32)
  | .shop             => (0.37 : Float32)
  | .regularEncounter => (0.37 : Float32)
  | .blitz            => (0.5 : Float32)
  | .blitzNeow        => (0.4 : Float32)
  | .uniform          => (0.33 : Float32)
  | .none             => (0.0 : Float32)

def roll (odds : CardRarityOddsF32) (t : CardRarityOddsType) (rng : Rng) :
    CardRarity × CardRarityOddsF32 × Rng :=
  let effOff := if t == .bossEncounter then (0.0 : Float32) else odds.currentValue
  let (num, rng') := nextFloat rng
  let rareThresh : Float32 := baseRareOdds t odds.isScarcity + effOff
  let uncThresh : Float32 := baseUncommonOdds t + rareThresh
  let rarity :=
    if num < rareThresh then CardRarity.rare
    else if num < uncThresh then CardRarity.uncommon
    else CardRarity.common
  let growth : Float32 := if odds.isScarcity then (0.005 : Float32) else (0.01 : Float32)
  let nextVal : Float32 :=
    if rarity == .rare then (-0.05 : Float32)
    else
      let sum : Float32 := odds.currentValue + growth
      if sum < (0.4 : Float32) then sum else (0.4 : Float32)
  (rarity, { odds with currentValue := nextVal }, rng')

end CardRarityOddsF32

-- ============================================================================
-- PotionRewardOdds (`PotionRewardOdds.cs`)
-- ============================================================================

structure PotionRewardOdds where
  currentValue : Dec := Dec.ofScaled 4 1  -- 0.40
  deriving Repr, DecidableEq, Inhabited

namespace PotionRewardOdds

def eliteBonus : Dec := Dec.ofScaled 25 2  -- 0.25

def rollFromSample (odds : PotionRewardOdds) (roomType : RoomType) (sample : Dec)
    (forcePotion : Bool := false) : Bool × PotionRewardOdds :=
  if forcePotion then (true, odds)
  else
    let bonus := if roomType == .elite then Dec.mul eliteBonus (Dec.ofScaled 5 1) else Dec.zero
    let thresh := Dec.add odds.currentValue bonus
    if sample < thresh then
      (true, { currentValue := Dec.sub odds.currentValue (Dec.ofScaled 1 1) })
    else
      (false, { currentValue := Dec.add odds.currentValue (Dec.ofScaled 1 1) })

end PotionRewardOdds

-- ============================================================================
-- UnknownMapPointOdds (`UnknownMapPointOdds.cs`)
-- ============================================================================

structure UnknownMapPointOdds where
  monsterOdds     : Dec := Dec.ofScaled 10 2   --  0.10
  eliteOdds       : Dec := Dec.ofScaled (-1) 0 -- -1.00 (never rolled initially)
  treasureOdds    : Dec := Dec.ofScaled 2 2    --  0.02
  shopOdds        : Dec := Dec.ofScaled 3 2    --  0.03
  baseMonsterOdds : Dec := Dec.ofScaled 10 2
  baseEliteOdds   : Dec := Dec.ofScaled (-1) 0
  baseTreasureOdds : Dec := Dec.ofScaled 2 2
  baseShopOdds    : Dec := Dec.ofScaled 3 2
  deriving Repr, DecidableEq, Inhabited

namespace UnknownMapPointOdds

def getOdds (u : UnknownMapPointOdds) : RoomType → Dec
  | .monster  => u.monsterOdds
  | .elite    => u.eliteOdds
  | .treasure => u.treasureOdds
  | .shop     => u.shopOdds
  | _         => Dec.zero

def getBaseOdds (u : UnknownMapPointOdds) : RoomType → Dec
  | .monster  => u.baseMonsterOdds
  | .elite    => u.baseEliteOdds
  | .treasure => u.baseTreasureOdds
  | .shop     => u.baseShopOdds
  | _         => Dec.zero

def setOdds (u : UnknownMapPointOdds) (rt : RoomType) (v : Dec) : UnknownMapPointOdds :=
  match rt with
  | .monster  => { u with monsterOdds := v }
  | .elite    => { u with eliteOdds := v }
  | .treasure => { u with treasureOdds := v }
  | .shop     => { u with shopOdds := v }
  | _         => u

def resetToBase (u : UnknownMapPointOdds) : UnknownMapPointOdds :=
  { u with
    monsterOdds  := u.baseMonsterOdds
  , eliteOdds    := u.baseEliteOdds
  , treasureOdds := u.baseTreasureOdds
  , shopOdds     := u.baseShopOdds }

def trackedTypes : List RoomType := [.monster, .elite, .treasure, .shop]

/-- Positive sum of non-event room odds (`UnknownMapPointOdds.cs` line 97). -/
def sumPositiveNonEvent (u : UnknownMapPointOdds) : Dec :=
  trackedTypes.foldl (fun acc rt =>
    let v := u.getOdds rt
    if Dec.zero < v then Dec.add acc v else acc) Dec.zero

def eventOdds (u : UnknownMapPointOdds) : Dec :=
  Dec.maxZero (Dec.sub Dec.one (u.sumPositiveNonEvent))

/-- Roll next unknown map room type. Rooms with negative odds (`< 0`) or blacklisted are never rolled. -/
def rollFromSample (u : UnknownMapPointOdds) (blacklist : List RoomType) (sample : Dec) :
    RoomType × UnknownMapPointOdds :=
  let allowed (rt : RoomType) := !blacklist.contains rt
  let defaultRoom := if allowed .event then RoomType.event else .monster
  let (_, rolledOpt) := trackedTypes.foldl (fun (accSum, picked) rt =>
    if picked.isSome then (accSum, picked)
    else
      let v := u.getOdds rt
      if allowed rt && !(v < Dec.zero) then
        let acc' := Dec.add accSum v
        if sample ≤ acc' then (acc', some rt) else (acc', none)
      else (accSum, none)) (Dec.zero, none)
  let rolled := rolledOpt.getD defaultRoom
  let u' := trackedTypes.foldl (fun acc rt =>
    let baseV := u.getBaseOdds rt
    if rolled == rt then acc.setOdds rt baseV
    else if allowed rt then acc.setOdds rt (Dec.add (acc.getOdds rt) baseV)
    else acc) u
  (rolled, u')

end UnknownMapPointOdds

-- ============================================================================
-- RelicGrabBag (`RelicGrabBag.cs`)
-- ============================================================================

structure RelicGrabBag where
  common         : List ModelId := []
  uncommon       : List ModelId := []
  rare           : List ModelId := []
  shop           : List ModelId := []
  fallback       : List ModelId := []
  refreshAllowed : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace RelicGrabBag

def getDeque (b : RelicGrabBag) : RelicRarity → List ModelId
  | .common   => b.common
  | .uncommon => b.uncommon
  | .rare     => b.rare
  | .shop     => b.shop
  | _         => []

def setDeque (b : RelicGrabBag) (r : RelicRarity) (xs : List ModelId) : RelicGrabBag :=
  match r with
  | .common   => { b with common := xs }
  | .uncommon => { b with uncommon := xs }
  | .rare     => { b with rare := xs }
  | .shop     => { b with shop := xs }
  | _         => b

def totalCount (b : RelicGrabBag) : Nat :=
  b.common.length + b.uncommon.length + b.rare.length + b.shop.length + b.fallback.length

def findNonEmptyRarity (b : RelicGrabBag) (r : RelicRarity) : Option RelicRarity :=
  let order : List RelicRarity := match r with
    | .shop     => [.shop, .common, .uncommon, .rare]
    | .common   => [.common, .uncommon, .rare]
    | .uncommon => [.uncommon, .rare]
    | .rare     => [.rare]
    | _         => []
  order.find? fun cand => !(b.getDeque cand).isEmpty

/-- Pull relic from the front of `rarity`'s bucket (with `Shop → Common → Uncommon → Rare → Fallback` chain).
    Ref: `RelicGrabBag.PullFromFront` & `GetAvailableDeque`. -/
def pullFromFront (b : RelicGrabBag) (rarity : RelicRarity) : RelicGrabBag × Option ModelId :=
  match findNonEmptyRarity b rarity with
  | some r =>
      match b.getDeque r with
      | [] => (b, none)
      | x :: xs => (b.setDeque r xs, some x)
  | none =>
      match b.fallback with
      | [] => (b, none)
      | x :: xs => ({ b with fallback := xs }, some x)

/-- Pull relic from the back (used by Shops). Ref: `RelicGrabBag.PullFromBack`. -/
def pullFromBack (b : RelicGrabBag) (rarity : RelicRarity) : RelicGrabBag × Option ModelId :=
  match findNonEmptyRarity b rarity with
  | some r =>
      match (b.getDeque r).reverse with
      | [] => (b, none)
      | x :: revXs => (b.setDeque r revXs.reverse, some x)
  | none =>
      match b.fallback.reverse with
      | [] => (b, none)
      | x :: revXs => ({ b with fallback := revXs.reverse }, some x)

def removeRelic (b : RelicGrabBag) (mid : ModelId) : RelicGrabBag :=
  { b with
    common   := b.common.filter (· != mid)
  , uncommon := b.uncommon.filter (· != mid)
  , rare     := b.rare.filter (· != mid)
  , shop     := b.shop.filter (· != mid)
  , fallback := b.fallback.filter (· != mid) }

end RelicGrabBag
end Sts2Model.Run

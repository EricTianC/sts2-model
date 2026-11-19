/-
  Card, Enchantment, Affliction, CardPlay, CardPile, and PlayerPiles models.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Models/CardModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/EnchantmentModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/AfflictionModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Cards/CardPile.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Cards/CardPlay.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Model.Cost

namespace Sts2Model.Model

open Sts2Model.Core

/-- Card enchantment instance. Ref: `Core.Models/EnchantmentModel.cs`. -/
structure EnchantmentInstance where
  modelId  : ModelId
  amount   : Int := 0
  damageAdd : Dec := Dec.zero
  damageMul : Dec := Dec.one
  blockAdd  : Dec := Dec.zero
  blockMul  : Dec := Dec.one
  deriving Repr, DecidableEq, Inhabited

/-- Card affliction instance (Bound, Entangled, Galvanized, Hexed, Ringing, Smog, Tainted).
    Ref: `Core.Models/AfflictionModel.cs`. -/
structure AfflictionInstance where
  modelId     : ModelId
  preventsPlay : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Mutable card instance in deck or combat piles.
    Ref: `Core.Models/CardModel.cs`. -/
structure CardInstance where
  instanceId       : CardInstanceId
  modelId          : ModelId
  ownerId          : PlayerId
  cardType         : CardType
  rarity           : CardRarity
  targetType       : TargetType
  keywords         : List CardKeyword := []
  tags             : List CardTag := []
  energyCost       : CardEnergyCost
  baseStarCost     : Int := 0
  hasStarCostX     : Bool := false
  temporaryStarCost : Option TemporaryCardCost := none
  upgradeLevel     : Nat := 0
  baseDamage       : Dec := Dec.zero
  baseBlock        : Dec := Dec.zero
  gainsBlock       : Bool := false
  exhaustOnNextPlay : Bool := false
  isDupe           : Bool := false
  isCanonical      : Bool := false
  enchantment      : Option EnchantmentInstance := none
  affliction       : Option AfflictionInstance := none
  deriving Repr, DecidableEq, Inhabited

namespace CardInstance

def hasKeyword (c : CardInstance) (kw : CardKeyword) : Bool :=
  c.keywords.contains kw

def hasTag (c : CardInstance) (t : CardTag) : Bool :=
  c.tags.contains t

def addKeyword (c : CardInstance) (kw : CardKeyword) : CardInstance :=
  if c.hasKeyword kw then c else { c with keywords := c.keywords ++ [kw] }

def removeKeyword (c : CardInstance) (kw : CardKeyword) : CardInstance :=
  { c with keywords := c.keywords.filter (· != kw) }

/-- Ref: `CardModel.GetResultLocationForCardPlay()`. -/
def defaultResultPile (c : CardInstance) : PileType :=
  if c.isDupe || c.cardType == .power then
    .none
  else if c.exhaustOnNextPlay || c.hasKeyword .exhaust then
    .exhaust
  else
    .discard

/-- Ref: `CardModel.EndOfTurnCleanup()`. -/
def endOfTurnCleanup (c : CardInstance) : CardInstance :=
  let (ecost', _) := c.energyCost.endOfTurnCleanup
  let star' := match c.temporaryStarCost with
    | some tc => if tc.clearsWhenTurnEnds then none else some tc
    | none => none
  { c with energyCost := ecost', temporaryStarCost := star' }

def afterCardPlayedCleanup (c : CardInstance) : CardInstance :=
  let (ecost', _) := c.energyCost.afterCardPlayedCleanup
  let star' := match c.temporaryStarCost with
    | some tc => if tc.clearsWhenCardIsPlayed then none else some tc
    | none => none
  { c with energyCost := ecost', temporaryStarCost := star', exhaustOnNextPlay := false }

end CardInstance

/-- Metadata for an active card play. Ref: `Core.Entities.Cards/CardPlay.cs`. -/
structure CardPlay where
  cardId      : CardInstanceId
  playerId    : PlayerId
  targetId    : Option CreatureId := none
  resultPile  : PileType := .discard
  energySpent : Nat := 0
  starsSpent  : Nat := 0
  isAutoPlay  : Bool := false
  playIndex   : Nat := 0
  playCount   : Nat := 1
  deriving Repr, DecidableEq, Inhabited

/-- Five combat card piles belonging to a `PlayerCombatState`.
    Ref: `Core.Entities.Players/PlayerCombatState.cs` & `Core.Entities.Cards/CardPile.cs`. -/
structure PlayerPiles where
  draw    : List CardInstance := []
  hand    : List CardInstance := []
  discard : List CardInstance := []
  exhaust : List CardInstance := []
  play    : List CardInstance := []
  deriving Repr, DecidableEq, Inhabited

namespace PlayerPiles

def maxCardsInHand : Nat := 10

def getPile (p : PlayerPiles) : PileType → List CardInstance
  | .draw    => p.draw
  | .hand    => p.hand
  | .discard => p.discard
  | .exhaust => p.exhaust
  | .play    => p.play
  | .none    => []
  | .deck    => []

def setPile (p : PlayerPiles) (pt : PileType) (cs : List CardInstance) : PlayerPiles :=
  match pt with
  | .draw    => { p with draw := cs }
  | .hand    => { p with hand := cs }
  | .discard => { p with discard := cs }
  | .exhaust => { p with exhaust := cs }
  | .play    => { p with play := cs }
  | .none    => p
  | .deck    => p

def allCards (p : PlayerPiles) : List CardInstance :=
  p.hand ++ p.draw ++ p.discard ++ p.exhaust ++ p.play

def totalCount (p : PlayerPiles) : Nat :=
  p.hand.length + p.draw.length + p.discard.length + p.exhaust.length + p.play.length

def findPileOf (p : PlayerPiles) (cid : CardInstanceId) : Option PileType :=
  if p.hand.any (·.instanceId == cid) then some .hand
  else if p.draw.any (·.instanceId == cid) then some .draw
  else if p.discard.any (·.instanceId == cid) then some .discard
  else if p.exhaust.any (·.instanceId == cid) then some .exhaust
  else if p.play.any (·.instanceId == cid) then some .play
  else none

def findCard (p : PlayerPiles) (cid : CardInstanceId) : Option CardInstance :=
  p.allCards.find? (·.instanceId == cid)

end PlayerPiles
end Sts2Model.Model

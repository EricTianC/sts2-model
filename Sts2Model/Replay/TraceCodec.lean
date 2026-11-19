/-
  Versioned, lossless, 64-bit-safe External Trace JSON Wire Protocol (`schemaVersion = 1`).
  Aligns headless snapshots & replay events with `NetFullCombatState.cs` and
  `CombatReplayEvent.cs` for C# (.NET 9) Mod -> Lean 4 interoperability.
-/
import Lean.Data.Json
import Sts2Model.Replay.Timeline

namespace Sts2Model.Replay

open Lean
open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Multiplayer
open Sts2Model.Sim

def traceSchemaVersion : Nat := 1

-- ============================================================================
-- Forgiving JSON Helpers & 64-bit Decimal-String Serialization
-- ============================================================================

def getFieldReq [FromJson α] (j : Json) (k : String) : Except String α := do
  let v ← j.getObjVal? k
  fromJson? v

def getFieldOpt [FromJson α] (j : Json) (k : String) : Except String (Option α) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => (fromJson? v).map some

def getFieldD [FromJson α] (j : Json) (k : String) (defaultVal : α) : Except String α :=
  match j.getObjVal? k with
  | .error _ => .ok defaultVal
  | .ok .null => .ok defaultVal
  | .ok v => fromJson? v

@[inline] def uInt64ToStr (u : UInt64) : String :=
  toString u.toNat

def parseUInt64Str (s : String) : Except String UInt64 :=
  match s.toNat? with
  | some n => .ok (UInt64.ofNat n)
  | none   => .error s!"Invalid UInt64 decimal string: {s}"

-- ============================================================================
-- Lossless Bidirectional Enum Codecs
-- ============================================================================

def encodeCombatSide : CombatSide → String
  | .none   => "none"
  | .player => "player"
  | .enemy  => "enemy"

def decodeCombatSide : String → Except String CombatSide
  | "none"   => .ok .none
  | "player" => .ok .player
  | "enemy"  => .ok .enemy
  | s        => .error s!"Unknown CombatSide: {s}"

def encodeCardType : CardType → String
  | .none   => "none"
  | .attack => "attack"
  | .skill  => "skill"
  | .power  => "power"
  | .status => "status"
  | .curse  => "curse"
  | .quest  => "quest"

def decodeCardType : String → Except String CardType
  | "none"   => .ok .none
  | "attack" => .ok .attack
  | "skill"  => .ok .skill
  | "power"  => .ok .power
  | "status" => .ok .status
  | "curse"  => .ok .curse
  | "quest"  => .ok .quest
  | s        => .error s!"Unknown CardType: {s}"

def encodeCardRarity : CardRarity → String
  | .none     => "none"
  | .basic    => "basic"
  | .common   => "common"
  | .uncommon => "uncommon"
  | .rare     => "rare"
  | .ancient  => "ancient"
  | .event    => "event"
  | .token    => "token"
  | .status   => "status"
  | .curse    => "curse"
  | .quest    => "quest"

def decodeCardRarity : String → Except String CardRarity
  | "none"     => .ok .none
  | "basic"    => .ok .basic
  | "common"   => .ok .common
  | "uncommon" => .ok .uncommon
  | "rare"     => .ok .rare
  | "ancient"  => .ok .ancient
  | "event"    => .ok .event
  | "token"    => .ok .token
  | "status"   => .ok .status
  | "curse"    => .ok .curse
  | "quest"    => .ok .quest
  | s          => .error s!"Unknown CardRarity: {s}"

def encodeTargetType : TargetType → String
  | .none               => "none"
  | .self               => "self"
  | .anyEnemy           => "anyEnemy"
  | .allEnemies         => "allEnemies"
  | .randomEnemy        => "randomEnemy"
  | .anyPlayer          => "anyPlayer"
  | .anyAlly            => "anyAlly"
  | .allAllies          => "allAllies"
  | .targetedNoCreature => "targetedNoCreature"
  | .osty               => "osty"

def decodeTargetType : String → Except String TargetType
  | "none"               => .ok .none
  | "self"               => .ok .self
  | "anyEnemy"           => .ok .anyEnemy
  | "allEnemies"         => .ok .allEnemies
  | "randomEnemy"        => .ok .randomEnemy
  | "anyPlayer"          => .ok .anyPlayer
  | "anyAlly"            => .ok .anyAlly
  | "allAllies"          => .ok .allAllies
  | "targetedNoCreature" => .ok .targetedNoCreature
  | "osty"               => .ok .osty
  | s                    => .error s!"Unknown TargetType: {s}"

def encodePowerType : PowerType → String
  | .none   => "none"
  | .buff   => "buff"
  | .debuff => "debuff"

def decodePowerType : String → Except String PowerType
  | "none"   => .ok .none
  | "buff"   => .ok .buff
  | "debuff" => .ok .debuff
  | s        => .error s!"Unknown PowerType: {s}"

def encodePowerStackType : PowerStackType → String
  | .none    => "none"
  | .counter => "counter"
  | .single  => "single"

def decodePowerStackType : String → Except String PowerStackType
  | "none"    => .ok .none
  | "counter" => .ok .counter
  | "single"  => .ok .single
  | s         => .error s!"Unknown PowerStackType: {s}"

def encodeRelicRarity : RelicRarity → String
  | .none     => "none"
  | .starter  => "starter"
  | .common   => "common"
  | .uncommon => "uncommon"
  | .rare     => "rare"
  | .shop     => "shop"
  | .event    => "event"
  | .ancient  => "ancient"

def decodeRelicRarity : String → Except String RelicRarity
  | "none"     => .ok .none
  | "starter"  => .ok .starter
  | "common"   => .ok .common
  | "uncommon" => .ok .uncommon
  | "rare"     => .ok .rare
  | "shop"     => .ok .shop
  | "event"    => .ok .event
  | "ancient"  => .ok .ancient
  | s          => .error s!"Unknown RelicRarity: {s}"

def encodeRoomType : RoomType → String
  | .unassigned => "unassigned"
  | .monster    => "monster"
  | .elite      => "elite"
  | .boss       => "boss"
  | .treasure   => "treasure"
  | .shop       => "shop"
  | .event      => "event"
  | .restSite   => "restSite"
  | .map        => "map"

def decodeRoomType : String → Except String RoomType
  | "unassigned" => .ok .unassigned
  | "monster"    => .ok .monster
  | "elite"      => .ok .elite
  | "boss"       => .ok .boss
  | "treasure"   => .ok .treasure
  | "shop"       => .ok .shop
  | "event"      => .ok .event
  | "restSite"   => .ok .restSite
  | "map"        => .ok .map
  | s            => .error s!"Unknown RoomType: {s}"

def encodeMapPointType : MapPointType → String
  | .unassigned => "unassigned"
  | .unknown    => "unknown"
  | .shop       => "shop"
  | .treasure   => "treasure"
  | .restSite   => "restSite"
  | .monster    => "monster"
  | .elite      => "elite"
  | .boss       => "boss"
  | .ancient    => "ancient"

def decodeMapPointType : String → Except String MapPointType
  | "unassigned" => .ok .unassigned
  | "unknown"    => .ok .unknown
  | "shop"       => .ok .shop
  | "treasure"   => .ok .treasure
  | "restSite"   => .ok .restSite
  | "monster"    => .ok .monster
  | "elite"      => .ok .elite
  | "boss"       => .ok .boss
  | "ancient"    => .ok .ancient
  | s            => .error s!"Unknown MapPointType: {s}"

def encodeCombatReplayEventType : CombatReplayEventType → String
  | .none         => "none"
  | .gameAction   => "gameAction"
  | .hookAction   => "hookAction"
  | .resumeAction => "resumeAction"
  | .playerChoice => "playerChoice"

def decodeCombatReplayEventType : String → Except String CombatReplayEventType
  | "none"         => .ok .none
  | "gameAction"   => .ok .gameAction
  | "hookAction"   => .ok .hookAction
  | "resumeAction" => .ok .resumeAction
  | "playerChoice" => .ok .playerChoice
  | s              => .error s!"Unknown CombatReplayEventType: {s}"

-- ============================================================================
-- Wire Data Transfer Objects (camelCase JSON matching C# System.Text.Json)
-- ============================================================================

structure WireModelId where
  category : String
  entry    : String
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireModelId where
  toJson m := Json.mkObj [("category", toJson m.category), ("entry", toJson m.entry)]

instance : FromJson WireModelId where
  fromJson? j := do
    let cat ← getFieldReq j "category"
    let ent ← getFieldReq j "entry"
    .ok { category := cat, entry := ent }

structure WirePower where
  instanceId    : Nat := 0
  modelEntry    : String
  powerType     : String := "buff"
  stackType     : String := "counter"
  allowNegative : Bool := false
  amount        : Int := 0
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WirePower where
  toJson p := Json.mkObj
    [ ("instanceId", toJson p.instanceId)
    , ("modelEntry", toJson p.modelEntry)
    , ("powerType", toJson p.powerType)
    , ("stackType", toJson p.stackType)
    , ("allowNegative", toJson p.allowNegative)
    , ("amount", toJson p.amount) ]

instance : FromJson WirePower where
  fromJson? j := do
    let iid ← getFieldD j "instanceId" 0
    let ent ← getFieldReq j "modelEntry"
    let pt ← getFieldD j "powerType" "buff"
    let st ← getFieldD j "stackType" "counter"
    let an ← getFieldD j "allowNegative" false
    let amt ← getFieldD j "amount" 0
    .ok { instanceId := iid, modelEntry := ent, powerType := pt, stackType := st, allowNegative := an, amount := amt }

structure WireCard where
  instanceId   : Nat
  modelEntry   : String
  ownerId      : Nat := 1
  cardType     : String := "attack"
  rarity       : String := "common"
  targetType   : String := "anyEnemy"
  baseCost     : Int := 1
  costsX       : Bool := false
  starCost     : Int := 0
  upgradeLevel : Nat := 0
  baseDamage   : Int := 0
  baseBlock    : Int := 0
  gainsBlock   : Bool := false
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireCard where
  toJson c := Json.mkObj
    [ ("instanceId", toJson c.instanceId)
    , ("modelEntry", toJson c.modelEntry)
    , ("ownerId", toJson c.ownerId)
    , ("cardType", toJson c.cardType)
    , ("rarity", toJson c.rarity)
    , ("targetType", toJson c.targetType)
    , ("baseCost", toJson c.baseCost)
    , ("costsX", toJson c.costsX)
    , ("starCost", toJson c.starCost)
    , ("upgradeLevel", toJson c.upgradeLevel)
    , ("baseDamage", toJson c.baseDamage)
    , ("baseBlock", toJson c.baseBlock)
    , ("gainsBlock", toJson c.gainsBlock) ]

instance : FromJson WireCard where
  fromJson? j := do
    let iid ← getFieldReq j "instanceId"
    let ent ← getFieldReq j "modelEntry"
    let oid ← getFieldD j "ownerId" 1
    let ct ← getFieldD j "cardType" "attack"
    let rar ← getFieldD j "rarity" "common"
    let tt ← getFieldD j "targetType" "anyEnemy"
    let bc ← getFieldD j "baseCost" 1
    let cx ← getFieldD j "costsX" false
    let sc ← getFieldD j "starCost" 0
    let upg ← getFieldD j "upgradeLevel" 0
    let bd ← getFieldD j "baseDamage" 0
    let bb ← getFieldD j "baseBlock" 0
    let gb ← getFieldD j "gainsBlock" false
    .ok { instanceId := iid, modelEntry := ent, ownerId := oid, cardType := ct
        , rarity := rar, targetType := tt, baseCost := bc, costsX := cx
        , starCost := sc, upgradeLevel := upg, baseDamage := bd, baseBlock := bb, gainsBlock := gb }

structure WireRelic where
  modelEntry : String
  rarity     : String := "common"
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireRelic where
  toJson r := Json.mkObj [("modelEntry", toJson r.modelEntry), ("rarity", toJson r.rarity)]

instance : FromJson WireRelic where
  fromJson? j := do
    let ent ← getFieldReq j "modelEntry"
    let rar ← getFieldD j "rarity" "common"
    .ok { modelEntry := ent, rarity := rar }

structure WirePotion where
  modelEntry : Option String := none
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WirePotion where
  toJson p := Json.mkObj [("modelEntry", toJson p.modelEntry)]

instance : FromJson WirePotion where
  fromJson? j := do
    let ent ← getFieldOpt j "modelEntry"
    .ok { modelEntry := ent }

structure WireCreature where
  id              : Nat
  modelEntry      : String
  modelCategory   : String := "MONSTER"
  side            : String := "enemy"
  playerId        : Option Nat := none
  currentHp       : Nat
  maxHp           : Nat
  block           : Nat := 0
  powers          : List WirePower := []
  monsterMoveId   : Option String := none
  monsterStateLog : List String := []
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireCreature where
  toJson c := Json.mkObj
    [ ("id", toJson c.id)
    , ("modelEntry", toJson c.modelEntry)
    , ("modelCategory", toJson c.modelCategory)
    , ("side", toJson c.side)
    , ("playerId", toJson c.playerId)
    , ("currentHp", toJson c.currentHp)
    , ("maxHp", toJson c.maxHp)
    , ("block", toJson c.block)
    , ("powers", toJson c.powers)
    , ("monsterMoveId", toJson c.monsterMoveId)
    , ("monsterStateLog", toJson c.monsterStateLog) ]

instance : FromJson WireCreature where
  fromJson? j := do
    let cid ← getFieldReq j "id"
    let ent ← getFieldReq j "modelEntry"
    let cat ← getFieldD j "modelCategory" "MONSTER"
    let sd ← getFieldD j "side" "enemy"
    let pid ← getFieldOpt j "playerId"
    let hp ← getFieldReq j "currentHp"
    let mhp ← getFieldReq j "maxHp"
    let blk ← getFieldD j "block" 0
    let pows ← getFieldD j "powers" []
    let mm ← getFieldOpt j "monsterMoveId"
    let mlog ← getFieldD j "monsterStateLog" []
    .ok { id := cid, modelEntry := ent, modelCategory := cat, side := sd, playerId := pid
        , currentHp := hp, maxHp := mhp, block := blk, powers := pows
        , monsterMoveId := mm, monsterStateLog := mlog }

structure WirePlayer where
  playerId       : Nat
  creatureId     : Nat
  characterEntry : String := "IRONCLAD"
  energy         : Nat := 3
  baseMaxEnergy  : Nat := 3
  stars          : Nat := 0
  turnNumber     : Nat := 1
  hand           : List WireCard := []
  draw           : List WireCard := []
  discard        : List WireCard := []
  exhaust        : List WireCard := []
  relics         : List WireRelic := []
  potions        : List WirePotion := []
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WirePlayer where
  toJson p := Json.mkObj
    [ ("playerId", toJson p.playerId)
    , ("creatureId", toJson p.creatureId)
    , ("characterEntry", toJson p.characterEntry)
    , ("energy", toJson p.energy)
    , ("baseMaxEnergy", toJson p.baseMaxEnergy)
    , ("stars", toJson p.stars)
    , ("turnNumber", toJson p.turnNumber)
    , ("hand", toJson p.hand)
    , ("draw", toJson p.draw)
    , ("discard", toJson p.discard)
    , ("exhaust", toJson p.exhaust)
    , ("relics", toJson p.relics)
    , ("potions", toJson p.potions) ]

instance : FromJson WirePlayer where
  fromJson? j := do
    let pid ← getFieldReq j "playerId"
    let cid ← getFieldReq j "creatureId"
    let ch ← getFieldD j "characterEntry" "IRONCLAD"
    let eng ← getFieldD j "energy" 3
    let bme ← getFieldD j "baseMaxEnergy" 3
    let strs ← getFieldD j "stars" 0
    let tn ← getFieldD j "turnNumber" 1
    let hd ← getFieldD j "hand" []
    let dr ← getFieldD j "draw" []
    let ds ← getFieldD j "discard" []
    let ex ← getFieldD j "exhaust" []
    let rel ← getFieldD j "relics" []
    let pot ← getFieldD j "potions" []
    .ok { playerId := pid, creatureId := cid, characterEntry := ch
        , energy := eng, baseMaxEnergy := bme, stars := strs, turnNumber := tn
        , hand := hd, draw := dr, discard := ds, exhaust := ex, relics := rel, potions := pot }

structure WireRng where
  counter : Nat := 0
  s0      : String := ""
  s1      : String := ""
  s2      : String := ""
  s3      : String := ""
  seed    : Option String := none
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireRng where
  toJson r := Json.mkObj
    [ ("counter", toJson r.counter)
    , ("s0", toJson r.s0)
    , ("s1", toJson r.s1)
    , ("s2", toJson r.s2)
    , ("s3", toJson r.s3)
    , ("seed", toJson r.seed) ]

instance : FromJson WireRng where
  fromJson? j := do
    let cnt ← getFieldD j "counter" 0
    let s0 ← getFieldD j "s0" ""
    let s1 ← getFieldD j "s1" ""
    let s2 ← getFieldD j "s2" ""
    let s3 ← getFieldD j "s3" ""
    let sd ← getFieldOpt j "seed"
    .ok { counter := cnt, s0 := s0, s1 := s1, s2 := s2, s3 := s3, seed := sd }

structure WireCombatSnapshot where
  combatId       : Nat := 1
  roundNumber    : Nat := 1
  currentSide    : String := "player"
  isInProgress   : Bool := true
  isEnding       : Bool := false
  nextInstanceId : Nat := 1000
  rng            : WireRng := {}
  allies         : List WireCreature := []
  enemies        : List WireCreature := []
  players        : List WirePlayer := []
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireCombatSnapshot where
  toJson c := Json.mkObj
    [ ("combatId", toJson c.combatId)
    , ("roundNumber", toJson c.roundNumber)
    , ("currentSide", toJson c.currentSide)
    , ("isInProgress", toJson c.isInProgress)
    , ("isEnding", toJson c.isEnding)
    , ("nextInstanceId", toJson c.nextInstanceId)
    , ("rng", toJson c.rng)
    , ("allies", toJson c.allies)
    , ("enemies", toJson c.enemies)
    , ("players", toJson c.players) ]

instance : FromJson WireCombatSnapshot where
  fromJson? j := do
    let cid ← getFieldD j "combatId" 1
    let rn ← getFieldD j "roundNumber" 1
    let cs ← getFieldD j "currentSide" "player"
    let ip ← getFieldD j "isInProgress" true
    let ie ← getFieldD j "isEnding" false
    let nid ← getFieldD j "nextInstanceId" 1000
    let rng ← getFieldD j "rng" {}
    let al ← getFieldD j "allies" []
    let en ← getFieldD j "enemies" []
    let pl ← getFieldD j "players" []
    .ok { combatId := cid, roundNumber := rn, currentSide := cs, isInProgress := ip
        , isEnding := ie, nextInstanceId := nid, rng := rng, allies := al, enemies := en, players := pl }

structure WireRunSnapshot where
  runSeed         : String := "0"
  currentActIndex : Nat := 0
  ascensionLevel  : Nat := 0
  gold            : Nat := 99
  totalFloors     : Nat := 0
  currentRoom     : String := "unassigned"
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireRunSnapshot where
  toJson r := Json.mkObj
    [ ("runSeed", toJson r.runSeed)
    , ("currentActIndex", toJson r.currentActIndex)
    , ("ascensionLevel", toJson r.ascensionLevel)
    , ("gold", toJson r.gold)
    , ("totalFloors", toJson r.totalFloors)
    , ("currentRoom", toJson r.currentRoom) ]

instance : FromJson WireRunSnapshot where
  fromJson? j := do
    let rs ← getFieldD j "runSeed" "0"
    let act ← getFieldD j "currentActIndex" 0
    let asc ← getFieldD j "ascensionLevel" 0
    let g ← getFieldD j "gold" 99
    let fl ← getFieldD j "totalFloors" 0
    let rm ← getFieldD j "currentRoom" "unassigned"
    .ok { runSeed := rs, currentActIndex := act, ascensionLevel := asc
        , gold := g, totalFloors := fl, currentRoom := rm }

structure WireInitialState where
  run            : WireRunSnapshot := {}
  combat         : Option WireCombatSnapshot := none
  playerIds      : List Nat := [1]
  nextActionId   : Nat := 0
  nextHookId     : Nat := 0
  nextChecksumId : Nat := 0
  isInCombat     : Bool := true
  canceledCount  : Nat := 0
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireInitialState where
  toJson s := Json.mkObj
    [ ("run", toJson s.run)
    , ("combat", toJson s.combat)
    , ("playerIds", toJson s.playerIds)
    , ("nextActionId", toJson s.nextActionId)
    , ("nextHookId", toJson s.nextHookId)
    , ("nextChecksumId", toJson s.nextChecksumId)
    , ("isInCombat", toJson s.isInCombat)
    , ("canceledCount", toJson s.canceledCount) ]

instance : FromJson WireInitialState where
  fromJson? j := do
    let run ← getFieldD j "run" {}
    let cmb ← getFieldOpt j "combat"
    let pids ← getFieldD j "playerIds" [1]
    let na ← getFieldD j "nextActionId" 0
    let nh ← getFieldD j "nextHookId" 0
    let nc ← getFieldD j "nextChecksumId" 0
    let ic ← getFieldD j "isInCombat" true
    let cc ← getFieldD j "canceledCount" 0
    .ok { run := run, combat := cmb, playerIds := pids, nextActionId := na
        , nextHookId := nh, nextChecksumId := nc, isInCombat := ic, canceledCount := cc }

structure WireChoiceResult where
  «type»     : String
  ids        : List Nat := []
  creatureId : Option Nat := none
  index      : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireChoiceResult where
  toJson c := Json.mkObj
    [ ("type", toJson c.«type»)
    , ("ids", toJson c.ids)
    , ("creatureId", toJson c.creatureId)
    , ("index", toJson c.index) ]

instance : FromJson WireChoiceResult where
  fromJson? j := do
    let t ← getFieldReq j "type"
    let ids ← getFieldD j "ids" []
    let cid ← getFieldOpt j "creatureId"
    let idx ← getFieldOpt j "index"
    .ok { «type» := t, ids := ids, creatureId := cid, index := idx }

structure WireActionPayload where
  «type»     : String
  cardId     : Option Nat := none
  targetId   : Option Nat := none
  slotIdx    : Option Nat := none
  canBackOut : Bool := true
  hookId     : Option Nat := none
  row        : Option Nat := none
  col        : Option Nat := none
  relicId    : Option WireModelId := none
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireActionPayload where
  toJson p := Json.mkObj
    [ ("type", toJson p.«type»)
    , ("cardId", toJson p.cardId)
    , ("targetId", toJson p.targetId)
    , ("slotIdx", toJson p.slotIdx)
    , ("canBackOut", toJson p.canBackOut)
    , ("hookId", toJson p.hookId)
    , ("row", toJson p.row)
    , ("col", toJson p.col)
    , ("relicId", toJson p.relicId) ]

instance : FromJson WireActionPayload where
  fromJson? j := do
    let t ← getFieldReq j "type"
    let cid ← getFieldOpt j "cardId"
    let tid ← getFieldOpt j "targetId"
    let si ← getFieldOpt j "slotIdx"
    let cbo ← getFieldD j "canBackOut" true
    let hid ← getFieldOpt j "hookId"
    let r ← getFieldOpt j "row"
    let c ← getFieldOpt j "col"
    let rid ← getFieldOpt j "relicId"
    .ok { «type» := t, cardId := cid, targetId := tid, slotIdx := si
        , canBackOut := cbo, hookId := hid, row := r, col := c, relicId := rid }

structure WireCombatReplayEvent where
  eventType    : String
  playerId     : Option Nat := none
  payload      : Option WireActionPayload := none
  hookId       : Option Nat := none
  actionId     : Option Nat := none
  choiceId     : Option Nat := none
  choiceResult : Option WireChoiceResult := none
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireCombatReplayEvent where
  toJson e := Json.mkObj
    [ ("eventType", toJson e.eventType)
    , ("playerId", toJson e.playerId)
    , ("payload", toJson e.payload)
    , ("hookId", toJson e.hookId)
    , ("actionId", toJson e.actionId)
    , ("choiceId", toJson e.choiceId)
    , ("choiceResult", toJson e.choiceResult) ]

instance : FromJson WireCombatReplayEvent where
  fromJson? j := do
    let et ← getFieldReq j "eventType"
    let pid ← getFieldOpt j "playerId"
    let pl ← getFieldOpt j "payload"
    let hid ← getFieldOpt j "hookId"
    let aid ← getFieldOpt j "actionId"
    let cid ← getFieldOpt j "choiceId"
    let cr ← getFieldOpt j "choiceResult"
    .ok { eventType := et, playerId := pid, payload := pl, hookId := hid
        , actionId := aid, choiceId := cid, choiceResult := cr }

structure WireOutOfCombatSyncEvent where
  «type»    : String
  row       : Nat := 0
  col       : Nat := 0
  pointType : Option String := none
  roomType  : Option String := none
  optionKey : Option String := none
  goldDelta : Int := 0
  hpDelta   : Int := 0
  cardModel : Option WireModelId := none
  goldCost  : Nat := 0
  healAmt   : Nat := 0
  goldGain  : Nat := 0
  relicId   : Option WireModelId := none
  rarity    : String := "common"
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireOutOfCombatSyncEvent where
  toJson e := Json.mkObj
    [ ("type", toJson e.«type»)
    , ("row", toJson e.row)
    , ("col", toJson e.col)
    , ("pointType", toJson e.pointType)
    , ("roomType", toJson e.roomType)
    , ("optionKey", toJson e.optionKey)
    , ("goldDelta", toJson e.goldDelta)
    , ("hpDelta", toJson e.hpDelta)
    , ("cardModel", toJson e.cardModel)
    , ("goldCost", toJson e.goldCost)
    , ("healAmt", toJson e.healAmt)
    , ("goldGain", toJson e.goldGain)
    , ("relicId", toJson e.relicId)
    , ("rarity", toJson e.rarity) ]

instance : FromJson WireOutOfCombatSyncEvent where
  fromJson? j := do
    let t ← getFieldReq j "type"
    let r ← getFieldD j "row" 0
    let c ← getFieldD j "col" 0
    let pt ← getFieldOpt j "pointType"
    let rt ← getFieldOpt j "roomType"
    let ok ← getFieldOpt j "optionKey"
    let gd ← getFieldD j "goldDelta" 0
    let hd ← getFieldD j "hpDelta" 0
    let cm ← getFieldOpt j "cardModel"
    let gc ← getFieldD j "goldCost" 0
    let ha ← getFieldD j "healAmt" 0
    let gg ← getFieldD j "goldGain" 0
    let rid ← getFieldOpt j "relicId"
    let rar ← getFieldD j "rarity" "common"
    .ok { «type» := t, row := r, col := c, pointType := pt, roomType := rt
        , optionKey := ok, goldDelta := gd, hpDelta := hd, cardModel := cm
        , goldCost := gc, healAmt := ha, goldGain := gg, relicId := rid, rarity := rar }

structure WireIdDelta where
  id    : Nat
  delta : Int
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireIdDelta where
  toJson d := Json.mkObj [("id", toJson d.id), ("delta", toJson d.delta)]

instance : FromJson WireIdDelta where
  fromJson? j := do
    let i ← getFieldReq j "id"
    let d ← getFieldReq j "delta"
    .ok { id := i, delta := d }

structure WirePowerDelta where
  creatureId : Nat
  category   : String := "POWER"
  entry      : String
  delta      : Int
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WirePowerDelta where
  toJson d := Json.mkObj
    [ ("creatureId", toJson d.creatureId)
    , ("category", toJson d.category)
    , ("entry", toJson d.entry)
    , ("delta", toJson d.delta) ]

instance : FromJson WirePowerDelta where
  fromJson? j := do
    let cid ← getFieldReq j "creatureId"
    let cat ← getFieldD j "category" "POWER"
    let ent ← getFieldReq j "entry"
    let dlt ← getFieldReq j "delta"
    .ok { creatureId := cid, category := cat, entry := ent, delta := dlt }

structure WireOpaqueDelta where
  label        : String := "opaque"
  hpDeltas     : List WireIdDelta := []
  blockDeltas  : List WireIdDelta := []
  powerDeltas  : List WirePowerDelta := []
  energyDeltas : List WireIdDelta := []
  starsDeltas  : List WireIdDelta := []
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireOpaqueDelta where
  toJson o := Json.mkObj
    [ ("label", toJson o.label)
    , ("hpDeltas", toJson o.hpDeltas)
    , ("blockDeltas", toJson o.blockDeltas)
    , ("powerDeltas", toJson o.powerDeltas)
    , ("energyDeltas", toJson o.energyDeltas)
    , ("starsDeltas", toJson o.starsDeltas) ]

instance : FromJson WireOpaqueDelta where
  fromJson? j := do
    let lbl ← getFieldD j "label" "opaque"
    let hp ← getFieldD j "hpDeltas" []
    let blk ← getFieldD j "blockDeltas" []
    let pow ← getFieldD j "powerDeltas" []
    let eng ← getFieldD j "energyDeltas" []
    let str ← getFieldD j "starsDeltas" []
    .ok { label := lbl, hpDeltas := hp, blockDeltas := blk, powerDeltas := pow
        , energyDeltas := eng, starsDeltas := str }

structure WireTimelineEvent where
  seqIdx                : Nat
  actIndex              : Nat := 0
  floor                 : Nat := 1
  roundNumber           : Nat := 1
  actorPlayerId         : Nat := 1
  kind                  : String
  combat                : Option WireCombatReplayEvent := none
  pauseActionId         : Option Nat := none
  cancelPlayCardActions : Bool := false
  runSync               : Option WireOutOfCombatSyncEvent := none
  opaqueDelta           : Option WireOpaqueDelta := none
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireTimelineEvent where
  toJson e := Json.mkObj
    [ ("seqIdx", toJson e.seqIdx)
    , ("actIndex", toJson e.actIndex)
    , ("floor", toJson e.floor)
    , ("roundNumber", toJson e.roundNumber)
    , ("actorPlayerId", toJson e.actorPlayerId)
    , ("kind", toJson e.kind)
    , ("combat", toJson e.combat)
    , ("pauseActionId", toJson e.pauseActionId)
    , ("cancelPlayCardActions", toJson e.cancelPlayCardActions)
    , ("runSync", toJson e.runSync)
    , ("opaque", toJson e.opaqueDelta) ]

instance : FromJson WireTimelineEvent where
  fromJson? j := do
    let si ← getFieldReq j "seqIdx"
    let act ← getFieldD j "actIndex" 0
    let fl ← getFieldD j "floor" 1
    let rn ← getFieldD j "roundNumber" 1
    let ap ← getFieldD j "actorPlayerId" 1
    let k ← getFieldReq j "kind"
    let cmb ← getFieldOpt j "combat"
    let pai ← getFieldOpt j "pauseActionId"
    let cpc ← getFieldD j "cancelPlayCardActions" false
    let rs ← getFieldOpt j "runSync"
    let opq ← getFieldOpt j "opaque"
    .ok { seqIdx := si, actIndex := act, floor := fl, roundNumber := rn
        , actorPlayerId := ap, kind := k, combat := cmb, pauseActionId := pai
        , cancelPlayCardActions := cpc, runSync := rs, opaqueDelta := opq }

structure WireChecksumEntry where
  eventIndex : Nat
  checksum   : String
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireChecksumEntry where
  toJson c := Json.mkObj [("eventIndex", toJson c.eventIndex), ("checksum", toJson c.checksum)]

instance : FromJson WireChecksumEntry where
  fromJson? j := do
    let idx ← getFieldReq j "eventIndex"
    let cs ← getFieldReq j "checksum"
    .ok { eventIndex := idx, checksum := cs }

structure WireTraceBundle where
  schemaVersion     : Nat := traceSchemaVersion
  viewerPlayerId    : Nat := 1
  keyframeStride    : Nat := 2
  initialState      : WireInitialState
  events            : List WireTimelineEvent := []
  expectedChecksums : List WireChecksumEntry := []
  deriving Repr, DecidableEq, Inhabited

instance : ToJson WireTraceBundle where
  toJson b := Json.mkObj
    [ ("schemaVersion", toJson b.schemaVersion)
    , ("viewerPlayerId", toJson b.viewerPlayerId)
    , ("keyframeStride", toJson b.keyframeStride)
    , ("initialState", toJson b.initialState)
    , ("events", toJson b.events)
    , ("expectedChecksums", toJson b.expectedChecksums) ]

instance : FromJson WireTraceBundle where
  fromJson? j := do
    let sv ← getFieldD j "schemaVersion" traceSchemaVersion
    let vp ← getFieldD j "viewerPlayerId" 1
    let ks ← getFieldD j "keyframeStride" 2
    let init ← getFieldReq j "initialState"
    let evs ← getFieldD j "events" []
    let cs ← getFieldD j "expectedChecksums" []
    .ok { schemaVersion := sv, viewerPlayerId := vp, keyframeStride := ks
        , initialState := init, events := evs, expectedChecksums := cs }

-- ============================================================================
-- Pure Algebraic Encoders & Decoders
-- ============================================================================

def encodeModelId (m : ModelId) : WireModelId :=
  { category := m.category, entry := m.entry }

def decodeModelId (w : WireModelId) : ModelId :=
  { category := w.category, entry := w.entry }

def encodeChoiceResult : ChoiceResult → WireChoiceResult
  | .cards ids   => { «type» := "cards", ids := ids }
  | .creature c  => { «type» := "creature", creatureId := some c }
  | .index idx   => { «type» := "index", index := some idx }
  | .skipped     => { «type» := "skipped" }

def decodeChoiceResult (w : WireChoiceResult) : Except String ChoiceResult :=
  match w.«type» with
  | "cards"    => .ok (.cards w.ids)
  | "creature" =>
      match w.creatureId with
      | some cid => .ok (.creature cid)
      | none     => .error "ChoiceResult 'creature' missing creatureId"
  | "index"    =>
      match w.index with
      | some idx => .ok (.index idx)
      | none     => .error "ChoiceResult 'index' missing index"
  | "skipped"  => .ok .skipped
  | t          => .error s!"Unknown ChoiceResult type: {t}"

def encodeActionPayload : ReplayActionPayload → WireActionPayload
  | .playCard cid tid          => { «type» := "playCard", cardId := some cid, targetId := tid }
  | .usePotion slot tid        => { «type» := "usePotion", slotIdx := some slot, targetId := tid }
  | .discardPotion slot        => { «type» := "discardPotion", slotIdx := some slot }
  | .endPlayerTurn cbo         => { «type» := "endPlayerTurn", canBackOut := cbo }
  | .undoEndPlayerTurn         => { «type» := "undoEndPlayerTurn" }
  | .readyToBeginEnemyTurn     => { «type» := "readyToBeginEnemyTurn" }
  | .hookAction hid            => { «type» := "hookAction", hookId := some hid }
  | .voteMapCoord r c          => { «type» := "voteMapCoord", row := some r, col := some c }
  | .moveMapCoord r c          => { «type» := "moveMapCoord", row := some r, col := some c }
  | .pickRelic mid             => { «type» := "pickRelic", relicId := some (encodeModelId mid) }
  | .voteNextAct               => { «type» := "voteNextAct" }

def decodeActionPayload (w : WireActionPayload) : Except String ReplayActionPayload :=
  match w.«type» with
  | "playCard" =>
      match w.cardId with
      | some cid => .ok (.playCard cid w.targetId)
      | none     => .error "ActionPayload 'playCard' missing cardId"
  | "usePotion" =>
      match w.slotIdx with
      | some slot => .ok (.usePotion slot w.targetId)
      | none      => .error "ActionPayload 'usePotion' missing slotIdx"
  | "discardPotion" =>
      match w.slotIdx with
      | some slot => .ok (.discardPotion slot)
      | none      => .error "ActionPayload 'discardPotion' missing slotIdx"
  | "endPlayerTurn"         => .ok (.endPlayerTurn w.canBackOut)
  | "undoEndPlayerTurn"     => .ok .undoEndPlayerTurn
  | "readyToBeginEnemyTurn" => .ok .readyToBeginEnemyTurn
  | "hookAction" =>
      match w.hookId with
      | some hid => .ok (.hookAction hid)
      | none     => .error "ActionPayload 'hookAction' missing hookId"
  | "voteMapCoord" =>
      match w.row, w.col with
      | some r, some c => .ok (.voteMapCoord r c)
      | _, _           => .error "ActionPayload 'voteMapCoord' missing row/col"
  | "moveMapCoord" =>
      match w.row, w.col with
      | some r, some c => .ok (.moveMapCoord r c)
      | _, _           => .error "ActionPayload 'moveMapCoord' missing row/col"
  | "pickRelic" =>
      match w.relicId with
      | some rid => .ok (.pickRelic (decodeModelId rid))
      | none     => .error "ActionPayload 'pickRelic' missing relicId"
  | "voteNextAct"           => .ok .voteNextAct
  | t                       => .error s!"Unknown ActionPayload type: {t}"

def encodeCombatReplayEvent (ce : CombatReplayEvent) : WireCombatReplayEvent :=
  { eventType := encodeCombatReplayEventType ce.eventType
  , playerId := ce.playerId
  , payload := ce.payload.map encodeActionPayload
  , hookId := ce.hookId
  , actionId := ce.actionId
  , choiceId := ce.choiceId
  , choiceResult := ce.choiceResult.map encodeChoiceResult }

def decodeCombatReplayEvent (w : WireCombatReplayEvent) : Except String CombatReplayEvent := do
  let et ← decodeCombatReplayEventType w.eventType
  let pl ← match w.payload with
    | none => .ok none
    | some wp => (decodeActionPayload wp).map some
  let cr ← match w.choiceResult with
    | none => .ok none
    | some wc => (decodeChoiceResult wc).map some
  .ok { eventType := et, playerId := w.playerId, payload := pl
      , hookId := w.hookId, actionId := w.actionId, choiceId := w.choiceId, choiceResult := cr }

def encodeOutOfCombatSync : OutOfCombatSyncEvent → WireOutOfCombatSyncEvent
  | .mapVote r c =>
      { «type» := "mapVote", row := r, col := c }
  | .mapMove r c pt rt =>
      { «type» := "mapMove", row := r, col := c
      , pointType := some (encodeMapPointType pt), roomType := some (encodeRoomType rt) }
  | .eventChoice key gd hd =>
      { «type» := "eventChoice", optionKey := some key, goldDelta := gd, hpDelta := hd }
  | .merchantBuy cardOpt cost =>
      { «type» := "merchantBuy", cardModel := cardOpt.map encodeModelId, goldCost := cost }
  | .restSiteHeal amt =>
      { «type» := "restSiteHeal", healAmt := amt }
  | .rewardPick cardOpt gain =>
      { «type» := "rewardPick", cardModel := cardOpt.map encodeModelId, goldGain := gain }
  | .treasureRelicPick rid rar =>
      { «type» := "treasureRelicPick", relicId := some (encodeModelId rid), rarity := encodeRelicRarity rar }
  | .actAdvance =>
      { «type» := "actAdvance" }

def decodeOutOfCombatSync (w : WireOutOfCombatSyncEvent) : Except String OutOfCombatSyncEvent :=
  match w.«type» with
  | "mapVote" => .ok (.mapVote w.row w.col)
  | "mapMove" => do
      let pt ← match w.pointType with
        | some s => decodeMapPointType s
        | none   => .error "OutOfCombatSync 'mapMove' missing pointType"
      let rt ← match w.roomType with
        | some s => decodeRoomType s
        | none   => .error "OutOfCombatSync 'mapMove' missing roomType"
      .ok (.mapMove w.row w.col pt rt)
  | "eventChoice" =>
      match w.optionKey with
      | some k => .ok (.eventChoice k w.goldDelta w.hpDelta)
      | none   => .error "OutOfCombatSync 'eventChoice' missing optionKey"
  | "merchantBuy" =>
      .ok (.merchantBuy (w.cardModel.map decodeModelId) w.goldCost)
  | "restSiteHeal" =>
      .ok (.restSiteHeal w.healAmt)
  | "rewardPick" =>
      .ok (.rewardPick (w.cardModel.map decodeModelId) w.goldGain)
  | "treasureRelicPick" => do
      let rid ← match w.relicId with
        | some wm => .ok (decodeModelId wm)
        | none    => .error "OutOfCombatSync 'treasureRelicPick' missing relicId"
      let rar ← decodeRelicRarity w.rarity
      .ok (.treasureRelicPick rid rar)
  | "actAdvance" => .ok .actAdvance
  | t            => .error s!"Unknown OutOfCombatSync type: {t}"

def encodeOpaqueDelta (d : OpaqueStateDelta) : WireOpaqueDelta :=
  { label := d.label
  , hpDeltas := d.hpDeltas.map fun p => { id := p.1, delta := p.2 }
  , blockDeltas := d.blockDeltas.map fun p => { id := p.1, delta := p.2 }
  , powerDeltas := d.powerDeltas.map fun p =>
      { creatureId := p.1, category := p.2.1.category, entry := p.2.1.entry, delta := p.2.2 }
  , energyDeltas := d.energyDeltas.map fun p => { id := p.1, delta := p.2 }
  , starsDeltas := d.starsDeltas.map fun p => { id := p.1, delta := p.2 } }

def decodeOpaqueDelta (w : WireOpaqueDelta) : Except String OpaqueStateDelta :=
  .ok { label := w.label
      , hpDeltas := w.hpDeltas.map fun d => (d.id, d.delta)
      , blockDeltas := w.blockDeltas.map fun d => (d.id, d.delta)
      , powerDeltas := w.powerDeltas.map fun d => (d.creatureId, { category := d.category, entry := d.entry }, d.delta)
      , energyDeltas := w.energyDeltas.map fun d => (d.id, d.delta)
      , starsDeltas := w.starsDeltas.map fun d => (d.id, d.delta) }

def encodeTimelineEvent (ev : TimelineEvent) : WireTimelineEvent :=
  let base : WireTimelineEvent :=
    { seqIdx := ev.seqIdx
    , actIndex := ev.actIndex
    , floor := ev.floor
    , roundNumber := ev.roundNumber
    , actorPlayerId := ev.actorPlayerId
    , kind := "" }
  match ev.kind with
  | .combat ce =>
      { base with kind := "combat", combat := some (encodeCombatReplayEvent ce) }
  | .pauseActionForChoice aid opts =>
      { base with kind := "pauseActionForChoice", pauseActionId := some aid
                , cancelPlayCardActions := opts.cancelPlayCardActions }
  | .endRoundAndRunEnemies =>
      { base with kind := "endRoundAndRunEnemies" }
  | .runSync rEv =>
      { base with kind := "runSync", runSync := some (encodeOutOfCombatSync rEv) }
  | .opaqueStep delta =>
      { base with kind := "opaqueStep", opaqueDelta := some (encodeOpaqueDelta delta) }

def decodeTimelineEvent (w : WireTimelineEvent) : Except String TimelineEvent := do
  let kind ← match w.kind with
    | "combat" =>
        match w.combat with
        | some ce => (decodeCombatReplayEvent ce).map TimelineEventKind.combat
        | none    => .error s!"Event #{w.seqIdx} kind 'combat' missing combat payload"
    | "pauseActionForChoice" =>
        match w.pauseActionId with
        | some aid => .ok (.pauseActionForChoice aid { cancelPlayCardActions := w.cancelPlayCardActions })
        | none     => .error s!"Event #{w.seqIdx} kind 'pauseActionForChoice' missing pauseActionId"
    | "endRoundAndRunEnemies" =>
        .ok .endRoundAndRunEnemies
    | "runSync" =>
        match w.runSync with
        | some rEv => (decodeOutOfCombatSync rEv).map TimelineEventKind.runSync
        | none     => .error s!"Event #{w.seqIdx} kind 'runSync' missing runSync payload"
    | "opaqueStep" =>
        match w.opaqueDelta with
        | some opq => (decodeOpaqueDelta opq).map TimelineEventKind.opaqueStep
        | none     => .error s!"Event #{w.seqIdx} kind 'opaqueStep' missing opaque payload"
    | k => .error s!"Unknown TimelineEvent kind at #{w.seqIdx}: {k}"
  .ok { seqIdx := w.seqIdx
      , actIndex := w.actIndex
      , floor := w.floor
      , roundNumber := w.roundNumber
      , actorPlayerId := w.actorPlayerId
      , kind := kind }

-- ============================================================================
-- State Snapshot Codecs (`TimelineState` / `TimelineArchive` <-> `WireTraceBundle`)
-- ============================================================================

def encodePower (p : PowerInstance) : WirePower :=
  { instanceId := p.instanceId
  , modelEntry := p.modelId.entry
  , powerType := encodePowerType p.powerType
  , stackType := encodePowerStackType p.stackType
  , allowNegative := p.allowNegative
  , amount := p.amount }

def decodePower (ownerId : CreatureId) (w : WirePower) : Except String PowerInstance := do
  let pt ← decodePowerType w.powerType
  let st ← decodePowerStackType w.stackType
  .ok { instanceId := w.instanceId
      , modelId := ModelId.mkPower w.modelEntry
      , ownerId := ownerId
      , powerType := pt
      , stackType := st
      , allowNegative := w.allowNegative
      , amount := w.amount }

def encodeCard (c : CardInstance) : WireCard :=
  { instanceId := c.instanceId
  , modelEntry := c.modelId.entry
  , ownerId := c.ownerId
  , cardType := encodeCardType c.cardType
  , rarity := encodeCardRarity c.rarity
  , targetType := encodeTargetType c.targetType
  , baseCost := c.energyCost.baseCost
  , costsX := c.energyCost.costsX
  , starCost := c.baseStarCost
  , upgradeLevel := c.upgradeLevel
  , baseDamage := c.baseDamage.truncate
  , baseBlock := c.baseBlock.truncate
  , gainsBlock := c.gainsBlock }

def decodeCard (w : WireCard) : Except String CardInstance := do
  let ct ← decodeCardType w.cardType
  let rar ← decodeCardRarity w.rarity
  let tt ← decodeTargetType w.targetType
  .ok { instanceId := w.instanceId
      , modelId := ModelId.mkCard w.modelEntry
      , ownerId := w.ownerId
      , cardType := ct
      , rarity := rar
      , targetType := tt
      , energyCost := CardEnergyCost.mkCanonical w.baseCost w.costsX
      , baseStarCost := w.starCost
      , upgradeLevel := w.upgradeLevel
      , baseDamage := Dec.ofInt w.baseDamage
      , baseBlock := Dec.ofInt w.baseBlock
      , gainsBlock := w.gainsBlock }

def encodeRelic (r : RelicInstance) : WireRelic :=
  { modelEntry := r.modelId.entry, rarity := encodeRelicRarity r.rarity }

def decodeRelic (w : WireRelic) : Except String RelicInstance := do
  let rar ← decodeRelicRarity w.rarity
  .ok { modelId := ModelId.mkRelic w.modelEntry, rarity := rar }

def encodePotion : Option PotionInstance → WirePotion
  | none   => { modelEntry := none }
  | some p => { modelEntry := some p.modelId.entry }

def decodePotion (w : WirePotion) : Option PotionInstance :=
  w.modelEntry.map fun ent => { modelId := ModelId.mkPotion ent }

def encodeCreature (c : Creature) : WireCreature :=
  { id := c.id
  , modelEntry := c.modelId.entry
  , modelCategory := c.modelId.category
  , side := encodeCombatSide c.side
  , playerId := c.playerId
  , currentHp := c.currentHp
  , maxHp := c.maxHp
  , block := c.block
  , powers := c.powers.map encodePower
  , monsterMoveId := c.monster.map (·.currentMoveId)
  , monsterStateLog := (c.monster.map (·.stateLog)).getD [] }

def decodeCreature (w : WireCreature) : Except String Creature := do
  let sd ← decodeCombatSide w.side
  let pows ← w.powers.mapM (decodePower w.id)
  let mid : ModelId := { category := w.modelCategory, entry := w.modelEntry }
  let monsterOpt : Option MonsterInfo :=
    w.monsterMoveId.map fun mv =>
      { modelId := mid, currentMoveId := mv, stateLog := w.monsterStateLog }
  .ok { id := w.id
      , modelId := mid
      , side := sd
      , playerId := w.playerId
      , currentHp := w.currentHp
      , maxHp := w.maxHp
      , block := w.block
      , powers := pows
      , monster := monsterOpt }

def encodePlayer (p : Player) : WirePlayer :=
  let (eng, bme, strs, tn, hd, dr, ds, ex) :=
    match p.combatState with
    | none => (0, 3, 0, 1, [], [], [], [])
    | some pcs =>
        ( pcs.energy, pcs.baseMaxEnergy, pcs.stars, pcs.turnNumber
        , pcs.piles.hand.map encodeCard
        , pcs.piles.draw.map encodeCard
        , pcs.piles.discard.map encodeCard
        , pcs.piles.exhaust.map encodeCard )
  { playerId := p.playerId
  , creatureId := p.creatureId
  , characterEntry := p.characterId.entry
  , energy := eng
  , baseMaxEnergy := bme
  , stars := strs
  , turnNumber := tn
  , hand := hd
  , draw := dr
  , discard := ds
  , exhaust := ex
  , relics := p.relics.map encodeRelic
  , potions := p.potions.map encodePotion }

def decodePlayer (w : WirePlayer) : Except String Player := do
  let hd ← w.hand.mapM decodeCard
  let dr ← w.draw.mapM decodeCard
  let ds ← w.discard.mapM decodeCard
  let ex ← w.exhaust.mapM decodeCard
  let rels ← w.relics.mapM decodeRelic
  let pots := w.potions.map decodePotion
  .ok { playerId := w.playerId
      , creatureId := w.creatureId
      , characterId := ModelId.mkCharacter w.characterEntry
      , relics := rels
      , potions := pots
      , combatState := some
          { turnNumber := w.turnNumber
          , energy := w.energy
          , baseMaxEnergy := w.baseMaxEnergy
          , stars := w.stars
          , piles := { hand := hd, draw := dr, discard := ds, exhaust := ex } } }

def encodeRng (r : Rng) : WireRng :=
  { counter := r.counter
  , s0 := uInt64ToStr r.state.s0
  , s1 := uInt64ToStr r.state.s1
  , s2 := uInt64ToStr r.state.s2
  , s3 := uInt64ToStr r.state.s3 }

def decodeRng (w : WireRng) : Except String Rng :=
  if w.s0 == "" && w.s1 == "" && w.s2 == "" && w.s3 == "" then
    match w.seed with
    | some sdStr => do
        let sd ← parseUInt64Str sdStr
        .ok { (Rng.ofSeed sd) with counter := w.counter }
    | none => .error "WireRng missing s0..s3 and seed"
  else do
    let s0 ← parseUInt64Str w.s0
    let s1 ← parseUInt64Str w.s1
    let s2 ← parseUInt64Str w.s2
    let s3 ← parseUInt64Str w.s3
    .ok { counter := w.counter, state := { s0 := s0, s1 := s1, s2 := s2, s3 := s3 } }

def encodeCombatSnapshot (cs : CombatState) : WireCombatSnapshot :=
  { combatId := cs.combatId
  , roundNumber := cs.roundNumber
  , currentSide := encodeCombatSide cs.currentSide
  , isInProgress := cs.isInProgress
  , isEnding := cs.isEnding
  , nextInstanceId := cs.nextInstanceId
  , rng := encodeRng cs.rng
  , allies := cs.allies.map encodeCreature
  , enemies := cs.enemies.map encodeCreature
  , players := cs.players.map encodePlayer }

def decodeCombatSnapshot (w : WireCombatSnapshot) : Except String CombatState := do
  let sd ← decodeCombatSide w.currentSide
  let rng ← decodeRng w.rng
  let al ← w.allies.mapM decodeCreature
  let en ← w.enemies.mapM decodeCreature
  let pl ← w.players.mapM decodePlayer
  .ok { combatId := w.combatId
      , roundNumber := w.roundNumber
      , currentSide := sd
      , isInProgress := w.isInProgress
      , isEnding := w.isEnding
      , nextInstanceId := w.nextInstanceId
      , rng := rng
      , allies := al
      , enemies := en
      , players := pl }

def encodeRunSnapshot (rs : RunState) : WireRunSnapshot :=
  { runSeed := uInt64ToStr rs.runSeed
  , currentActIndex := rs.currentActIndex
  , ascensionLevel := rs.ascensionLevel
  , gold := rs.gold
  , totalFloors := rs.totalFloors
  , currentRoom := encodeRoomType rs.currentRoom }

def decodeRunSnapshot (w : WireRunSnapshot) : Except String RunState := do
  let rs ← parseUInt64Str w.runSeed
  let rm ← decodeRoomType w.currentRoom
  .ok { runSeed := rs
      , currentActIndex := w.currentActIndex
      , ascensionLevel := w.ascensionLevel
      , gold := w.gold
      , totalFloors := w.totalFloors
      , currentRoom := rm
      , rngSet := RunRngSet.ofSeed rs }

def encodeTimelineState (st : TimelineState) : WireInitialState :=
  let pids :=
    if !st.queueSet.queues.isEmpty then st.queueSet.queues.map (·.ownerId)
    else match st.combat with
      | some cs => cs.players.map (·.playerId)
      | none    => [1]
  { run := encodeRunSnapshot st.runState
  , combat := st.combat.map encodeCombatSnapshot
  , playerIds := pids
  , nextActionId := st.queueSet.nextActionId
  , nextHookId := st.queueSet.nextHookId
  , nextChecksumId := st.counters.nextChecksumId
  , isInCombat := st.queueSet.isInCombat
  , canceledCount := st.queueSet.canceledCount }

def decodeTimelineState (w : WireInitialState) : Except String TimelineState := do
  let rs ← decodeRunSnapshot w.run
  let cmb ← match w.combat with
    | none => .ok none
    | some wc => (decodeCombatSnapshot wc).map some
  let baseQs := ActionQueueSet.init w.playerIds w.nextActionId w.nextHookId
  let qs0 := if w.isInCombat then baseQs.combatStarted else baseQs
  let qs := { qs0 with canceledCount := w.canceledCount }
  let ctrs : SyncCounters :=
    { nextActionId := w.nextActionId
    , nextHookId := w.nextHookId
    , nextChecksumId := w.nextChecksumId }
  .ok { runState := rs
      , combat := cmb
      , queueSet := qs
      , choiceSync := PlayerChoiceSynchronizer.init w.playerIds
      , counters := ctrs }

def encodeArchiveBundle (archive : TimelineArchive) (keyframeStride : Nat := 2) :
    WireTraceBundle :=
  let csums := archive.keyframes.map fun kf =>
    { eventIndex := kf.eventIndex, checksum := uInt64ToStr kf.checksum }
  { schemaVersion := traceSchemaVersion
  , viewerPlayerId := archive.viewerPlayerId
  , keyframeStride := max 1 keyframeStride
  , initialState := encodeTimelineState archive.initialState
  , events := archive.events.map encodeTimelineEvent
  , expectedChecksums := csums }

def decodeArchiveBundle (env : EffectEnv) (bundle : WireTraceBundle) :
    Except String TimelineArchive :=
  if bundle.schemaVersion != traceSchemaVersion then
    .error s!"Unsupported trace schemaVersion={bundle.schemaVersion} (expected {traceSchemaVersion})"
  else do
    let initSt ← decodeTimelineState bundle.initialState
    let evs ← bundle.events.mapM decodeTimelineEvent
    .ok (buildArchive env initSt evs bundle.keyframeStride bundle.viewerPlayerId)

def parseTraceJson (raw : String) : Except String WireTraceBundle := do
  let j ← Json.parse raw
  fromJson? j

def serializeTraceJson (bundle : WireTraceBundle) (pretty : Bool := false) : String :=
  let j := toJson bundle
  if pretty then j.pretty else j.compress

-- ============================================================================
-- Generic Keyframe Checksum Verification & Headless Step Inspector
-- ============================================================================

structure ChecksumMismatch where
  eventIndex : Nat
  expected   : String
  actual     : String
  deriving Repr, DecidableEq, Inhabited

structure ChecksumAuditReport where
  totalChecked : Nat
  mismatches   : List ChecksumMismatch
  allMatched   : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Compare actual `seek` FNV-1a checksums of `archive` against expected external checksum entries. -/
def verifyTraceChecksums (env : EffectEnv) (archive : TimelineArchive)
    (expected : List WireChecksumEntry) : ChecksumAuditReport :=
  let mm := expected.filterMap fun ent =>
    let act := uInt64ToStr (computeStateChecksum (seek env archive ent.eventIndex))
    if act == ent.checksum then none
    else some { eventIndex := ent.eventIndex, expected := ent.checksum, actual := act }
  { totalChecked := expected.length
  , mismatches := mm
  , allMatched := mm.isEmpty }

/-- Render a generic UI-free inspection dump for `archive` at step `stepIdx` (viewer-aware). -/
def inspectArchiveStep (env : EffectEnv) (archive : TimelineArchive) (stepIdx : Nat) : String :=
  let st := seek env archive stepIdx
  let csum := computeStateChecksum st
  let hexCs := String.ofList (Nat.toDigits 16 csum.toNat)
  let runLine :=
    s!"RunState: Act={st.runState.currentActIndex}, Floor={st.runState.totalFloors}, Gold={st.runState.gold}, Seed={uInt64ToStr st.runState.runSeed}"
  let combatLines :=
    match st.combat with
    | none => ["Combat: <inactive>"]
    | some cs =>
        let fmtC (c : Creature) : String :=
          let pStr :=
            if c.powers.isEmpty then "none"
            else String.intercalate ", " (c.powers.map fun p => s!"{p.modelId.entry}={p.amount}")
          s!"  - Creature#{c.id} {c.modelId.entry} [{encodeCombatSide c.side}]: HP={c.currentHp}/{c.maxHp}, Blk={c.block}, Powers=[{pStr}]"
        let fmtP (p : Player) : String :=
          let (e, s, hn, dn, dsn, exn) := match p.combatState with
            | none => (0, 0, 0, 0, 0, 0)
            | some pcs =>
                (pcs.energy, pcs.stars, pcs.piles.hand.length, pcs.piles.draw.length,
                 pcs.piles.discard.length, pcs.piles.exhaust.length)
          s!"  - Player#{p.playerId} ({p.characterId.entry}): Energy={e}, Stars={s}, Hand={hn}, Draw={dn}, Discard={dsn}, Exhaust={exn}"
        [ s!"Combat#{cs.combatId}: Round={cs.roundNumber}, Side={encodeCombatSide cs.currentSide}, InProgress={cs.isInProgress}, Ending={cs.isEnding}"
        , "Allies:" ] ++ cs.allies.map fmtC ++
        ["Enemies:"] ++ cs.enemies.map fmtC ++
        ["Players:"] ++ cs.players.map fmtP
  let stepHist := st.combatHistory.filter fun te => te.stepIdx + 1 == stepIdx
  let histLine :=
    if stepHist.isEmpty then "StepCombatHistory: []"
    else "StepCombatHistory: [" ++ String.intercalate ", " (stepHist.map fun te => te.entry.kindName) ++ "]"
  let stepAttrs :=
    if stepIdx == 0 then []
    else st.attributions.filter fun a => a.stepIdx + 1 == stepIdx
  let attrLine :=
    if stepAttrs.isEmpty then "StepAttributions: 0"
    else
      let details := String.intercalate "; " (stepAttrs.map fun a =>
        s!"{a.cardModelId.map (·.entry) |>.getD "hit"}->#{a.targetId}: mod={a.modifiedDamage.toNat}, unblk={a.unblockedDamage}, blk={a.blockedDamage}")
      s!"StepAttributions ({stepAttrs.length}): {details}"
  String.intercalate "\n"
    ([ s!"=== Timeline Step #{stepIdx} (Viewer=P{archive.viewerPlayerId}) ==="
     , s!"Checksum: 0x{hexCs} ({uInt64ToStr csum})"
     , runLine ] ++ combatLines ++ [histLine, attrLine])

end Sts2Model.Replay
# STS2 Lean 4 逻辑建模溯源与验证审计矩阵

本文档记录 `sts2_ideal` 项目中每个 Lean 4 模型、定理、静态目录提取脚本及 `.NET 9` 差分测试预言机与反编译 C# 参考源码（`reference/sts2/`）的精确对应关系。Windows x64 的同版本参考树可按 [本地重建流程](../README.md#从本机安装重建-c-参考源码)导出；`decompilation.json` 记录输入程序集、引用和 C# 产物的指纹。

**规则与证据边界**：`v0.113.1`（`d09d48e5`）的原版无 UI 规则只从核验后的 C# 调用链建模，含基类、命令和钩子。反编译结果不清楚时看同一程序集的 IL，不以局部录制替代规则。种子、解锁进度、玩家选择和服务器时间作为输入。目录收录、行为实现、独立 C# 差分、实机观测是不同证据；未录到的分支仍按源码实现和构造定向用例。

**换机后的首批行为建模**：先做 `RingOfTheSnake` 和 `BagOfPreparation`。两者的 `ModifyHandDraw` 都只给持有者在 `TurnNumber ≤ 1` 时加 2。沿 `Hook.ModifyHandDraw` → `CombatManager.SetupPlayerTurn` 核对普通／Late 两阶段，以及 Innate、手牌上限的处理顺序；Lean 接点是 `Hook/Pipeline.lean` 与 `Combat/TurnLoop.lean::setupPlayerTurn`。验收覆盖两遗物叠加、不影响其他玩家及后续回合、不改变普通效果抽牌。`Akabeko` 留给攻击生命周期批次：它施加的 Vigor 要追踪整条攻击命令和起始层数，不能近似成每次伤害扣层。

- **Lean 工具链**: `leanprover/lean4:v4.36.0`（纯 `Std`，零 `Mathlib`）
- **可信核保证**: `Sts2Model/` 与 `Sts2Sim/` 的代码主体无 `sorry`、自定义 `axiom` 或 `native_decide`
- **核心边界保证**: 核心 `Sts2Model/` 不含特定复盘启发式或求解算法，且绝不 `import Sts2Model.Examples.*`；具体下游工具示例如 [ReplayAnalyzerExample.lean](../Sts2Model/Examples/ReplayAnalyzerExample.lean) 严格建构在核心公开 API 之上
- **差分验证工具**: `.NET 9` (`net9.0`，零第三方 NuGet 包) + `uv run python`（仅使用 Python 标准库）

---

## 1. 模块溯源对照表（Lean 4 / .NET 9 ↔ C# Reference）

### 1.1 `Sts2Model/Core/` 基础设施层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Core/Dec.lean](../Sts2Model/Core/Dec.lean) | `System.Decimal`（贯穿 `Hook.cs`、`CreatureCmd.cs`、`PowerCmd.cs`、`Core.Models/*`） | 任意精度 base-10 有符号定点数 `(mantissa : Int, scale : Nat)`；`truncate` 采用 `Int.tdiv` 向零截断，严格对齐 C# `decimal.Truncate` 与 `(int)decimalVal`；含符号保号、交换律与单调性引理 |
| [Sts2Model/Core/Enums.lean](../Sts2Model/Core/Enums.lean) | `Core.ValueProps/ValueProp.cs`, `ValuePropExtensions.cs` 及 `CardType` / `CardRarity` / `TargetType` / `CardKeyword` / `CardTag` / `PowerType` / `PowerStackType` / `PowerInstanceType` / `RelicRarity` / `PileType` 等枚举 | 位标志与枚举定义完全对应 C# 原值；提供 `isPowered` / `isUnblockable` 等扩展判定函数 |
| [Sts2Model/Core/Enums.lean](../Sts2Model/Core/Enums.lean) 的 `AscensionLevel` / `AscensionVal` | `AscensionHelper.GetValueIfAscension` / `AscensionLevel` | A8 Tough Enemies 与 A9 Deadly Enemies 等进阶阈值；`AscensionVal.eval` 选择基础值或进阶值 |
| [Sts2Model/Core/Ids.lean](../Sts2Model/Core/Ids.lean) | `Core.Models/ModelId.cs`, `AbstractModel.cs`, `Core.Entities.Models/DeterministicModelComparer.cs`, `Core.Combat/CombatId.cs` | `ModelId (category, entry)`、`CreatureId` / `PlayerId` / `CardInstanceId` 等运行时 ID、`CanonicalModel α` vs 可变战斗实例区分，及字典序/确定性比较 |
| [Sts2Model/Core/Rng.lean](../Sts2Model/Core/Rng.lean) | `Core.Random/MegaRandom.cs`, `Rng.cs`, `RunRngSet.cs`, `Core.Extensions/ListExtensions.cs` | **Bit-exact** `SplitMix64` + `Xoshiro256**`、`NextDouble` / `NextFloat` / `NextGaussian` 前进状态及子 RNG 派生的 Fisher-Yates `UnstableShuffle`；含长度保持与置换群 (`List.Perm`) 证明 |

### 1.2 `Sts2Model/Model/` 领域实体状态层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Model/Cost.lean](../Sts2Model/Model/Cost.lean) | `Core.Entities.Cards/CardEnergyCost.cs`, `LocalCostModifier.cs`, `TemporaryCardCost.cs` | 绝对/相对局地费用修正 (`Absolute` / `Relative`, `IsReduceOnly`)、过期策略 (`WhenPlayed` / `EndOfTurn` / `EndOfCombat`)、X 费捕获值、升级减费及 `GetWithModifiers` 计算顺序 |
| [Sts2Model/Model/Card.lean](../Sts2Model/Model/Card.lean) | `Core.Models/CardModel.cs`, `EnchantmentModel.cs`, `AfflictionModel.cs`, `Core.Entities.Cards/CardPile.cs`, `CardPlay.cs` | `CardInstance`、`EnchantmentInstance`、`AfflictionInstance`、`PlayerPiles`（Draw / Hand / Discard / Exhaust / Play 五个战斗牌堆，上限 `maxCardsInHand = 10`）与 `CardPlay` 记录 |
| [Sts2Model/Model/Power.lean](../Sts2Model/Model/Power.lean) | `Core.Models/PowerModel.cs`, `Core.Entities.Powers/*.cs` | `PowerInstance`、`clampPowerAmount`（`[-999999999, 999999999]`）、`shouldRemoveDueToAmount` 及 `getTypeForAmount`（处理 `Counter + AllowNegative` 在负值时显式视为 Debuff） |
| [Sts2Model/Model/Creature.lean](../Sts2Model/Model/Creature.lean) | `Core.Entities.Creatures/Creature.cs`, `DamageResult.cs`, `SummonResult.cs` | 生物 HP / Block / Powers / `IsPrimaryEnemy` / Osty 标志、`loseHpInternal` 与 `DamageResult` 全字段（含 `overkillDamage` / `wasBlockBroken` / `wasFullyBlocked`） |
| [Sts2Model/Model/Orb.lean](../Sts2Model/Model/Orb.lean) | `Core.Entities.Orbs/OrbQueue.cs`, `Core.Models/OrbModel.cs`, `Core.Models.Orbs/*.cs` | `OrbQueue`（最大槽位 `maxCapacity = 10`）及 Lightning / Frost / Dark / Plasma / Glass 五类充能球模型 |
| [Sts2Model/Model/Player.lean](../Sts2Model/Model/Player.lean) | `Core.Entities.Players/Player.cs`, `PlayerCombatState.cs`, `Core.Entities.FoolArrows/ArrowSlot.cs` | 玩家套牌 `deck`、战斗资源 `energy` / `stars`、遗物/药水、Fool `ArrowSlot` 及 Regret/Regent 星能换算检查 `checkResourcesFor` |
| [Sts2Model/Model/State.lean](../Sts2Model/Model/State.lean) | `Core.Combat/CombatState.cs`, `PendingLossState.cs`, `Core.Runs/RunState.cs` | 完整 `CombatState`（`allies`、`enemies`、`players`、`modifiers`、`dominion`、`history`、`pendingLoss`、`rng`）与 `RunState` |

### 1.3 `Sts2Model/Hook/` 钩子总线与 Modding 注册层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Hook/Registry.lean](../Sts2Model/Hook/Registry.lean) | `Core.Hooks/Hook.cs`, `CombatState.cs` (`IterateHookListeners`, `Contains`), `RunState.cs` (`IterateHookListeners`) | `Hook.cs` 全部 **154** 个公开钩子名录（`16 Before` / `68 After` / `41 Modify` / `27 Should` / `2 Try`）、13 种 `ListenerRef`、快照收集 (`snapshotCombatListeners` / `snapshotRunListeners`) 与执行前存活校验 (`isListenerAlive`) |
| [Sts2Model/Hook/ModHelper.lean](../Sts2Model/Hook/ModHelper.lean) | `Core.Modding/ModHelper.cs`, `Core.Models/AbstractModel.cs`, `Core.Models.Powers/*.cs`, `Core.Models.Relics/*.cs` | 统一建模 `HookBehavior` 接口、`ModPoolRegistry`（卡池/遗物池/药水池不可逆冻结 `isFrozen`）与 `ModHookRegistry`（Ordinal 字符串排序去重注册表） |
| [Sts2Model/Hook/Pipeline.lean](../Sts2Model/Hook/Pipeline.lean) | `Core.Hooks/Hook.cs` | 完整还原 `ModifyDamage` / `ModifyDamageInternal`（附魔 → 加算 → 乘算 → 后期乘算 → 上限截断 → `max 0`）、`ModifyBlock`、`ModifyHpLost`（Before/After Osty 四阶段与截断增量日志）、`ModifyEnergyCostInCombat`（含 `originalCost < 0` 早返回）、`ModifyPowerAmountGiven/Received`、`ModifyPreBlockDamageTarget`、`ModifyUnblockedDamageTarget` 及 `Should*` / `Before*` / `After*` 流水线 |

### 1.4 `Sts2Model/Command/` 与 `Sts2Model/Combat/` 战斗命令与状态机层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Command/AttackCommand.lean](../Sts2Model/Command/AttackCommand.lean) | `Core.Commands.Builders/AttackCommand.cs` | 多段攻击构建器，按段分发伤害、汇总 `DamageResult` 并驱动 `AfterAttack` |
| [Sts2Model/Command/CreatureCmd.lean](../Sts2Model/Command/CreatureCmd.lean) | `Core.Commands/CreatureCmd.cs`, `Core.Entities.Creatures/Creature.cs` | `CreatureCmd.Damage` 全流程：伤前目标改写 (`ModifyPreBlockDamageTarget` 如 `DieForYou`)、格挡吸收、AfterOsty 转嫁过量伤害、Unblockable 绕过格挡、`LoseHp`、`GainBlock`、`Heal`、`GainMaxHp` 与死亡判定 |
| [Sts2Model/Command/CardCmd.lean](../Sts2Model/Command/CardCmd.lean) | `Core.Commands/CardCmd.cs`, `CardPileCmd.cs`, `Core.Models/CardModel.cs` | 原子化抽牌/弃牌/消耗/洗牌、`moveCard` 五堆转移、`canPlay` 合法性校验、`spendResources` 资源扣除及 `cloneDeckForCombat`（战斗卡变更不回写主牌组） |
| [Sts2Model/Command/PowerCmd.lean](../Sts2Model/Command/PowerCmd.lean) | `Core.Commands/PowerCmd.cs`, `Core.Models/PowerModel.cs`, `Core.Models.Powers/ArtifactPower.cs` | 能力施加：`Single` 幂等覆盖、`Counter` 叠加、Artifact 对可见 Debuff（含可负 Counter 降为负数场景）拦截并自减 1、`±999999999` 截断、零/非正值自动移除 |
| [Sts2Model/Command/OrbCmd.lean](../Sts2Model/Command/OrbCmd.lean) | `Core.Commands/OrbCmd.cs`, `Core.Models.Orbs/*.cs` | 充能球 `channel`（满槽时先触发首位 `evoke`）、`evoke`（Dark 打最高血量敌、Plasma 回能、Glass 双倍触发且衰减）、扩容/缩容 |
| [Sts2Model/Combat/GameAction.lean](../Sts2Model/Combat/GameAction.lean) | `Core.GameActions/{GameAction,ActionExecutor,PlayCardAction,EndPlayerTurnAction,UndoEndPlayerTurnAction}.cs` | 多人同步确定的 `GameAction` 队列模型与序列化执行器 |
| [Sts2Model/Combat/MonsterAI.lean](../Sts2Model/Combat/MonsterAI.lean) | `Core.MonsterMoves.MonsterMoveStateMachine/*.cs` | `MonsterState`（`MoveState` / `ConditionalBranchState` / `RandomBranchState`）与良基无环 (`StrictlyDecreasingRank`) 状态机解析 |
| [Sts2Model/Combat/TurnLoop.lean](../Sts2Model/Combat/TurnLoop.lean) | `Core.Combat/CombatManager.cs`、`Core.Models.Powers/{Poison,Doom,Plating,Ritual,Vulnerable,Weak,Frail}Power.cs`、`OrbQueue.cs` | 两阶段结束玩家回合，Hook 收集/执行回合始末效果；Poison 先伤后按存活减层、Doom 敌侧回合末处决、Plating 格挡与衰减、Ritual 叠加力量、球被动及停战早退 |

### 1.5 `Sts2Model/Multiplayer/`、`Sim/` 与 `Replay/` 无头多人时间线与仿真层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Multiplayer/ActionQueueSet.lean](../Sts2Model/Multiplayer/ActionQueueSet.lean) | `Core.Entities.Actions/GameActionState.cs`, `Core.Entities.Multiplayer/{GameActionType,PlayerChoiceOptions}.cs`, `Core.GameActions.Multiplayer/{ActionQueueSet,PlayerChoiceSynchronizer}.cs` | 多玩家独立动作队列、`getReadyAction` 最小 ID 选择、`pauseActionForPlayerChoice`（含 `cancelPlayCardActions` 与 `waitingForResumption` 缓冲）、`resumeAction` 及 `ChoiceStream` |
| [Sts2Model/Replay/History.lean](../Sts2Model/Replay/History.lean) | `Core.Combat.History/CombatHistory.cs`, `Entries/*.cs` (18 种), `Core.Runs.History/*.cs` (9 种) | 全量 18 种战斗语义历史 (`CombatHistoryEntryEx`)、通用步索引包装 `TimedCombatHistoryEntry`、9 种局外历史 (`RunHistoryEntryEx`) 与单次命中归因快照 `DamageAttribution` |
| [Sts2Model/Sim/EffectIR.lean](../Sts2Model/Sim/EffectIR.lean) | 脱机无 UI 效果 DSL（抽象自 `Cards/*.cs`, `Potions/*.cs`, `Monsters/*.cs`） | 闭环纯函数效果解释器（`execPlayCardHeadless`、`execUsePotionHeadless`、`execEnemyTurnHeadless`）与长尾 `OpaqueStateDelta` 黑盒步进 |
| [Sts2Model/Sim/VanillaEffects.lean](../Sts2Model/Sim/VanillaEffects.lean) | `Core.Models.{Powers,Cards,Potions,Monsters}/*.cs` | `tier1EffectEnv` 保持轻量；`fullVanillaEffectEnv` 优先手写 Tier-1，其次生成 Tier-2，否则通用回退；`--inspect` 使用全量环境 |
| [Sts2Model/Replay/Timeline.lean](../Sts2Model/Replay/Timeline.lean) | `Core.Multiplayer.Replay/{CombatReplay,CombatReplayEvent,CombatReplayEventType,CombatReplayWriter}.cs`, `ChecksumTracker.cs` | 统一时间线事件流、`buildArchive` 关键帧归档、随机定位 `seek`、通用分叉 `forkTimeline`、纯内核可归约 64 位 FNV-1a 状态校验和 (`computeStateChecksum`) 与视角切换 `switchViewer` |
| [Sts2Model/Replay/TraceCodec.lean](../Sts2Model/Replay/TraceCodec.lean) | `NetFullCombatState.cs`, `CombatReplayEvent.cs`, `ChecksumTracker.cs` | `schemaVersion = 1`，64 位整数用十进制字符串，战斗 `ascensionLevel` 可缺省并回退到局状态；`verifyTraceChecksums` 与 `inspectArchiveStep` |

### 1.6 `Sts2Model/Mechanics/` 角色核心机制层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Mechanics/Orbs.lean](../Sts2Model/Mechanics/Orbs.lean) | `OrbModel.cs`, `Core.Models.Orbs/*.cs`, `FocusPower.cs`, `OrbCmd.cs` | Defect 充能球系统：Focus 免疫规则（Plasma 无视 Focus）、Glass 被动衰减与 `evoke = 2 * passive`、Dark 充能蓄力、Hibernate 护甲共享与回合始末触发顺序 |
| [Sts2Model/Mechanics/Necrobinder.lean](../Sts2Model/Mechanics/Necrobinder.lean) | `Core.Commands/OstyCmd.cs`, `Core.Models.Powers/DieForYouPower.cs`, `DoomPower.cs` | Osty 召唤/复活与动力攻击代伤；模型在敌方回合末对 `HP ≤ DoomAmount` 的活目标调用 `kill`，未覆盖玩家侧 Doom 结算 |
| [Sts2Model/Mechanics/Regent.lean](../Sts2Model/Mechanics/Regent.lean) | `Core.Commands/ForgeCmd.cs`, `Core.Models.Cards/SovereignBlade.cs`, `PlayerCombatState.cs` | 星辰 (`Stars`) 资源、1 点缺少的能量由 2 颗星替代 (`shouldPayExcessEnergyCostWithStars`)、`Forge` 自动生成/强化 `SovereignBlade` 并标记锻造状态 |
| [Sts2Model/Mechanics/Fool.lean](../Sts2Model/Mechanics/Fool.lean) | `Core.Entities.FoolArrows/{ArrowSlot,ArrowStatus}.cs`, `Core.Commands/{ArrowCmd,MelodyCmd}.cs`, `ImpaledPower.cs` | `ArrowSlot` 状态流转（`Ready` / `Impaled` / `Destroyed`，已毁箭槽不可回收）与旋律 (`Wah` / `Cho` / `Ki`) 回合去重统计（每回合至多 3 种不同旋律） |
| [Sts2Model/Mechanics/Dread.lean](../Sts2Model/Mechanics/Dread.lean) | `Core.Models.Dread/{DreadRunModel,DominionModel}.cs`, `Core.Models.Cards/AscendersBane.cs` | `Dread` 模式生命周期：`actIndex > 0` 插入 `Ascender's Bane`、进房附加 `Dominion`、进入 Boss 房强制清除当前幕 `Dominion` |

### 1.7 `Sts2Model/Run/` 局外爬塔地图与概率层

| Lean 4 模块 | C# 参考源码 (`reference/sts2/`) | 建模范围与关键对齐点 |
|---|---|---|
| [Sts2Model/Run/Map.lean](../Sts2Model/Run/Map.lean) | `Core.Map/{MapCoord,MapPoint,StandardActMap}.cs` | 坐标图、行单调递增路径 (`StrictlyRowIncreasing`) 与 `ActMap` DAG 拓扑结构 |
| [Sts2Model/Run/Odds.lean](../Sts2Model/Run/Odds.lean) | `Core.Odds/{CardRarityOdds,PotionRewardOdds,UnknownMapPointOdds}.cs`, `Core.Runs/RelicGrabBag.cs` | 双轨建模：精确 `Dec` 版 `CardRarityOddsDec`（供内核定量/边界定理证明）+ bit-exact IEEE-754 `Float32` 版 `CardRarityOddsF32`（供 `.NET 9` 位级对拍）；未知房间保底负概率排除与 `RelicGrabBag` 前后抽取队列 |
| [Sts2Model/Run/RunLoop.lean](../Sts2Model/Run/RunLoop.lean) | `Core.Rewards/LinkedRewardSet.cs`, `Core.Runs/RunState.cs` | 地图跳转、`LinkedRewardSet` 互斥选取、切幕重置 `UnknownMapPointOdds` 与 Dread 领域状态刷新 |
| [Sts2Model/Run/Expedition.lean](../Sts2Model/Run/Expedition.lean) | `RunManager.EnterMapCoord` / `EnterNextAct` / `WinRun`、`CombatRoom`、`Player.PopulateCombatState` / `AfterCombatEnd`、`RewardsSet` | 显式地图/房间输入，分离战斗实例与永久牌组，使用战斗引擎首次返回的结果；奖励处理、二 Boss 与最终事件分阶段 |

### 1.8 `Sts2Model/Catalog/`, `Examples/`, `Sts2Sim/`, `DiffTest/` 与 `scripts/`

| 文件 | 参考源 / 职责 | 说明 |
|---|---|---|
| [Sts2Model/Catalog/Types.lean](../Sts2Model/Catalog/Types.lean) | 静态目录类型与排序归并引理 | 定义 `CardCatalogEntry`、`RelicCatalogEntry`、`PowerCatalogEntry` 与 `isStrictlySorted` / `strictlySorted_join` / `isStrictlySorted_implies_nodup` |
| [Sts2Model/Catalog/Cards.lean](../Sts2Model/Catalog/Cards.lean) | `MegaCrit.Sts2.Core.Models.Cards/*.cs` | 自动生成：全部 717 张原版卡牌（分 24 个块，每块至多 30 项） |
| [Sts2Model/Catalog/Relics.lean](../Sts2Model/Catalog/Relics.lean) | `MegaCrit.Sts2.Core.Models.Relics/*.cs` | 自动生成：全部 316 个原版遗物（分 11 个块） |
| [Sts2Model/Catalog/Powers.lean](../Sts2Model/Catalog/Powers.lean) | `MegaCrit.Sts2.Core.Models.Powers/*.cs` | 自动生成：全部 304 个具体能力（分 11 个块） |
| [Sts2Model/Catalog/Verify.lean](../Sts2Model/Catalog/Verify.lean) | 纯 Lean 4 内核目录证明 | 自动生成：精确数量定理、ID 严格递增 + `Nodup` 定理（零 `native_decide`）与 `lookupCard`/`lookupRelic`/`lookupPower` |
| [Sts2Model/Examples/VanillaShowcase.lean](../Sts2Model/Examples/VanillaShowcase.lean) | 30 个原版核心规则验证用例 | 覆盖伤害/格挡、Osty/Doom、Forge/SovereignBlade、Orb/Dark/Glass、Fool 箭矢与旋律、RNG 洗牌、地图/稀有度保底等 |
| [Sts2Model/Examples/ModTemplates.lean](../Sts2Model/Examples/ModTemplates.lean) | 4 个 Mod 开发者模板与安全证明 | `modBloodthirst`（Power）、`modAegisWard`（Relic）、`modStarStrike`（Card）、`modComposition`（组合安全性） |
| [Sts2Model/Examples/TimelineShowcase.lean](../Sts2Model/Examples/TimelineShowcase.lean) | 14 个可执行 `Bool` 场景 | 前 10 个覆盖排队、唤醒、Seek、分叉、视角、Opaque 步与 Trace 往返/审计；`tl_11`–`tl_14` 覆盖生命周期、球、Tier-2 卡/药及怪物进阶效果，不是通用定理 |
| [Sts2Model/Examples/ReplayAnalyzerExample.lean](../Sts2Model/Examples/ReplayAnalyzerExample.lean) | **[非核心] 独立下游参考示例项目** | 演示如何仅调用公开核心 API 构建迟打易伤分析 `analyzeMissedVulnerable`、`branchCounterfactual`、`findLethalActionOrder`、2 项可运行校验与 CLI 演示 `runLateVulnerableDemo` |
| [Sts2Sim/Main.lean](../Sts2Sim/Main.lean) | CLI 仿真器与 `--diff <input.tsv>` 入口 | 59 项回归；包含 [跨房、换幕与终局](../Sts2Model/Examples/ExpeditionShowcase.lean)。原生文件审计不使用 v1 Trace |
| [Sts2Sim/RunHistoryAudit.lean](../Sts2Sim/RunHistoryAudit.lean) · [Sts2Sim/ActMapAudit.lean](../Sts2Sim/ActMapAudit.lean) | `RunHistory` / `MapPointHistoryEntry` 与 `SerializableRun` / `SerializableActMap` | 两个独立只读命令：schema 9 账目与终局记录，schema 16 当前幕图和已走边 |
| [scripts/check_observed_survivor.py](../scripts/check_observed_survivor.py) | `Survivor.OnPlay` → `CardSelectCmd.FromHandForDiscard` → `FromHand` | 首次支付、移入 Play、给格挡，随后等本次预订的手牌实例选择并从原动作恢复；单候选/空手不消费 `PlayerChoice` 结果 |
| [DiffTest/Sts2Oracle/Sts2Oracle.csproj](../DiffTest/Sts2Oracle/Sts2Oracle.csproj) | `.NET 9` 对拍项目配置 | `net9.0`，零第三方依赖 |
| [DiffTest/Sts2Oracle/Program.cs](../DiffTest/Sts2Oracle/Program.cs) | `reference/sts2/` C# 语义直译对拍程序 | 按行解析 `--diff <input.tsv>`，支持 `--export-sample-trace` 与 `--verify-trace`，执行原生 C# `System.Text.Json` / `ulong` / `decimal` / `float` / FNV-1a 验证 |
| [DiffTest/Sts2Oracle/CombatEffects.cs](../DiffTest/Sts2Oracle/CombatEffects.cs) | C# 回合与效果执行 | `RunRound` 共用回合序列；按生成操作/节点执行 `TIER2_EFFECTS`，不调用 Lean |
| [tools/Sts2AstExtractor/Program.cs](../tools/Sts2AstExtractor/Program.cs) | 参考源码中的卡、药、怪物与能力定义 | SDK 内置 Roslyn AST：解析效果与怪物状态图；不能识别的语义拒收整条目 |
| [Sts2Model/Sim/Generated/](../Sts2Model/Sim/Generated) · [Tier2OracleData.cs](../DiffTest/Sts2Oracle/Tier2OracleData.cs) | 同源生成的两端效果表 | Lean [Verify.lean](../Sts2Model/Sim/Generated/Verify.lean) 对数量、有序唯一性和结构良构提供纯内核证明 |
| [提取审计](tier2_extraction_audit.md) · [全量卡牌清单](tier2_cards.json) | 用户侧提取审计 | 卡 373/717、药水 36/68、怪物 19/122；清单区分基础/升级程序与整卡拒收的首个源码位置；不将覆盖率或两端对拍视为游戏等价 |
| [scripts/extract_catalog.py](../scripts/extract_catalog.py) | 方案 C 静态目录提取脚本 (`uv run python`) | 扫描 `reference/sts2/` 生成 `Cards.lean` / `Relics.lean` / `Powers.lean` / `Verify.lean` |
| [scripts/run_diff_test.py](../scripts/run_diff_test.py) | `.NET 9` ↔ Lean 4 对拍驱动 | 16 族 1110 条；保留逐行全串比较，固定预期分别核对两端，双向 JSON 文件交接；临时输入/输出隔离于 `.agent_works/diff-*` |

---

## 2. 已证明的形式化定理全表（全部纯 Lean 4 内核证明，零 `sorry` / `native_decide`）

### 2.1 伤害与格挡管线 — [Sts2Model/Proofs/DamagePipeline.lean](../Sts2Model/Proofs/DamagePipeline.lean)

| 定理名 | 核心保证 |
|---|---|
| `modifyDamageWithListeners_nonneg` | 带监听器伤害管线输出恒满足 `Dec.Nonneg` |
| `modifyDamage_nonneg` | `Hook.ModifyDamage` 结果恒非负 |
| `modifyBlockWithListeners_nonneg` | 带监听器格挡管线输出恒非负 |
| `modifyBlock_nonneg` | `Hook.ModifyBlock` 结果恒非负 |
| `damage_cap_dominates` | 伤害上限（如 `IntangiblePower` 压制至 1）最终主导结果上界 |
| `enchantment_applied_before_listeners` | 附魔伤害修正必先于能力/遗物全局监听器生效 |
| `unpowered_ignores_powered_damage_modifiers` | 非动力攻击（`!isPoweredAttack`）跳过力量等动力加算与易伤/虚弱等动力乘算 |
| `unpowered_ignores_powered_block_modifiers` | 非动力获得格挡（`!isPoweredCardOrMonsterBlock`）跳过敏捷与脆弱修正 |
| `unblockable_bypasses_block` | `ValueProp.unblockable` 伤害完全无视目标现有格挡、不消耗格挡直接扣血 |
| `truncate_ofNat` | 自然数转换与向零截断幂等一致性引理 (`(Dec.ofNat n).truncate = (n : Int)`) |
| `damage_block_hp_conservation` | 存活生物受 `dmg ≤ Creature.statCap` 伤害时严格满足 `blocked + res.unblockedDamage + res.overkillDamage = dmg`，且准确扣减 `block` 与 `currentHp` |
| `osty_redirection_conservation` | Osty 与 Necrobinder 本体均存活且 `unblocked ≤ Creature.statCap` 时，Osty 承伤与溢出转伤满足 `res1.unblockedDamage + res2.unblockedDamage + res2.overkillDamage = unblocked` |
| `vulnerable_factor_bounds` / `vulnerable_damage_ge_unvulnerable` / `vulnerable_damage_strictly_gt_for_ge_two` | 易伤 `×1.5` 与 Paper Phrog `×1.75` 对非负伤害严格单调；且对任意整数基础伤害 `n ≥ 2`，易伤截断后整数伤害严格更高 |

### 2.2 Hook 快照与 Modding 安全性 — [Sts2Model/Proofs/HookSafety.lean](../Sts2Model/Proofs/HookSafety.lean)

| 定理名 | 核心保证 |
|---|---|
| `runSnapshotHooksTraced_fst_eq` | 快照钩子追踪执行的主结果与无追踪版本完全一致 |
| `snapshot_ignores_newly_added_listeners` | 触发循环期间在状态中新增的监听器不会被当轮快照回溯执行 |
| `snapshot_skips_removed_listeners` | 触发期间已被移除的监听器即使尚在旧快照列表内也会被 `isListenerAlive` 跳过 |
| `snapshot_cons_skips_dead` | 对失活首元监听器的归纳跳过定理 |
| `modHelper_pool_freeze_monotonic` | `ModPoolRegistry` 冻结操作具有单调持久性（一旦冻结不可解冻再注入条目） |
| `modHelper_combat_sort_order_independent` | `ModHookRegistry` 对战斗钩子按 Ordinal 字典序规范化排序去重后，与各 Mod 加载顺序无关 |
| `modHelper_run_sort_order_independent` | 局外钩子订阅注册表同样满足按 Ordinal 排序后的加载顺序无关性 |
| `mod_additive_hooks_commute` | 任意两个纯加法型 Hook 修改器满足交换律 |
| `mod_multiplicative_hooks_commute` | 任意两个纯乘法型 Hook 修改器满足交换律 |
| `mod_mixed_add_mul_noncommutative` | 显式构造反例证明加乘混合 Mod 钩子**不满足**交换律（因此需要固定阶段与确定性注册顺序） |

### 2.3 卡牌堆守恒与费用安全 — [Sts2Model/Proofs/CardPiles.lean](../Sts2Model/Proofs/CardPiles.lean)

| 定理名 | 核心保证 |
|---|---|
| `removeCardById_none` | 按不存在 `instanceId` 删除牌时原列表无损保留 |
| `removeCardById_some_perm` | 删除存在的卡牌时与原列表互为单元素移除置换 |
| `removeCardById_some_length` | 成功删除后列表长度精确减 1 |
| `insertIntoPileList_perm` | 插入 (`top` / `bottom`) 形成包含该新卡的准确置换 (`List.Perm`) |
| `insertIntoPileList_length` | 插入卡牌后列表长度精确加 1 |
| `moveCard_totalCount` | 战斗内五个牌堆之间移动卡牌（非移回 `deck`/`none`）总张数严格不变 |
| `moveCard_preserves_invariant` | `moveCard` 维持跨牌堆两两互斥无重复不变量 |
| `shuffleDiscardIntoDraw_totalCount` | 弃牌堆洗入抽牌堆不改变玩家战斗总牌数 |
| `shuffleDiscardIntoDraw_preserves_invariant` | 洗牌操作维持牌堆互异与无重不变量 |
| `cloneDeckForCombat_preserves_deck` | 开战克隆生成临时实例后，原始局外主牌组 `deck` 与其中卡牌列表严格不变 |
| `canPlay_implies_sufficient_resources` | 若 `canPlay` 返回 `true`，则资源检定保证能量/星辰足以支付且不发生无符号下溢 |
| `canonicalModel_toMutable_preserves_id` | 权威静态原型转换为战斗可变实例时保留 `ModelId` |

### 2.4 能力叠加与 Artifact — [Sts2Model/Proofs/PowerSystem.lean](../Sts2Model/Proofs/PowerSystem.lean)

| 定理名 | 核心保证 |
|---|---|
| `shouldRemoveDueToAmount_false_iff` | 未被移除的能力精确满足：`allowNegative` 时 `amount ≠ 0`，否则 `amount > 0` |
| `validPowerEntry_of_not_removed` | 结合 `Single`、`±999999999` 界与移除谓词证明条目有效性 |
| `filter_not_removed_preserves_valid` | 按移除谓词过滤列表保留全部条目有效性 |
| `filter_preserves_uniqueness` | 过滤保持能力集合唯一键不变量 |
| `map_filter_preserves_powerListInvariant` | 修改现有能力数值并清理零/非正条目后仍维持整个 `PowerListInvariant` |
| `append_new_power_preserves_invariant` | 插入尚未持有的合法新能力保持 `PowerListInvariant`（区分 `None` 与 `InstancedPerApplier` 键语义） |
| `artifact_blocks_visible_debuff` | 持有正数层 `Artifact` 时，首次生效的可见 Debuff 申请被完全抵消且 `Artifact` 层数减 1 |
| [`tickDownDuration_clears_skip_without_decrementing`](../Sts2Model/Proofs/PowerSystem.lean#L185) | 已置跳过标志时仅清标志 |
| [`tickDownDuration_decrements_when_not_skipped`](../Sts2Model/Proofs/PowerSystem.lean#L194) | 未置跳过标志时执行层数递减 |
| [`thornsBehavior_ignores_unpowered_attacks`](../Sts2Model/Proofs/PowerSystem.lean#L203) | 无动力攻击不触发 Thorns |
| [`poisonBehavior_emits_unblockable_unpowered_damage_and_decrement`](../Sts2Model/Proofs/PowerSystem.lean#L212) | Hook 发出无动力穿甲伤害和后续递减指令；执行器在伤后检查存活 |
| [`doomBehavior_triggers_only_on_enemy_side`](../Sts2Model/Proofs/PowerSystem.lean#L228) | 模型 Hook 只在敌侧回合末发出处决指令 |

### 2.5 回合状态机与怪物 AI — [Sts2Model/Proofs/TurnMachine.lean](../Sts2Model/Proofs/TurnMachine.lean)

| 定理名 | 核心保证 |
|---|---|
| `checkWinCondition_none_ongoing_when_stopped` | 当全局战斗结束锁存为已结束或停机标志生效时不会维持进行中状态 |
| `pendingLoss_implies_defeat` | `PendingLossState` 激活时优先结算为失败，压倒常规胜利分支 |
| `checkWinCondition_respects_stopCombatHook` | 即使主要敌方单位全灭，只要存在监听器声明 `ShouldStopCombatFromEnding = true` 就阻断胜利判定 |
| `victory_iff_conditions` | 胜利状态充要刻画：无等待失败、敌方主单位全灭、无监听器阻断 |
| `win_loss_mutually_exclusive` | 胜利与失败严格互斥 |
| `monster_stateMachine_terminates` | 具备良序等级函数 `rank` 的无环 `MonsterStateMachine` 必然在有限步内停机于 `MoveState` |
| [`orb_turn_end_passives_preserve_capacity`](../Sts2Model/Proofs/TurnMachine.lean#L433) | 回合末球被动保持各玩家球槽容量 |
| [`runSideTurnEndLifecycle_noop_when_not_in_progress`](../Sts2Model/Proofs/TurnMachine.lean#L459) | 停战后回合末生命周期保持原状态 |
| [`ascensionVal_eval_monotone_when_asc_ge_base`](../Sts2Model/Proofs/TurnMachine.lean#L466) | 进阶值不低于基础值时，`eval` 随等级单调不减 |

### 2.6 PRNG 与多人确定性 — [Sts2Model/Proofs/Determinism.lean](../Sts2Model/Proofs/Determinism.lean)

| 定理名 | 核心保证 |
|---|---|
| `splitmix64_deterministic` | 相同输入下 `SplitMix64` 输出比特完全相同 |
| `xoshiro_ofSeed_deterministic` | 相同 64-bit 种子导出完全一致的 `Xoshiro256**` 四字初始状态 |
| `xoshiro_nextULong_deterministic` | 相同生成器状态下 `NextULong` 单步状态与返回值唯一确定 |
| `rng_nextULong_stream_deterministic` | 相同种子导出的任意长度随机流完全一致 |
| `unstableShuffle_deterministic` | 相同列表与相同 `Rng` 下的洗牌结果严格相等 |
| `unstableShuffle_preserves_length` | `unstableShuffle` 不改变列表长度 |
| `unstableShuffle_preserves_elements` | `unstableShuffle` 严格保留多重集合元素 (`List.Perm`) |
| `actionQueue_multiplayer_deterministic` | 多人同一动作队列在同状态与同种子下执行产生完全相同的终态与历史记录 |
| `actionQueue_preserves_sync_invariants` | `ActionExecutor` 队列化处理保持序列与历史日志同步不变式 |
| `actionQueue_nil` / `actionQueue_append` | 空队列恒等性与动作批次追加同态律（函子结合律） |

### 2.7 角色机制不变量 — [Sts2Model/Proofs/Mechanics.lean](../Sts2Model/Proofs/Mechanics.lean)

| 定理名 | 核心保证 |
|---|---|
| `orbQueue_addCapacity_le_max` / `orbQueue_removeCapacity_le_max` | 充能球队列容量始终有界 `≤ 10` |
| `plasma_immune_to_focus` | Plasma 球无视任意正负 `Focus` 层数加成/削减 |
| `effectivePassiveVal_nonneg` | 任意充能球的实际被动数值均截断保护非负 |
| `glass_evoke_is_double_passive` / `glass_passive_nonneg` | Glass 球 `evoke` 数值严格为 `passive` 的 2 倍且被动值非负 |
| `dieForYou_ignores_unpowered` / `dieForYou_ignores_dead_osty` | `DieForYouPower` 绝不拦截非动力攻击且跳过已死 Osty |
| `isCreatureDoomed_iff` | 生物因 Doom 被处决当且仅当有正数 Doom 层且 `currentHp ≤ doomAmt` |
| `updatePlayer_findPlayer` | 更新玩家状态与查询函数互换律 |
| `forge_sets_forged_flag` | `ForgeCmd` 必定在牌组内构造或强化 `SovereignBlade` 并置已锻造标志 |
| `loseStars_le_available` | 星辰消耗量严格不超过玩家当前持有量 |
| `retrieveArrowSlot_destroyed_none` | 已被摧毁 (`Destroyed`) 的 Fool 箭槽不可再次回收 |
| `melodiesThisTurn_le_three` | Fool 每回合激活的不同旋律标签严格 `≤ 3` |
| `dreadBeforeRoomEntered_boss_clears_dominion` | 进入 Boss 房间时必定清空当前活跃的 `Dominion` 模型 |

### 2.8 地图拓扑、赔率与局外运行 — [Sts2Model/Proofs/MapTopology.lean](../Sts2Model/Proofs/MapTopology.lean)

| 定理名 | 核心保证 |
|---|---|
| `validPath_row_strictly_increasing` | 合法地图路径中节点行号严格单调递增 |
| `validMap_acyclic` | 符合 `StrictlyRowIncreasing` 的 `ActMap` 为严格有向无环图（不存在自环或路径环） |
| `validPath_length_bounded` / `validPath_from_zero_le_bound` | 路径节点数以最大行号加一为上界，确保爬塔路径探索必定停机 |
| `cardRarityOdds_offset_invariant` | 滚轮稀有度补偿偏移恒保持在 `[-0.05, 0.40]` 区间 |
| `cardRarityOdds_rare_resets` | 抽出稀有卡后偏移重置回 `-0.05`（不超出合法区间） |
| `cardRarityOdds_boss_always_rare` | Boss 战卡牌掉落保底稳定返回 `Rare` |
| `unknownMapPointOdds_never_rolls_negative` | 未知问号房随机采样永不落入当前赔率 `< 0` 的分支 |
| `relicGrabBag_pullFromFront_decreases_count` | 从非空稀有度池头抽取遗物时该池及总计数严格减 1 |

### 2.9 并发队列与通用关键帧时间线引擎 — [Sts2Model/Proofs/ReplayTimeline.lean](../Sts2Model/Proofs/ReplayTimeline.lean)

| 定理名 | 核心保证 |
|---|---|
| `actionQueueSet_enqueue_increments_id` | 每次入队严格递增全局 `nextActionId` |
| `pickBestReady_some_of_eligible` / `pickBestReady_le_eligible` / `actionQueueSet_getReadyAction_is_min_id` | `ActionQueueSet.getReadyAction` 清理Canceled队头后恒返回跨所有玩家就绪队头中的最小 `actionId` 动作 |
| `actionQueueSet_pause_blocks_only_owner` | 玩家 1 队列暂停等待选牌（`gatheringPlayerChoice`）期间不阻塞玩家 2 就绪队列的执行选择 |
| `actionQueueSet_early_resume_buffered_and_applied` | 早于 `pauseActionForPlayerChoice` 到达的 `resumeAction` 会进入 `waitingForResumption` 并在暂停时立即消费赋值并转为 `readyToResumeExecuting` |
| `replayEvents_nil` / `replayEvents_append` | 空时间线恒等律与分段事件重放的结合律 (`foldl_append`) |
| `list_take_split` | 前缀切片等价引理（用于将全量重放拆分为关键帧前缀与增量切片） |
| `buildArchive_validKeyframes` | 由 `buildArchive` 生成的任一时间线归档恒满足 `ValidKeyframes` 不变量（含精确前缀状态与 64 位 FNV-1a 校验和） |
| `keyframe_seek_exact_equivalence` | 在 `ValidKeyframes` 条件下，从最近关键帧 `seek env archive k` 恢复与增量执行严格等于从事件 `0` 全量重放 `events.take k` |
| `forkTimeline_exact_equivalence` | 在 `ValidKeyframes` 条件下，`forkTimeline env archive branchIdx altEvents` 严格等价于从事件 `0` 重放 `events.take branchIdx ++ altEvents` |
| `viewer_switch_preserves_seek_and_checksum` | `switchViewer` 切换检视玩家视角后，任意步 `seek` 状态及 64 位 FNV-1a 状态校验和完全不变 |
| `decodeChoiceResult_encodeChoiceResult` / `decodeActionPayload_encodeActionPayload` / `decodeCombatReplayEvent_encodeCombatReplayEvent` / `decodeOutOfCombatSync_encodeOutOfCombatSync` / `decodeOpaqueDelta_encodeOpaqueDelta` / `decodeTimelineEvent_encodeTimelineEvent` | 外部 JSON Trace 线协议对全部 `ChoiceResult`、`ReplayActionPayload` (11 类)、`CombatReplayEvent`、`OutOfCombatSyncEvent` (8 类)、`OpaqueStateDelta` 与 `TimelineEvent` 满足零损双向可逆 (`decode (encode x) = .ok x`) |
| `decodeArchiveBundle_rejects_bad_version` | 当输入 Trace `schemaVersion ≠ traceSchemaVersion (= 1)` 时解码必定安全拒绝 (`isOk = false`) |
| `verifyTraceChecksums_of_validKeyframes` | 任意满足 `ValidKeyframes` 的时间线归档经 `verifyTraceChecksums` 审计自身导出关键帧列表时必返回 `allMatched = true` |

### 2.10 静态目录、钩子目录、历史数量与 Mod / 下游示例定理

- [Sts2Model/Hook/Registry.lean](../Sts2Model/Hook/Registry.lean):
  `hookCatalog_before_count` (`= 16`)、`hookCatalog_after_count` (`= 68`)、`hookCatalog_modify_count` (`= 41`)、`hookCatalog_should_count` (`= 27`)、`hookCatalog_try_count` (`= 2`)、`hookCatalog_total` (`= 154`)。
- [Sts2Model/Replay/History.lean](../Sts2Model/Replay/History.lean):
  `combatHistoryKindCount` (`= 18`)、`runHistoryKindCount` (`= 9`)。
- [Sts2Model/Catalog/Verify.lean](../Sts2Model/Catalog/Verify.lean):
  `allCards_count` (`= 717`)、`allCards_nodup`、`allRelics_count` (`= 316`)、`allRelics_nodup`、`allPowers_count` (`= 304`)、`allPowers_nodup`。
- [Sts2Model/Examples/ModTemplates.lean](../Sts2Model/Examples/ModTemplates.lean):
  `modBloodthirst_unpowered_safe`、`modBloodthirst_factor_nonneg`、`modAegisWard_caps_at_five`、`modAegisWard_monotone_le`、`modStarStrike_pile_and_resource_safe`、`modComposition_safe`。
- [Sts2Model/Examples/ReplayAnalyzerExample.lean](../Sts2Model/Examples/ReplayAnalyzerExample.lean)（非核心下游参考项目示例定理）:
  `late_vulnerable_counterfactual_witness`（以纯内核 `decide` 证毕双人协作迟打 `BASH` 错失 8 点易伤漏伤、先出 `BASH` 即可斩杀 `COOP_GUARDIAN`）。

---

## 3. 方案 C 全量静态目录提取审计

通过 [scripts/extract_catalog.py](../scripts/extract_catalog.py) 对 `reference/sts2/` 静态提取的结果已经集成于 `Sts2Model/Catalog/`，具体清单与精准排除说明如下：

| 模型类别 | C# 源码目录 (`reference/sts2/`) | 具体实例数 | 精确排除项说明 | 内核证明方式 |
|---|---|---|---|---|
| **Cards** | `MegaCrit.Sts2.Core.Models.Cards/*.cs` | **717** | 无 | 24 个 30-item 分块 + `strictlySorted_join` + 纯内核 `decide` → `allCards_count` & `allCards_nodup` |
| **Relics** | `MegaCrit.Sts2.Core.Models.Relics/*.cs` | **316** | `VakuuCardSelector.cs`（非 `RelicModel` 子类的辅助选择器） | 11 个 30-item 分块 + `strictlySorted_join` + 纯内核 `decide` → `allRelics_count` & `allRelics_nodup` |
| **Powers** | `MegaCrit.Sts2.Core.Models.Powers/*.cs` | **304** | `TemporaryDexterityPower.cs`、`TemporaryFocusPower.cs`、`TemporaryStrengthPower.cs`、`TemporaryThornsPower.cs`（4 个 `abstract` 基类模板） | 11 个 30-item 分块 + `strictlySorted_join` + 纯内核 `decide` → `allPowers_count` & `allPowers_nodup` |
| **Hooks** | `MegaCrit.Sts2.Core.Hooks/Hook.cs` | **154** | 全部 `public static` 钩子 | `Hook/Registry.lean` 中由 `rfl` / `simp` 核验证（`16+68+41+27+2 = 154`） |

> **零 `native_decide` 技巧说明**：在 Lean 4 内核中直接对长度 717 的列表执行 `List.Nodup` 的 `decide` 会展开为 $O(N^2) \approx 514{,}089$ 次字符串相等对比，极易触及内核归约上限或逼近 `native_decide` 妥协。本项目采取先按 `String.lt` 严格升序排序（30 项为一块），先由内核 `decide` 证明每一小块 `isStrictlySorted = true` 以及相邻块交界处 `last < head`，再通过已证引理 `strictlySorted_join` 与 `isStrictlySorted_implies_nodup` 仅用线性代价导出全局 `Nodup`。

---

## 4. `.NET 9` ↔ Lean 4 差分对拍覆盖与关键发现

由 [scripts/run_diff_test.py](../scripts/run_diff_test.py) 生成 **16 族 1110 条** TSV 向量，逐行全串比对 `sts2sim --diff` 与 `dotnet .../Sts2Oracle.dll --diff`。固定向量还将两端各自与源码预期比较，最后验证双向 v1 JSON Trace 文件交接。

| 族 ID | 向量数 | 对拍目标与精度要求 |
|---|---:|---|
| `RNG_SEQ` | 60 | `SplitMix64` + `Xoshiro256**` 连续输出的 `NextULong`、`NextInt(100)`、`NextBool` 与 IEEE-754 `NextDouble().toBits`（UInt64 位一致） |
| `RNG_SHUFFLE` | 65 | `Rng.unstableShuffle`（从当前 RNG 派生局部种子执行 Fisher-Yates 洗牌）的完整排列序列 |
| `DMG_PIPE` | 100 | `Hook.ModifyDamageInternal`（Base → Powered 加法 Strength → Powered 乘法 Weak/Vulnerable/PaperPhrog → LateMul → Cap → Truncate & Dec 全格式化串） |
| `BLK_PIPE` | 60 | `Hook.ModifyBlock`（Dexterity + Frail，显式对抗校验 `Unpowered` 标记绕过逻辑） |
| `CREATURE_DMG` | 100 | `CreatureCmd.Damage`（护甲吸收 + `Unblockable` + `Intangible` 压制 1 伤 + `DieForYou` Osty 代承伤 + 溢出致死伤害回流本体） |
| `POWER_STACK` | 80 | `PowerCmd.Apply`（`Single` vs `Counter`、`AllowNegative` 负数行为、`±999999999` 截断、Artifact 对 `GetTypeForAmount == Debuff` 抵消并减层） |
| `CARD_COST` | 80 | `CardEnergyCost.GetWithModifiers` + `CheckResourcesFor`（Local `Absolute`/`Relative` 修正 → `Hook.ModifyEnergyCostInCombat` 全局增量 → 截断非负 → X 费与星能 1:2 补足） |
| `RARITY_ODDS` | 80 | `CardRarityOdds` 多房间类型与 `Scarcity` 模式序列及 IEEE-754 `Float32.toBits`（UInt32 位一致） |
| `MOD_SORT` | 45 | `ModHelper` 战斗钩子按 Ordinal 字典序排序并去重（大小写敏感、`a9`/`A9`/`com.A`/`com.1` 边界） |
| `QUEUE_SET` | 60 | 多玩家并发 `ActionQueueSet`（入队取消守护、min-ID `getReadyAction`、`pauseActionForPlayerChoice` 仅阻断持有者、早发 `resumeAction` 缓冲、停战清理） |
| `TIMELINE_SEEK` | 60 | 双人协作多回合无头回放（出牌 + 药水 + 跨回合 `Rng.unstableShuffle` 重洗 + `COOP_GUARDIAN` AI + 关键帧 `seek` + 64 位 FNV-1a 状态校验和位一致） |
| `TRACE_JSON` | 60 | `schemaVersion = 1` 外部 JSON 线协议（`> 2^53` 全 64 位字符串 `runSeed`、`CULTIST` / `COOP_GUARDIAN` 多回合、`Artifact` / 药水 / 局外 `runSync` / `opaqueStep` 与双向序列化回放 FNV-1a 一致性） |
| `TURN_LIFECYCLE` | 60 | 减益首次跳过和有符号 Artifact 判定、Poison 存活减层、敌侧 Doom、Thorns、Plating、Ritual、五种球的 Focus/停战边界 |
| `TIER2_EFFECTS` | 80 | 40 张卡牌版本用例、16 药水、20 怪物、4 缺表边界；验证效果而非出牌支付。怪物初始 HP 由 TSV 提供，仅对拍动作参数的进阶缩放和实际执行的 move |
| `TIER2_CARD` | 119 | 读实时格挡/弃牌/能量，带条件的出牌，球槽边界、对象作用域与同名实例的整场费用；对拍基础/升级和固定源码预期 |
| `EXPEDITION` | 1 | [独立 C# 参考](../DiffTest/Sts2Oracle/ExpeditionReference.cs)：合法图边、跨幕、已结算房恢复、战败、奖励互斥、战斗实例清理；不是原版 RNG 或游戏整局对拍 |
| **合计** | **1110** | **逐行比较与两端固定预期；之后双向 JSON 交接** |

`found=1` 仅表示对应 Tier-2 表存在 ID（如执行 `NOTHING` 的 `BIG_DUMMY`）；`found=0` 不排除 Tier-1 效果（如 `HEAL_POTION`）。代表锚点独立取自 `ThornsPower.BeforeDamageReceived`、`DaggerThrow.OnPlay`、`Bloodletting.OnPlay`、`SuckerPunch.OnPlay`、`PotionOfDoom.OnUse` 和 `BowlbugEgg.BiteMove`。

共享生成表对拍验证的是两个解释器在向量上的一致性，不证明提取器与游戏等价。固定种子的加权分支只锁定模型 RNG；未注册能力的持续行为不在覆盖范围。`ShrinkPower.StackType` 随层数动态变化，而表中为静态值，不能作为原版预期。`FightMe.OnUpgrade` 的属性与规范键现在指向同一个变量，升级固定预期为两击各 6、自己力量 +4、对手 +1。

原生文件验收不能合并：v0.107.1 的 48 点胜局只核对该局报告的事实与 47 次跨点余额；schema 16 保存地图只核对当前幕路线；v0.111.1 的战斗归档只核对 `#1→#5` 与独立的 `#21→#22` 的投影。没有同局动作流就不称为整局逐动作重演。

### 差分测试捕获的真实语义边界示例（`CARD_COST` #505 / #513）

首轮对拍中，第 505 号向量 `CARD_COST\t1\t0\t2\t3\t2\t2\t-2\t1\t2`（基础 1 费 + 局地相对修正 `-2` + 全局战斗钩子 `+2`）与第 513 号向量揭露了一个极易在手写 Mod 或重实现时写错的原版规则：

- `CardEnergyCost.GetWithModifiers` 先叠加局地修正得到 `num = 1 + (-2) = -1`；
- 随后调用 `Hook.ModifyEnergyCostInCombat(combatState, card, modifiedCost)`；
- 在原版 `reference/sts2/MegaCrit.Sts2.Core.Hooks/Hook.cs:1626` 中存在显式早返回：
  ```csharp
  if (originalCost < 0m)
  {
      return originalCost;
  }
  ```
- 因此当局部减费暂时把费用压成负数 `-1` 时，**所有全局 `ModifyEnergyCostInCombat` 加费效果都会被直接跳过**，最后由 `Math.Max(0, num)` 钳制为 `0`！
- Lean 模型（[Sts2Model/Hook/Pipeline.lean](../Sts2Model/Hook/Pipeline.lean)）忠实实现了该早返回分支并输出 `0`，反而在首轮对拍中揪出并修复了初版 `DiffTest/Sts2Oracle/Program.cs` 中漏写 `if (afterLocal < 0)` 的问题。

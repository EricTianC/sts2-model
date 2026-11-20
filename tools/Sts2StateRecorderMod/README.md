# `Sts2StateRecorderMod` — STS2 全局完整状态与动作录制 Mod（轨道 A）

本工具为 `sts2_ideal` 提供零侵入、无本地硬编码路径依赖的《杀戮尖塔 2》（Slay the Spire 2）全局状态与行为录制 Mod。

- **Mod ID**：`Sts2StateRecorder`（产出 `Sts2StateRecorder.dll` + `mod_manifest.json`）
- **`affects_gameplay`**：`false`（纯只读观测，不修改任何 RNG、状态或卡牌/遗物逻辑）
- **零本机路径强依赖**：默认使用仓内轻量级 `sts2` / `0Harmony` 元数据桩（`Version=0.0.0.0`）完成独立编译，运行时由游戏原生 `ModManager` 与 .NET 9 `AssemblyLoadContext` 自动绑定到实机程序集；亦支持通过环境变量 `STS2_DATA_DIR` 或 `-p:Sts2DataDir=...` 指定实机 DLL 目录编译。

---

## 1. 编译与安装

### 1.1 独立编译（无需指定游戏安装路径）

```bash
dotnet build tools/Sts2StateRecorderMod/Sts2StateRecorderMod.csproj -c Release --nologo
```

编译产物位于 `tools/Sts2StateRecorderMod/bin/Release/net9.0/`，仅包含两个文件：
- `Sts2StateRecorder.dll`
- `mod_manifest.json`

### 1.2 部署到游戏目录

将上述两个文件复制到《杀戮尖塔 2》安装目录下的 `mods/Sts2StateRecorder/` 文件夹中：

```text
<Slay the Spire 2 游戏根目录>/
├── mods/
│   └── Sts2StateRecorder/
│       ├── Sts2StateRecorder.dll
│       ├── mod_manifest.json
│       └── recorder_config.json   # (可选) 自定义输出目录
└── state_recordings/              # 默认录制文件输出目录
    └── run_<yyyyMMdd_HHmmss>_<seed>.full.ndjson
```

### 1.3 自定义录制输出路径（可选）

按以下优先级决定 `.full.ndjson` 录制文件的保存目录（默认不写在 `mods/` 内，避免游戏启动递归扫描 `.json` 清单）：
1. 环境变量 `STS2_RECORDER_OUTPUT_DIR`；
2. `Sts2StateRecorder.dll` 同级目录下的 `recorder_config.json`（格式：`{"output_dir": "/path/to/recordings"}`）；
3. 默认值：`<游戏根目录>/state_recordings/`。

---

## 2. 轨道 A (`run_*.full.ndjson`) 录制覆盖范围

每局游戏生成一个 Append-only 的 `.full.ndjson` 文件（每行一个完整 JSON 对象，实时 `AutoFlush`，即使游戏崩溃或强退也不会丢失已发生的步骤）。

### 2.1 录制的事件种类 (`event_kind`)

| 类别 | `event_kind` | 触发时机与携带信息 |
|---|---|---|
| **全局/局生命周期** | `run_initialized_new`<br>`run_initialized_from_save`<br>`run_started`<br>`run_cleanup` | 新开局、读档续局、正式开局、局结束/清理；附带官方 `SerializableRun` 全量存档 JSON (`canonical_serializable_run`) |
| **层数/地图/房间切换** | `act_entered`<br>`room_entered`<br>`room_exited`<br>`map_changed`<br>`map_vote_changed` | 进幕、进出房间、地图重生成、地图坐标投票变化；附带房间栈 (`room_stack`) 与完整存档快照 |
| **战斗与回合阶段** | `combat_setup`<br>`combat_began`<br>`turn_started`<br>`player_ended_turn`<br>`player_unended_turn`<br>`about_to_switch_to_enemy_turn`<br>`turn_ended`<br>`combat_creatures_changed`<br>`combat_won`<br>`combat_ended` | 战斗初始化、开始、回合开始/结束、玩家点击/取消结束回合、切入敌方回合、生物增减（召唤/死亡/逃跑）、战斗胜利与结束 |
| **`GameAction` 全生命周期** | `action_enqueued`<br>`action_before_execute`<br>`action_paused_for_player_choice`<br>`action_ready_to_resume_after_choice`<br>`action_resumed_in_queue`<br>`action_resumed_after_choice`<br>`action_just_before_finished`<br>`action_after_execute`<br>`action_cancelled` | 每个玩家/钩子动作（出牌、喝药、弃药、结束回合、地图移动、选遗物、`GenericHookGameAction`）从入队、执行前、因选牌暂停、唤醒恢复、完成前、完成后到取消的全过程及前后完整状态快照 |
| **微观战斗历史流 (18 类)** | `combat_history_entry` | 实时捕获 `CombatManager.Instance.History` 新增的每一条微观事件（`CardPlayStarted`、`CardPlayFinished`、`CardDrawn`、`CardDiscarded`、`CardExhausted`、`CardGenerated`、`CardAfflicted`、`CreatureAttacked`、`DamageReceived`、`BlockGained`、`EnergySpent`、`MonsterPerformedMove`、`OrbChanneled`、`ArrowShot`、`PotionUsed`、`PowerReceived`、`StarsModified`、`Summoned`），**每条微观事件均附带当步完整 `state_snapshot`** |
| **玩家交互与选牌** | `player_choice_received`<br>`card_select_cmd_choice` | 捕获 `PlayerChoiceSynchronizer` 的 `choice_id` 与 `NetPlayerChoiceResult`（索引、战斗卡 ID、牌组卡、衍生卡）及 `CardSelectCmd` 所有选牌界面的最终选牌列表 |
| **局外房间交互** | `event_began`<br>`event_vote_changed`<br>`event_option_chosen`<br>`merchant_entered`<br>`merchant_entry_purchased`<br>`merchant_exited`<br>`rest_site_began`<br>`rest_site_option_before`<br>`rest_site_option_after`<br>`rewards_set_began`<br>`rewards_set_skipped`<br>`rewards_skipped_during_room_exit` | 事件房选项列表与每次选择、商店库存与每次购买、火堆选项与每次休息/锻造前后、战后奖励池生成与跳过 |
| **联机校验和与同步快照** | `checksum_generated`<br>`state_diverged` | 捕获原版 `ChecksumTracker` 在每个 Action 后及 5 个回合阶段生成的 32 位引擎校验和、上下文、原版 `NetFullCombatState` 以及 64 位 FNV-1a 校验和 |

### 2.2 每步 `state_snapshot` 冗余状态深度

除了原版 `NetFullCombatState` 与 `SerializableRun` 的全部字段外，`state_snapshot` 还通过反射补齐了原版快照未导出的深层运行时信息：
- **精度零损失**：所有 64 位无符号整数（`seed_u64`、RNG `s0..s3`、`net_id`、`fnv1a_checksum_u64`）均以十进制字符串编码；所有 32 位浮点概率（`card_rarity_odds`、`potion_reward_odds`、`UnknownMapPoint` 五类房间权重）同时导出浮点值、`f32_bits`（`uint32`）与 `f32_hex`（完美对齐 `Sts2Model/Run/Odds.lean` 的 `Float32.toBits`）。
- **怪物 AI 状态机 (`monster.move_state_machine`)**：导出私有 `_currentState`、`_initialState`、`_performedFirstMove`、`StateLog` 招式历史、`NextMove` 及其全部 `Intents`、怪物专属 `Rng` (`counter`, `s0..s3`) 以及怪物子类自定义私有字段。
- **能力内部状态 (`powers[*].internal_data` & `custom_fields`)**：完整递归导出 `PowerModel._internalData` 私有数据对象、`AmountOnTurnStart`、`SkipNextDurationTick`、`TypeForCurrentAmount`、`Applier`/`Target` `CombatId`、`DynamicVars` 及能力子类私有字段。
- **5 大战斗牌堆 (`Hand`/`Draw`/`Discard`/`Exhaust`/`Play`) 与主牌组 (`master_deck`)**：每张卡包含 `CombatCardIndex`、`EnergyCost`（含 `Canonical`、`Base`、`CostsX`、`CapturedXValue`、`AmountToSpend` 及私有 `_localModifiers` 列表）、`StarCost`（含私有 `_temporaryStarCosts` 列表）、`Keywords`、`Tags`、`BaseReplayCount`、`ExtraReplayThisTurn`、`ExhaustOnNextPlay`、`ShouldRetainThisTurn` (`_hasSingleTurnRetain`)、`IsSlyThisTurn` (`_hasSingleTurnSly`)、`Affliction`、`Enchantment`、`SavedProperties`、`DynamicVars` 及卡牌子类私有字段。
- **多玩家并发队列 (`action_queues`)**：导出 `NextActionId`、`ActionExecutor` 暂停/运行状态、当前执行 Action、各玩家 `ActionQueue` 内部队列与 3 个取消标志位（`isCancellingPlayCardActions`、`isCancellingPlayerDrivenCombatActions`、`isCancellingCombatActions`）以及 `_actionsWaitingForResumption` (`oldId -> newId`)。

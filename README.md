# sts2_ideal — 《杀戮尖塔 2》(Slay the Spire 2) Lean 4 逻辑建模参考项目

面向 **Slay the Spire 2 (STS2) Mod 开发者**的完整可执行 Lean 4 形式化建模与跨语言差分验证参考工程，严格溯源于反编译 C# 参考源码（`sts2.zip` → `reference/sts2/`）。

## 核心设计保障

- **纯粹 Lean 4.36.0 (`Std`)**：零 `Mathlib` 依赖。
- **核心与下游严格隔离**：核心 `Sts2Model/` 仅建模 STS2 原版逻辑、通用无 UI 时间线引擎（`TimedCombatHistoryEntry` / `seek` / `switchViewer` / `forkTimeline` / FNV-1a）与标准化外部 JSON Trace 协议（[TraceCodec.lean](Sts2Model/Replay/TraceCodec.lean)）；特定局后分析、What-If 对比与斩杀求解示例隔离于 [ReplayAnalyzerExample.lean](Sts2Model/Examples/ReplayAnalyzerExample.lean)，绝不反向侵入核心库。
- **纯净可信证明内核**：`Sts2Model/` 与 `Sts2Sim/` 的代码主体无 `sorry`、自定义 `axiom` 或 `native_decide`。
- **方案 C 全量静态目录与核证**：自动扫描并核证原版 **717 张卡牌**、**316 个遗物**（不含辅助类 `VakuuCardSelector`）、**304 个具体能力**（不含 4 个 `Temporary*Power` 抽象基类）以及 `Hook.cs` 全部 **154 个公开钩子**（`Nodup` 全数经纯内核 `decide` + `strictlySorted_join` 证毕）。
- **`.NET 9` ↔ Lean 4 差分验证**：内置 C# 预言机、**16 族 1110 条**确定性向量与双向 v1 JSON Trace 交接。新增 119 条实际出牌/动态效果向量和 1 条跨房路线向量；两端分别核对源码固定预期。
- **Tier-2 离线提取**：SDK 内置 Roslyn 生成 [Lean 效果表](Sts2Model/Sim/Generated)与 [C# 效果表](DiffTest/Sts2Oracle/Tier2OracleData.cs)。[卡牌清单](docs/tier2_cards.json)对齐 717 个 ordinal ID：373 项生成、344 项整卡拒收；[审计](docs/tier2_extraction_audit.md)另列药水 36/68、怪物 19/122。表命中和解释器一致性不等于游戏等价。
- **显式单人整局模型**：[Expedition.step](Sts2Model/Run/Expedition.lean) 连接合法地图边、房间、战斗、独立/互斥奖励、换幕和终局。地图、遭遇与填充后的奖励由场景给出；严格模式拒绝缺规则的卡牌，不以 v1 Trace 补齐局外信息。

---

## 目录导航

| 路径 | 说明 |
|---|---|
| [Sts2Model/Core/](Sts2Model/Core) | 定点十进制 `Dec`、枚举与位标志、模型与实体 ID、Bit-exact `SplitMix64` / `Xoshiro256**` RNG 与 Fisher-Yates 洗牌 |
| [Sts2Model/Model/](Sts2Model/Model) | `CardEnergyCost` / `CardInstance` / `PlayerPiles` / `PowerInstance` / `Creature` / `OrbQueue` / `Player` / `CombatState` / `RunState` |
| [Sts2Model/Hook/](Sts2Model/Hook) | 154 个原版钩子目录与快照迭代器、统一 `HookBehavior` 接口、`ModHelper` 注册表与全部核心管线 |
| [Sts2Model/Command/](Sts2Model/Command) | `AttackCommand`、`CreatureCmd`、`CardCmd`、`PowerCmd`、`OrbCmd` |
| [Sts2Model/Combat/](Sts2Model/Combat) | 多人 `GameAction` 队列、`MonsterAI` 无环状态机、Hook 驱动的回合生命周期 |
| [Sts2Model/Multiplayer/](Sts2Model/Multiplayer) | 多人并发 `ActionQueueSet`（分玩家队列、选牌暂停、早发唤醒缓冲、取消标志）与 `PlayerChoiceSynchronizer` |
| [Sts2Model/Sim/](Sts2Model/Sim) | `EffectIR` 无头执行、`OpaqueStateDelta` 与 Tier-1 → Tier-2 → 通用回退效果环境 |
| [Sts2Model/Replay/](Sts2Model/Replay) | 全 18+9 语义历史与通用步索引记录 (`History.lean`)、关键帧 Seek / `forkTimeline` 分叉原语与 64 位 FNV-1a 校验和 (`Timeline.lean`)、外部 JSON Trace 协议与审计 (`TraceCodec.lean`) |
| [Sts2Model/Mechanics/](Sts2Model/Mechanics) | Orbs (Defect)、Necrobinder (Osty/Doom)、Regent (Stars/Forge)、Fool (Arrows/Melodies)、Dread (`Dominion` / `Ascender's Bane`) |
| [Sts2Model/Run/](Sts2Model/Run) | `ActMap` DAG 拓扑、`CardRarityOdds` (`Dec` + `Float32`)、`UnknownMapPointOdds`、`RelicGrabBag`、`RunLoop` |
| [Sts2Model/Catalog/](Sts2Model/Catalog) | 自动抽取的 717 卡 / 316 遗物 / 304 能力目录与纯内核唯一性证明 (`Verify.lean`) |
| [Sts2Model/Proofs/](Sts2Model/Proofs) | 9 大主题证明集（伤害管线、Hook 安全、牌堆守恒、能力系统、回合机与 AI 停机、多人确定性、角色机制、地图/赔率、并发时间线 `seek`/`forkTimeline` 等价及 `TraceCodec` 无损往返/审计） |
| [Sts2Model/Examples/](Sts2Model/Examples) | 核心引擎展示（`VanillaShowcase.lean`、`ModTemplates.lean`、`TimelineShowcase.lean`）与独立下游复盘/求解参考项目（`ReplayAnalyzerExample.lean`） |
| [Sts2Sim/Main.lean](Sts2Sim/Main.lean) | 可执行仿真 CLI (`lake exe sts2sim`、`--timeline-demo`、`--export-sample-trace`、`--inspect`、`--diff`) |
| [DiffTest/Sts2Oracle/](DiffTest/Sts2Oracle) | 零依赖 `.NET 9` C# 差分参考预言机 |
| [tools/Sts2AstExtractor/](tools/Sts2AstExtractor) | 零第三方依赖 Roslyn 提取器，生成两端 Tier-2 表和审计 |
| [scripts/](scripts) | 静态目录抽取、`.NET 9` ↔ Lean 4 对拍与 [原版战斗观测查看器](scripts/view_combat_replay.py) |
| [docs/traceability.md](docs/traceability.md) | 完整 C# 源码溯源矩阵、全部已证定理清单与审计报告 |
| [docs/modder_guide.md](docs/modder_guide.md) | STS2 Modder 实战指南、模板改造手册与形式化避坑清单 |
| [AGENTS.md](AGENTS.md) | AI Agent 与贡献者工程红线、命令清单与 Git 协作规范 |

---

## 离线查看原版战斗观测

将原版回放读取器导出的 `native-observations.json` 路径作为输入。不接受原始 `.mcr` 或 Lean Trace，也不运行游戏或模拟器。

```bash
p=/path/to/native-observations.json
uv run python scripts/view_combat_replay.py "$p"
uv run python scripts/view_combat_replay.py "$p" --checkpoint 5
uv run python scripts/view_combat_replay.py "$p" --event 3
```

默认按原始顺序分别列出状态快照与录制事件。`--checkpoint` 和 `--event` 使用录制的 ID 或序号精确查找。出牌与恢复事件仅在单玩家录制中、执行号和出牌签名都吻合时链接到完成帧；链接不是事件发生瞬间的状态。末帧不是清理后状态，未录制的牌堆不等于空堆。`exactRoundtrip` 是导出器的报告，查看器不重新校验。

## 审计原版文件

```bash
lake exe sts2sim --audit-run-history /path/to/history.run
lake exe sts2sim --audit-act-map /path/to/current_run.save
uv run python scripts/check_observed_survivor.py CAPTURE_DIR
```

三种证据独立：`.run` schema 9 核对录入的路线事实与跨点账目，不能导出地图边；`.save` schema 16 核对当前幕存图及已走的边，不能确认领过奖励或终局；Survivor 脚本只比较归档的开场 `#1→#5` 与独立的 `#21→#22`，没有重演中间回合。不修改或上传原版文件。

实机验收：v0.107.1 的 SILENT 胜局三幕 17/16/15 点，47 次跨点余额相符；副本第二点金币加 1 即报错。schema 16 存图的当前幕索引为 1、16 个已访问坐标与 15 条边；只删除 `(3,0)→(4,1)` 即报首段断边。两份文件不同局，不拼接验收。

---

## 构建与验证命令

```bash
# 编译 Lean 4 模型库、证明与可执行模拟器
lake build

# 验证零 sorry / axiom / native_decide
rg '\bsorry\b|\baxiom\b|\bnative_decide\b' Sts2Model Sts2Sim

# 59 项内置测试：原版规则、模板、目录、时间线、下游示例和跨房流程
lake exe sts2sim

# 输出基于核心无 UI 引擎构建的下游复盘/What-If/求解示例演示
lake exe sts2sim --timeline-demo

# 导出与脱机审计外部 JSON Trace 文件 (`schemaVersion = 1`)
mkdir -p .agent_works
lake exe sts2sim --export-sample-trace .agent_works/sample_trace.json
lake exe sts2sim --inspect .agent_works/sample_trace.json --verify --viewer 2 --seek 2

# 16 族 1110 条差分向量 + 双向 JSON 交接验证
dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo
uv run python scripts/run_diff_test.py

# 原版观测与审计：匿名回归
uv run python scripts/test_view_combat_replay.py
uv run python scripts/test_run_history_audit.py
uv run python scripts/test_act_map_audit.py

# 从 reference/sts2/ 重新静态抽取全量目录并生成 Verify.lean
uv run python scripts/extract_catalog.py

# 从 reference/sts2/ 重建 Tier-2 Lean/C# 效果表及提取审计
dotnet build tools/Sts2AstExtractor/Sts2AstExtractor.csproj --nologo
dotnet run --no-build --project tools/Sts2AstExtractor/Sts2AstExtractor.csproj -- .
uv run python scripts/check_tier2_cards.py --check-continuation
```

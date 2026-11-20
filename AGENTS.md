# AGENTS.md — `sts2_ideal` 开发与形式化验证协作规范

本文档面向在本仓库中协作的 AI Agent 与人类贡献者，约定工程边界、可信核（TCB）约束、原版语义规则、标准构建/测试命令及 Git 提交规范。

---

## 1. 项目定位与参考源码边界

- **目标**：为《杀戮尖塔 2》（Slay the Spire 2, STS2）Mod 开发者提供基于 Lean 4 的形式化逻辑建模参考、不变量证明模板与 `.NET 9` 跨语言差分测试基准。
- **真相来源**：反编译 C# 参考源码位于本地解压目录 `reference/sts2/`（来源压缩包 `sts2.zip`）。
- **严格隔离规则**：
  - `reference/` 与 `sts2.zip` 均已在 `.gitignore` 中排除，**严禁**将其加入 Git 暂存区或提交至版本库。
  - 若需要重新解压，可通过 `nix run nixpkgs#unzip` 执行（不要在仓内保留额外临时解压产物）。

---

## 2. 不可违背的工程红线

1. **核心库独立性与泛用性边界**：
   - `Sts2Model/` 核心层（除 `Sts2Model/Examples/` 外）**严禁**耦合具体业务启发式（如局后迟打易伤扫描）、特定结局对比视图或上层出牌搜索求解器；核心库只承载 STS2 原版规则语义与通用无 UI 模拟/时间线原语（`TimedCombatHistoryEntry`、`seek`、`switchViewer`、`forkTimeline`、FNV-1a 校验和）。
   - 核心模块禁止 `import Sts2Model.Examples.*`。面向具体下游工具（如复盘分析器、斩杀搜索器）的参考实现与独立见证定理一律放在 `Sts2Model/Examples/` 下明确隔离。
   - `.NET 9` 差分对拍仅用于核验原版 C# 语义与核心协议（不对拍自创复盘启发式）。
2. **纯 Lean 4.36.0 (`Std`) — 零 `Mathlib`**：
   - 工具链固定为 `leanprover/lean4:v4.36.0`（见 `lean-toolchain`），`lakefile.toml` 与 `lake-manifest.json` 不得引入 `Mathlib` 或任何第三方 Lake 依赖。
3. **零 `sorry`、零 `axiom`、零 `native_decide`**：
   - `Sts2Model/` 与 `Sts2Sim/` 代码主体（注释之外）禁止出现任何 `sorry`、`axiom` 或 `native_decide`。
   - 核心证明经 `#print axioms` 检查，必须仅依赖 Lean 内置标准公理（`propext`、`Classical.choice`、`Quot.sound`）。
   - 大规模枚举列表的 `Nodup` 证明（如 717 张卡牌 / 316 个遗物 / 304 个能力）不得回退到 `native_decide`；须沿用 `Sts2Model/Catalog/Types.lean` 中的分块 `isStrictlySorted` + `strictlySorted_join` + 纯内核 `decide` 模式。
4. **零警告与零错误**：
   - `lake build`（含 `lake clean && lake build`）与 `dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo` 均须达到 **0 errors / 0 warnings**。
5. **轻量零外依测试栈**：
   - `.NET 9` 对拍预言机（`DiffTest/Sts2Oracle`）保持纯 `net9.0`，零 NuGet 外部包。
   - 自动化脚本（`scripts/`）一律通过 `uv run python ...` 运行，且仅使用 Python 标准库。
6. **差分失败绝不放宽断言**：
   - 当 `.NET 9` 预言机与 Lean 4 (`lake exe sts2sim --diff`) 出现任何不一致时，**必须立即核对 `reference/sts2/` 原版 C# 实现**并修复真实语义偏差，严禁修改断言阈值、跳过用例或掩盖差异。
7. **非交付物只存本地**：
   - 人工记录、交接、草稿、临时脚本、临时测试输入/输出与验证日志统一放在根目录 `.agent_works/`，不提交。
   - 永久差分驱动、正式回归、可再生源码表及面向使用者的提取审计是交付物；Lake/MSBuild 的常规构建输出仍留在各自的忽略路径。

---

## 3. 代码结构概览

| 目录 / 文件 | 职责与对应范围 |
|---|---|
| `Sts2Model/Core/` | 定点十进制 `Dec`、`Enums`、`Ids`、Bit-exact `SplitMix64` / `Xoshiro256**` 与 `UnstableShuffle` (`Rng`) |
| `Sts2Model/Model/` | `Cost`、`Card`、`Power`、`Creature`、`Orb`、`Player`、`State` (`CombatState` / `RunState`) |
| `Sts2Model/Hook/` | `Hook.cs` 全量 154 个钩子名录与快照 (`Registry`)、`HookBehavior` / `ModHelper` 注册表、`Pipeline` |
| `Sts2Model/Command/` | `AttackCommand`、`CreatureCmd`、`CardCmd`、`PowerCmd`、`OrbCmd` |
| `Sts2Model/Combat/` | 多人确定性 `GameAction` 队列、`MonsterAI` 无环状态机、`TurnLoop` 的 Hook 驱动回合生命周期 |
| `Sts2Model/Multiplayer/` | 多人并发 `ActionQueueSet`（分玩家队列、选牌暂停/唤醒、取消标志）与 `PlayerChoiceSynchronizer` |
| `Sts2Model/Sim/` | 无 UI 效果解释器 (`EffectIR`)、`OpaqueStateDelta` 与分层效果环境（Tier-1 → Tier-2 → 通用回退） |
| `Sts2Model/Sim/Generated/` | Tier-2 效果表、怪物状态图及纯内核数量、`Nodup` 与结构良构证明 |
| `Sts2Model/Replay/` | 全 18+9 语义历史 (`History` 含 `TimedCombatHistoryEntry`)、关键帧 Seek / `forkTimeline` 与 64 位 FNV-1a (`Timeline`)、版本化外部 Trace JSON 线协议 (`TraceCodec`) |
| `Sts2Model/Mechanics/` | `Orbs` (Defect)、`Necrobinder` (Osty / Doom)、`Regent` (Stars / Forge)、`Fool` (Arrow / Melody)、`Dread` |
| `Sts2Model/Run/` | `ActMap` DAG、`CardRarityOdds` / `UnknownMapPointOdds` / `RelicGrabBag`、`RunLoop`、显式单人 `Expedition` |
| `Sts2Model/Catalog/` | 由 `scripts/extract_catalog.py` 自动生成的 `Cards` (717) / `Relics` (316) / `Powers` (304) 与 `Verify.lean` |
| `Sts2Model/Proofs/` | 9 个形式化证明模块：`DamagePipeline`、`HookSafety`、`CardPiles`、`PowerSystem`、`TurnMachine`、`Determinism`、`Mechanics`、`MapTopology`、`ReplayTimeline` |
| `Sts2Model/Examples/` | 原版、Mod 模板、时间线、独立下游和跨房换幕流程示例 |
| `Sts2Model.lean` | 公共伞形导出模块；新增 `Sts2Model/**/*.lean` 后必须同步在此 `import` |
| `Sts2Sim/` | `lake exe sts2sim` 回归测试（59 项）、v1 Trace、`--diff`、原版局史与当前幕地图审计 |
| `DiffTest/Sts2Oracle/` | `.NET 9` C# 预言机（`Program.cs`、`CombatEffects.cs`、生成表 `Tier2OracleData.cs`） |
| `tools/Sts2AstExtractor/` | 使用 .NET 9 SDK 内置 Roslyn 离线生成 Lean/C# Tier-2 表与提取审计，零第三方包 |
| `scripts/` | 静态目录与 Tier-2 卡牌清单校验、16 族 1110 向量、双向 JSON 交接、原生文件及战斗观测检查 |
| `docs/` | [源码与定理溯源](docs/traceability.md)、[Mod 指南](docs/modder_guide.md)、[Tier-2 提取审计](docs/tier2_extraction_audit.md)与[卡牌清单](docs/tier2_cards.json)（373/717；保留全部 361 个基线 ID） |

---

## 4. 关键 STS2 原版语义约定（修改时务必保持一致）

- **数值精度分离**：
  - C# `System.Decimal` 逻辑一律通过 `Dec` 精确有理定点数建模，`Dec.truncate` 使用 `Int.tdiv` 向零截断。
  - 原版显式使用单精度浮点的赔率滚轮（`CardRarityOdds`）在 `Run/Odds.lean` 中保留双轨建模：`CardRarityOddsDec` 用于纯内核定量/区间定理，`CardRarityOddsF32` 用于 IEEE-754 `Float32.toBits` 位精确对拍。
- **`ValueProp` 动力与穿甲隔离**：
  - 加减伤与格挡修正钩子必须严格检查 `props.isPoweredAttack` / `props.isPoweredCardOrMonsterBlock`；`ValueProp.unblockable` 跳过格挡吸收直接进入 `loseHpInternal`。
- **Hook 快照语义**：
  - 钩子执行先对监听者列表做快照（`snapshotCombatListeners` / `snapshotRunListeners`），每步前经 `isListenerAlive` 重检，从而天然跳过循环期间已移除实体且不回溯触发新增实体。
- **回合生命周期与层级分派**：
  - 新施加与叠加的持续时间状态不能混用；Poison 伤后仅存活时减层；Thorns 的无动力反伤不穿甲。Doom 差分仅核验敌侧处决。
  - Tier-2 `found` 只表示对应生成表含该 ID；不表示执行了有效果的动作。共享表的对拍验证执行一致性，不证明提取器或游戏等价。
- **费用计算早返回 (`Hook.cs:1626`)**：
  - `Hook.ModifyEnergyCostInCombat` 在 `originalCost < 0` 时直接返回原值，跳过战斗内全局钩子，最终再在外层截断为 `max 0`（已由 `CARD_COST` 差分测试验证）。
- **`ModHelper` 与目录边界**：
  - `ModPoolRegistry.concatModelsFromMods` 执行后永久冻结对应池（不可再注入）；`ModHookRegistry` 使用 C# `StringComparison.Ordinal` 等价字典序排序并去重。
  - 静态目录提取精确统计 `Cards = 717`、`Relics = 316`（排除非 `RelicModel` 的 `VakuuCardSelector.cs`）、`Powers = 304`（排除 4 个 `abstract` 基类 `TemporaryDexterityPower.cs` / `TemporaryFocusPower.cs` / `TemporaryStrengthPower.cs` / `TemporaryThornsPower.cs`）。

---

## 5. 标准构建、检验与环境说明

```bash
# 1. 构建全量 Lean 模型库与 sts2sim
lake build

# 2. 检查非注释 sorry / axiom / native_decide（应无真实代码命中）
rg -n '(\baxiom\b|\bnative_decide\b|by\s+sorry|:=\s*sorry)' Sts2Model Sts2Sim

# 3. 验证关键定理仅使用标准公理
lake env lean --stdin <<'EOF'
import Sts2Model
#print axioms Sts2Model.Proofs.damage_block_hp_conservation
#print axioms Sts2Model.Catalog.allCards_nodup
#print axioms Sts2Model.Proofs.orb_turn_end_passives_preserve_capacity
#print axioms Sts2Model.Sim.Generated.allGeneratedCards_nodup
EOF

# 4. 运行 59 项回归（原版、模板、目录、时间线、下游、跨房）
lake exe sts2sim
lake exe sts2sim --timeline-demo
mkdir -p .agent_works
lake exe sts2sim --export-sample-trace .agent_works/sample_trace.json
lake exe sts2sim --inspect .agent_works/sample_trace.json --verify --viewer 2 --seek 2

# 5. 16 族 1110 向量及双向 JSON 交接
dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo
uv run python scripts/run_diff_test.py

# 6. 从 reference/sts2/ 重新生成静态目录（仅在参考源码更新或调整解析器时执行）
uv run python scripts/extract_catalog.py

# 7. 从 reference/sts2/ 重建 Tier-2 表及审计
dotnet build tools/Sts2AstExtractor/Sts2AstExtractor.csproj --nologo
dotnet run --no-build --project tools/Sts2AstExtractor/Sts2AstExtractor.csproj -- .
```

- **NixOS / Linux 运行提示**：`.NET 9` 在 Nix 环境通过 `dotnet` 包装器注入 `DOTNET_ROOT`，因此 `scripts/run_diff_test.py` 显式调用 `dotnet DiffTest/Sts2Oracle/bin/Debug/net9.0/Sts2Oracle.dll --diff <tsv>`，不要直接执行裸 apphost 二进制。其他临时 CLI 工具按需使用 `nix run nixpkgs#<name>`。

---

## 6. 变更协同与 Git 提交规范

- **改逻辑必同步**：
  1. 新增 `Sts2Model/` 子模块时同步更新 `Sts2Model.lean`；
  2. 修改或新增规则/不变量时同步补齐 `Sts2Model/Proofs/` 定理、`Sts2Sim/Main.lean` / `Examples/` 用例，并为对应的新旧原版语义家族更新两端差分实现与 `scripts/run_diff_test.py`；
  3. 确保 `fnv1aString` 保持纯内核可归约（避免使用不可在 Lean 内核 `decide` 展开的 `@[extern]` `ByteArray` 函数）并与 `.NET 9` `ComputeTimelineChecksum` 位精确同步；
  4. 更新目录脚本、定理名、计数或对拍覆盖面后同步刷新 `docs/traceability.md`、`docs/modder_guide.md` 与 `README.md`。
- **提交风格**：采用常规语义化前缀与作用域（如 `chore:`、`feat(core,model):`、`feat(engine):`、`feat(catalog):`、`feat(proofs,examples):`、`test(sim,difftest):`、`docs:`），按逻辑层做原子提交；每次提交前确认 `git status` 不含 `reference/`、`sts2.zip`、`.lake/` 或 `.NET` 编译产物。

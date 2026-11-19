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

1. **纯 Lean 4.36.0 (`Std`) — 零 `Mathlib`**：
   - 工具链固定为 `leanprover/lean4:v4.36.0`（见 `lean-toolchain`），`lakefile.toml` 与 `lake-manifest.json` 不得引入 `Mathlib` 或任何第三方 Lake 依赖。
2. **零 `sorry`、零 `axiom`、零 `native_decide`**：
   - `Sts2Model/` 与 `Sts2Sim/` 代码主体（注释之外）禁止出现任何 `sorry`、`axiom` 或 `native_decide`。
   - 核心证明经 `#print axioms` 检查，必须仅依赖 Lean 内置标准公理（`propext`、`Classical.choice`、`Quot.sound`）。
   - 大规模枚举列表的 `Nodup` 证明（如 717 张卡牌 / 316 个遗物 / 304 个能力）不得回退到 `native_decide`；须沿用 `Sts2Model/Catalog/Types.lean` 中的分块 `isStrictlySorted` + `strictlySorted_join` + 纯内核 `decide` 模式。
3. **零警告与零错误**：
   - `lake build`（含 `lake clean && lake build`）与 `dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo` 均须达到 **0 errors / 0 warnings**。
4. **轻量零外依测试栈**：
   - `.NET 9` 对拍预言机（`DiffTest/Sts2Oracle`）保持纯 `net9.0`，零 NuGet 外部包。
   - 自动化脚本（`scripts/`）一律通过 `uv run python ...` 运行，且仅使用 Python 标准库。
5. **差分失败绝不放宽断言**：
   - 当 `.NET 9` 预言机与 Lean 4 (`lake exe sts2sim --diff`) 出现任何不一致时，**必须立即核对 `reference/sts2/` 原版 C# 实现**并修复真实语义偏差，严禁修改断言阈值、跳过用例或掩盖差异。

---

## 3. 代码结构概览

| 目录 / 文件 | 职责与对应范围 |
|---|---|
| `Sts2Model/Core/` | 定点十进制 `Dec`、`Enums`、`Ids`、Bit-exact `SplitMix64` / `Xoshiro256**` 与 `UnstableShuffle` (`Rng`) |
| `Sts2Model/Model/` | `Cost`、`Card`、`Power`、`Creature`、`Orb`、`Player`、`State` (`CombatState` / `RunState`) |
| `Sts2Model/Hook/` | `Hook.cs` 全量 154 个钩子名录与快照 (`Registry`)、`HookBehavior` / `ModHelper` 注册表、`Pipeline` |
| `Sts2Model/Command/` | `AttackCommand`、`CreatureCmd`、`CardCmd`、`PowerCmd`、`OrbCmd` |
| `Sts2Model/Combat/` | 多人确定性 `GameAction` 队列、`MonsterAI` 无环状态机、`TurnLoop` (`CombatManager`) |
| `Sts2Model/Mechanics/` | `Orbs` (Defect)、`Necrobinder` (Osty / Doom)、`Regent` (Stars / Forge)、`Fool` (Arrow / Melody)、`Dread` |
| `Sts2Model/Run/` | `ActMap` DAG、`CardRarityOdds` / `UnknownMapPointOdds` / `RelicGrabBag`、`RunLoop` |
| `Sts2Model/Catalog/` | 由 `scripts/extract_catalog.py` 自动生成的 `Cards` (717) / `Relics` (316) / `Powers` (304) 与 `Verify.lean` |
| `Sts2Model/Proofs/` | 8 个形式化证明模块：`DamagePipeline`、`HookSafety`、`CardPiles`、`PowerSystem`、`TurnMachine`、`Determinism`、`Mechanics`、`MapTopology` |
| `Sts2Model/Examples/` | `VanillaShowcase.lean`（30 个原版规则验证）与 `ModTemplates.lean`（4 个 Mod 模板及安全契约） |
| `Sts2Model.lean` | 公共伞形导出模块；新增 `Sts2Model/**/*.lean` 后必须同步在此 `import` |
| `Sts2Sim/Main.lean` | `lake exe sts2sim` 默认回归测试入口（37 项断言）及 `--diff <tsv>` 对拍服务端 |
| `DiffTest/Sts2Oracle/` | `.NET 9` C# 直译参考预言机（`Sts2Oracle.csproj`、`Program.cs`） |
| `scripts/` | `extract_catalog.py`（静态目录抽取）与 `run_diff_test.py`（9 族 670 向量差分对拍） |
| `docs/` | `traceability.md`（源码溯源与定理全表）与 `modder_guide.md`（Mod 开发者建模指南） |

---

## 4. 关键 STS2 原版语义约定（修改时务必保持一致）

- **数值精度分离**：
  - C# `System.Decimal` 逻辑一律通过 `Dec` 精确有理定点数建模，`Dec.truncate` 使用 `Int.tdiv` 向零截断。
  - 原版显式使用单精度浮点的赔率滚轮（`CardRarityOdds`）在 `Run/Odds.lean` 中保留双轨建模：`CardRarityOddsDec` 用于纯内核定量/区间定理，`CardRarityOddsF32` 用于 IEEE-754 `Float32.toBits` 位精确对拍。
- **`ValueProp` 动力与穿甲隔离**：
  - 加减伤与格挡修正钩子必须严格检查 `props.isPoweredAttack` / `props.isPoweredCardOrMonsterBlock`；`ValueProp.unblockable` 跳过格挡吸收直接进入 `loseHpInternal`。
- **Hook 快照语义**：
  - 钩子执行先对监听者列表做快照（`snapshotCombatListeners` / `snapshotRunListeners`），每步前经 `isListenerAlive` 重检，从而天然跳过循环期间已移除实体且不回溯触发新增实体。
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
EOF

# 4. 运行 37 项可执行回归测试
lake exe sts2sim

# 5. 构建 .NET 9 对拍预言机并执行 9 族 670 向量差分测试
dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo
uv run python scripts/run_diff_test.py

# 6. 从 reference/sts2/ 重新生成静态目录（仅在参考源码更新或调整解析器时执行）
uv run python scripts/extract_catalog.py
```

- **NixOS / Linux 运行提示**：`.NET 9` 在 Nix 环境通过 `dotnet` 包装器注入 `DOTNET_ROOT`，因此 `scripts/run_diff_test.py` 显式调用 `dotnet DiffTest/Sts2Oracle/bin/Debug/net9.0/Sts2Oracle.dll --diff <tsv>`，不要直接执行裸 apphost 二进制。其他临时 CLI 工具按需使用 `nix run nixpkgs#<name>`。

---

## 6. 变更协同与 Git 提交规范

- **改逻辑必同步**：
  1. 新增 `Sts2Model/` 子模块时同步更新 `Sts2Model.lean`；
  2. 修改或新增规则/不变量时同步补齐 `Sts2Model/Proofs/` 定理、`Sts2Sim/Main.lean` / `Examples/` 用例，以及（若属 9 大对拍族或新家族）`DiffTest/Sts2Oracle/Program.cs` + `scripts/run_diff_test.py`；
  3. 更新目录脚本、定理名、计数或对拍覆盖面后同步刷新 `docs/traceability.md`、`docs/modder_guide.md` 与 `README.md`。
- **提交风格**：采用常规语义化前缀与作用域（如 `chore:`、`feat(core,model):`、`feat(engine):`、`feat(catalog):`、`feat(proofs,examples):`、`test(sim,difftest):`、`docs:`），按逻辑层做原子提交；每次提交前确认 `git status` 不含 `reference/`、`sts2.zip`、`.lake/` 或 `.NET` 编译产物。

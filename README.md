# sts2_ideal — 《杀戮尖塔 2》(Slay the Spire 2) Lean 4 逻辑建模参考项目

面向 **Slay the Spire 2 (STS2) Mod 开发者**的完整可执行 Lean 4 形式化建模与跨语言差分验证参考工程，严格溯源于反编译 C# 参考源码（`sts2.zip` → `reference/sts2/`）。

## 核心设计保障

- **纯粹 Lean 4.36.0 (`Std`)**：零 `Mathlib` 依赖，全部编译秒级完成。
- **纯净可信证明内核**：全项目 `Sts2Model/` 与 `Sts2Sim/` 合计 **10,360 行**代码，**0 `sorry`**、**0 `axiom`**、**0 `native_decide`**。
- **方案 C 全量静态目录与核证**：自动扫描并核证原版 **717 张卡牌**、**316 个遗物**（不含辅助类 `VakuuCardSelector`）、**304 个具体能力**（不含 4 个 `Temporary*Power` 抽象基类）以及 `Hook.cs` 全部 **154 个公开钩子**（`Nodup` 全数经纯内核 `decide` + `strictlySorted_join` 证毕）。
- **`.NET 9` ↔ Lean 4 跨语言位精确对拍**：内置原生 C# 预言机 (`DiffTest/Sts2Oracle`) 与 9 大族 **670 条**确定性/对抗边界测试向量，覆盖 `SplitMix64` / `Xoshiro256**`、IEEE-754 `Float64`/`Float32` 比特表示、`System.Decimal` 定点运算与 `Hook` / `Command` / `CardEnergyCost` / `ModHelper` 全链路。

---

## 目录导航

| 路径 | 说明 |
|---|---|
| [Sts2Model/Core/](Sts2Model/Core) | 定点十进制 `Dec`、枚举与位标志、模型与实体 ID、Bit-exact `SplitMix64` / `Xoshiro256**` RNG 与 Fisher-Yates 洗牌 |
| [Sts2Model/Model/](Sts2Model/Model) | `CardEnergyCost` / `CardInstance` / `PlayerPiles` / `PowerInstance` / `Creature` / `OrbQueue` / `Player` / `CombatState` / `RunState` |
| [Sts2Model/Hook/](Sts2Model/Hook) | 154 个原版钩子目录与快照迭代器、统一 `HookBehavior` 接口、`ModHelper` 注册表与全部核心管线 |
| [Sts2Model/Command/](Sts2Model/Command) | `AttackCommand`、`CreatureCmd`、`CardCmd`、`PowerCmd`、`OrbCmd` |
| [Sts2Model/Combat/](Sts2Model/Combat) | 多人同步确定性 `GameAction` 队列、`MonsterAI` 无环状态机、`CombatManager` 回合状态机 |
| [Sts2Model/Mechanics/](Sts2Model/Mechanics) | Orbs (Defect)、Necrobinder (Osty/Doom)、Regent (Stars/Forge)、Fool (Arrows/Melodies)、Dread (`Dominion` / `Ascender's Bane`) |
| [Sts2Model/Run/](Sts2Model/Run) | `ActMap` DAG 拓扑、`CardRarityOdds` (`Dec` + `Float32`)、`UnknownMapPointOdds`、`RelicGrabBag`、`RunLoop` |
| [Sts2Model/Catalog/](Sts2Model/Catalog) | 自动抽取的 717 卡 / 316 遗物 / 304 能力目录与纯内核唯一性证明 (`Verify.lean`) |
| [Sts2Model/Proofs/](Sts2Model/Proofs) | 8 大主题证明集（伤害管线、Hook 安全、牌堆守恒、能力系统、回合机与 AI 停机、多人确定性、角色机制、地图/赔率） |
| [Sts2Model/Examples/](Sts2Model/Examples) | 30 个原版规则演示用例 (`VanillaShowcase.lean`) + 4 个带安全契约证明的 Mod 模板 (`ModTemplates.lean`) |
| [Sts2Sim/Main.lean](Sts2Sim/Main.lean) | 可执行仿真与回归 CLI (`lake exe sts2sim`) 及 `--diff` 差分服务端 |
| [DiffTest/Sts2Oracle/](DiffTest/Sts2Oracle) | 零依赖 `.NET 9` C# 差分参考预言机 |
| [scripts/](scripts) | `extract_catalog.py`（静态目录抽取）与 `run_diff_test.py`（`.NET 9` ↔ Lean 4 对拍） |
| [docs/traceability.md](docs/traceability.md) | 完整 C# 源码溯源矩阵、全部已证定理清单与审计报告 |
| [docs/modder_guide.md](docs/modder_guide.md) | STS2 Modder 实战指南、模板改造手册与形式化避坑清单 |
| [AGENTS.md](AGENTS.md) | AI Agent 与贡献者工程红线、命令清单与 Git 协作规范 |

---

## 构建与验证命令

```bash
# 编译 Lean 4 模型库、证明与可执行模拟器
lake build

# 验证零 sorry / axiom / native_decide
rg '\bsorry\b|\baxiom\b|\bnative_decide\b' Sts2Model Sts2Sim

# 运行全部 37 项内置测试 (30 原版 + 4 Mod 模板 + 3 目录断言)
lake exe sts2sim

# 构建 .NET 9 对拍预言机并跑通全部 670 条差分测试向量
dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo
uv run python scripts/run_diff_test.py

# 从 reference/sts2/ 重新静态抽取全量目录并生成 Verify.lean
uv run python scripts/extract_catalog.py
```

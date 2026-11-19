# Slay the Spire 2 Mod 开发者 Lean 4 逻辑验证指南

本指南面向《杀戮尖塔 2》（STS2）Mod 开发者，介绍如何利用 `sts2_ideal` 中的 Lean 4 形式化引擎与 `.NET 9` 差分对拍体系，在动手写 C# Harmony/ModHelper 补丁或实装前，于数学层面预先验证自定义能力、遗物、卡牌与钩子的安全性与原版一致性。

---

## 1. 工程结构与设计原则

```text
sts2_ideal/
├── Sts2Model/
│   ├── Core/        # Dec 定点十进制、Enums、ModelId、Bit-exact RNG (SplitMix64 + Xoshiro256**)
│   ├── Model/       # Cost、Card、Power、Creature、Orb、Player、CombatState/RunState
│   ├── Hook/        # Registry (154 hooks)、ModHelper (HookBehavior / Pool & Hook 注册表)、Pipeline
│   ├── Command/     # AttackCommand、CreatureCmd、CardCmd、PowerCmd、OrbCmd
│   ├── Combat/      # GameAction 队列、MonsterAI 状态机、TurnLoop 回合控制
│   ├── Mechanics/   # Orbs、Necrobinder (Osty/Doom)、Regent (Stars/Forge)、Fool (Arrow/Melody)、Dread
│   ├── Run/         # ActMap DAG、CardRarityOdds / UnknownMapPointOdds / RelicGrabBag、RunLoop
│   ├── Catalog/     # 从 reference/sts2/ 自动抽取的 717 Cards / 316 Relics / 304 Powers 与核证明
│   ├── Examples/    # 30 个原版演示 (VanillaShowcase) + 4 个 Mod 模板及证明 (ModTemplates)
│   └── Proofs/      # 8 个主题定理证明模块（全项目零 sorry / zero axiom / zero native_decide）
├── Sts2Sim/         # 可执行验证入口 (`lake exe sts2sim` 与 `--diff`)
├── DiffTest/        # .NET 9 C# 对拍预言机 (`Sts2Oracle`, 零第三方依赖)
├── scripts/         # `extract_catalog.py` 与 `run_diff_test.py` (`uv run python`)
└── docs/            # 溯源矩阵 (`traceability.md`) 与本开发指南 (`modder_guide.md`)
```

核心工程约束：
1. **纯粹 Lean 4.36.0（零 `Mathlib`）**：编译快速轻量，仅使用标准库与核心 Tactics（`omega`、`simp`、`decide`）。
2. **双精度与浮点严格分离**：所有遵循 C# `System.Decimal` 的金额/伤害/格挡/费用使用精确有理定点数 [Dec](../Sts2Model/Core/Dec.lean) 建模；而原版显式使用 32 位浮点的 `CardRarityOdds` 与 RNG 序列同时提供 [IEEE-754 `Float32` / `UInt64` 位精确模型](../Sts2Model/Run/Odds.lean) 用于与 `.NET 9` 逐比特对拍。
3. **无禁用公理**：`Sts2Model/` 与 `Sts2Sim/` 内严格禁用 `sorry`、`axiom` 与 `native_decide`，一切性质均经 Lean 内核直接检验。

---

## 2. 快速上手与常用命令

```bash
# 1. 编译全量 Lean 模型与证明
lake build

# 2. 运行全部 37 项内置可执行测试（30 个原版场景 + 4 个 Mod 模板 + 3 项目录断言）
lake exe sts2sim

# 3. 编译 .NET 9 对拍预言机并执行 670 条跨语言差分测试
dotnet build DiffTest/Sts2Oracle/Sts2Oracle.csproj --nologo
uv run python scripts/run_diff_test.py

# 4. 可选：从 reference/sts2/ 重新生成原版 Cards/Relics/Powers 目录与 Nodup 证明
uv run python scripts/extract_catalog.py
```

---

## 3. 在 Lean 4 中建模并验证自己的 Mod（四大模板实战）

[Sts2Model/Examples/ModTemplates.lean](../Sts2Model/Examples/ModTemplates.lean) 内置了四个可直接仿写的 Mod 建模模板，涵盖最常见的 Power、Relic、Card 以及多 Mod 协同注册场景。

### 3.1 模板一：自定义 Power（遵守 `ValueProp` 动力隔离）

假设你要实现一个 Mod 能力 `BloodthirstPower`：“当拥有者当前生命值不超过最大生命一半时，其打出的动力攻击伤害 × 1.5（`Dec.ofScaled 15 1`）。”

在 Lean 中通过覆盖 `HookBehavior.neutral` 来描述其行为：

```lean
def modBloodthirstPowerId : ModelId := ⟨"MOD_EXAMPLE", "BLOODTHIRST_POWER"⟩

def modBloodthirstBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyDamageMultiplicative := fun ctx _ _ props dealer _ =>
      match dealer, ctx.ownerId with
      | some d, some oid =>
          if d.id == oid && props.isPoweredAttack && d.currentHp * 2 ≤ d.maxHp then
            Dec.ofScaled 15 1
          else Dec.one
      | _, _ => Dec.one }
```

紧接着可以立即在 Lean 中证明两个安全契约：
- `modBloodthirst_unpowered_safe`：若 `!props.isPoweredAttack`，倍率为 `Dec.one`（不会误伤中毒、反伤、生命流失等无动力伤害）。
- `modBloodthirst_factor_nonneg`：无论当前属性状态如何，倍率输出恒非负（绝不导致负伤害翻转成回血）。

### 3.2 模板二：自定义 Relic（护甲外生命流失封顶）

假设你想设计遗物 `AegisWard`：“每次装备者受到生命流失（`ModifyHpLostAfterOsty` 阶段）时，最多损失 5 点 HP。”

```lean
def modAegisWardRelicId : ModelId := ⟨"MOD_EXAMPLE", "AEGIS_WARD_RELIC"⟩

def modAegisWardBehavior : HookBehavior :=
  { HookBehavior.neutral with
    modifyHpLostAfterOsty := fun ctx target amt _ _ _ =>
      match ctx.ownerId with
      | some oid => if target.id == oid then Dec.min amt (Dec.ofNat 5) else amt
      | none => amt }
```

可证明的遗物契约：
- `modAegisWard_caps_at_five`：对宿主产生的输出恒 `≤ Dec.ofNat 5`。
- `modAegisWard_monotone_le`：输出永远 `≤` 原始输入量（绝不会把本来小于 5 的伤害放大成 5）。

### 3.3 模板三：自定义 Card（手牌资源校验与牌堆守恒）

Regent 风格的费星双资源攻击牌 `modStarStrikeCardId`（由 `mkModStarStrike` 构造 2 能量 + 1 星辰卡牌）：
1. 构造 `CardInstance` 后可将其代入 `CombatState`；
2. 利用通用的 `CardPiles` 定理与 `modStarStrike_pile_and_resource_safe`，证明打出此牌检查 `canPlay` 通过后，`spendResources` 的能量与星辰消耗量必然各自不超过玩家现有资源（零下溢），且从手牌移入弃牌堆的 `moveCard` 操作严格保留玩家战斗总牌数不变。

### 3.4 模板四：多 Mod 共存与 `ModHelper` 注册校验

真实环境中玩家往往同时开启数十个 Mod。使用 [ModHookRegistry](../Sts2Model/Hook/ModHelper.lean) 与 [ModPoolRegistry](../Sts2Model/Hook/ModHelper.lean)：
- `ModHookRegistry.subscribeCombatHooks` 使用 `insertSubscriberSorted`（按 Ordinal 字符串严格比较、去重插入）保证多 Mod 无论先加载哪一个，触发顺序完全一致；
- `ModPoolRegistry.concatModelsFromMods` 一旦执行拼池即冻结对应 `poolKey`（`isFrozen = true`），后续调用 `addModelToPool` 均为空操作（`modHelper_pool_freeze_monotonic`）；
- `modComposition_safe` 示例展示了上述三条静态保证的联合证明写法。

---

## 4. 利用静态目录查找原版模型细节

编写兼容性 Mod 时经常需要检索原版卡牌关键词、能力叠层模式与遗物稀有度。[Sts2Model/Catalog/Verify.lean](../Sts2Model/Catalog/Verify.lean) 提供了经内核证明覆盖全量 **717 张卡牌 / 316 个遗物 / 304 个能力**（外加 [traceability.md](./traceability.md) 中列明的辅助/抽象基类注释）的查询函数：
- `lookupCard "SOVEREIGN_BLADE"` → `Option CardCatalogEntry`
- `lookupRelic "..."` → `Option RelicCatalogEntry`
- `lookupPower "DOOM_POWER"` → `Option PowerCatalogEntry`（含 `powerType`、`stackType`、`instanceType`、`allowNegative`）

若参考游戏版本更新导致 `reference/sts2/` 内容变动，只需再次运行：

```bash
uv run python scripts/extract_catalog.py
lake build
```

即可全自动重新生成 `Cards.lean` / `Relics.lean` / `Powers.lean` 与纯内核 `Nodup` 证明（不使用 `native_decide`）。

---

## 5. 添加可执行测试与 `.NET 9` 差分对拍

### 5.1 增加 Lean 可执行断言
1. 在 `Sts2Model/Examples/ModTemplates.lean` 的 `allModTemplateTests`（或新建模块）中追加一条 `(testName, Bool)` 断言函数；
2. 运行 `lake build && lake exe sts2sim`，确认输出 `Summary: N/N tests passed (failed=0)`。

### 5.2 增加 C# ↔ Lean 差分测试向量
如果你想把一条自己的复杂算法（比如某种全新 Buff 叠加公式或牌费修正逻辑）纳入跨语言对拍：
1. 在 `Sts2Sim/Main.lean` 的 `evalDiffLine` 中增加新的操作码分支；
2. 在 `DiffTest/Sts2Oracle/Program.cs` 的主分发中用直译 C# 实现同一输入格式的分支；
3. 在 `scripts/run_diff_test.py` 的 `generate_vectors()` 里生成几十条正常值 + 极值（负数、零、溢出界 `999999999`、`Unpowered`/`Unblockable` 组合）的 TSV 行；
4. 重新构建两者并运行 `uv run python scripts/run_diff_test.py` 直到 `mismatches: 0`。

---

## 6. STS2 Mod 开发高频避坑指南（基于形式化证明总结）

1. **误对非动力效果施加力量/敏捷/易伤/虚弱**
   - *依据定理*：`unpowered_ignores_powered_damage_modifiers`、`unpowered_ignores_powered_block_modifiers`（[DamagePipeline.lean](../Sts2Model/Proofs/DamagePipeline.lean)）。
   - *实践建议*：自定义增伤/加甲钩子时务必检查 `props.isPoweredAttack` 或 `props.isPoweredCardOrMonsterBlock`，否则会让毒、反伤、`Unpowered` 生命损失等技能意外吃到倍率。

2. **假设多 Mod 的“加伤”和“乘伤”钩子位置可互换**
   - *依据定理*：`mod_additive_hooks_commute`、`mod_multiplicative_hooks_commute` 与反例定理 `mod_mixed_add_mul_noncommutative`（[HookSafety.lean](../Sts2Model/Proofs/HookSafety.lean)）。
   - *实践建议*：不要在同一个 `ModifyDamageMultiplicative` 阶段里靠侧效应做加法，严格按阶段拆入 `modifyDamageAdditive` / `modifyDamageMultiplicative` / `modifyDamageMultiplicativeLate`；否则极易受 Mod 安装顺序影响而失衡（虽有 `ModHelper` Ordinal 排序兜底确定性）。

3. **在 `After*` 钩子里动态召唤随从或贴新 Power，却期望同轮钩子立刻回调它**
   - *依据定理*：`snapshot_ignores_newly_added_listeners`、`snapshot_skips_removed_listeners`（[HookSafety.lean](../Sts2Model/Proofs/HookSafety.lean)）。
   - *实践建议*：`Hook.cs` 通过 `snapshotCombatListeners` 拍摄当拍监听器快照，并在分发每个监听器前检查 `isListenerAlive`。触发途中新增的单位/能力在本轮剩余钩子阶段中**不会被调用**，已被移除的则会被立即跳过。

4. **牌费局部减成负数后的全局 Hook 早返回机制**
   - *依据事实*：`Hook.cs:1626`（`if (originalCost < 0m) return originalCost;`）及 `.NET 9` ↔ Lean 对拍 #505/#513。
   - *实践建议*：只要局部修正把牌费降到 `< 0`，战斗内全局费用修改钩子（`ModifyEnergyCostInCombat` / `Late`）将完全跳过不执行，随后外层再取 `max 0`。设计“本回合费用 +2”的负面状态/怪物能力时要注意它无法抬高已经被减到负数的牌费。

5. **`DieForYou` 与 `Osty` 溢伤传导 + `Unblockable` 分界**
   - *依据定理*：`dieForYou_ignores_unpowered`、`dieForYou_ignores_dead_osty`（[Mechanics.lean](../Sts2Model/Proofs/Mechanics.lean)）及 `osty_redirection_conservation`（[DamagePipeline.lean](../Sts2Model/Proofs/DamagePipeline.lean)）。
   - *实践建议*：`Unblockable` 跳过格挡（`unblockable_bypasses_block`），而对 Necrobinder 本体打出的动力攻击若由活 Osty 代挡，Osty 阵亡后的过量伤害 `overkillDamage` 仍会回流并扣减主人本体 HP（注意自身带有护甲封顶或 `Intangible` 时 `ModifyHpLost` 四阶段 `BeforeOsty` vs `AfterOsty` 的触发差异）。

6. **AllowNegative Counter Power 在负值时的 Artifact 判定**
   - *依据源码*：`PowerInstance.getTypeForAmount` 与 `PowerCmd.lean`、`artifact_blocks_visible_debuff`（[PowerSystem.lean](../Sts2Model/Proofs/PowerSystem.lean)）。
   - *实践建议*：对于允许负数的计数能力（如可扣成负数的力量/敏捷），向对方施加负值时其瞬时类型会被判作 `Debuff`，因此能触发对方持有的 `Artifact` 并消耗 1 层人工制品将其格挡；但若是一个**不允许负数**且本身标为 Debuff 的能力收到负delta（如减少毒层数），类型反而会被视为 `Buff` 而绕过 Artifact。

7. **千万不要在 `Should*` 或 RNG 流里混用非确定性迭代顺序**
   - *依据定理*：`actionQueue_multiplayer_deterministic`（[Determinism.lean](../Sts2Model/Proofs/Determinism.lean)）与 `unstableShuffle_deterministic`。
   - *实践建议*：STS2 支持多人联机确定性同步，凡遍历状态字典或从卡池/奖励池抽取条目，务必经 `DeterministicModelComparer` / 固定 ID 排序后再消费 `Rng` 子流；不要直接依赖无序集合遍历顺序。

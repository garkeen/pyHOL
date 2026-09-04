# holpy 手册

> 项目主页见顶层 [`../README.md`](../README.md)。本页只是手册 7 章的阅读索引。

## 阅读路线

### 新手（学 HOL + 学 holpy）

按顺序读：
1. [`01_hol_logic.md`](01_hol_logic.md) -- HOL 逻辑基础（纯理论，无代码）
2. [`02_kernel.md`](02_kernel.md) -- 内核实现（Type/Term/Thm/原语/ProofTerm）
3. [`03_macro.md`](03_macro.md) -- 宏系统与信任模型
4. [`04_conv_matcher.md`](04_conv_matcher.md) -- 转换与匹配
5. [`05_tactic.md`](05_tactic.md) -- 策略系统
6. [`06_method.md`](06_method.md) -- 方法层与证明状态
7. [`07_system.md`](07_system.md) -- 系统组织总览

### 开发者（按需跳读）

- 想理解证明可信度：01 -> 02 -> 03
- 想写自动证明：04 -> 05 -> 03
- 想理解 `.pyhol` 证明格式：06 -> 07
- 想理解理论加载：07

## 文件索引

| 文件 | 内容 | 详细程度 |
|---|---|---|
| [`01_hol_logic.md`](01_hol_logic.md) | HOL 逻辑理论（类型/项/λ/sequent/原语/命题/谓词/归纳） | 最详细 |
| [`02_kernel.md`](02_kernel.md) | 内核（Type/Term/Thm/15原语/Proof/ProofTerm/Theory/Extension/Report） | 详细 |
| [`03_macro.md`](03_macro.md) | 宏（Macro/eval/level/expand/信任模型/核心宏目录） | 详细 |
| [`04_conv_matcher.md`](04_conv_matcher.md) | 转换（Conv/组合子/遍历/rewr_conv）+ 匹配（first_order_match/Inst） | 详细 |
| [`05_tactic.md`](05_tactic.md) | 策略（Tactic/tactical/内置策略目录） | 详细 |
| [`06_method.md`](06_method.md) | 方法（Method/ProofState/四种分发/方法目录/属性/step格式） | 中等 |
| [`07_system.md`](07_system.md) | 系统总览（.pyhol/Item/理论加载/domain/自动化/SAINT/参数化系统/目录索引/数据流） | 粗略 |

## 详细程度原则

**越根本越细、越易改越略**：
- 01-05（逻辑理论与核心抽象）最详细，因为这些极难改动。
- 06（方法层）中等，较稳定但可能微调。
- 07（系统组织）粗略，因为实现层（如 `domains/` 包机制）是权益之计，后续可能调整。

## 速查

### 15 条原语

`assume` / `implies_intr` / `implies_elim` / `reflexive` / `symmetric` / `transitive` / `combination` / `equal_intr` / `equal_elim` / `subst_type` / `substitution` / `beta_conv` / `abstraction` / `forall_intr` / `forall_elim`

### 核心宏

`framework/macros/core.py` 注册（领域无关）：

`intros` / `resolve_theorem` / `beta_norm` / `apply_theorem` / `apply_theorem_for` / `apply_theorem_inst` / `apply_induct` / `apply_fact` / `apply_fact_for` / `rewrite_goal` / `rewrite_goal_sym` / `rewrite_goal_with_prev` / `rewrite_goal_with_prev_sym` / `rewrite_fact` / `rewrite_fact_sym` / `rewrite_fact_with_prev` / `forall_elim_gen` / `trivial` / `auto_close`

领域宏示例：`imp_conj` / `imp_disj` / `resolution`（domains/logic）、`nat_norm` / `real_norm`、`eval_Sem` / `vcg`（imperative）、`z3`（framework/macros/z3.py，oracle）。

### 内置策略

向后：`rule` / `resolve` / `var_induct` / `datatype_cases` / `intros` / `rewrite_goal` / `rewrite_goal_with_conv` / `rewrite_goal_with_prev` / `apply_prev` / `cases` / `inst_exists_goal` / `assumption` / `reflexive` / `equal_intr` / `trans` / `trivial` / `accept` / `elim_exists`

正向：`apply_theorem_forward` / `rewrite_fact_forward` / `apply_fact_forward` / `rewrite_fact_with_prev_forward` / `forall_elim_forward`

### 方法分发模式

- **A 策略路径**：`rule` / `cases` / `type_cases` / `rewrite`（goal）/ `induct` / `refl` / `eq_intro` / `trans` / `unfold` / `simp` / ...
- **B 受检宏调用**：`norm` / 领域宏方法（`nat_norm` / `real_norm` / `eval_Sem` / ...）
- **C 正向路径**：`forward` / `rewrite`（fact）/ `inst`（fact）
- **D 直接操作**：`cut` / `var` / `elim` / `intro` / `z3`

> 行不可变：fact/goal 生成后不可改写，已移除 `thin` / `sym` / `revert_intro` / `drule` 等行改写方法。

### 属性

`hint_rewrite` / `hint_rewrite_sym` / `hint_backward` / `hint_backward1` / `hint_forward` / `hint_resolve` / `var_induct`

### 信任级别

| level | 含义 |
|---|---|
| `None` | 永远展开 |
| `0` | oracle（不可展开） |
| `1` | 标准宏（可展开） |
| `10` | 领域计算 |

# 策略系统

> 代码事实以 `core/tactic.py` 为准。

策略（Tactic）是证明构造的中间层：Method 层调用策略，策略执行推理决策（匹配、参数检测、效果检查），返回 `ProofTerm`（其 rule 为宏或原语）。策略本身不直接出现在 `.pyhol` 证明文件中——那是 Method 层的序列化产物。

## 1. 统一接口

```python
class Tactic:
    def get_proof_term(self, *, args=None, prevs=None) -> ProofTerm:
        raise NotImplementedError
```

- `args`：策略参数（定理名、实例化、变量名、项等）。
- `prevs`：`List[ProofTerm]`，已有事实的证明项。
- 返回：`ProofTerm`，其 `rule` 为宏名或原语名。

**goal 的传递方式**：向后策略将目标作为 `prevs[0]` 携带（一个 `ProofTerm.atom` 或 `sorry`），在方法体内取 `goal = prevs[0].th` 后 `prevs = prevs[1:]`。正向策略不使用 goal，`prevs` 全部是输入事实。

这一设计消除了"每次操作必须绑定一个 goal"的强制——正向推理无需虚构目标。

## 2. gap 与 sorry

`ProofTerm.sorry(th)` 创建一个 gap：`th` 是待证目标，`gaps = [th]`。

策略返回的 ProofTerm 中，`sorry` 节点就是"尚待证明的子目标"。例如 `cases` 把目标 `C` 拆为两个 gap：`A ⟶ C` 和 `¬A ⟶ C`。

## 3. 向后推理策略

向后策略：`prevs[0]` 是目标，`prevs[1:]` 是可选的输入事实。返回的 ProofTerm 证明目标，其中 `sorry` 节点是新生成的子目标。

| 策略 | args | 子目标 | 说明 |
|---|---|---|---|
| `rule()` | `th_name` 或 `(th_name, inst)` | 每个未匹配假设 | 向后应用定理（MATCH_MP_TAC 语义）：匹配结论与 goal，匹配已有假设与 prevs，未匹配假设变 sorry；**不做整条命题回退**（蕴含目标用 `intro` 或 `accept`） |
| `resolve()` | `th_name` | 0 | 消解：`~A` 定理 + 事实 `A` 证任意目标；定理接受三种形状（C4）：`~A`、`A = false`、`A --> false` |
| `intros()` | `[var_names]` | 1 | 引入全称变量与蕴含假设（`!x. A ⟶ B` -> `B`） |
| `var_induct()` | `(th_name, var)` | 每个归纳情况 | 结构归纳；目标不得以绑定归纳变量的 forall 开头（C10），此时须先 intro |
| `datatype_cases()` | `Term` 或 `(Term, cases_thm)` | 每个构造子分支 | 归纳数据类型分情况：用 `<tyname>_cases` 定理，谓词实例化为 `%x. goal`（无归纳假设）；默认定理名为 `<type>_cases` |
| `rewrite_goal(sym=)` | `th_name` | 0 或 1 | 用定理重写目标（`top_sweep_conv` + β-norm）；重写后若自反则 0 子目标 |
| `rewrite_goal_with_conv(cv)` | - | 0 或 1 | 用预构造 Conv 重写目标 |
| `rewrite_goal_with_prev()` | - | 0 或 1 | 用已有等式事实（含 forall）重写目标 |
| `apply_prev()` | `inst?` | 每个未匹配假设 | 向后应用已有事实（forall/implies 形式）；无剩余前提时直接返回事实本身 |
| `cases()` | `Term` 或 `(Term, thm_name)` | 2 | 分情况：`A⟶C` 与 `¬A⟶C`（默认 `classical_cases`） |
| `inst_exists_goal()` | `Term` 或 `(Term, thm_name)` | 1 | 用见证实例化存在目标（默认 `exI`） |
| `assumption()` | - | 0 | 目标已在假设中则关闭，否则抛 `TacticException` |
| `reflexive()` | - | 0 | 证明 `t = t` |
| `equal_intr()` | - | 2 | 证明 `A = B`，拆为 `A⟶B` 与 `B⟶A` |
| `trans()` | `Term`（中间项 u） | 1 或 2 | 证明 `s = t` 拆为 `s = u` 与 `u = t`；`ProofTerm.transitive` 跳过自反侧（u = s 或 u = t 时不产生对应子目标） |
| `trivial()` | - | 0 | 探测 trivial 目标（`A_1 ⟶ … ⟶ A_n ⟶ B` 其中 `B` 与某 `A_i` 相同）；失败在宏展开/校验时抛异常 |
| `elim_exists()` | `(names, exists_pt, wired_prev_pts, wired_args)` | - | 已接线的 intros 内容推导（消除存在事实的受检推导）；由 `elim` 方法配合状态重排使用，不直接面向用户 |
| `accept()` | `th_name` | 0 | 直接用定理关闭目标（HOL Light `MATCH_ACCEPT_TAC` 对应）：阶段 1 结论一阶匹配 goal、前提逐一匹配 goal 的假设；阶段 2（C6 回退，无 prevs 时）整条命题匹配 goal，记录单条 `apply_theorem_inst` 宏行 |

### rule 详解

`rule` 是最核心的向后策略（MATCH_MP_TAC 语义）。流程：

1. 取定理 `th`，分解 `(As, C)`。
2. 匹配 `C` 与 `goal.prop`，匹配 `As[:len(prevs)]` 与 prevs（一阶匹配）。
3. 检查所有 schematic 变量已实例化（否则抛 `ParameterQueryException` 询问参数）。
4. 未匹配的 `As` 创建 sorry。
5. 返回 `apply_theorem(th_name, *pts)` 或 `apply_theorem(th_name, *pts, inst=inst)`——即宏 `apply_theorem` / `apply_theorem_for` 的 ProofTerm。

**没有整条命题回退**：蕴含形目标（未 intro）必须先用 `intro` 拆分，或直接用 `accept`（MATCH_ACCEPT_TAC 语义，见下）一步闭合——`rule` 与 `accept` 严格分离，与 HOL Light 的 MATCH_MP_TAC / MATCH_ACCEPT_TAC 分工一致。

**关键**：匹配（推理）在策略层完成，`implies_elim` 链接（机械操作）由宏完成。

### rule / intro / accept 的柯里化语义

因为函数是柯里化的，`A → B → C` 与 `A → (B → C)` 是同一个项。关键是 `rule` 究竟匹配哪一层——答案是**确定性的，不靠尝试**：

- `strip_implies` **贪心地剥到最内层**：`A → B → C` ⟹ `(As=[A,B], C=C)`。`rule` 永远用这个最内层 `C` 去匹配目标（`goal.prop` 本身，不拆目标）。
- 所以："`rule` 匹配 `C` 还是 `B→C`"不是一个可选项——只认 `C`（剥到底的最内层）。
- 若目标的**最内层结论**恰好是蕴含形（如 `imp_trans: (A→B) ⟶ (B→C) ⟶ A→C`，剥掉前提后尾是 `A→C`），则 `C` 能匹配 `A→C` 目标，`rule` 直接可用。
- 若目标整个是 `B → C` 而定理尾是原子 `C`（如 `not_or_elim1` 的 `¬?p`），`rule` 匹配失败——**不能"只证 A 就闭合 `B→C`"**。必须 `intro`（goal 变 `C`、fact=`B`），再 `rule` 用 `C` 匹配 `C`。

一句话：**`rule` 匹配定理的"尾"对目标的"整体"；尾能匹配整体就用 rule，否则 intro 让尾去匹配更小的整体。**

#### 与 Isabelle/HOL 的对比

| | holpy `rule` | Isabelle `rule` |
|---|---|---|
| goal 形态 | 可能是一个未 intro 的蕴含项 `B → C` | 永远是序贯 `B ⟹ C`（假设与结论分开） |
| 匹配对象 | 尾 `C` vs **整个 goal 项** | 尾 `C` vs **goal 结论**（不含假设） |
| 前提处理 | 未匹配前提全部变子目标 | 与假设可消解的前提自动消掉 |
| 未 intro 的蕴含目标 | 匹配不上，强制先 intro | 概念上不存在（goal 已拆分） |

即：Isabelle 里 `rule` 也是尾匹配、不拆右结合蕴含；但它的目标天然是 `As ⟹ C` 序贯，所以"已 intro 的前提"自动消解。holpy 的 `intro` 正是把 `B → C` 变成 Isabelle 式的假设 `B` + 结论 `C`，之后 `rule` 行为与 Isabelle 一致。区别只在 holpy 显式引入"未 intro 的蕴含目标"这一步。

#### accept 的整条命题匹配

`accept`（阶段 2，C6 回退）**不拆**：拿定理**整条命题**（`A → B → C` 全体）一阶匹配目标的整条命题。所以：
- 想一步闭合 `A → B → C` 目标 → `accept <整条命题等于它的定理>`。
- 想拆子目标 → `rule`（尾匹配）+ `intro`。

## 4. 正向推理策略

正向策略：无 goal，`prevs` 全部是输入事实。返回的 ProofTerm 推导出新事实。

| 策略 | args | prevs | 说明 |
|---|---|---|---|
| `apply_theorem_forward()` | `th_name` 或 `(th_name, inst, provided)` | ≤ 定理假设数 | 向前应用定理：匹配假设与 prevs，未匹配变量若不在 `provided` 中则询问参数；返回 `apply_theorem` 宏 ProofTerm |
| `rewrite_fact_forward(sym=)` | `th_name` | ≥ 1 | 用定理重写首个 fact（`has_rewrite` 预检在策略层）；返回 `rewrite_fact` / `rewrite_fact_sym` 宏 ProofTerm |
| `apply_fact_forward()` | `inst?` | ≥ 2 | 把 forall/implies fact 应用到其他 fact（匹配在策略层）；返回 `apply_fact` / `apply_fact_for` 宏 ProofTerm |
| `rewrite_fact_with_prev_forward()` | - | 2 | 用一个等式 fact（含 forall）重写另一个 fact（效果检查在策略层）；返回 `rewrite_fact_with_prev` 宏 ProofTerm |
| `forall_elim_forward()` | `Term` | 1 | 实例化 forall fact（断言 fact 确为 forall）；返回 `forall_elim_gen` 宏 ProofTerm |

**设计原则**：正向策略镜像对应的向后策略——推理（匹配、检测）在策略层，机械链接在宏层。`provided` 列表支持"留作 forall"语义（空值参数不询问，由宏 forall_intr）。

## 5. 领域宏的受检入口（MacroTactic 已移除）

```python
# ProofState.apply_macro(id, macro_name, args=None, prevs=None)
assert theory.has_macro(macro_name)   # 注册表检查
macro = theory.get_macro(macro_name)
assert theory.thy.has_theorem(macro.limit)  # limit 闸门
macro_args = (goal_prop,) + tuple(args)     # 宏的第一个参数是目标命题
pt = ProofTerm(macro_name, macro_args, prevs)
```

> 旧版的 `MacroTactic`（把宏包成向后策略的通用适配器）已移除，宏不得绕过注册表检查直接执行。

领域计算类方法（`norm` 及 `nat_norm`/`real_norm`/`eval_Sem` 等领域宏方法）无推理可做，直接走 `ProofState.apply_macro` 受检入口：宏名先经注册表与 limit 检查，展开结果经 `check_proof` 验证。

## 6. 分层关系

```
Method (作者交互)
  ↓ 调用 tactic.get_proof_term(args, prevs)
Tactic (推理决策：匹配、参数检测、效果检查)
  ↓ 返回 ProofTerm(rule=宏/原语, ...)
Macro + Primitive (机械求值/展开)
```

- **策略层做推理**：一阶匹配、schematic 变量检测、`has_rewrite` 效果预检。
- **宏层做机械操作**：`implies_elim` 链、`forall_elim`/`forall_intr`、conv 重写。
- 策略返回的 ProofTerm 的 `rule` 始终是宏名或原语名，不引用其他策略——**无同层调用**。
- `cases` 和 `inst_exists_goal` 内部调用 `apply_theorem`（`core.logic` 函数，非策略），产生宏 ProofTerm——这是函数调用，不是策略间调用。
- `_backward_rule` 是模块级辅助函数（非 Tactic），被 `rule` 和 `inst_exists_goal` 共享以避免代码重复。

## 7. 策略与转换的关系

`rewrite_goal_with_conv(cv)` 是桥梁：把 `Conv` 包成"对目标应用转换"的策略。它构造 `cv.get_proof_term(goal.prop)` 得 `goal = new_goal` 的等式，用 `equal_elim`（原语）传递。

---

**下一章**：[`06_method.md`](06_method.md) -- 方法层与证明状态。
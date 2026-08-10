# 策略系统

> 代码事实以 `logic/tactic.py` 为准。

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
| `rule()` | `th_name` 或 `(th_name, inst)` | 每个未匹配假设 | 向后应用定理：匹配结论与 goal，匹配已有假设与 prevs，未匹配假设变 sorry |
| `resolve()` | `th_name` | 0 | 消解：`~A` 定理 + 事实 `A` 证任意目标 |
| `intros()` | `[var_names]` | 1 | 引入全称变量与蕴含假设（`!x. A ⟶ B` -> `B`） |
| `var_induct()` | `(th_name, var)` | 每个归纳情况 | 结构归纳 |
| `rewrite_goal(sym=)` | `th_name` | 0 或 1 | 用定理重写目标（`top_sweep_conv` + β-norm）；重写后若自反则 0 子目标 |
| `rewrite_goal_with_conv(cv)` | - | 0 或 1 | 用预构造 Conv 重写目标 |
| `rewrite_goal_with_prev()` | - | 0 或 1 | 用已有等式事实（含 forall）重写目标 |
| `apply_prev()` | `inst?` | 每个未匹配假设 | 向后应用已有事实（forall/implies 形式） |
| `cases()` | `Term` 或 `(Term, thm_name)` | 2 | 分情况：`A⟶C` 与 `¬A⟶C`（默认 `classical_cases`） |
| `inst_exists_goal()` | `Term` 或 `(Term, thm_name)` | 1 | 用见证实例化存在目标（默认 `exI`） |
| `assumption()` | - | 0 | 目标已在假设中则关闭 |
| `reflexive()` | - | 0 | 证明 `t = t` |
| `equal_intr()` | - | 2 | 证明 `A = B`，拆为 `A⟶B` 与 `B⟶A` |
| `trivial()` | - | 0 | 探测 trivial 目标（`A_1 ⟶ … ⟶ A_n ⟶ B` 其中 `B` 与某 `A_i` 相同）；构造失败则抛异常 |
| `accept()` | `th_name` | 0 | 直接用定理关闭目标：结论一阶匹配 goal，前提逐一匹配 goal 的假设；不产 sorry（HOL Light `MATCH_ACCEPT_TAC` 对应） |

### rule 详解

`rule` 是最核心的向后策略。流程：

1. 取定理 `th`，分解 `(As, C)`。
2. 匹配 `C` 与 `goal.prop`，匹配 `As[:len(prevs)]` 与 prevs（一阶匹配）。
3. 检查所有 schematic 变量已实例化（否则抛 `ParameterQueryException` 询问参数）。
4. 未匹配的 `As` 创建 sorry。
5. 返回 `apply_theorem(th_name, *pts)` 或 `apply_theorem(th_name, *pts, inst=inst)`——即宏 `apply_theorem` / `apply_theorem_for` 的 ProofTerm。

**关键**：匹配（推理）在策略层完成，`implies_elim` 链接（机械操作）由宏完成。

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

## 5. MacroTactic 桥接

```python
class MacroTactic(Tactic):
    def __init__(self, macro: str): ...
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th; prevs = prevs[1:]
        args = (goal.prop,) if args is None else (goal.prop,) + args
        return ProofTerm(self.macro, args, prevs)
```

把宏包成向后策略：宏的第一个参数须是目标命题。用于自动化方法（`norm`、`eval`、`linarith`），这些方法无推理可做，直接委托宏。

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
- `cases` 和 `inst_exists_goal` 内部调用 `apply_theorem`（`logic.logic` 函数，非策略），产生宏 ProofTerm——这是函数调用，不是策略间调用。
- `_backward_rule` 是模块级辅助函数（非 Tactic），被 `rule` 和 `inst_exists_goal` 共享以避免代码重复。

## 7. 策略与转换的关系

`rewrite_goal_with_conv(cv)` 是桥梁：把 `Conv` 包成"对目标应用转换"的策略。它构造 `cv.get_proof_term(goal.prop)` 得 `goal = new_goal` 的等式，用 `equal_elim`（原语）传递。

---

**下一章**：[`06_method.md`](06_method.md) -- 方法层与证明状态。
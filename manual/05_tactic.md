# 策略系统

> 代码事实以 `logic/tactic.py` 为准。

策略（Tactic）是"目标分解"的抽象：输入一个目标定理，返回证明该目标的证明项（可能含 gap）。

## 1. 定义

```python
class Tactic:
    def get_proof_term(self, goal: Thm, *, args=None, prevs=None) -> ProofTerm:
        raise NotImplementedError
```

- `goal`：要证明的目标（`Thm`，含 `prop` 与 `hyps`）。
- `args`：策略参数（如定理名、实例化、变量等）。
- `prevs`：已有的输入事实（`List[ProofTerm]`）。
- 返回：`ProofTerm`，其 `th.prop == goal.prop`，`th.hyps ⊆ goal.hyps`（子集语义）。返回的 ProofTerm 可含 `gaps`（`sorry`），表示尚待证明的子目标。

**策略视角**：策略把目标化为若干子目标（gap）。`pt.gaps` 就是子目标列表。

## 2. gap 与 sorry

`ProofTerm.sorry(th)` 创建一个 gap：`th` 是待证目标，`gaps = [th]`。

策略返回的 ProofTerm 中，`sorry` 部分就是"剩下的子目标"。例如 `cases` 策略把目标 `C`（在 hyps `Γ` 下）拆为两个子目标 `A ⟶ C` 和 `¬A ⟶ C`，返回的 ProofTerm 含两个 gap。

## 3. ProofTerm 上的策略应用

| 方法 | 作用 |
|---|---|
| `pt.tac(tactic)` | 对 `pt` 的**首个 gap** 应用策略，返回新 ProofTerm |
| `pt.tacs(*tactics)` | 依次对首个 gap 应用多个策略 |

```python
pt = ProofTerm.sorry(goal)
pt = pt.tac(tac1)   # 对首个 gap 应用 tac1
pt = pt.tac(tac2)   # 对新的首个 gap 应用 tac2
# 等价于
pt = ProofTerm.sorry(goal).tacs(tac1, tac2)
```

## 4. tactical（策略组合子）

| 组合子 | 说明 |
|---|---|
| `then_tac(t1, t2)` | 先 t1 再 t2 |
| `else_tac(t1, t2)` | t1 失败（`TacticException`）则 t2 |
| `repeat_tac(t)` | 重复 t 直到失败 |

预定义：`intros_tac = repeat_tac(else_tac(intro_imp_tac(), intro_forall_tac()))`（反复引入蕴含与全称）。

## 5. 内置策略目录

### 5.1 向后推理（goal -> 子目标）

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `rule()` | `(th_name, inst?)` | 每个未匹配假设一个 | 向后应用定理：匹配结论，替换为假设 |
| `rule_tac(th_name, inst=)` | `th_name, inst` | 按定理 | 带实例化的 `rule` |
| `resolve()` | `th_name` | 0 | 消解：`~A` 定理 + 事实 `A` 证任意目标 |
| `var_induct()` | `(th_name, var)` | 每个归纳情况一个 | 结构归纳 |

### 5.2 引入

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `intros()` | `[names]` | 1 | 引入变量与假设（处理 `!x. A ⟶ B`） |
| `intro_imp_tac()` | - | 1 | 引入蕴含（逆向 `implies_intr`） |
| `intro_forall_tac(var_name=)` | `var_name?` | 1 | 引入全称（逆向 `forall_intr`） |

### 5.3 重写

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `rewrite_goal(sym=)` | `th_name` | 0 或 1 | 用定理重写目标 |
| `rewrite_goal_with_conv(cv)` | `cv` | 0 或 1 | 用预构造的 Conv 重写目标 |
| `rewrite_goal_with_prev()` | - | 0 或 1 | 用已有等式事实重写目标 |

`rewrite_goal` 内部用 `top_sweep_conv(rewr_conv(th_name))` + `beta_norm_conv()`，若重写后目标变为自反等式则 0 子目标（直接关闭）。

### 5.4 事实应用

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `apply_prev()` | `inst?` | 每个未匹配假设一个 | 向后应用已有事实 |

### 5.5 分情况与存在

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `cases()` | `Term` 或 `(Term, thm_name)` | 2 | 分情况：`A⟶C` 与 `¬A⟶C`（默认用 `classical_cases`） |
| `inst_exists_goal()` | `Term` 或 `(Term, thm_name)` | 1 | 用见证实例化存在目标（默认用 `exI`） |

### 5.6 闭合

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `assumption()` | - | 0 | 目标已在假设中则关闭 |
| `reflexive()` | - | 0 | 证明 `t = t` |
| `equal_intr()` | - | 2 | 证明 `A = B`，拆为 `A⟶B` 与 `B⟶A` |

### 5.7 消除

| 策略 | 参数 | 子目标 | 说明 |
|---|---|---|---|
| `elim_tac(th_name, cond=, inst=)` | `th_name` | 按定理 | 消除式应用（如 `disjE`、`conjE`）：匹配结论+首假设 |
| `conj_elim_tac()` | - | 多个 | 合取假设消除 |

### 5.8 桥接

| 策略 | 说明 |
|---|---|
| `MacroTactic(name)` | 把宏包成策略（第一个参数须是目标命题） |

## 6. rule 策略详解

`rule` 是最常用的向后推理策略。流程：

1. 取定理 `th = theory.get_theorem(th_name)`，分解 `(As, C)`。
2. 匹配 `C` 与 `goal.prop`，匹配 `As[:len(prevs)]` 与 `prevs`。
3. 检查所有 schematic 变量已实例化（否则抛 `ParameterQueryException` 询问参数）。
4. `pt = ProofTerm.theorem(th_name).substitution(inst).on_prop(beta_norm_conv())`。
5. 对每个未匹配的 `A` 创建 `sorry`，`implies_elim` 消除。

## 7. var_induct 策略详解

`var_induct` 应用归纳原理。流程：

1. 取归纳定理 `th`，其结论形如 `f x`（`f` 是归纳谓词，`x` 是归纳变量）。
2. 构造 `P = Lambda(var, goal.prop)`。
3. 匹配 `th.concl` 的 `x` 与 `var`，把 `f` 赋为 `P`。
4. `apply_theorem(th_name, *sorrys, inst=inst)`。

## 8. 证明示例：n + 0 = n

用策略证明 `n + 0 = n`（吸收 tutorial peano/tactics2 的示例）：

```python
goal = Thm(Eq(Var("n", NatType) + 0, Var("n", NatType)))

pt = ProofTerm.sorry(goal).tacs(
    # 0: 对 n 归纳（用 nat_induct）
    tactic.var_induct(th_name='nat_induct', var=Var("n", NatType)),
    # 基础情况：重写 0 + 0 = 0
    tactic.rewrite_goal(sym=False).get_proof_term(..., args='nat_plus_def_1'),
    # 归纳情况：引入变量与归纳假设
    tactic.intros(),
    # 重写 Suc n + 0 = Suc (n + 0)
    tactic.rewrite_goal(sym=False).get_proof_term(..., args='nat_plus_def_2'),
    # 用归纳假设 n + 0 = n 重写
    tactic.rewrite_goal_with_prev(),
)
```

对应的 `.pyhol` 写法：
```
0: induction n nat_induct
0: rewrite_goal nat_plus_def_1 sym=false
1: introduction m
1.2: rewrite_goal nat_plus_def_2 sym=false
1.2: rewrite_goal_with_prev @1.1
```

## 9. 策略与宏的关系

- **策略**面向"目标分解"：`goal -> ProofTerm(含 gap)`。
- **宏**面向"证明步骤缩写"：`args + prevs -> ProofTerm`。
- `MacroTactic` 把宏包成策略：`MacroTactic('nat_norm').get_proof_term(goal)` 等价于 `ProofTerm('nat_norm', (goal,), [])`。
- 策略内部常调用宏（如 `rule` 调 `apply_theorem`，`rewrite_goal` 调 `rewrite_goal` 宏）。

## 10. 策略与转换的关系

`rewrite_goal_with_conv(cv)` 是桥梁：把一个 `Conv` 包成"对目标应用转换"的策略。它构造 `cv.get_proof_term(goal.prop)` 得 `goal = new_goal` 的等式，用 `equal_elim` 传递。

---

**下一章**：[`06_method.md`](06_method.md) -- 方法层与证明状态。

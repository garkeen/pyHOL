# 第二层：策略（Tactic）与转换（Conversion）

> 依据作者 `tutorial/tactics.ipynb`、`tactics2.ipynb`、`conversions.ipynb`、`conversions2.ipynb` 校正。代码事实以 `logic/tactic.py`、`logic/conv/core.py` 等为准。

> **与 HOL Light 的对应关系及边界**：本手册的「转换(Conv)」与「策略(Tactic)」两层是 holpy 对 HOL Light（`equal.ml` / `tactics.ml`）的**对应实现**——类型签名、组合子命名、遍历语义逐项对应。但 holpy 的 **宏(Macro)、信任级别(level)、序列化证明项 + check_proof、方法层(Method)** 在 HOL Light 中**不存在**（见 manual 01 顶部边界说明）。不要把 holpy 的每一层都默认能在 HOL Light 找到对应物。

## 1. 架构与两种自动化基元

```
Conv（转换）:  term -> Thm( |- t = t' )     做「等价变换」
  │  组合子: then_conv / else_conv / try_conv / * _conv / top_conv / bottom_conv ...
  ▼ 使用
Tactic（策略）:  goal(Thm) -> ProofTerm(可能含 gap)   做「目标分解」
  │  组合子(tactical): then_tac / else_tac / repeat_tac
  ▼ 使用
ProofTerm（证明项）   两层通过 ProofTerm 连接（见 manual 01）
```

**转换（conversion）**：输入一个项 `t`，返回一个定理 `|- t = t'`。它与宏**同构**（都是「输入 → ProofTerm」的封装，只是 conv 的参数是单个项、无输入证明项）。因其有良好的组合性质，被单独抽象为 `Conv` 类（实现 `get_proof_term(theory, t)`）。

**策略（tactic）**：输入一个目标定理 `Thm`，返回证明该目标的 `ProofTerm`；返回的 ProofTerm 可能含 **gap**（由 `sorry` 构造），表示尚待证明的子目标。因此策略也可看作「把目标化为若干子目标」。策略同样用 `Tactic` 类（实现 `get_proof_term(goal)`）表示，可用 *tactical* 组合。

> 简记：转换改变「项」，策略改变「目标的结构」。两者最终都产出 `ProofTerm`。

## 2. 基础转换（`logic/conv/core.py`）

| 类/函数 | 类别 | 功能 |
|------|------|------|
| `all_conv` | Conv | 恒等：`refl(t)` |
| `no_conv` | Conv | 总是失败：`raise ConvException` |
| `beta_conv` | Conv | 单步 β 归约 `|- (%x. t1) t2 = t1[t2/x]` |
| `beta_norm_conv` | Conv | 完全 β 归一化 |
| `eta_conv` | Conv | Eta：`|- (%x. f x) = f` |
| `combination_conv` | Conv | 对 `f a` 的 f、a 分别转换 |
| `then_conv(cv1, cv2)` | 组合子(函数) | 先 cv1 再 cv2 |
| `else_conv(cv1, cv2)` | 组合子(函数) | cv1 失败则 cv2 |
| `try_conv(cv)` | 组合子(函数) | cv 或恒等 |
| `comb_conv(cv)` | 组合子(函数) | 对函数与参数都套 cv |
| `arg_conv(cv)` | 组合子(函数) | 只转换参数（右） |
| `fun_conv(cv)` | 组合子(函数) | 只转换函数（左） |
| `arg1_conv(cv)` | 组合子(函数) | 转换第一个参数 |
| `binop_conv(cv)` | 组合子(函数) | 转换两个参数 |
| `argn_conv(cv, n)` | Conv | 转换第 n 个参数 |
| `every_conv(*cvs)` | 组合子(函数) | 依次应用 |
| `repeat_conv(cv)` | Conv | 重复直到失败 |
| `abs_conv(cv)` | Conv | 进入 λ 体：`|- (%x. body) = (%x. body')` |
| `assums_conv(cv)` | Conv | 对假设逐个应用 cv（作者库新增） |
| `sub_conv(cv)` | Conv | 对直接子项（comb 或 abs）应用 |
| `bottom_conv(cv)` | Conv | 自底向上，重复 |
| `top_conv(cv)` | Conv | 自顶向下，重复（应用于 t 后再递归子项） |
| `top_sweep_conv(cv)` | Conv | 自顶向下，成功即停（ONCE 语义） |
| `rewr_conv(th)` | Conv | 用 `|- lhs = rhs` 重写匹配子项；支持 `sym=`、`conds=` |
| `replace_conv(pt)` | Conv | 直接用已有 proof term 替换 |
| `has_rewrite(th, t, *, sym, conds)` | 函数 | 判断 th 能否在 t 上重写（辅助） |
| `beta_norm(t)` | 函数 | 直接返回 β 归一化后的项（非 Conv） |

`rewr_conv` 是最核心的转换，工作方式（作者描述）：匹配 lhs（或 `sym=True` 时 rhs）→ 实例化等式 → 若非一阶模式则 β 归一化 → 若 lhs 不精确匹配则尝试 eta。

## 3. 遍历策略（top/bottom）语义

| 转换 | 行为 | 对应 HOL Light |
|------|------|----------------|
| `top_conv(cv)` | 先作用于 t，再递归子项（top-down，重复） | `TOP_DEPTH_CONV` |
| `top_sweep_conv(cv)` | 自顶向下，命中即停 | `ONCE_DEPTH_CONV` |
| `bottom_conv(cv)` | 先递归子项，再作用于 t（bottom-up） | `DEPTH_CONV` |

> `top_conv` 的「先 t 后子项」顺序很关键：作用后产生的新项若还能被 cv 作用，会在一遍内继续。作者用分配律 `a·((b+c)+d)` 演示了这种「一遍到位」的特性。

## 4. 自然数 / 整数 / 实数转换

这些多为领域归一化转换，分布在 `logic/conv/nat.py`、`integer.py`、`real.py`、`proplogic.py`、`function.py`。常用者有：

- **自然数**：`Suc_conv`、`add_conv`、`mult_conv`、`nat_conv`、`nat_eval_conv`、`swap_add_r`、`norm_add_monomial`、`combine_monomial`、`norm_full`、`nat_eq_conv` 等（多项式/算术归一化）。
- **整数**：与 nat 类似，另有 `omega_form_conv`（转 `0 <= expr`）、`int_simplex_form`（Simplex 标准形）等。
- **实数**：`real_nat_power_conv`、`real_power_conv`、`norm_real_ineq_conv`、`real_simplex_form` 等。
- **命题逻辑**：`nnf_conv`、`norm_conj_atom`、`norm_disj_atom`、`norm_full`、`sort_conj`/`sort_disj`（检测矛盾、去重排序）。
- **函数更新**：`fun_upd_eval_conv`、`fun_upd_norm_conv`。

## 5. 转换组合模式

```python
# 重写链
then_conv(rewr_conv('th1'), rewr_conv('th2'))

# 全局重写
top_conv(rewr_conv('th'))

# 条件重写
rewr_conv('th', conds=[proof_of_condition])

# 深度遍历 + 重写
bottom_conv(then_conv(rewr_conv('th1'), rewr_conv('th2')))

# 位置特定重写：对 f(g(x)) 中的 g(x) 重写
fun_conv(arg_conv(rewr_conv('th')))
```

## 6. 基础策略（`logic/tactic.py`）

> 注意：下表全部是 `logic/tactic.py` 中真实存在的策略类（继承自 `Tactic`）。`apply_backward_step` 等「方法」只是它们的用户层封装，见 manual 03。

| 策略类 | 功能 | 子目标 |
|--------|------|--------|
| `rule(th_name)` | 向后应用定理：匹配结论，替换为假设 | 每个未匹配假设一个 |
| `rule_tac(th_name, inst)` | 带实例化的 `rule` | 同上 |
| `resolve(th_name)` | 消解 | 0 |
| `intros()` | 引入变量与假设（处理 `!x. A --> B`） | 1 |
| `var_induct(th_name, var)` | 结构归纳 | 每个归纳情况一个 |
| `rewrite_goal(th_name, sym=)` | 用定理重写目标 | 0 或 1 |
| `rewrite_goal_with_conv(cv)` | 用转换重写目标 | 0 或 1 |
| `rewrite_goal_with_prev()` | 用事实重写目标 | 0 或 1 |
| `apply_prev()` | 向后应用已有事实 | 每个未匹配假设一个 |
| `cases(A)` | 分情况：`A-->C` 与 `~A-->C` | 2 |
| `inst_exists_goal(t)` | 用见证实例化存在量词目标 | 1：`P(t)` |
| `intro_imp_tac()` | 引入蕴含（逆向 `implies_intr`） | 1 |
| `intro_forall_tac()` | 引入全称（逆向 `forall_intr`） | 1 |
| `assumption()` | 目标已在假设中则关闭 | 0 |
| `reflexive()` | 证明 `t = t` | 0 |
| `equal_intr()` | 证明 `A = B`，拆为 `A-->B` 与 `B-->A` | 2 |
| `elim_tac(th_name, term=)` | 消除式应用（如 `disjE`、`conjE`）：匹配结论+首假设 | 按定理 |
| `conj_elim_tac()` | 合取假设消除（如 `conjE`） | 多个 |
| `MacroTactic(name)` | 把宏包装成策略 | 取决于宏 |

> `MacroTactic`（把宏包成策略）是 holpy 的一个**小自创装置**——HOL Light 没有，它只是「为了能在策略组合里用宏」而加的桥接。

## 7. 策略组合子（tactical）

| 组合子 | 功能 |
|--------|------|
| `then_tac(t1, t2)` | 先 t1 再 t2 |
| `else_tac(t1, t2)` | t1 失败则 t2 |
| `repeat_tac(t)` | 重复直到 `TacticException` |

预定义组合：`intros_tac = repeat_tac(else_tac(intro_imp_tac(), intro_forall_tac()))`（反复引入蕴含与全称）。`pt.tac(t)` 对证明项首个 gap 应用 `t`；`pt.tacs(*ts)` 等价于用 `then_tac` 串起这些策略。

## 8. 与 HOL Light 对比（参考）

| 概念 | HOL Light | holpy |
|------|-----------|-------|
| 转换类型 | `term -> thm` | `Conv` 类（`get_proof_term`） |
| 组合子 | `THENC`/`ORELSEC`/`REPEATC` | `then_conv`/`else_conv`/`repeat_conv` |
| 遍历 | `DEPTH_CONV`/`TOP_DEPTH_CONV`/`ONCE_DEPTH_CONV` | `bottom_conv`/`top_conv`/`top_sweep_conv` |
| 重写 | `REWR_CONV`/`REWRITE_CONV` | `rewr_conv`（统一） |
| 策略 | `TAC`（目标→子目标） | `Tactic` 类（目标→ProofTerm，可含 gap） |
| 简化器 | 完整 simpset + term net + 同余规则 | `simp` 方法（基础，见 manual 03） |

> **来源边界（与 manual 01 呼应）**：上表只覆盖「转换」与「策略」两层——这两层是 holpy 对 HOL Light（`equal.ml` / `tactics.ml`）的**对应实现**。但 holpy 的 **宏(Macro)、信任级别(level)、序列化证明项 + check_proof、方法层(Method)** 这四样在 HOL Light 中**不存在**。HOL Light 最接近 `check_proof` 的是 `tactics.ml:113` 的 `VALID`——它校验的是 tactic 的产出 sound 性，作用在运行时 tactic 而非序列化证明对象。另外，HOL Light 的 `REWRITE_TAC`/`MATCH_MP_TAC`/`GEN_TAC`/`DISCH_TAC` 等**具体策略不在 `tactics.ml`**（在 `simp.ml`/`drule.ml`/`bool.ml`），`tactics.ml` 只放基础设施——这与 holpy 把具体策略放在 `logic/tactic.py` 略有不同。

**holpy 与 HOL Light 的能力差异（缺失方向）**：无 term net 索引（O(1) 规则查找）、无 congruence rules（上下文敏感重写）、无完整 SIMP_TAC 级简化器。

## 9. 与 manual 01 的衔接

- 策略与转换在底层都通过 `ProofTerm` 落地，最终都能展开为 manual 01 的 15 条原始推理规则 + 已证定理。
- `rewrite_goal_with_conv(cv)` 这类策略就是把一个 `Conv` 包成「对目标应用转换」的策略。
- 用户一般不手写策略/转换，而是通过 manual 03 的「方法」间接调用它们。

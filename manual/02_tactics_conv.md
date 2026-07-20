# 第二层：策略与转换

## 架构

```
Conv（转换）: Term → Thm( |- t = t' )
  ↓ 组合
组合子: then_conv, top_conv, rewr_conv ...
  ↓ 使用
Tactic（策略）: Thm → ProofTerm (可能有 gap)
  ↓ 组合
组合子: then_tac, else_tac, repeat_tac
```

转换做**等价变换**，策略做**目标分解**。两者通过 ProofTerm 连接。

---

## 全部转换

### 基础转换 (`logic/conv/core.py`)

| 类名 | 功能 | 等价 |
|------|------|------|
| `all_conv` | 恒等 | `refl(t)` |
| `no_conv` | 总是失败 | `raise ConvException` |
| `beta_conv` | 单步 beta | `|- (%x. t1) t2 = t1[t2/x]` |
| `beta_norm_conv` | 完全 beta 归一化 | 递归 beta 化简 |
| `eta_conv` | Eta 转换 | `\|- (%x. f x) = f` |

### 组合子 (`logic/conv/core.py`)

| 组合子 | 功能 | 等价 |
|--------|------|------|
| `then_conv(cv1, cv2)` | 先 cv1 再 cv2 | `|- t = t2 = t3` |
| `else_conv(cv1, cv2)` | cv1 失败则 cv2 | try cv1 except cv2 |
| `combination_conv(cv1, cv2)` | 对 f a 分别转换 | `|- f a = f' a'` |
| `try_conv(cv)` | cv 或恒等 | `else_conv(cv, all_conv())` |
| `comb_conv(cv)` | 对函数和参数都应用 cv | `combination_conv(cv, cv)` |
| `arg_conv(cv)` | 只转换参数 | `combination_conv(all_conv(), cv)` |
| `fun_conv(cv)` | 只转换函数 | `combination_conv(cv, all_conv())` |
| `arg1_conv(cv)` | 转换第一个参数 | `fun_conv(arg_conv(cv))` |
| `binop_conv(cv)` | 转换两个参数 | `combination_conv(arg_conv(cv), cv)` |
| `every_conv(*cvs)` | 依次应用 | `then_conv(cv1, then_cv(cv2, ...))` |
| `repeat_conv(cv)` | 重复直到失败 | while changed: cv |
| `abs_conv(cv)` | 进入 lambda body | `|- (%x. body) = (%x. body')` |
| `sub_conv(cv)` | 对 immediate subterms | comb 或 abs |
| `argn_conv(n, cv)` | 第 n 个参数 | fun_conv 嵌套 |

### 遍历策略 (`logic/conv/core.py`)

| 策略 | 行为 | HOL Light 对应 |
|------|------|----------------|
| `top_conv(cv)` | 自顶向下，重复 | `TOP_DEPTH_CONV` |
| `top_sweep_conv(cv)` | 自顶向下，成功就停 | `ONCE_DEPTH_CONV` |
| `bottom_conv(cv)` | 自底向上 | `DEPTH_CONV` |

### 重写转换 (`logic/conv/core.py`)

| 转换 | 功能 |
|------|------|
| `rewr_conv(th)` | 用 `|- lhs = rhs` 重写匹配的子项 |
| `rewr_conv(th, sym=True)` | 反向重写 |
| `rewr_conv(th, conds=[...])` | 条件重写 |
| `replace_conv(pt)` | 直接用已有 proof term 替换 |

`rewr_conv` 是最核心的转换。工作方式：
1. 匹配 lhs（或 rhs）与目标项
2. 实例化等式
3. 如果不是一阶模式，beta 归一化
4. 如果 lhs 不精确匹配，尝试 eta 转换

---

## 自然数转换 (`logic/conv/nat.py`)

| 转换 | 功能 |
|------|------|
| `Suc_conv` | 计算 Suc n |
| `add_conv` | 计算 m + n |
| `mult_conv` | 计算 m * n |
| `rewr_of_nat_conv` | 移除/应用 of_nat |
| `nat_conv` | 完全算术简化 |
| `nat_eval_conv` | 宏驱动的计算 |
| `swap_add_r` | (a+b)+c → (a+c)+b |
| `norm_add_atom_1` | 加法归一化 |
| `norm_add_1` | 合并两个和 |
| `swap_times_r` | (a*b)*c → (a*c)*b |
| `norm_mult_atom` | 乘法归一化 |
| `norm_mult_monomial` | 单项式乘法 |
| `combine_monomial` | 合并同类项 |
| `norm_add_monomial` | 多项式加法 |
| `norm_add_polynomial` | 多项式合并 |
| `norm_mult_poly_monomial` | 多项式×单项式 |
| `norm_mult_polynomial` | 多项式×多项式 |
| `norm_full` | 完全归一化 |
| `nat_eq_conv` | n=m → True/False |

---

## 整数转换 (`logic/conv/integer.py`)

与自然数类似的多项式归一化，加上：
- `omega_norm_add_num` — 数字常数移到最右
- `omega_form_conv` — 转为 `0 <= expr` 形式
- `int_norm_eq` — 线性方程正系数归一化
- `int_gcd_compares` — 提取 GCD
- `int_simplex_form` — Simplex 标准形

---

## 实数转换 (`logic/conv/real.py`)

与整数类似，加上：
- `real_nat_power_conv` — 展开 (a+b)^2, (a+b)^3
- `real_power_conv` — 实数幂处理
- `norm_real_ineq_conv` — 不等式转 `expr <op> 0`
- `norm_neg_real_ineq_conv` — 否定不等式归一化
- `real_norm_comparison` — 正首系数归一化
- `real_simplex_form` — Simplex 标准形

---

## 命题逻辑转换 (`logic/conv/proplogic.py`)

| 转换 | 功能 |
|------|------|
| `nnf_conv` | 否定范式 |
| `swap_conj_r` | 合取交换 |
| `norm_conj_atom` | 合取归一化（消除 true/false，检测矛盾） |
| `norm_conj_conjunction` | 合并合取链 |
| `swap_disj_r` | 析取交换 |
| `norm_disj_atom` | 析取归一化 |
| `norm_disj_disjunction` | 合并析取链 |
| `norm_full` | 完全命题归一化 |
| `sort_conj` | 合取规范化（去重、排序、检测矛盾） |
| `sort_disj` | 析取规范化 |

---

## 函数转换 (`logic/conv/function.py`)

| 转换 | 功能 |
|------|------|
| `fun_upd_eval_conv` | 计算 f(a := b)(c) |
| `fun_upd_norm_one_conv` | 单步排序 |
| `fun_upd_norm_conv` | 完全归一化 |

---

## 转换组合模式

```python
# 重写链
then_conv(rewr_conv('th1'), rewr_conv('th2'))

# 全局重写
top_conv(rewr_conv('th'))

# 条件重写
rewr_conv('th', conds=[proof_of_condition])

# 深度遍历 + 重写
bottom_conv(then_conv(rewr_conv('th1'), rewr_conv('th2')))

# 位置特定重写
fun_conv(arg_conv(rewr_conv('th')))  # 对 f(g(x)) 中的 g(x) 重写
```

---

## HOL Light 对比

| 概念 | HOL Light | holpy |
|------|-----------|-------|
| 转换类型 | `term -> thm` | `Conv` 类（有 `get_proof_term`） |
| 组合子 | `THENC`, `ORELSEC`, `REPEATC` | `then_conv`, `else_conv`, `repeat_conv` |
| 遍历 | `DEPTH_CONV`, `TOP_DEPTH_CONV`, `ONCE_DEPTH_CONV` | `bottom_conv`, `top_conv`, `top_sweep_conv` |
| 重写 | `REWR_CONV`, `PURE_REWRITE_CONV`, `REWRITE_CONV` | `rewr_conv`（统一） |
| 简化器 | 完整 simpset + term net + congruence rules | `simp` 方法（基础） |

**holpy 缺少**：
- Term net 索引（O(1) 规则查找）
- Congruence rules（上下文敏感重写）
- 完整简化器（SIMP_TAC）

---

## 全部策略

### 基础策略 (`logic/tactic.py`)

| 策略 | 功能 | 子目标 |
|------|------|--------|
| `rule(th_name)` | 向后应用定理 | 每个未匹配的假设一个子目标 |
| `assumption` | 从假设证明 | 0 |
| `reflexive` | 证明 t = t | 0 |
| `equal_intr` | 证明 A = B | 2: A-->B 和 B-->A |
| `intros` | 引入变量和假设 | 1 |
| `var_induct` | 结构归纳 | 每个归纳情况一个 |
| `rewrite_goal(th)` | 用定理重写 | 0 或 1 |
| `rewrite_goal_with_conv(cv)` | 用转换重写 | 0 或 1 |
| `rewrite_goal_with_prev` | 用事实重写 | 0 或 1 |
| `apply_prev` | 应用已有事实 | 每个未匹配假设一个 |
| `cases(A)` | 分情况讨论 | 2: A-->C 和 ~A-->C |
| `inst_exists_goal(t)` | 实例化存在量词 | 1: P(t) |
| `resolve(th_name)` | 消解 | 0 |
| `intro_imp_tac` | 引入蕴含 | 1 |
| `intro_forall_tac` | 引入全称 | 1 |
| `MacroTactic(name)` | 宏转策略 | 取决于宏 |

### 组合子 (`logic/tactic.py`)

| 组合子 | 功能 |
|--------|------|
| `then_tac(t1, t2)` | 先 t1 再 t2 |
| `else_tac(t1, t2)` | t1 失败则 t2 |
| `repeat_tac(t)` | 重复直到失败 |

### 预定义组合

```python
intros_tac = repeat_tac(else_tac(intro_imp_tac(), intro_forall_tac()))
```

---

## HOL Light 策略对比

| HOL Light | holpy | 说明 |
|-----------|-------|------|
| `DISCH_TAC` | `intro_imp_tac` | 引入蕴含 |
| `GEN_TAC` | `intro_forall_tac` | 引入全称 |
| `CONJ_TAC` | 无 | 拆分合取（需要 `apply_backward_step conjI`） |
| `DISJ1_TAC` / `DISJ2_TAC` | 无 | 选择析取分支 |
| `DISJ_CASES_TAC` | `cases` | 分情况 |
| `EXISTS_TAC t` | `inst_exists_goal(t)` | 存在量词实例化 |
| `CHOOSE_TAC` | 无 | 存在量词消除 |
| `EQ_TAC` | `equal_intr` | 等价拆分 |
| `REFL_TAC` | `reflexive` | 自反性 |
| `ACCEPT_TAC` | 无 | 直接接受 |
| `CONV_TAC cv` | 无（内建在方法中） | 应用转换 |
| `MATCH_MP_TAC` | 无 | 匹配 MP |
| `STRIP_TAC` | `intros_tac` | 逐层拆解 |
| `REWRITE_TAC` | `rewrite_goal` 方法 | 重写 |
| `ASM_REWRITE_TAC` | 无 | 带假设重写 |
| `SIMP_TAC` | `simp` 方法 | 简化 |

**holpy 缺少的关键策略**：
- `CONJ_TAC`（合取消除）
- `DISJ1_TAC` / `DISJ2_TAC`（析取引入）
- `CHOOSE_TAC`（存在消除）
- `MATCH_MP_TAC`（匹配 MP）
- `ASM_REWRITE_TAC`（带假设重写）

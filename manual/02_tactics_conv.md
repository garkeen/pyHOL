# 第二层：策略与转换

## 概述

策略（Tactic）将目标分解为子目标。转换（Conversion）对项做等价变换。两者通过组合子构建复杂自动化。

## 全部策略（23 个，`logic/tactic.py`）

### 原子策略

| # | 类名 | 说明 |
|---|------|------|
| 1 | `MacroTactic` | 从宏构造策略 |
| 2 | `rule` | 向后应用定理（最核心） |
| 3 | `resolve` | 消解：用 ~A 和事实 A 解目标 |
| 4 | `intros` | 引入变量和假设 |
| 5 | `var_induct` | 对变量应用归纳 |
| 6 | `rewrite_goal` | 用定理重写目标 |
| 7 | `rewrite_goal_with_conv` | 用预建 Conv 重写目标 |
| 8 | `rewrite_goal_with_prev` | 用已有事实重写目标 |
| 9 | `apply_prev` | 向后应用已有事实 |
| 10 | `cases` | 分情况讨论 |
| 11 | `inst_exists_goal` | 实例化存在量词目标 |
| 12 | `intro_imp_tac` | 引入蕴含假设 |
| 13 | `intro_forall_tac` | 引入全称变量 |
| 14 | `assumption` | 从假设证明 |
| 15 | `reflexive` | 自反性证明 t = t |
| 16 | `equal_intr` | 等价拆分 A=B → A-->B, B-->A |
| 17 | `rule_tac` | 匹配定理创建子目标 |
| 18 | `elim_tac` | 消除策略 |
| 19 | `conj_elim_tac` | 合取消除 |

### 组合子

| # | 类名 | 说明 |
|---|------|------|
| 20 | `then_tac(t1, t2)` | 先 t1 再 t2（对所有子目标） |
| 21 | `else_tac(t1, t2)` | 尝试 t1，失败则 t2 |
| 22 | `repeat_tac(t)` | 重复直到失败 |

### 预定义组合

| 名称 | 定义 | 说明 |
|------|------|------|
| `intros_tac` | `repeat_tac(else_tac(intro_imp_tac(), intro_forall_tac()))` | 自动引入 |

### 领域策略

| # | 类名 | 文件 | 说明 |
|---|------|------|------|
| 23 | `vcg_tactic` | `imperative/imp.py` | 验证条件生成 |

---

## 全部转换（~110 个）

### 核心转换 (`logic/conv/core.py`)

**类（20 个）：**

| # | 类名 | 说明 |
|---|------|------|
| 1 | `all_conv` | 恒等 t = t |
| 2 | `no_conv` | 总是失败 |
| 3 | `combination_conv(cv1, cv2)` | 对 f x 分别转换 |
| 4 | `then_conv(cv1, cv2)` | 顺序组合 |
| 5 | `else_conv(cv1, cv2)` | 备选 |
| 6 | `beta_conv` | 单步 beta |
| 7 | `beta_norm_conv` | 完全 beta 归一化 |
| 8 | `eta_conv` | Eta 转换 |
| 9 | `abs_conv(cv)` | 进入 lambda body |
| 10 | `repeat_conv(cv)` | 重复 |
| 11 | `argn_conv(n, cv)` | 第 n 个参数 |
| 12 | `assums_conv(cv)` | 对所有假设 |
| 13 | `sub_conv(cv)` | 对 immediate subterms |
| 14 | `bottom_conv(cv)` | 自底向上 |
| 15 | `top_conv(cv)` | 自顶向下 |
| 16 | `top_sweep_conv(cv)` | 自顶向下扫描 |
| 17 | `rewr_conv(th)` | 用等式定理重写（最核心） |
| 18 | `replace_conv(pt)` | 直接替换 |

**函数（7 个）：**

| # | 函数 | 等价于 |
|---|------|--------|
| 1 | `try_conv(cv)` | `else_conv(cv, all_conv())` |
| 2 | `comb_conv(cv)` | `combination_conv(cv, cv)` |
| 3 | `arg_conv(cv)` | `combination_conv(all_conv(), cv)` |
| 4 | `fun_conv(cv)` | `combination_conv(cv, all_conv())` |
| 5 | `arg1_conv(cv)` | `fun_conv(arg_conv(cv))` |
| 6 | `binop_conv(cv)` | `combination_conv(arg_conv(cv), cv)` |
| 7 | `every_conv(*cvs)` | 依次 then_conv |

### 自然数转换 (`logic/conv/nat.py`, 21 个)

| # | 类名 | 说明 |
|---|------|------|
| 1 | `Suc_conv` | Suc 计算 |
| 2 | `add_conv` | 加法计算 |
| 3 | `mult_conv` | 乘法计算 |
| 4 | `rewr_of_nat_conv` | of_nat 处理 |
| 5 | `nat_conv` | 算术简化 |
| 6 | `nat_eval_conv` | 宏驱动的算术计算 |
| 7 | `swap_add_r` | (a+b)+c → (a+c)+b |
| 8 | `norm_add_atom_1` | 加法归一化 |
| 9 | `norm_add_1` | 多项式加法 |
| 10 | `swap_times_r` | (a*b)*c → (a*c)*b |
| 11 | `norm_mult_atom` | 乘法归一化 |
| 12 | `norm_mult_monomial` | 单项式乘法 |
| 13 | `to_coeff_form` | 转系数形式 |
| 14 | `from_coeff_form` | 从系数形式 |
| 15 | `combine_monomial` | 合并同类项 |
| 16 | `norm_add_monomial` | 单项式加法 |
| 17 | `norm_add_polynomial` | 多项式加法 |
| 18 | `norm_mult_poly_monomial` | 多项式×单项式 |
| 19 | `norm_mult_polynomial` | 多项式×多项式 |
| 20 | `norm_full` | 完全归一化 |
| 21 | `nat_eq_conv` | 等式简化为 True/False |

### 整数转换 (`data/integer.py`, 26 个)

| # | 类名 | 说明 |
|---|------|------|
| 1 | `swap_mult_r` | 乘法交换 |
| 2 | `int_eval_conv` | 整数计算 |
| 3-11 | `norm_mult_*`, `norm_add_*`, `simp_full` | 多项式归一化 |
| 12 | `int_norm_conv` | 整数归一化 |
| 13 | `norm_eq` | 等式归一化 |
| 14-16 | `omega_*` | Omega 归一化 |
| 17 | `int_norm_eq` | 整数等式归一化 |
| 18 | `int_norm_neg_compares` | 否定比较归一化 |
| 19 | `int_gcd_compares` | GCD 比较 |
| 20 | `int_neq_false_conv` | 不等式转 false |
| 21 | `int_compare_to_real` | 整数比较转实数 |
| 22 | `int_simplex_form` | Simplex 形式 |
| 23 | `int_const_compares` | 常量比较 |

### 实数转换 (`data/real.py`, 27 个)

| # | 类名 | 说明 |
|---|------|------|
| 1 | `real_eval_conv` | 实数计算 |
| 2-14 | `to_coeff_form`, `norm_*`, `real_*_conv` | 多项式归一化 |
| 15 | `real_nat_power_conv` | 自然数幂 |
| 16 | `real_power_conv` | 实数幂 |
| 17 | `real_norm_conv` | 实数归一化 |
| 18 | `norm_real_ineq_conv` | 不等式归一化 |
| 19 | `norm_neg_real_ineq_conv` | 否定不等式归一化 |
| 20 | `real_const_eq_conv` | 常量等式 |
| 21 | `real_norm_comparison` | 比较归一化 |
| 22 | `real_simplex_form` | Simplex 形式 |
| 23 | `replace_conv` | 替换 |
| 24 | `real_const_compares` | 常量比较 |

### 命题逻辑转换 (`data/proplogic.py`, 10 个)

| # | 类名 | 说明 |
|---|------|------|
| 1 | `nnf_conv` | 否定范式 |
| 2 | `swap_conj_r` | 合取交换 |
| 3 | `norm_conj_atom` | 合取归一化 |
| 4 | `norm_conj_conjunction` | 合取链归一化 |
| 5 | `swap_disj_r` | 析取交换 |
| 6 | `norm_disj_atom` | 析取归一化 |
| 7 | `norm_disj_disjunction` | 析取链归一化 |
| 8 | `norm_full` | 完全归一化 |
| 9 | `sort_conj` | 合取排序 |
| 10 | `sort_disj` | 析取排序 |

### 函数转换 (`data/function.py`, 3 个)

| # | 类名 | 说明 |
|---|------|------|
| 1 | `fun_upd_eval_conv` | 函数更新计算 |
| 2 | `fun_upd_norm_one_conv` | 单步归一化 |
| 3 | `fun_upd_norm_conv` | 完全归一化 |

### 其他转换

| 类名 | 文件 | 说明 |
|------|------|------|
| `numseg_conv` | `data/interval.py` | 区间转换 |
| `auto_conv` | `logic/auto.py` | 自动转换 |
| `const_min_conv` | `integral/inequality.py` | 常量最小值 |
| `const_max_conv` | `integral/inequality.py` | 常量最大值 |
| `norm_sin_conv` | `integral/proof.py` | sin 归一化 |
| `norm_cos_conv` | `integral/proof.py` | cos 归一化 |
| `norm_exp_conv` | `integral/proof.py` | exp 归一化 |
| `norm_log_conv` | `integral/proof.py` | log 归一化 |
| `real_integral_cong` | `integral/proof.py` | 积分同余 |
| `simplify_rewr_conv` | `integral/proof.py` | 简化重写 |
| `combine_fraction` | `integral/proof.py` | 分数合并 |
| `fraction_rewr_conv` | `integral/proof.py` | 分数重写 |
| `substitution` | `integral/proof.py` | 替换 |
| `substitution_inverse` | `integral/proof.py` | 反向替换 |
| `integrate_by_parts` | `integral/proof.py` | 分部积分 |
| `trig_rewr_conv` | `integral/proof.py` | 三角重写 |
| `split_region_conv` | `integral/proof.py` | 区域分割 |
| `location_conv` | `integral/proof.py` | 位置转换 |
| `replace_conv` | `sat/zchaff.py` | 替换（zChaff） |
| `replace_conv` | `prover/simplex_strict.py` | 替换（Simplex） |
| `flat_left_assoc_conj_conv` | `prover/proofrec.py` | 合取展平 |
| `flat_left_assoc_disj_conv` | `prover/proofrec.py` | 析取展平 |

---

## 转换组合模式

```python
# 重写链
then_conv(rewr_conv('th1'), rewr_conv('th2'))

# 全局重写
top_conv(rewr_conv('th'))

# 条件重写（只在匹配时应用）
try_conv(rewr_conv('th'))

# 深度遍历 + 重写
bottom_conv(then_conv(rewr_conv('th1'), rewr_conv('th2')))

# 进入 lambda 后重写
abs_conv(rewr_conv('th'))

# 对参数重写
arg_conv(rewr_conv('th'))
```

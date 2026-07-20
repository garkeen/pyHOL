# 第一层：内核原语与宏

## 架构

```
Thm（定理）= hyps + prop
  ↓ 只能通过 15 条原始规则构造
Primitive（原始规则）
  ↓ 组合
Macro（宏）= eval + get_proof_term + expand
```

内核是可信计算基。宏出错不影响 soundness——可展开为原始步骤验证。

---

## 15 条原始规则

### 1. assume

```
签名: assume(A) → A |- A
前置: A 是 Term
异常: 无
```

最基础的规则。创建假设。

### 2. implies_intr

```
签名: implies_intr(A, th) → H\{A} |- A --> B
前置: th = H |- B
异常: 无
```

从假设中移除 A，放入结论。如果 A 不在 hyps 中，仍创建 A --> B（合法但无意义）。

### 3. implies_elim

```
签名: implies_elim(th1, th2) → H1∪H2 |- B
前置: th1 = H1 |- A-->B, th2 = H2 |- A
异常: InvalidDerivationException（th1 不是蕴含，或 A 不匹配）
```

Modus ponens。

### 4. reflexive

```
签名: reflexive(x) → |- x = x
前置: 无
异常: 无
```

### 5. symmetric

```
签名: symmetric(th) → H |- y = x
前置: th = H |- x = y
异常: InvalidDerivationException（不是等式）
```

### 6. transitive

```
签名: transitive(th1, th2) → H1∪H2 |- x = z
前置: th1 = H1 |- x=y, th2 = H2 |- y=z
异常: InvalidDerivationException（不是等式，或中间项不匹配）
```

### 7. combination

```
签名: combination(th1, th2) → H1∪H2 |- f x = g y
前置: th1 = H1 |- f=g, th2 = H2 |- x=y, f 的域类型 = x 的类型
异常: InvalidDerivationException（不是等式，或类型不匹配）
```

同余规则。类型检查确保 `f` 能应用到 `x`。

### 8. equal_intr

```
签名: equal_intr(th1, th2) → H1∪H2 |- A = B
前置: th1 = H1 |- A-->B, th2 = H2 |- B-->A
异常: InvalidDerivationException（不是蕴含，或方向不匹配）
```

从双向蕴含构造等价。

### 9. equal_elim

```
签名: equal_elim(th1, th2) → H1∪H2 |- B
前置: th1 = H1 |- A=B, th2 = H2 |- A
异常: InvalidDerivationException（不是等式，或 A 不匹配）
```

### 10. substitution

```
签名: substitution(inst, th) → H[s] |- B[s]
前置: inst 是 Inst, th 是 Thm
异常: InvalidDerivationException（替换导致类型错误）
```

同时替换项变量和类型变量。

### 11. subst_type

```
签名: subst_type(tyinst, th) → H[s] |- B[s]
前置: tyinst 是 TyInst
异常: 无
```

只替换类型变量。

### 12. beta_conv

```
签名: beta_conv(t) → |- (%x. t1) t2 = t1[t2/x]
前置: t 是 beta-redex
异常: InvalidDerivationException（不是 beta-redex）
```

### 13. abstraction

```
签名: abstraction(x, th) → H |- (%x. t1) = (%x. t2)
前置: th = H |- t1=t2, x 不在 H 中自由出现
异常: InvalidDerivationException（x 在假设中，或不是等式）
```

### 14. forall_intr

```
签名: forall_intr(x, th) → H |- !x. t
前置: th = H |- t, x 不在 H 中自由出现, x 是 Var 或 SVar
异常: InvalidDerivationException（x 在假设中，或 x 不是变量）
```

### 15. forall_elim

```
签名: forall_elim(s, th) → H |- t[s/x]
前置: th = H |- !x. t, s 的类型 = 绑定变量的类型
异常: InvalidDerivationException（不是全称量词，或类型不匹配）
```

---

## 辅助规则（不在 primitive_deriv 中）

### convert_svar

```
签名: convert_svar(th) → |- B'（其中 B' 用 SVar 替换 TVar）
前置: th 无假设
异常: InvalidDerivationException（有假设）
```

用于从对象层切换到模式层。

### mk_VAR

```
签名: mk_VAR(v) → |- _VAR(v)
前置: v 是 Var
异常: InvalidDerivationException
```

元层变量声明。

---

## ProofTerm 操作速查

| 操作 | 等价原语 | 说明 |
|------|----------|------|
| `ProofTerm.assume(A)` | `Thm.assume` | A |- A |
| `ProofTerm.reflexive(x)` | `Thm.reflexive` | \|- x = x |
| `ProofTerm.theorem('conjI')` | 查找定理 | 获取已证明的定理 |
| `ProofTerm.sorry(th)` | 无 | 创建 gap |
| `pt.implies_intr(A)` | `Thm.implies_intr` | 蕴含引入 |
| `pt.implies_elim(pt2)` | `Thm.implies_elim` | MP |
| `pt.symmetric()` | `Thm.symmetric` | 对称 |
| `pt.transitive(pt2)` | `Thm.transitive` | 传递 |
| `pt.equal_intr(pt2)` | `Thm.equal_intr` | 等价引入 |
| `pt.equal_elim(pt2)` | `Thm.equal_elim` | 等价消除 |
| `pt.substitution(inst)` | `Thm.substitution` | 替换 |
| `pt.subst_type(tyinst)` | `Thm.subst_type` | 类型替换 |
| `pt.forall_intr(x)` | `Thm.forall_intr` | 全称引入 |
| `pt.forall_elim(s)` | `Thm.forall_elim` | 全称消除 |
| `pt.abstraction(x)` | `Thm.abstraction` | 抽象 |
| `pt.combination(pt2)` | `Thm.combination` | 同余 |
| `pt.on_prop(*convs)` | 转换应用 | 对命题应用转换链 |
| `pt.on_rhs(*convs)` | 转换应用 | 对右侧应用 |
| `pt.on_lhs(*convs)` | 转换应用 | 对左侧应用 |
| `pt.tac(tactic)` | 策略应用 | 对第一个 gap 应用策略 |
| `pt.tacs(*tactics)` | 策略应用 | 依次对 gap 应用策略 |
| `pt.export()` | 导出 | 转为线性 Proof |

---

## 全部宏（44 个）

### 核心宏 (`logic/macros/core.py`)

| 宏名 | 签名 | 功能 |
|------|------|------|
| `beta_norm` | args=None, prevs=[th] | Beta 归一化定理 |
| `intros` | args=None, prevs=[vars+assums+main] | 引入变量和假设 |
| `apply_theorem` | args=th_name, prevs=[...] | 应用定理（最核心） |
| `apply_theorem_for` | args=(th_name, inst), prevs=[...] | 带显式实例化的应用定理 |
| `apply_induct` | args=(th_name, var, goal), prevs=[...] | 应用归纳原理 |
| `apply_fact` | args=None, prevs=[fact, ...] | 应用 forall/implies 事实 |
| `apply_fact_for` | args=inst, prevs=[fact, ...] | 带实例化的应用事实 |
| `rewrite_goal` | args=(th_name, goal), prevs=[...] | 用定理重写目标 |
| `rewrite_goal_sym` | args=(th_name, goal), prevs=[...] | 反向重写目标 |
| `rewrite_goal_with_prev` | args=goal, prevs=[eq_fact, ...] | 用已有事实重写目标 |
| `rewrite_goal_with_prev_sym` | args=goal, prevs=[eq_fact, ...] | 反向 |
| `rewrite_fact` | args=th_name, prevs=[fact] | 用定理重写事实 |
| `rewrite_fact_sym` | args=th_name, prevs=[fact] | 反向重写事实 |
| `rewrite_fact_with_prev` | args=None, prevs=[eq_fact, fact] | 用事实重写事实 |
| `forall_elim_gen` | args=term, prevs=[th] | 通用全称消除 |
| `trivial` | args=goal, prevs=[] | 平凡证明（C 在假设中） |
| `resolve_theorem` | args=(th_name, goal), prevs=[fact] | 消解 |
| `imp_conj` | args=goal, prevs=[] | 蕴含合取 |
| `imp_disj` | args=goal, prevs=[] | 蕴含析取 |
| `resolution` | args=None, prevs=[clause1, clause2] | 命题消解 |

### 自然数宏 (`logic/macros/nat.py`)

| 宏名 | level | limit | 功能 |
|------|-------|-------|------|
| `nat_eval` | 0 | None | 自然数计算（eval only，无 proof term） |
| `nat_norm` | 10 | nat_nat_power_def_1 | 多项式归一化 |
| `nat_const_ineq` | 10 | bit1_neq_one | 常量不等式 n≠m |
| `nat_const_less_eq` | 10 | bit1_neq_one | 常量 n≤m |
| `nat_const_less` | 10 | bit1_neq_one | 常量 n<m |

### 整数宏 (`logic/conv/integer.py`)

| 宏名 | level | 功能 |
|------|-------|------|
| `int_eval` | 0 | 整数计算（eval only） |
| `int_eq_macro` | 1 | 整数等式归一化 |
| `int_ineq` | — | 不等式转 < 形式 |
| `int_ineq_mul_const` | — | 乘常数不等式 |
| `int_const_ineq` | 0 | 常量不等式 |
| `int_multiple_ineq_equiv` | — | 多倍不等式等价 |
| `omega_norm_int_ineq` | 1 | 转 >= 形式 |
| `int_eq_comparison` | 1 | 比较等价 |

### 实数宏 (`logic/conv/real.py`)

| 宏名 | level | limit | 功能 |
|------|-------|-------|------|
| `real_eval` | 0 | None | 实数计算（eval only） |
| `real_norm` | 0 | real_neg_0 | 多项式归一化（**无 proof term**） |
| `real_const_eq` | 0 | None | 常量等式/不等式 → true/false |
| `real_compare` | 0 | None | 常量比较 |
| `real_const_ineq` | 0 | None | 常量不等式 |
| `real_eq_comparison` | 0 | None | 比较等价 |
| `non_strict_simplex` | 1 | None | 严格→非严格不等式转换 |

### 其他宏

| 宏名 | 文件 | 功能 |
|------|------|------|
| `fun_upd_eval` | `logic/macros/function.py` | 函数更新计算 |
| `prove_avalI` | `logic/macros/expr.py` | 表达式求值证明 |
| `z3` | `logic/macros/z3.py` | Z3 SMT 求解器（**oracle**） |
| `auto` | `logic/auto.py` | 自动证明（solve + norm） |

---

## level 信任级别

| level | 含义 | 行为 |
|-------|------|------|
| 0 | oracle/不可展开 | `eval` 直接信任，`get_proof_term` 可能不存在 |
| 1 | 标准宏 | 有完整 proof term，可展开验证 |
| 10 | 领域计算 | 有 proof term，但依赖 `limit` 定理存在 |

---

## Theory 数据

```python
theory.thy.data['type_sig']    # {name: arity}
theory.thy.data['term_sig']    # {name: Type}
theory.thy.data['theorems']    # {name: Thm}
theory.thy.data['attributes']  # {name: (attr, ...)}
theory.thy.data['overload']    # {name: True}
theory.thy.data['thm_status']  # {name: status}
```

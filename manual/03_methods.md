# 第三层：方法（Method）

## 概述

方法是用户面对的 API，对应前端按钮和 `.pyhol` 证明步骤。每种方法封装一个证明操作，内部调用策略和宏。

## 全部方法（41 个）

### 核心方法 (`server/methods/core.py`, 34 个)

| # | 方法名 | 参数 | 说明 |
|---|--------|------|------|
| 1 | `cut` | goal | 插入中间目标（have） |
| 2 | `cases` | case | 分情况讨论 |
| 3 | `apply_prev` | [fact_ids] | 向后应用已有事实 |
| 4 | `rewrite_goal_with_prev` | [fact_ids] | 用已有等式重写目标 |
| 5 | `rewrite_goal` | theorem, [sym] | 用定理重写目标 |
| 6 | `rewrite_fact` | theorem, [fact_ids] | 用定理重写事实 |
| 7 | `rewrite_fact_with_prev` | [fact_ids] | 用事实重写事实 |
| 8 | `apply_forward_step` | theorem, [fact_ids] | 向前应用定理 |
| 9 | `apply_backward_step` | theorem, [fact_ids], [params] | 向后应用定理（最常用） |
| 10 | `apply_resolve_step` | theorem, [fact_ids] | 消解 |
| 11 | `introduction` | [names] | 引入变量和假设 |
| 12 | `revert_intro` | — | 撤销引入 |
| 13 | `exists_elim` | [names] | 消除存在量词 |
| 14 | `forall_elim` | term | 实例化全称量词 |
| 15 | `inst_exists_goal` | term | 实例化存在量词目标 |
| 16 | `induction` | theorem, var | 结构归纳 |
| 17 | `new_var` | name, type | 声明新变量 |
| 18 | `apply_fact` | [fact_ids] | 应用 forall/implies 事实 |
| 19 | `call_tactic` | tactic_name, [params] | 直接调用策略（逃生口） |
| 20 | `call_macro` | macro_name | 直接调用宏（逃生口） |
| 21 | `simp` | — | 简化（用 hint_rewrite 定理） |
| 22 | `norm` | — | 归一化（自动选 nat/real） |
| 23 | `eval` | — | 计算（自动选 nat/real） |
| 24 | `sym` | — | 翻转等式 a=b → b=a |
| 25 | `reflexive` | — | 证明 t = t |
| 26 | `equal_intr` | — | 证明 A=B（拆为两个子目标） |
| 27 | `subst` | theorem | 用等式替换 |
| 28 | `unfold` | theorem | 展开定义 |
| 29 | `fold` | theorem | 折叠定义 |
| 30 | `thin` | index | 删除假设（weakening） |
| 31 | `insert` | theorem | 插入定理 |
| 32 | `drule` | theorem, [fact_ids] | 向前推理（消耗事实） |
| 33 | `frule` | theorem, [fact_ids] | 向前推理（保留事实） |
| 34 | `linarith` | — | 线性算术（自动选 nat/real/int） |

### 领域方法

**`server/methods/nat.py` (2 个)：**

| # | 方法名 | 参数 | 说明 |
|---|--------|------|------|
| 35 | `nat_norm` | — | 自然数归一化 |
| 36 | `nat_const_ineq` | — | 自然数常量不等式 |

**`server/methods/z3.py` (1 个)：**

| # | 方法名 | 参数 | 说明 |
|---|--------|------|------|
| 37 | `z3` | — | Z3 SMT 求解器 |

**`data/real.py` (1 个)：**

| # | 方法名 | 参数 | 说明 |
|---|--------|------|------|
| 38 | `real_norm` | — | 实数归一化 |

**`data/expr.py` (1 个)：**

| # | 方法名 | 参数 | 说明 |
|---|--------|------|------|
| 39 | `prove_avalI` | — | 表达式求值 |

**`imperative/imp.py` (2 个)：**

| # | 方法名 | 参数 | 说明 |
|---|--------|------|------|
| 40 | `eval_Sem` | — | 语义求值 |
| 41 | `vcg` | — | 验证条件生成 |

---

## `.pyhol` 证明步骤格式

```
goal_id: method_name [args] [@fact_ids] [param_key=value]
```

**goal_id**：层级 ID（`0`, `0.1`, `1.1.0`）
**@fact_ids**：引用已有行（`@0.0`, `@1.0,1.1`）
**param_***：额外参数（`param_A=true`, `param_t="{x. x <= n}"`）

## 证明模式速查

### 等式

```
?- t = t           →  reflexive
?- a = b (有 b=a)  →  apply_backward_step eq_sym_eq
?- A = B           →  equal_intr (拆为 A-->B 和 B-->A)
```

### 合取

```
?- A & B           →  apply_backward_step conjI
?- A (有 A & B)    →  apply_backward_step conjD1 @fact
?- B (有 A & B)    →  apply_backward_step conjD2 @fact
```

### 析取

```
?- A | B           →  apply_backward_step disjI1 (或 disjI2)
?- C (有 A|B)      →  apply_backward_step disjE @fact
```

### 否定

```
?- ~A              →  apply_backward_step negI
?- false (有 ~A,A) →  apply_backward_step negE @fact1,fact2
?- C (有 false)    →  apply_backward_step falseE @fact
```

### 蕴含

```
?- A --> B         →  introduction (把 A 加入假设)
?- B (有 A-->B, A) →  apply_backward_step implies_elim @fact1,fact2
```

### 量词

```
?- !x. P x         →  introduction (引入 x)
?- P t (有 !x.P x) →  apply_backward_step forall_elim @fact param_t=t
?- ?x. P x         →  apply_backward_step exI param_x=t
?- C (有 ?x. P x)  →  apply_backward_step exE @fact
```

### 等价

```
?- A <--> B        →  apply_backward_step iffI
```

### 重写

```
?- G (用定理 th)    →  rewrite_goal th
?- G (用事实 @f)    →  rewrite_goal_with_prev @f
?- G (多步)         →  rewrite_goal th1 / rewrite_goal th2 / ...
```

### 自动化

```
?- G (简化)         →  simp
?- G (算术)         →  norm 或 linarith 或 eval
?- G (Z3)           →  z3
```

---

## 属性

| 属性 | 作用 |
|------|------|
| `hint_rewrite` | 可用于 `simp` |
| `hint_backward` | 向后推理搜索 |
| `hint_backward1` | 需要 ≥1 个事实的向后推理 |
| `hint_forward` | 向前推理搜索 |
| `hint_resolve` | 消解搜索 |
| `var_induct` | 归纳原理 |

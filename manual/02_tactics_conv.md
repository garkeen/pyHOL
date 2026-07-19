# 第二层：策略与转换

## 概述

策略（Tactic）和转换（Conversion）是证明构造的核心工具。策略将目标分解为子目标，转换对项进行等价变换。两者通过组合子可以构建复杂的证明自动化。

## 转换（Conversion）

转换将一个项 `t` 变换为 `t'`，返回 `|- t = t'` 的证明。

### 原子转换

| 转换 | 说明 |
|------|------|
| `all_conv(t)` | 恒等：返回 `refl(t)` |
| `no_conv(t)` | 总是失败 |
| `beta_conv(t)` | 单步 beta 化简：`(%x. t1) t2 = t1[t2/x]` |
| `beta_norm_conv(t)` | 完全 beta 归一化 |
| `eta_conv(t)` | Eta 转换：`%x. f x = f`（x 不在 f 中自由出现） |

### 组合子

| 组合子 | 说明 |
|--------|------|
| `then_conv(cv1, cv2)` | 先 cv1 再 cv2，用传递性组合 |
| `else_conv(cv1, cv2)` | 尝试 cv1，失败则 cv2 |
| `combination_conv(cv1, cv2)` | 对 `f x` 分别转换 f 和 x |
| `arg_conv(cv)` | 只转换参数：`all_conv` 和 `cv` |
| `fun_conv(cv)` | 只转换函数：`cv` 和 `all_conv` |
| `binop_conv(cv)` | 对二元运算的两个参数都转换 |
| `every_conv(cv1, cv2, ...)` | 依次应用多个转换 |
| `repeat_conv(cv)` | 重复应用直到失败 |
| `abs_conv(cv)` | 进入 lambda 抽象的 body |
| `sub_conv(cv)` | 对 immediate subterms 应用 |
| `try_conv(cv)` | `else_conv(cv, all_conv)`，永不失败 |

### 遍历策略

| 策略 | 说明 |
|------|------|
| `top_conv(cv)` | 自顶向下：先应用 cv，再递归子项 |
| `top_sweep_conv(cv)` | 自顶向下扫描：成功就停，失败才递归 |
| `bottom_conv(cv)` | 自底向上：先递归子项，再应用 cv |

### 重写转换

| 转换 | 说明 |
|------|------|
| `rewr_conv(th)` | 用 `|- lhs = rhs` 重写。最核心的转换。 |
| `rewr_conv(th, sym=True)` | 用 `|- rhs = lhs` 重写（反向） |

`rewr_conv` 的工作方式：
1. 匹配 lhs（或 rhs）与目标项
2. 实例化等式
3. 用 beta_norm 处理高阶匹配结果

## 策略（Tactic）

策略将目标分解为子目标。返回 ProofTerm，可能包含 `sorry` gap。

### 原子策略

| 策略 | 目标 → 子目标 | 说明 |
|------|---------------|------|
| `rule(th_name)` | `?- G` → `?- A1, ..., ?- An` | 向后应用定理 |
| `assumption` | `A |- A` → 无 | 目标在假设中 |
| `reflexive` | `?- t = t` → 无 | 自反性 |
| `equal_intr` | `?- A = B` → `?- A-->B, ?- B-->A` | 等价拆分 |
| `intros` | `?- !x. A-->B` → `x, A |- B` | 引入变量和假设 |
| `var_induct` | `?- P x` → 归纳情况 | 结构归纳 |
| `rewrite_goal(th)` | `?- G` → `?- G'` | 用定理重写目标 |
| `rewrite_goal_with_prev` | `?- G` → `?- G'` | 用已有事实重写 |
| `apply_prev` | `?- C` → 无或子目标 | 应用已有事实 |
| `cases(A)` | `?- C` → `A-->C, ~A-->C` | 分情况讨论 |

### 组合子

| 组合子 | 说明 |
|--------|------|
| `then_tac(t1, t2)` | 先 t1，对所有子目标应用 t2 |
| `else_tac(t1, t2)` | 尝试 t1，失败则 t2 |
| `repeat_tac(t)` | 重复应用直到失败 |
| `try_tac(t)` | 应用 t，失败则什么都不做 |
| `first_tac([t1, t2, ...])` | 依次尝试，第一个成功的 |
| `every_tac([t1, t2, ...])` | 依次应用所有 |
| `thenl_tac(t, [t1, t2, ...])` | 先 t，然后 ti 应用到第 i 个子目标 |

### 证明模式

**蕴含引入**：
```
目标: ?- A --> B
策略: intro_imp_tac
结果: A |- B
```

**全称引入**：
```
目标: ?- !x. P x
策略: intro_forall_tac
结果: P x（x 是新变量）
```

**定理应用**：
```
目标: ?- C
策略: rule('conjI')
结果: ?- A, ?- B（其中 A-->B-->C 是 conjI 的实例）
```

**重写链**：
```
目标: ?- C
策略: then_tac(rewrite_goal('th1'), rewrite_goal('th2'))
结果: ?- C''
```

## 设计原则

1. **原子策略做一件事**：`rule` 只做匹配和应用，`assumption` 只检查假设，`reflexive` 只证等式。

2. **组合子构建复杂策略**：`repeat_tac(first_tac([conjI_tac, negI_tac, assumption_tac]))` 可以自动处理多种情况。

3. **转换可复用**：同一个 `rewr_conv` 在 `rewrite_goal`、`rewrite_fact`、`simp` 中都使用。

4. **策略和宏的关系**：策略返回 ProofTerm（可能有 gap），宏提供 eval（快速）和 get_proof_term（详细）。策略调用宏来构造证明。

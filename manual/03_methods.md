# 第三层：方法（Method）

## 架构

```
Method（用户API）
  ├── search(state, id, prevs) → 搜索建议
  ├── apply(state, id, data, prevs) → 执行操作
  └── display_step(state, data) → 显示描述
```

方法是前端面对的 API。内部调用策略和宏。

---

## 分发模式

### 模式 A：策略路径（向后推理）
```
method.apply() → state.apply_tactic(tactic) → tactic.get_proof_term() → ProofTerm
```
使用：`cases`, `apply_prev`, `rewrite_goal`, `apply_backward_step`, `introduction`, `reflexive`, `equal_intr`, `subst`, `unfold`, `fold`

### 模式 B：MacroTactic 路径（领域计算）
```
method.apply() → state.apply_tactic(MacroTactic('name')) → macro.eval() → Thm
```
使用：`nat_norm`, `nat_const_ineq`, `real_norm`, `prove_avalI`, `norm`, `eval`, `linarith`

### 模式 C：宏直接路径（向前推理）
```
method.apply() → macro.eval(args, prevs) → Thm → state.set_line()
```
使用：`apply_forward_step`, `rewrite_fact`, `rewrite_fact_with_prev`, `apply_fact`, `drule`, `frule`

### 模式 D：直接操作（无策略/宏）
```
method.apply() → state.set_line(rule, args, prevs, th)
```
使用：`cut`, `new_var`, `thin`, `sym`, `insert`

---

## 全部方法（41 个）

### 1. cut

**参数**：`[goal]`
**功能**：插入中间目标（have）。
**分发**：模式 D。创建一个新的 sorry 行，原目标保持。

### 2. cases

**参数**：`[case]`
**功能**：分情况讨论。
**分发**：模式 A。`tactic.cases(A)` 创建 `A-->C` 和 `~A-->C` 两个子目标。

### 3. apply_prev

**参数**：`[]`
**功能**：向后应用已有事实。
**分发**：模式 A。`tactic.apply_prev()` 匹配事实结论与目标。
**搜索**：尝试每个 prev 的 `apply_prev` 策略。

### 4. rewrite_goal_with_prev

**参数**：`[]`
**功能**：用已有等式事实重写目标。
**分发**：模式 A。`tactic.rewrite_goal_with_prev()`
**搜索**：尝试每个 prev 的重写。

### 5. rewrite_goal

**参数**：`[theorem, sym]`
**功能**：用定理重写目标。
**分发**：模式 A。`tactic.rewrite_goal(th_name, sym=sym)`
**搜索**：遍历所有 `hint_rewrite` 定理。
**特殊**：支持 `loc` 参数进行位置特定重写。

### 6. rewrite_fact

**参数**：`[theorem, sym]`
**功能**：用定理重写事实。
**分发**：模式 C。`rewrite_fact_macro`
**搜索**：遍历所有 `hint_rewrite` 定理。

### 7. rewrite_fact_with_prev

**参数**：`[]`
**功能**：用一个事实重写另一个。
**分发**：模式 C。`rewrite_fact_with_prev_macro`
**搜索**：尝试 prev 组合。

### 8. apply_forward_step

**参数**：`[theorem]`
**功能**：向前应用定理，推导新事实。
**分发**：模式 C。`apply_theorem_macro(with_inst=True)`
**搜索**：遍历 `hint_forward` 定理。

### 9. apply_backward_step

**参数**：`[theorem]`
**功能**：向后应用定理，分解目标。**最常用的方法**。
**分发**：模式 A。`tactic.rule(th_name)`
**搜索**：遍历 `hint_backward` 定理。

### 10. apply_resolve_step

**参数**：`[theorem]`
**功能**：消解。定理 ~A + 事实 A → 证明任何目标。
**分发**：模式 A。`tactic.resolve()`
**搜索**：遍历 `hint_resolve` 定理。

### 11. introduction

**参数**：`[names]`
**功能**：引入变量和假设。处理 `!x. A --> B` 形式。
**分发**：模式 E（子证明导出）。`tactic.intros()`
**搜索**：目标是 forall 或 implies 时可用。

### 12. revert_intro

**参数**：`[]`
**功能**：撤销引入。移除 assume 行，调整目标。
**分发**：模式 D。直接操作 proof state。

### 13. exists_elim

**参数**：`[names]`
**功能**：消除存在量词事实。
**分发**：模式 D。插入 variable 和 assume 行。

### 14. forall_elim

**参数**：`[s]`
**功能**：实例化全称量词。
**分发**：模式 C。`forall_elim_gen_macro`

### 15. inst_exists_goal

**参数**：`[s]`
**功能**：用见证实例化存在量词目标。
**分发**：模式 A。`tactic.inst_exists_goal(t)`

### 16. induction

**参数**：`[theorem, var]`
**功能**：结构归纳。
**分发**：模式 A。`tactic.var_induct(th_name, var)`
**搜索**：遍历 `var_induct` 属性的定理。

### 17. new_var

**参数**：`[name, type]`
**功能**：声明新变量。
**分发**：模式 D。插入 `variable` 行。

### 18. apply_fact

**参数**：`[]`
**功能**：应用 forall/implies 事实到其他事实。
**分发**：模式 C。`apply_fact_macro`
**搜索**：尝试 prev 组合。

### 19. call_tactic

**参数**：`[tactic_name, ...]`
**功能**：直接调用策略（逃生口）。
**分发**：模式 A。支持：`rule`, `rewrite_goal`, `apply_prev`, `intros`, `assumption`, `resolve`, `cases`

### 20. call_macro

**参数**：`[macro_name]`
**功能**：直接调用宏（逃生口）。
**分发**：模式 C。`macro.eval()`

### 21. simp

**参数**：`[]`
**功能**：简化。用所有 `hint_rewrite` 定理重写。
**分发**：模式 A。构建 `top_conv(rewr_conv(...))` 链。
**搜索**：存在 `hint_rewrite` 定理时可用。

### 22. norm

**参数**：`[]`
**功能**：归一化。自动选 nat/real。
**分发**：模式 B。`MacroTactic('nat_norm')` 或 `MacroTactic('real_norm')`

### 23. eval

**参数**：`[]`
**功能**：计算。自动选 nat/real。
**分发**：模式 B。`MacroTactic('nat_eval')` 等。

### 24. sym

**参数**：`[]`
**功能**：翻转等式 a=b → b=a。
**分发**：模式 D。创建 sorry 交换两侧。

### 25. reflexive

**参数**：`[]`
**功能**：证明 t = t。
**分发**：模式 A。`tactic.reflexive()`
**搜索**：目标是 `t = t` 时可用。

### 26. equal_intr

**参数**：`[]`
**功能**：证明 A = B，拆为 A-->B 和 B-->A。
**分发**：模式 A。`tactic.equal_intr()`
**搜索**：目标是等式时可用。

### 27. subst

**参数**：`[theorem]`
**功能**：用等式替换。
**分发**：模式 A。`top_sweep_conv(rewr_conv(th))`

### 28. unfold

**参数**：`[theorem]`
**功能**：展开定义。
**分发**：模式 A。`top_conv(rewr_conv(th))`

### 29. fold

**参数**：`[theorem]`
**功能**：折叠定义。
**分发**：模式 A。`top_conv(rewr_conv(th, sym=True))`

### 30. thin

**参数**：`[index]`
**功能**：删除假设（weakening）。
**分发**：模式 D + `find_goal`。利用 `can_prove` 的子集语义。

### 31. insert

**参数**：`[theorem]`
**功能**：插入定理作为新行。
**分发**：模式 D。插入 `theorem` 行。

### 32. drule

**参数**：`[theorem, fact_ids]`
**功能**：向前推理，**消耗**第一个 fact。
**分发**：模式 C + 替换。`apply_theorem_macro.eval()`，替换 fact 行。

### 33. frule

**参数**：`[theorem, fact_ids]`
**功能**：向前推理，**保留**所有 fact。
**分发**：模式 C + 插入。`apply_theorem_macro.eval()`，插入新行。

### 34. linarith

**参数**：`[]`
**功能**：线性算术。自动选 nat/real/int。
**分发**：模式 B。

### 35-36. nat_norm / nat_const_ineq

**参数**：`[]`
**功能**：自然数归一化 / 常量不等式。
**分发**：模式 B。`MacroTactic('nat_norm')` / `MacroTactic('nat_const_ineq')`
**limit**：`nat_nat_power_def_1` / `bit1_neq_one`

### 37. z3

**参数**：`[]`
**功能**：Z3 SMT 求解器。
**分发**：模式 C。调用 `z3wrapper.solve()`。

### 38. real_norm

**参数**：`[]`
**功能**：实数归一化。
**分发**：模式 B。`MacroTactic('real_norm')`
**limit**：`real_neg_0`

### 39. prove_avalI

**参数**：`[]`
**功能**：表达式求值证明。
**分发**：模式 B。`MacroTactic('prove_avalI')`
**limit**：`avalI_times`

### 40-41. eval_Sem / vcg

**参数**：`[]`
**功能**：命令式语言语义求值 / 验证条件生成。
**分发**：模式 B。

---

## .pyhol 证明步骤格式

```
goal_id: method_name [args] [@fact_ids] [param_key=value]
```

| 部分 | 说明 | 示例 |
|------|------|------|
| goal_id | 层级 ID | `0`, `0.1`, `1.1.0` |
| method_name | 方法名 | `apply_backward_step` |
| args | 位置参数 | `conjI` |
| @fact_ids | 引用事实 | `@0.0`, `@1.0,1.1` |
| param_* | 额外参数 | `param_A=true` |

---

## 证明模式速查

### 等式
```
?- t = t           →  reflexive
?- a = b (有 b=a)  →  sym
?- A = B           →  equal_intr
```

### 合取
```
?- A & B           →  apply_backward_step conjI
?- A (有 A & B)    →  apply_backward_step conjD1 @fact
?- B (有 A & B)    →  apply_backward_step conjD2 @fact
```

### 析取
```
?- A | B           →  apply_backward_step disjI1 或 disjI2
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
?- A --> B         →  introduction
?- B (有 A-->B, A) →  apply_backward_step implies_elim @fact1,fact2
```

### 量词
```
?- !x. P x         →  introduction
?- P t (有 !x.P x) →  forall_elim param_t=t
?- ?x. P x         →  inst_exists_goal t
?- C (有 ?x. P x)  →  apply_backward_step exE @fact
```

### 重写
```
?- G (用定理)       →  rewrite_goal th
?- G (用事实)       →  rewrite_goal_with_prev @f
```

### 自动化
```
?- G (简化)         →  simp
?- G (算术)         →  norm 或 eval 或 linarith
?- G (Z3)           →  z3
```

---

## 属性速查

| 属性 | 作用 | 使用者 |
|------|------|--------|
| `hint_rewrite` | 可用于 simp 和 rewrite_goal 搜索 | simp, rewrite_goal |
| `hint_backward` | 向后推理搜索 | apply_backward_step |
| `hint_backward1` | 需要 ≥1 个事实的向后推理 | apply_backward_step |
| `hint_forward` | 向前推理搜索 | apply_forward_step |
| `hint_resolve` | 消解搜索 | apply_resolve_step |
| `var_induct` | 归纳原理 | induction |

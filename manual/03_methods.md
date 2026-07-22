# 第三层：方法（Method，用户层 API）

> 依据作者 `tutorial/` 概念框架 + `server/methods/core.py` 源码校正。`method` 是前端/IDE 面对的 API；其本质是对 manual 01/02 中策略与宏的**用户层封装**。

> **holpy 自创（与 HOL Light 无对应物）**：方法层（Method）是 holpy 面向 web IDE / 前端 API 而设计的**用户层封装**，HOL Light **没有**对应物。HOL Light 的交互直接走 OCaml REPL 调 tactic，没有「带搜索建议、带显示、带参数封装」的方法层。本手册其它两层（内核 / 策略+转换）才是直接对应 HOL Light 的实现（见 manual 01/02 顶部说明）。

## 1. 架构

```
Method（用户 API）
  ├── search(state, id, prevs)  → 给出该步可用的搜索建议
  ├── apply(state, id, data, prevs) → 执行操作，改动 proof state
  └── display_step(state, data) → 显示这一步的人类可读描述
```

方法是**最靠近用户的入口**：你在 `.pyhol` 证明脚本里写的每一步（`1: apply_backward_step conjI @0`），调用的就是某个 `Method`。它内部再转去调用策略（manual 02）或宏（manual 01）。

> 关键认知：方法本身**不新增逻辑内容**——它只是把「怎么用策略/宏」封装成带参数、带搜索建议、带显示的人类友好接口。真正产生证明项的是底下的策略与宏。

## 2. 四种分发模式

方法 `apply` 内部大致走四条路径之一：

### 模式 A：策略路径（向后推理）
```
method.apply() → state.apply_tactic(tactic) → tactic.get_proof_term() → ProofTerm
```
典型：`apply_backward_step`、`introduction`、`cases`、`rewrite_goal`、`rewrite_goal_with_prev`、`apply_prev`、`inst_exists_goal`、`equal_intr`、`reflexive`、`subst`、`unfold`、`fold`、`simp`。

### 模式 B：可信宏求值路径（领域计算，快但信任 level）
```
method.apply() → state.apply_tactic(MacroTactic('name')) → macro.eval() → Thm
```
典型：`norm`、`eval`、`linarith`、`nat_norm`、`real_norm`、`nat_const_ineq`、`prove_avalI`、`z3`。

> `level` 与 `eval` 是 holpy 自创的可信宏机制（见 manual 01 §5、§6）。HOL Light 无此概念。

### 模式 C：宏直接路径（向前推理）
```
method.apply() → macro.eval(args, prevs) → Thm → state.set_line()
```
典型：`apply_forward_step`、`rewrite_fact`、`rewrite_fact_with_prev`、`apply_fact`、`forall_elim`、`drule`、`frule`。

### 模式 D：直接操作（无策略/宏，直接改 proof state）
```
method.apply() → state.set_line(rule, args, prevs, th)
```
典型：`cut`、`new_var`、`thin`、`insert`、`sym`、`revert_intro`、`exists_elim`。

> `call_tactic` / `call_macro` 是直接调用底层策略/宏的接口，可让你直接指定底层策略/宏名。

## 3. 方法总表（来自 `register_method`）

> 名称与 `server/methods/core.py` 的 `register_method(...)` 一一对应。

### 逻辑方法

| 方法 | 参数 | 功能 | 分发 |
|------|------|------|------|
| `cut` | `[goal]` | 插入中间目标（have） | D |
| `cases` | `[case]` | 分情况 `A-->C` 与 `~A-->C` | A |
| `apply_prev` | `[]` | 向后应用已有事实 | A |
| `rewrite_goal_with_prev` | `[]` | 用已有等式事实重写目标 | A |
| `rewrite_goal` | `[theorem, sym]` | 用定理重写目标（支持 `loc`） | A |
| `rewrite_fact` | `[theorem, sym]` | 用定理重写事实 | C |
| `rewrite_fact_with_prev` | `[]` | 用一个事实重写另一个 | C |
| `apply_forward_step` | `[theorem]` | 向前应用定理推新事实 | C |
| `apply_backward_step` | `[theorem]` | **最常用**：向后应用定理分解目标 | A |
| `apply_resolve_step` | `[theorem]` | 消解（`~A` + `A` → 任意目标） | A |
| `introduction` | `[names]` | 引入变量与假设（处理 `!x. A-->B`） | A（= `intros`） |
| `revert_intro` | `[]` | 撤销引入（移除 assume 行） | D |
| `exists_elim` | `[names]` | 消除存在量词事实 | D |
| `forall_elim` | `[s]` | 实例化全称量词 | C |
| `inst_exists_goal` | `[s]` | 用见证实例化存在目标 | A |
| `induction` | `[theorem, var]` | 结构归纳 | A |
| `new_var` | `[name, type]` | 声明新变量 | D |
| `apply_fact` | `[]` | 应用 forall/implies 事实 | C |
| `call_tactic` | `[tactic_name, ...]` | 直接调用策略（底层接口） | A |
| `call_macro` | `[macro_name]` | 直接调用宏（底层接口） | C |
| `sym` | `[]` | 翻转等式 `a=b → b=a` | D |
| `reflexive` | `[]` | 证明 `t = t` | A |
| `equal_intr` | `[]` | 证明 `A = B`（拆 `A-->B`,`B-->A`） | A |
| `subst` | `[theorem]` | 用等式替换（顶层扫描重写） | A（`top_sweep_conv(rewr_conv(th))`） |
| `unfold` | `[theorem]` | 展开定义（常量→体 + β 归一） | A（`top_conv(rewr_conv(th))`+`beta_norm`） |
| `fold` | `[theorem]` | 折叠定义（体→常量） | A（`top_conv(rewr_conv(th, sym=True))`） |
| `thin` | `[index]` | 删除假设（weakening，利用子集语义） | D |
| `insert` | `[theorem]` | 插入定理作为新行 | D |
| `drule` | `[theorem, fact_ids]` | 向前推理，**消耗**首个 fact | C |
| `frule` | `[theorem, fact_ids]` | 向前推理，**保留**所有 fact | C |

### 自动化 / 领域方法

| 方法 | 功能 | 分发 |
|------|------|------|
| `simp` | 用所有 `hint_rewrite` 定理重写（构建 `top_conv(rewr_conv(...))` 链） | A |
| `norm` | 归一化，自动选 nat/real | B |
| `eval` | 计算，自动选 nat/real | B |
| `linarith` | 线性算术，自动选 nat/real/int | B |
| `nat_norm` / `nat_const_ineq` | 自然数归一化 / 常量不等式 | B |
| `real_norm` | 实数归一化 | B |
| `z3` | Z3 SMT 求解器（oracle） | C |
| `prove_avalI` | 表达式求值证明 | B |
| `eval_Sem` / `vcg` | 命令式语言语义求值 / 验证条件生成 | B |

## 4. `.pyhol` 证明步骤格式

```
goal_id: method_name [args] [@fact_ids] [param_key=value]
```

| 部分 | 说明 | 示例 |
|------|------|------|
| `goal_id` | 层级 ID | `0`, `0.1`, `1.1.0` |
| `method_name` | 方法名 | `apply_backward_step` |
| `args` | 位置参数 | `conjI` |
| `@fact_ids` | 引用事实 | `@0.0`, `@1.0,1.1` |
| `param_*` | 额外参数 | `param_A=true` |

示例（来自 `library/nat.pyhol` 真实写法）：
```
1.1: apply_prev @0
1.1: induction x nat_induct
1.3.1.2: apply_backward_step disjE @1.3.1.1
1.3.1: introduction m
```

## 5. 证明模式速查

### 等式
```
?- t = t            →  reflexive
?- a = b (有 b=a)   →  sym
?- A = B            →  equal_intr
```

### 合取
```
?- A & B            →  apply_backward_step conjI
?- A (有 A & B)     →  apply_backward_step conjD1 @fact
?- B (有 A & B)     →  apply_backward_step conjD2 @fact
```

### 析取
```
?- A | B            →  apply_backward_step disjI1 / disjI2
?- C (有 A|B)       →  apply_backward_step disjE @fact
```

### 蕴含 / 否定
```
?- A --> B          →  introduction
?- B (有 A-->B, A)  →  apply_backward_step implies_elim @f1,@f2
?- ~A               →  apply_backward_step negI
?- false (有 ~A,A)  →  apply_backward_step negE @f1,@f2
?- C (有 false)     →  apply_backward_step falseE @fact
```

### 量词
```
?- !x. P x          →  introduction
?- P t (有 !x.P x)  →  forall_elim param_t=t
?- ?x. P x          →  inst_exists_goal t
?- C (有 ?x. P x)   →  apply_backward_step exE @fact
```

### 重写 / 自动化
```
?- G (用定理)       →  rewrite_goal th
?- G (用事实)       →  rewrite_goal_with_prev @f
?- G (简化)         →  simp
?- G (算术)         →  norm / eval / linarith
?- G (Z3)           →  z3
```

## 6. 属性（attribute）速查

方法靠定理上的 **attribute** 决定搜索时该用哪条定理：

| 属性 | 作用 | 使用者 |
|------|------|--------|
| `hint_rewrite` | 可用于 simp / rewrite_goal 搜索 | `simp`, `rewrite_goal`, `rewrite_fact` |
| `hint_backward` | 向后推理搜索 | `apply_backward_step` |
| `hint_backward1` | 需要 ≥1 个事实的向后推理 | `apply_backward_step` |
| `hint_forward` | 向前推理搜索 | `apply_forward_step` |
| `hint_resolve` | 消解搜索 | `apply_resolve_step` |
| `var_induct` | 归纳原理 | `induction` |

> 在 `.pyhol` 里，`fun`/`def` 项的每条规则会自动带上 `hint_rewrite` 属性（见 manual 01 §8）；`def.pred`（归纳谓词）的规则带 `hint_backward`。这正是 `rewrite_goal`/`apply_backward_step` 能「自动找到」它们的原因。

## 7. 信任模型小结（与 manual 01/02 串联）

- 你在 `.pyhol` 里写的每一步方法 → 调用策略/宏 → 最终展开为 **15 条原始推理规则 + 已证定理**（manual 01）。这条「证明可被独立校验」的链路是真实的、可信的。
- 方法的「搜索建议」只是便利：**真正决定证明是否成立的，是底层证明项能否通过 `check_proof`**。
- `z3` 等 oracle 方法（level 0）不可展开，其正确性依赖外部求解器——这是系统里唯一依赖外部工具正确性的环节。
- **定义（`fun`/`def`）与归纳类型（`Datatype`）不在此校验链内**：它们经 `unchecked_extend` 直接作为公理加入，**不查良基性**；`Datatype` 只产 `_induct` 不产 `_RECURSION`（详见 manual 01 §8）。对比 HOL Light：通用递归 `define` 强制 WF 证明、结构递归借 `*_RECURSION` 预制证据、归纳类型由 `define_type` 证明生成保守扩展。holpy 内核层不提供等价 HOL Light 的保守扩展保证。holpy 的可信度来自「证明可被独立校验」，而非「定义被强制保证一致」。

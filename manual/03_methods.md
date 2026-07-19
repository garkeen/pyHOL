# 第三层：方法（Method）

## 概述

方法是用户面对的 API。每种方法封装一个证明操作，提供搜索（search）和执行（apply）两个接口。方法内部调用策略和宏来完成实际工作。

## 方法接口

```python
class Method:
    sig: list           # 参数签名，如 ['theorem'] 或 ['theorem', 'sym']
    limit: str | None   # 依赖的定理名（如果不存在则方法不可用）

    def search(self, state, id, prevs) -> list[dict]:
        # 搜索可用操作，返回建议列表
        ...

    def display_step(self, state, data) -> str:
        # 显示步骤描述
        ...

    def apply(self, state, id, data, prevs):
        # 执行方法，修改 proof state
        ...
```

## 核心方法

### 向后推理

| 方法 | 参数 | 说明 |
|------|------|------|
| `apply_backward_step` | theorem, [fact_ids], [params] | 向后应用定理。匹配结论，创建假设子目标。 |
| `apply_prev` | [fact_ids] | 向后应用已有事实。 |

**示例**：目标 `?- A & B`，应用 `conjI`：
```
0: apply_backward_step conjI
0: introduction
0.1: ... prove A ...
0.2: ... prove B ...
```

### 向前推理

| 方法 | 参数 | 说明 |
|------|------|------|
| `apply_forward_step` | theorem, [fact_ids] | 向前应用定理。从已有事实推导新事实。 |
| `apply_fact` | [fact_ids] | 应用 forall/implies 事实。 |
| `drule` | theorem, [fact_ids] | 消耗事实（替换为推导结果）。 |
| `frule` | theorem, [fact_ids] | 保留事实，添加推导结果。 |

### 引入

| 方法 | 参数 | 说明 |
|------|------|------|
| `introduction` | [names] | 引入变量和假设。处理 `!x. A --> B` 形式。 |

**示例**：目标 `?- !x. A x --> B x`：
```
0: introduction
0.1: A x |- B x（x 是新变量，A x 是假设）
```

### 重写

| 方法 | 参数 | 说明 |
|------|------|------|
| `rewrite_goal` | theorem, [sym] | 用定理重写目标。 |
| `rewrite_goal_with_prev` | [fact_ids] | 用已有等式事实重写目标。 |
| `rewrite_fact` | theorem, [fact_ids] | 用定理重写已有事实。 |
| `rewrite_fact_with_prev` | [fact_ids] | 用一个事实重写另一个。 |

**示例**：目标 `?- x + 0 = x`，用 `add_0_right` 重写：
```
0: rewrite_goal add_0_right
```

### 等式

| 方法 | 参数 | 说明 |
|------|------|------|
| `reflexive` | — | 证明 `t = t`。 |
| `equal_intr` | — | 证明 `A = B`，拆为 `A-->B` 和 `B-->A`。 |
| `sym` | — | 翻转等式 `a = b` → `b = a`。 |

### 逻辑

| 方法 | 参数 | 说明 |
|------|------|------|
| `cases` | term | 分情况讨论。 |
| `induction` | theorem, var | 结构归纳。 |
| `forall_elim` | term | 实例化全称量词。 |
| `inst_exists_goal` | term | 实例化存在量词目标。 |
| `insert` | theorem | 插入定理作为新行。 |

### 自动化

| 方法 | 参数 | 说明 |
|------|------|------|
| `simp` | — | 用 `hint_rewrite` 属性的定理简化目标。 |
| `norm` | — | 归一化（nat/real，根据目标类型自动选择）。 |
| `eval` | — | 计算（nat/real）。 |
| `z3` | — | 调用 Z3 求解器。 |

### 逃生口

| 方法 | 参数 | 说明 |
|------|------|------|
| `call_tactic` | tactic_name, [params] | 直接调用策略。 |
| `call_macro` | macro_name | 直接调用宏。 |

## 证明状态

```python
class ProofState:
    vars: list[Var]    # 上下文变量
    prf: Proof         # 证明对象
    rpt: ProofReport   # 检查报告
```

状态操作：

```python
state = server.parse_init_state(prop)  # 创建初始状态
state.apply_tactic(id, tactic, ...)    # 应用策略
state.check_proof()                    # 验证证明
state.export_proof()                   # 导出证明
state.json_data()                      # JSON 格式
```

## 前端交互流程

```
1. 用户输入命题
2. parse_init_state 创建初始状态（sorry 作为目标）
3. 用户选择方法和参数
4. apply_method 执行方法
5. 状态更新，显示新子目标
6. 重复 3-5 直到无 sorry
7. check_proof 验证
8. 保存到 .pyhol
```

## 证明步骤格式

在 `.pyhol` 文件中：

```yaml
proof
  0: apply_backward_step iffI
  0: introduction
  0.1: apply_backward_step conjD2 @0.0
  1: introduction
  1.1: apply_backward_step conjI
  1.1: apply_backward_step trueI
qed
```

格式：`goal_id: method_name [args] [@fact_ids] [param_key=value]`

- `goal_id`：目标的层级 ID（如 `0`, `0.1`, `1.1.0`）
- `method_name`：方法名
- `@fact_ids`：引用已有事实（如 `@0.0`, `@1.0,1.1`）
- `param_key=value`：额外参数（如 `param_A=true`）

## .pyhol 文件格式

```yaml
theory nat
imports logic
description "Natural numbers"

const zero :: nat
const Suc :: nat ⇒ nat

datatype nat = zero | Suc (n :: nat)

fun plus :: nat ⇒ nat ⇒ nat
  | 0 + n = n
  | Suc m + n = Suc (m + n)

theorem add_0_right
  fixes x :: nat
  prop x + 0 = x
  [hint_rewrite]
  proof
    0: induction x nat_induct
    0: rewrite_goal nat_plus_def_1
    1: introduction m
    1.2: rewrite_goal nat_plus_def_2
    1.2: rewrite_goal_with_prev @1.1
  qed
```

### 项类型

| 类型 | 关键字 | 说明 |
|------|--------|------|
| `def.ax` | `const` | 常量声明 |
| `def` | `def` | 常量定义 |
| `def.ind` | `fun` | 归纳定义函数 |
| `def.pred` | `inductive` | 归纳定义谓词 |
| `type.ax` | `type` | 类型声明 |
| `type.ind` | `datatype` | 归纳数据类型 |
| `thm.ax` | `axiom` | 公理（无证明） |
| `thm` | `theorem` | 定理（有证明） |
| `header` | `header` | 章节标题 |

### 属性

| 属性 | 说明 |
|------|------|
| `hint_rewrite` | 可用于 `simp` 自动重写 |
| `hint_backward` | 可用于向后推理搜索 |
| `hint_backward1` | 需要至少一个事实的向后推理 |
| `hint_forward` | 可用于向前推理搜索 |
| `hint_resolve` | 可用于消解 |
| `var_induct` | 归纳原理 |

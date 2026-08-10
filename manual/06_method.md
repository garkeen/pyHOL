# 方法层与证明状态

> 代码事实以 `server/methods/core.py` 为准。

方法（Method）是用户层 API：前端/IDE 面对的接口。每个 `.pyhol` 证明步骤调用的就是某个方法。方法本身不新增逻辑内容，只是把"怎么用策略/宏"封装成带参数、带搜索建议、带显示的人类友好接口。

## 1. Method 基类

```python
class Method:
    def search(self, state: ProofState, id, prevs):
        """搜索该步可用的参数建议。"""

    def apply(self, state: ProofState, id, data, prevs):
        """执行操作，改动 proof state。"""

    def display_step(self, state: ProofState, data):
        """显示这一步的人类可读描述。"""
```

- `state`：当前证明状态（`ProofState`）。
- `id`：当前目标行的稳定 ID（int）。
- `prevs`：引用的事实行稳定 ID 列表。
- `data`：方法的参数字典（如 `{'theorem': 'conjI', 'sym': 'false'}`）。

## 2. ProofState

```python
class ProofState:
    vars: List[Var]       # 上下文变量
    prf: Proof            # 线性证明
    rpt: ProofReport      # 校验报告
```

### 2.1 StableProofState

新管线使用 `StableProofState`（`server/stable_state.py`）包装旧的 `ProofState`：
- 稳定 ID（`#[N]`，int）通过 `th -> sid` 映射追踪，**不随插入/删除漂移**
- goal 变 fact 时 ID 不变
- `apply_method_dict(step)`：接受稳定 ID 的步骤，翻译为位置 ID 调用底层 `ProofState`
- 位置 ID 操作（`add_line_before`、`remove_line`、`replace_id`）仍在底层使用，但不暴露给 API

### 2.2 apply_tactic 流程

`state.apply_tactic(id, tactic, args, prevs)` 是方法调用策略的标准流程：

1. 取当前 `sorry` 行的目标 `cur_item.th`。
2. `pt = tactic.get_proof_term(args=args, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)`（goal 作为 prevs[0]）。
3. 若 `pt.rule == 'atom'`：直接用事实替换 sorry 行。
4. 否则 `new_prf = pt.export(prefix=id, subproof=False)`，插入新行。
5. `check_proof(compute_only=True)` 校验。
6. 对新 `sorry` 行调 `find_goal`：若已有证明能解，自动替换。
7. 对新 `sorry` 行调 `trivial` 策略：构造成功则自动关闭。

`StableProofState.apply_method_dict` 在此之上添加稳定 ID 管理：翻译 `goal=N`/`facts=[N]` 为位置 ID，调用 `apply_tactic`，然后为新 item 分配稳定 ID。

## 3. 四种分发模式

方法 `apply` 内部走四条路径之一：

### 模式 A：策略路径（向后推理）
```
method.apply -> state.apply_tactic(tactic) -> tactic.get_proof_term -> ProofTerm
```
典型：`apply_backward_step`、`introduction`、`cases`、`rewrite_goal`、`apply_prev`、`inst_exists_goal`、`induction`、`reflexive`、`equal_intr`、`subst`、`unfold`、`fold`、`simp`。

### 模式 B：可信宏求值（领域计算）
```
method.apply -> state.apply_tactic(MacroTactic(name)) -> macro.eval -> Thm
```
典型：`norm`、`eval`、`linarith`（按类型分发到 `nat_norm`/`real_norm`/`int_norm`）。

### 模式 C：正向策略路径（向前推理）
```
method.apply -> tactic.X_forward().get_proof_term(args, prevs) -> ProofTerm
            -> state.add_line_before + state.set_line(pt.rule, args, prevs)
```
正向方法不走 `apply_tactic`（那需要 sorry goal），而是直接调正向策略获取 ProofTerm，再手动插入新行。推理（匹配、效果检查）在策略层完成。

典型：`apply_forward_step`、`rewrite_fact`、`rewrite_fact_with_prev`、`apply_fact`、`forall_elim`、`frule`。

### 模式 D：直接操作
```
method.apply -> state.set_line(rule, args, prevs, th)
```
典型：`cut`、`new_var`、`insert`、`exists_elim`、`z3`。

> **行不可变约束**：已删除所有"改写已有行"的方法（`thin` / `sym` / `revert_intro` / `drule`）。fact 与 goal 一旦生成不可变：向后推理通过证明项展开覆盖 goal 行、以新 sorry 行产生子目标；正向推理只插入新事实行。`add_line_before` / `remove_line` / `replace_id` / `set_line` 仍在底层保留，但只用于 IDE 结构性编辑与上述路径，不用于改写已存在行的命题。


## 4. 方法目录

### 4.1 逻辑方法

| 方法 | 参数 | 分发 | 说明 |
|---|---|---|---|
| `cut` | `[goal]` | D | 插入中间目标（have） |
| `cases` | `[case]` | A | 分情况 `A⟶C` 与 `¬A⟶C` |
| `apply_prev` | `[]` | A | 向后应用已有事实 |
| `rewrite_goal_with_prev` | `[]` | A | 用已有等式事实重写目标 |
| `rewrite_goal` | `[theorem, sym]` | A | 用定理重写目标（支持 `loc`） |
| `rewrite_fact` | `[theorem, sym]` | C | 用定理重写事实 |
| `rewrite_fact_with_prev` | `[]` | C | 用一个事实重写另一个 |
| `apply_forward_step` | `[theorem]` | C | 向前应用定理推新事实 |
| `apply_backward_step` | `[theorem]` | A | **最常用**：向后应用定理分解目标 |
| `apply_resolve_step` | `[theorem]` | A | 消解（`~A` + `A` -> 任意目标） |
| `accept` | `[theorem]` | A | 直接用定理关闭：结论匹配 goal、前提匹配假设，无子目标 |
| `call_tactic` | `[tactic_name]` | A | 逃生舱：按名直接调用策略（rule/rewrite_goal/apply_prev/intros/assumption/resolve/cases） |
| `introduction` | `[names]` | A | 引入变量与假设 |
| `exists_elim` | `[names]` | D | 消除存在量词事实 |
| `forall_elim` | `[s]` | C | 实例化全称量词 |
| `inst_exists_goal` | `[s]` | A | 用见证实例化存在目标 |
| `induction` | `[theorem, var]` | A | 结构归纳 |
| `new_var` | `[name, type]` | D | 声明新变量 |
| `apply_fact` | `[]` | C | 应用 forall/implies 事实 |
| `reflexive` | `[]` | A | 证明 `t = t` |
| `equal_intr` | `[]` | A | 证明 `A = B`（拆两个方向） |
| `subst` | `[theorem]` | A | 用等式替换（`top_sweep_conv`） |
| `unfold` | `[theorem]` | A | 展开定义（`top_conv` + β） |
| `fold` | `[theorem]` | A | 折叠定义（反向 `top_conv`） |
| `insert` | `[theorem]` | D | 插入定理作为新行 |
| `frule` | `[theorem]` | C | 向前推理，**保留**所有 fact |

### 4.2 自动化方法

| 方法 | 分发 | 说明 |
|---|---|---|
| `simp` | A | 用所有 `hint_rewrite` 定理重写 |
| `norm` | B | 归一化，按类型选 nat/real |
| `eval` | B | 计算，按类型选 nat/int/real |
| `linarith` | B | 线性算术，按类型选 nat/real/int |
| `eval_Sem` | B | 计算命令式程序小步语义 `Sem com st st2`（imperative） |
| `z3` | D | Z3 SMT 求解器（oracle 宏行，直接 `set_line`） |
| `vcg` | A | Hoare 逻辑 VCG：将 `Valid P c Q` 分解为验证条件子目标 |

领域包还直接注册了无参宏方法（模式 B，`MacroTactic` 包装）：`nat_norm`、`real_norm`、`nat_const_ineq`（nat 常量不等式）、`prove_avalI`（数组访问求值）。

## 5. 属性系统

方法靠定理上的**属性**（attribute）决定搜索时该用哪条定理：

| 属性 | 作用 | 使用者 |
|---|---|---|
| `hint_rewrite` | 可用于重写 | `simp`, `rewrite_goal`, `rewrite_fact` |
| `hint_rewrite_sym` | 可反向重写 | `rewrite_goal(sym=True)`, `rewrite_fact(sym=True)` |
| `hint_backward` | 向后推理搜索 | `apply_backward_step` |
| `hint_backward1` | 需 ≥1 个事实的向后推理 | `apply_backward_step` |
| `hint_forward` | 向前推理搜索 | `apply_forward_step` |
| `hint_resolve` | 消解搜索 | `apply_resolve_step` |
| `var_induct` | 归纳原理 | `induction` |

在 `.pyhol` 里，`fun` 的每条规则自动带 `hint_rewrite`，`def.pred`（归纳谓词）的规则带 `hint_backward`，`Datatype` 的归纳定理带 `var_induct`。

## 6. .pyhol step 格式

新格式使用稳定 `#[N]` ID，无位置漂移：

```
[← |→ ] method_name [positional_args] [key=value ...] goal=N [facts=[N,...]]
  #[N] proposition          # 派生注解（replay 不验证命题）
```

| 部分 | 说明 | 示例 |
|---|---|---|
| `←` / `→` | 方向标注 | `←`（逆向，消耗 goal），`→`（正向，消耗 fact） |
| `method_name` | 方法名 | `apply_backward_step` |
| `positional_args` | 位置参数 | `conjI` |
| `goal=N` | 操作的 goal/fact 稳定 ID | `goal=0`, `goal=3` |
| `facts=[N,...]` | 引用事实的稳定 ID | `facts=[3]`, `facts=[1,2]` |
| `#[N]` | 派生 item 注解 | `#[1] A ∧ B` |

- **#0** = 要证明的定理（隐含，不写）
- **#[N]**（N≥1）= method 调用产生的 item（fact 或 subgoal）
- 命题有蕴含时，第一步必须是 `← introduction goal=0` 显式拆分
- `fixes` 变量在上下文中，不需要 `#[N]`
- replay 时 `#[N]` 的 ID 用于引用映射，命题不验证

示例：
```
proof
  ← apply_backward_step iffI goal=0
    #[1] A ∧ B ⟶ B ∧ A
    #[2] B ∧ A ⟶ A ∧ B
  ← introduction goal=1
    #[3] A ∧ B
    #[4] B ∧ A
  ← apply_backward_step conjI goal=4
    #[5] B
    #[6] A
  ← apply_backward_step conjD2 goal=5 facts=[3]
  ← apply_backward_step conjD1 goal=6 facts=[3]
qed
```

## 7. 自动搜索（前端 forward/backward-search）

搜索逻辑在前端触发、后端 `app/ide.py` 执行：

- `apply_backward_step.search`：遍历所有带 `hint_backward`/`hint_backward1` 属性的定理，尝试 `rule().get_proof_term`，成功则记录子目标。
- 每个方法按 `no_order` 属性决定是否对 `prevs` 做排列。
- 若有结果能"solves"（`_goal` 为空），只保留 solves 的结果。

## 8. loc 位置特定重写

`rewrite_goal` 方法支持 `loc` 参数，对目标的特定子位置重写：

- `loc="0"`：函数部分（`fun_conv`）
- `loc="1"`：参数部分（`arg_conv`）
- `loc="0.1"`：函数的参数（`fun_conv(arg_conv(...))`）
- 等等

内部用 `_loc_to_conv(loc, base_cv)` 把数字串转为 conv 组合子。

## 9. 方法的注册

```python
from server.methods.core import register_method

@register_method('my_method')
class my_method(Method):
    def __init__(self):
        self.sig = ['param1', 'param2']
        self.limit = None        # 可用性闸门（None 或定理名）
        self.no_order = False    # search 时是否对 prevs 排列
        list_params = set()       # 类属性：哪些参数是逗号分隔的变长列表（前端渲染 +/- 动态字段）
```

`list_params` 是类属性（非实例属性），声明哪些参数接受逗号分隔的多个值。
当前仅 `introduction`（`{'names'}`）与 `exists_elim`（`{'names'}`）使用。
前端 ProofQuery 对 `list_params` 中的字段渲染动态增减输入框，提交时用逗号 join。
后端通过 `get_method_list_params()` 汇总，序列化到 proof state 的 `method_list_params` 字段。

- `register_method(name)` 装饰器，存入 `global_methods` 字典（幂等）。
- `has_method(name)` 检查方法存在且 `limit` 满足。
- `get_method(name)` 取方法实例。

## 10. 信任模型衔接

- 方法不新增逻辑内容，真正产生证明项的是底层策略与宏。
- 你在 `.pyhol` 里写的每一步方法 -> 调用策略/宏 -> 最终展开为 15 条原始规则 + 已证定理。
- 方法的"搜索建议"只是便利：**真正决定证明是否成立的，是底层证明项能否通过 `check_proof`**。

---

**下一章**：[`07_system.md`](07_system.md) -- 系统组织总览。

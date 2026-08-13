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
典型：`rule`、`intro`、`cases`、`rewrite`（goal 模式）、`apply_prev`、`inst`（goal 模式）、`induct`、`refl`、`eq_intro`、`unfold`、`simp`、`assumption`、`accept`。

### 模式 B：受检宏调用（领域计算）
```
method.apply -> state.apply_macro(name, args) -> macro 展开 -> 受检原语行
```
宏一律走受检调用入口（无 MacroTactic 逃生门），展开结果经 `check_proof` 验证。典型：`norm`、领域注册的 `nat_norm`/`real_norm`/`nat_const_ineq`/`eval_Sem`/`prove_avalI`。

### 模式 C：正向策略路径（向前推理）
```
method.apply -> tactic.X_forward().get_proof_term(args, prevs) -> ProofTerm
            -> state.add_line_before + state.set_line(pt.rule, args, prevs)
```
正向方法不走 `apply_tactic`（那需要 sorry goal），而是直接调正向策略获取 ProofTerm，再手动插入新行。推理（匹配、效果检查）在策略层完成。

典型：`forward`（定理模式与 fact-on-facts 模式）、`rewrite`（fact 模式）、`inst`（fact 模式，即全称实例化）。

### 模式 D：直接操作
```
method.apply -> state.set_line(rule, args, prevs, th)
```
典型：`cut`、`var`、`elim`、`z3`。

> **行不可变约束**：已删除所有"改写已有行"的方法（`thin` / `sym` / `revert_intro` / `drule`）。fact 与 goal 一旦生成不可变：向后推理通过证明项展开覆盖 goal 行、以新 sorry 行产生子目标；正向推理只插入新事实行。`add_line_before` / `remove_line` / `replace_id` / `set_line` 仍在底层保留，但只用于 IDE 结构性编辑与上述路径，不用于改写已存在行的命题。


## 4. 方法目录

方法词表（`server/methods/core.py` 注册 + 领域宏方法）：
`rule` / `resolve` / `rewrite` / `intro` / `cases` / `type_cases` / `induct` / `cut` / `inst` /
`accept` / `refl` / `eq_intro` / `trans` / `unfold` / `forward` / `elim` / `var` /
`assumption` / `norm` / `simp` + oracle（`z3` / `vcg`）+ 领域宏方法。

`rewrite` 与 `inst` 是**双模式**方法，由状态形状推断模式（显式 `target`/`source` 标记可覆盖）：
- 目标行是缺口 → goal 模式；否则 fact 模式
- 带 `theorem` 参数 → 定理来源；否则用选中的事实
- 注意：对缺口位置做 fact 改写必须显式传 `target='fact'`（缺口 id 有歧义）

### 4.1 逻辑方法

| 方法 | 参数 | 分发 | 说明 |
|---|---|---|---|
| `rule` | `[theorem]` | A | **最常用**：向后应用定理分解目标（整条命题匹配 + 前提子目标） |
| `resolve` | `[theorem]` | A | 消解（`~A` + fact `A` -> 任意目标） |
| `apply_prev` | `[]` | A | 向后应用已有事实（可带 `param_*` 实例化） |
| `accept` | `[theorem]` | A | 直接用定理关闭：结论匹配 goal、前提匹配假设，无子目标 |
| `rewrite` | `[theorem, sym]` | A/C | 双模式：goal 模式重写目标（支持 `loc`），fact 模式重写事实；无 theorem 时用选中事实作重写规则 |
| `intro` | `[names]` | A | 引入变量与假设（names 为逗号分隔列表） |
| `elim` | `[names]` | D | 消除存在量词事实（引入新变量 + 假设） |
| `inst` | `[s]` | A/C | 双模式：goal 模式用见证实例化存在目标，fact 模式实例化全称事实 |
| `cases` | `[case]` | A | 布尔分情况 `A⟶C` 与 `¬A⟶C`（classical_cases 包装，cases_thm 可换） |
| `type_cases` | `[case]` | A | 数据类型分情况：用 datatype 扩展生成的 `<tyname>_cases` 定理，每个构造子一个分支（无归纳假设） |
| `induct` | `[theorem, var]` | A | 结构归纳 |
| `cut` | `[cut_goal]` | D | 插入中间目标（have） |
| `var` | `[name, type]` | D | 声明新变量 |
| `forward` | `[theorem]` | C | 正向推理推新事实：带 theorem 为定理模式，不带为 fact-on-facts 模式 |
| `unfold` | `[theorem, sym]` | A | 展开定义（`top_conv` + β）；`sym='true'` 即折叠 |
| `refl` | `[]` | A | 证明 `t = t` |
| `eq_intro` | `[]` | A | 证明 `A = B`（拆两个方向） |
| `trans` | `[s]` | A | 传递性（TRANS_TAC）：证 `s = t` 时选中间项 `u`，拆 `s = u` 与 `u = t`；自反一侧自动跳过 |
| `assumption` | `[]` | A | 用自身假设关闭目标 |

### 4.2 自动化方法

| 方法 | 分发 | 说明 |
|---|---|---|
| `simp` | A | 全体 `hint_rewrite` 无前提定理定点迭代重写 + β 归一，must-change |
| `norm` | B | 归一化，按类型选 nat/real 领域 conv |
| `eval_Sem` | B | 计算命令式程序小步语义 `Sem com st st2`（imperative） |
| `z3` | D | Z3 SMT 求解器（oracle 宏行，直接 `set_line`） |
| `vcg` | A | Hoare 逻辑 VCG：将 `Valid P c Q` 分解为验证条件子目标 |

领域包还直接注册了无参宏方法（模式 B，受检宏调用）：`nat_norm`、`real_norm`、`nat_const_ineq`（nat 常量不等式）、`prove_avalI`（数组访问求值）。

## 5. 属性系统

方法靠定理上的**属性**（attribute）决定搜索时该用哪条定理：

| 属性 | 作用 | 使用者 |
|---|---|---|
| `hint_rewrite` | 可用于重写 | `simp`, `rewrite` |
| `hint_rewrite_sym` | 可反向重写 | `rewrite(sym=true)` |
| `hint_backward` | 向后推理搜索 | `rule` |
| `hint_backward1` | 需 ≥1 个事实的向后推理 | `rule` |
| `hint_forward` | 向前推理搜索 | `forward` |
| `hint_resolve` | 消解搜索 | `resolve` |
| `var_induct` | 归纳原理 | `induct` |

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
| `method_name` | 方法名 | `rule` |
| `positional_args` | 位置参数 | `conjI` |
| `goal=N` | 操作的 goal/fact 稳定 ID | `goal=0`, `goal=3` |
| `facts=[N,...]` | 引用事实的稳定 ID | `facts=[3]`, `facts=[1,2]` |
| `#[N]` | 派生 item 注解 | `#[1] A ∧ B` |

- **#0** = 要证明的定理（隐含，不写）
- **#[N]**（N≥1）= method 调用产生的 item（fact 或 subgoal）
- 命题有蕴含时，第一步必须是 `← intro goal=0` 显式拆分
- `fixes` 变量在上下文中，不需要 `#[N]`
- replay 时 `#[N]` 的 ID 用于引用映射，命题不验证

示例：
```
proof
  ← rule iffI goal=0
    #[1] A ∧ B ⟶ B ∧ A
    #[2] B ∧ A ⟶ A ∧ B
  ← intro goal=1
    #[3] A ∧ B
    #[4] B ∧ A
  ← rule conjI goal=4
    #[5] B
    #[6] A
  ← rule conjD2 goal=5 facts=[3]
  ← rule conjD1 goal=6 facts=[3]
qed
```

## 7. 自动搜索（前端 forward/backward-search）

搜索逻辑在前端触发、后端 `app/ide_v2.py` + `server/stable_state.py` 执行：

- `rule.search`：遍历所有带 `hint_backward`/`hint_backward1` 属性的定理，尝试 `rule().get_proof_term`，成功则记录子目标。另有精确匹配通道：全局模式网中整条命题匹配 goal 的定理一律作为 `rule` 建议。
- 双模式方法在搜索层同时贡献两种模式的结果，以 `target`/`source` 标记区分；正向搜索只保留 fact 模式结果。
- 自动闭合（显式）：每步应用后对新缺口按**匹配**（first_order_match + hyps 子集）查找先行证明行，命中则落 `close_by` 可见行；未命中尝试 `trivial` 策略，成功落 `trivial` 行。
- 每个方法按 `no_order` 属性决定是否对 `prevs` 做排列。
- 若有结果能"solves"（`_goal` 为空），只保留 solves 的结果。

## 8. loc 位置特定重写

`rewrite` 方法（goal 模式）支持 `loc` 参数，对目标的特定子位置重写：

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
当前仅 `intro`（`{'names'}`）与 `elim`（`{'names'}`）使用。
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

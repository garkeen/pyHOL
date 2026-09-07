# 宏系统与信任模型

> 代码事实以 `kernel/macro.py`、`kernel/theory.py`（宏注册部分）、`core/macros/core.py` 为准。

宏（Macro）是 holpy 的核心抽象之一，是"初等证明步骤的缩写"。本章讲宏的机制、信任级别、与校验的关系。

## 1. 为什么需要宏

原始推理规则（15 条原语）是逻辑的根基，但直接用原语写证明极为冗长。例如应用一次已证定理 `conjI`（`A ⟶ B ⟶ A ∧ B`）来证明 `A ∧ B`，需要：取定理 -> 匹配 -> 替换 -> 两次 `implies_elim`，共 4 步原语。

**宏**把这样的常见模式封装为一步。一次宏调用在 `export` 后的线性证明里作为一条 `ProofItem` 出现，但在 `check_proof` 时可**按需展开**为完整原语证明。这让存储的证明足够短，使系统可扩展到大型证明。

## 2. Macro 基类（kernel/macro.py）

```python
class Macro:
    level = None       # 信任级别（见 §4）
    sig = None         # 参数签名（用于 parse）
    limit = None       # 可用性闸门定理名（见 §5）

    def eval(self, args, prevs) -> Thm:
        """直接求值：返回宏的结果定理（不产生证明）。"""

    def get_proof_term(self, args, prevs) -> ProofTerm:
        """展开：返回完整的证明项。"""

    def expand(self, prefix, args, prevs) -> Proof:
        """展开为线性证明（默认实现：调 get_proof_term 后 export）。"""
```

`eval` 的默认实现：把 `prevs` 包成 `sorry`，调 `get_proof_term` 取 `th`。所以普通宏只需实现 `get_proof_term`。

`expand` 的默认实现：把 `prevs` 包成 `atom`，调 `get_proof_term` 后 `export(prefix)`。

## 3. 宏的两种校验方式

| 方式 | 行为 | 信任度 |
|---|---|---|
| **展开（expand）** | 校验时用 `get_proof_term` 展开成完整证明再查 | 最高（宏实现有 bug 必暴露） |
| **求值（eval）** | 直接调 `eval` 算出结论，不展开 | 较低（bug 可能漏检），但快得多 |

- **普通宏**（仅 `get_proof_term`）：永远展开，安全性最高。
- **可信宏**（额外提供 `eval` 与 `level`）：校验时按 `check_level` 决定展开还是求值。

## 4. 信任级别（level）

| level | 含义 | 行为 |
|---|---|---|
| `None`（未指定） | 永远展开 | 每次校验都走 `get_proof_term` |
| `0` | oracle / 不可展开 | `eval` 直接信任，通常无 `get_proof_term` 或不展开 |
| `1` | 标准宏 | 有完整 `get_proof_term`，可展开验证 |
| `10` | 领域计算 | 有 `get_proof_term`，但依赖某个 `limit` 定理存在 |

`check_proof(prf, check_level=N)`：`macro.level <= N` 的宏**不展开**，只调 `eval` 求值。`level > N` 或 `level is None` 的宏展开校验。

**实践含义**：`check_level=0` 时所有宏都展开（最严格）；`check_level=10` 时所有有 level 的宏都求值（最快，报告步数骤减）。

## 5. limit 字段

`limit` 是一个定理名字。`has_macro(name)` 在检查宏是否可用时，除了检查宏是否注册，还检查 `macro.limit is None or thy.has_theorem(macro.limit)`。

这用于领域宏依赖特定定理存在的场景。例如 `nat_norm` 宏的 `limit = 'nat_nat_power_def_1'`，只有当该定理已加载时宏才可用。

## 6. 宏的注册

```python
from kernel.theory import register_macro

@register_macro('my_macro')
class my_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        # args: 宏参数; pts: 输入证明项列表
        ...
        return pt  # ProofTerm
```

- `register_macro(name)` 是装饰器，把 `Macro` 实例存入 `global_macros` 字典。
- **幂等**：重复注册同一名字是 no-op（支持理论重载）。
- 注册时不检查 `limit`，只在 `has_macro` 时检查。

## 7. ProofTerm 如何调用宏

`ProofTerm(rule, args, prevs, th)` 构造时：
1. 若 `rule` 是 `atom`/`sorry`/`variable`/`theorem` 或在 `primitive_deriv` 中：走对应路径。
2. 否则查 `theory.get_macro(rule)`：
   - 若 `th` 已提供：直接用。
   - 否则调 `macro.eval(args, [prev.th for prev in prevs])` 算 `th`。

注意：`ProofTerm` 构造时**总是调 `eval`**（如果 `th` 未提供），即使宏会被展开校验。这是因为 `th` 需要立即用于后续构造，而校验是后续步骤。

## 8. 核心宏目录

注册在 `core/macros/core.py`。最常用的宏：

| 宏名 | sig | 功能 |
|---|---|---|
| `apply_theorem` | `str` | 应用定理（自动匹配实例化） |
| `apply_theorem_for` | `(str, Inst)` | 应用定理（显式实例化） |
| `apply_induct` | `(str, Term, Term)` | 应用归纳原理 |
| `apply_fact` | `None` | 前向应用 forall/implies 事实 |
| `apply_fact_for` | `List[Term]` | 前向应用（显式实例化） |
| `rewrite_goal` | `(str, Term)` | 用定理重写目标 |
| `rewrite_goal_sym` | `(str, Term)` | 用定理反向重写目标 |
| `rewrite_goal_with_prev` | `Term` | 用已有事实重写目标 |
| `rewrite_goal_with_prev_sym` | `Term` | 用已有事实反向重写 |
| `rewrite_fact` | `str` | 用定理重写事实 |
| `rewrite_fact_sym` | `str` | 用定理反向重写事实 |
| `rewrite_fact_with_prev` | `None` | 用一个事实重写另一个 |
| `intros` | `List[Term]` | 引入变量与假设 |
| `trivial` | `Term` | 目标已在假设中则关闭 |
| `forall_elim_gen` | `Term` | 通用全称消除 |
| `beta_norm` | `None` | β 归一化 |
| `resolve_theorem` | `(str, Term)` | 用 `~A` 定理 + 事实 `A` 证任意目标 |
| `resolution` | `None` | 消解两条析取子句 |
| `imp_conj` | `Term` | 蕴含合取（子集关系） |
| `imp_disj` | `Term` | 蕴含析取（子集关系） |

## 9. apply_theorem 详解

`apply_theorem` 是最常用的宏。它的 `get_proof_term` 流程：

1. 取定理 `th = theory.get_theorem(name)`。
2. 分解 `th.prop` 为 `(As, C)`（假设列表与结论）。
3. 对 `prevs`（输入证明项）与 `As` 做一阶匹配，得到 `inst`。
4. 检查所有类型变量已实例化。
5. `pt = ProofTerm.theorem(name).subst_type(inst.tyinst).substitution(inst)`。
6. 若定理非一阶模式，对 `pt` 做 `beta_norm`。
7. `pt.implies_elim(*pts)` 消除假设。
8. 对剩余未匹配的 schematic 变量做 `forall_intr`。

`apply_theorem_for` 多接受一个 `Inst`，用于匹配失败时手填实例化。

`core.logic.apply_theorem(th_name, *pts, concl=None, inst=None)` 是包装函数：无 `concl`/`inst` 时用 `apply_theorem` 宏，否则用 `apply_theorem_for`。

## 10. rewrite_goal 详解

`rewrite_goal_macro` 的 `get_proof_term` 流程：

1. 取等式定理 `eq_pt = ProofTerm.theorem(name)`。
2. 用 `rewr_conv(eq_pt, sym, conds)` 构造转换。
3. `cv = then_conv(top_sweep_conv(rewr_cv), beta_norm_conv())`。
4. `pt = cv.get_proof_term(goal)` 得到 `goal = new_goal` 的等式。
5. `pt = pt.symmetric()` 得 `new_goal = goal`... 实际是 `pt.equal_elim(pts[0])` 用 `pts[0]`（原目标的 sorry）消除。

## 11. 编写宏的范式

```python
@register_macro('my_macro')
class my_macro(Macro):
    def __init__(self):
        self.level = 1           # 可展开验证
        self.sig = Term          # 参数类型
        self.limit = None

    def eval(self, args, prevs):
        # 可选：若想成为可信宏，提供快速求值
        ...

    def get_proof_term(self, args, pts):
        # 必须返回 ProofTerm
        ...
```

要点：
- `get_proof_term` 是核心，必须返回合法的 `ProofTerm`。
- 若提供 `eval`，需保证 `eval` 的结果与 `get_proof_term` 的 `th` 一致。
- `sig` 用于 `.pyhol` 格式的参数解析。
- 宏内部可调用其他宏（通过 `ProofTerm(rule, ...)` 或 `apply_theorem`）。

## 12. 与 HOL Light 的对比

holpy 的宏系统是**自创**的，HOL Light 没有对应物：
- HOL Light 的"证明"是 OCaml 运行时的调用序列，不序列化为可重验对象。
- HOL Light 没有"宏/level/eval"这层。
- holpy 的宏服务于"证明可独立校验 + web IDE"的目标。

## 13. 信任模型总结

holpy 的"严肃性"来自：**一切最终可展开为 15 条原始规则 + 已证定理，且能独立重验**。

- 普通宏：永远展开，安全性最高。
- 可信宏：用效率换信任，`level` 控制。
- oracle（Z3 等）：不可展开，依赖外部求解器正确性--这是系统里唯一依赖外部工具的环节。
- 定义/归纳类型：经 `unchecked_extend` 直接信任，**不在此校验链内**（不查良基性）。

---

**下一章**：[`04_conv_matcher.md`](04_conv_matcher.md) -- 转换系统与匹配。

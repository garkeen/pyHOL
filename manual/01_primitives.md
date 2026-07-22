# 第一层：内核、证明项与宏

> 本手册依据作者编写的 `tutorial/` 系列笔记本（特别是 `proofterms.ipynb`、`macros.ipynb`）整理与校正。代码事实以 `kernel/` 与 `logic/macros/` 源码为准。

> **与 HOL Light 的对应关系及边界（阅读前请注意）**：holpy 是 HOL Light 的「后端内核 + 转换(conv) + 策略(tactic) + 原始推理规则」的**对应实现**——这三层在词汇、语义、组合子上与 HOL Light（`fusion.ml` / `equal.ml` / `tactics.ml`）逐项对应。但本手册里出现的 **宏(Macro)、信任级别(level/eval)、序列化证明项(ProofTerm)+check_proof、方法层(Method)** 这四类机制**全是 holpy 自己的发明，HOL Light 没有对应物**（HOL Light 的「证明」只是 OCaml 运行时的调用序列，不序列化为可重验对象，也没有宏 / level / 方法层）。此外，holpy 的「定义 / 归纳类型」走的是比 HOL Light **更宽松的信任模型**（直接当公理加入、不查良基性）。阅读时请区分「继承自 HOL Light」与「holpy 自创」两部分，不要默认为一一对应。

## 1. 整体架构与「为什么可信」

holpy 的逻辑内容只有三层，从下到上依次构建，且越往下越可信：

```
Thm（定理）= 前提 hyps + 结论 prop
  │   只能由「原始推理规则」构造（见 §3）
  ▼
ProofTerm（证明项）= Thm + 完整推导历史
  │   由原始规则 + 宏组合而成（见 §4、§5）
  ▼
Macro（宏）= get_proof_term + (可选) eval/level
      是「初等证明步骤的缩写」，可展开为原始步骤验证（见 §5）
```

> **来源标注**：图中「Thm / 原始推理规则」与「Conv(转换)」是 LCF 风格内核的标准组成，HOL Light 同样具备（其原始规则在 `fusion.ml` 的 8 个原语、转换在 `equal.ml`）。但「ProofTerm 序列化 + Macro + level」这一条组合链路是 holpy 为「证明可独立校验 + web IDE」而**自创**的——HOL Light 的 `goalstate.justification` 只是一个运行时函数、从不序列化存储，更没有宏 / level 这两样东西。

**信任的核心思想（作者原话）**：只要我们只通过一组**有限的、正确实现了 HOL 原始推理规则的函数**（`Thm.assume`、`Thm.implies_intr` 等，及其组合）来构造定理，就能信任证明。更进一步，把证明的**踪迹（trace）**存下来，就可以由同一程序或第三方程序独立校验——这正是 `Proof`（线性证明）与 `ProofTerm`（证明项）两种踪迹存在的原因。

- `ProofTerm` 不可变：每个方法返回**新的**证明项，不修改原对象。
- 任何 `ProofTerm` 都可通过 `.export()` 转成线性 `Proof`，再交给 `theory.check_proof` 校验。
- 校验会记录每一步用到的定理与原始规则数量（`ProofReport`），可用于审计。

## 2. 两种证明踪迹

| 踪迹 | 类 | 形态 | 用途 |
|------|----|------|------|
| 线性证明 | `kernel.proof.Proof` | 带编号的 `ProofItem` 列表（规则名 + 参数 + 前驱编号） | 可读、可打印、易校验 |
| 证明项 | `kernel.proofterm.ProofTerm` | 树状（根是结论，边是依赖） | 易自动生成、易组合 |

最小示例（来自 `proofterms.ipynb`）：

```python
# 线性证明：A -> A
A = Var("A", BoolType)
prf = Proof()
prf.add_item(0, "assume", args=A)            # 0. A |- A
prf.add_item(1, "implies_intr", args=A, prevs=[0])  # 1. |- A -> A
res = theory.check_proof(prf)

# 等价地，证明项
pt1 = ProofTerm.assume(A).implies_intr(A)
theory.check_proof(pt1.export())   # 同样得到 |- A -> A
```

> 注意：两者的「原始推理规则」是**同一组**（见 §3）。「证明项是用原语构造的定理 + 推导历史」这一视角，是理解 holpy 的关键。

## 3. 原始推理规则（Primitive deduction rules）

这些规则是**唯一能凭空构造 `Thm` 的入口**。它们都实现在 `kernel/thm.py`（以及 `kernel/primitive_deriv.py` 中组合出的派生规则），共 15 条。这一层是 LCF 内核的标准组成，**与 HOL Light 的 8 个原语（`fusion.ml:498-565`）精神一致、逐项对应**：

| # | 规则 | 签名 | 说明 |
|---|------|------|------|
| 1 | `assume` | `assume(A) → A |- A` | 把命题作为假设引入 |
| 2 | `implies_intr` | `implies_intr(A, th) → H\{A} |- A --> B` | 蕴含引入（A 不在 hyps 中则仍合法） |
| 3 | `implies_elim` | `implies_elim(th1, th2) → H1∪H2 |- B` | 假言推理（MP）；th1=`H1|-A-->B`, th2=`H2|-A` |
| 4 | `reflexive` | `reflexive(x) → |- x = x` | 自反 |
| 5 | `symmetric` | `symmetric(th) → H |- y = x` | 等式对称；th=`H|-x=y` |
| 6 | `transitive` | `transitive(th1, th2) → H1∪H2 |- x = z` | 等式传递 |
| 7 | `combination` | `combination(th1, th2) → H1∪H2 |- f x = g y` | 同余：`f=g`、`x=y` ⇒ `f x = g y` |
| 8 | `equal_intr` | `equal_intr(th1, th2) → H1∪H2 |- A = B` | 双向蕴含 ⇒ 等价 |
| 9 | `equal_elim` | `equal_elim(th1, th2) → H1∪H2 |- B` | `A=B` + `A` ⇒ `B` |
| 10 | `substitution` | `substitution(inst, th) → H[s] |- B[s]` | 同时替换项变量与类型变量（Inst） |
| 11 | `subst_type` | `subst_type(tyinst, th) → H[s] |- B[s]` | 仅替换类型变量（TyInst） |
| 12 | `beta_conv` | `beta_conv(t) → |- (%x. t1) t2 = t1[t2/x]` | β-归约（t 须为 beta-redex） |
| 13 | `abstraction` | `abstraction(x, th) → H |- (%x. t1) = (%x. t2)` | λ 抽象；x 不在 H 中自由出现 |
| 14 | `forall_intr` | `forall_intr(x, th) → H |- !x. t` | 全称引入；x 不在 H 中自由出现 |
| 15 | `forall_elim` | `forall_elim(s, th) → H |- t[s/x]` | 全称消除；s 类型须匹配绑定变量类型 |

> 调用这些规则时若前提不满足，会抛 `InvalidDerivationException`。`ProofTerm` 上有一一对应的方法（`pt.symmetric()`、`pt.transitive(pt2)`、`pt.combination(pt2)` 等），返回新的证明项。**注意**：holpy 的 `Thm(prop, *hyps)` 构造器本身**不强制**走原语（docstring 自承「应由原语构造，但本模块不强制」，见 §8），这一点比 HOL Light 的 `thm` 完全抽象类型更「放水」。

## 4. 证明项（ProofTerm）常用操作

| 操作 | 等价原语 | 说明 |
|------|----------|------|
| `ProofTerm.assume(A)` | `Thm.assume` | `A |- A` |
| `ProofTerm.reflexive(x)` | `Thm.reflexive` | `|- x = x` |
| `ProofTerm.theorem('name')` | 查表 | 取得已证定理，作为证明项起点 |
| `pt.implies_intr(A)` | `Thm.implies_intr` | 蕴含引入 |
| `pt.implies_elim(pt2)` | `Thm.implies_elim` | MP |
| `pt.symmetric()` / `pt.transitive(pt2)` | `Thm.symmetric/transitive` | 等式 |
| `pt.equal_intr(pt2)` / `pt.equal_elim(pt2)` | `Thm.equal_intr/equal_elim` | 等价 |
| `pt.substitution(inst)` / `pt.subst_type(tyinst)` | `Thm.substitution/subst_type` | 替换 |
| `pt.forall_intr(x)` / `pt.forall_elim(s)` | `Thm.forall_intr/forall_elim` | 量词 |
| `pt.abstraction(x)` / `pt.combination(pt2)` | `Thm.abstraction/combination` | λ / 同余 |
| `pt.on_prop(*convs)` / `pt.on_rhs(*convs)` / `pt.on_lhs(*convs)` | 转换应用 | 对命题/右端/左端套用转换 |
| `pt.tac(t)` / `pt.tacs(*ts)` | 策略应用 | 对首个 gap / 依次对 gap 应用策略（见 manual 02） |
| `pt.export()` | — | 导出为线性 `Proof` |

`ProofTerm.theorem` 是引入外部已证结果的唯一正规途径；例：`ProofTerm.theorem('add_assoc').substitution(x=a, y=b, z=nat.one)`。

## 5. 宏（Macro）——「初等证明步骤的缩写」

> **holpy 自创**：HOL Light **没有**「宏」这一层。`hol-light` 源码里唯一的 "macro" 字样来自 camlp5 预处理器（`pa_j/pa_macro.cmo`），与「证明步骤缩写」无关。holpy 的「宏 = 可展开缩写 + level/eval 可信宏」完全是自己的设计，服务于 web IDE 与「证明可独立校验」的目标。

**定义（作者原话）**：宏是「充当更初等证明步骤缩写」的推理规则。在线性证明和证明项里，一次宏调用可替代多步证明；宏调用在校验时可**按需展开**。这让存储的证明足够短，使系统可扩展到大型证明。

### 标准写法

```python
from kernel.proofterm import ProofTerm
from logic.macros.core import register_macro, Macro

@register_macro('apply_theorem')   # 实际宏还分 apply_theorem / apply_theorem_for
class apply_theorem(Macro):
    def __init__(self):
        self.level = 10           # 见 §6
        self.sig = ...
    def get_proof_term(self, args, prevs):
        # 接收输入证明项 prevs + 参数 args，返回组合出的 ProofTerm
        ...
```

- `get_proof_term(args, prevs)` 是核心：合法时返回结果证明项，不合法时抛异常。
- 一次宏调用在 `export()` 后的线性证明里会原样出现（如 `apply_theorem` 作为一条 proof item）。

### 宏的两类校验方式

| 方式 | 行为 | 信任度 |
|------|------|--------|
| **展开（expand）** | 校验时用 `get_proof_term` 展开成完整原始证明再查 | 最高（宏实现有 bug 必暴露） |
| **求值（evaluate）** | 宏额外提供 `eval(args, prevs)` 与 `level` 字段，直接算出结论而不展开 | 较低（bug 可能漏检），但快得多 |

**可信宏（trusted macros）**：提供 `level` 和 `eval` 的宏即为可信宏。校验时传 `check_level` 参数——`level <= check_level` 的宏**不展开**，只求值。例：`check_proof(prf, check_level=10)` 会让 level≤10 的宏只求值，报告步数骤减且不再显示内部定理调用。

> 实践含义：普通宏（仅 `get_proof_term`）永远展开，安全性最高；可信宏（有 `eval`）用效率换信任。**holpy 的「严肃性」来自「一切最终可展开为 15 条原始规则 + 已证定理」，而非来自某个不可置疑的黑盒。**

### 核心宏速查（`logic/macros/core.py` 等）

| 宏名 | 功能 | 备注 |
|------|------|------|
| `apply_theorem` / `apply_theorem_for` | 应用定理（自动/显式实例化） | 最常用；`for` 版用于匹配失败需手填实例化 |
| `apply_induct` | 应用归纳原理 | 结构归纳 |
| `apply_fact` / `apply_fact_for` | 前向应用 forall/implies 事实 | |
| `rewrite_goal` / `rewrite_goal_sym` | 用定理重写目标（正/反向） | |
| `rewrite_goal_with_prev` / `_sym` | 用已有事实重写目标 | |
| `rewrite_fact` / `rewrite_fact_with_prev` | 重写事实 | |
| `intros` | 引入变量与假设 | |
| `trivial` | 目标已在假设中则直接关闭 | |
| `resolve_theorem` / `resolution` | 消解 | |
| `imp_conj` / `imp_disj` | 蕴含合取/析取 | |
| `forall_elim_gen` | 通用全称消除 | |
| `beta_norm` | β 归一化（返回定理） | |
| `nat_norm` / `nat_eval` 等 | 算术归一化/求值（领域宏） | level 多为 0/10 |
| `z3` | 调用 Z3 求解器（**oracle**，level 0） | 不可展开，靠外部信任 |
| `auto` | 自动证明（solve + norm） | |

> 领域相关的算术、整数、实数宏分散在 `logic/conv/*` 与对应 macro 文件中，详见 manual 02/03。

## 6. 信任级别（level）

> **holpy 自创**：HOL Light 没有「信任级别 / eval」这一概念。level 是 holpy 为「可信宏可跳过展开、换取效率」而引入的工程装置。

| level | 含义 | 行为 |
|-------|------|------|
| 未指定 | 永远展开 | 每次校验都走 `get_proof_term` |
| 0 | oracle / 不可展开 | `eval` 直接信任，通常无 `get_proof_term` 或不展开（如 `z3`、`*_eval`） |
| 1 | 标准宏 | 有完整 proof term，可展开验证 |
| 10 | 领域计算 | 有 proof term，但依赖某个 `limit` 定理存在（如 `nat_norm` 依赖 `nat_nat_power_def_1`） |

## 7. Theory 数据（`theory.thy.data`）

```python
theory.thy.data['type_sig']     # {name: arity}
theory.thy.data['term_sig']     # {name: Type}
theory.thy.data['theorems']     # {name: Thm}     已证定理表（ProofTerm.theorem 的来源）
theory.thy.data['attributes']   # {name: (attr, ...)}   定理属性（hint_rewrite 等）
theory.thy.data['overload']     # {name: True}   重载常量
theory.thy.data['thm_status']   # {name: status} 证明状态
```

## 8. 信任模型与设计边界（关键，易与 HOL Light 混淆）

holpy 在「定义 / 归纳类型如何进入理论」这一点上，较 HOL Light **不强制一致性保证**：

- **定义（fun / def）是公理式断言，不查良基性。** 加载 `.pyhol` 时，`Fun` / `Definition` 经 `theory.unchecked_extend`（`kernel/theory.py:483`，注释 "without proof checking"）直接加入一条 `Theorem(name, Thm(prop))`，`prf=None` 即当作公理。`Fun` 的文档字符串只写 "must be clearly terminating"——这是给用户的**约定 / 警告**，不是机械检查。对比 HOL Light：通用递归 `define` 强制要求 `WF(<<)` 证明（良基性检查的具体实现位置），结构递归 `new_recursive_definition` 借归纳类型的 `*_RECURSION` 定理预制证据免去手写 WF。holpy 两条路径都省略了。

- **归纳类型（Datatype）只产 `_induct`，不产 `_RECURSION`。** `Datatype` 把 distinct / inject / `*_induct` 全部当作 `Thm(prop)` 直接断言（公理式），且**不生成递归定理**（grep 全库无任何 `*_RECURSION` 生成或 `define_recursive` 对应物）。对比 HOL Light 的 `define_type`：它**证明**生成 `list_RECURSION` + `list_INDUCT` 这对保守扩展，结构递归才能免 WF。holpy 未提供该预制证据。

- **`Thm` 构造器本身不强制走原语。** `kernel/thm.py` 的 docstring 自承「应由原语构造，但本模块不强制，也不存证明对象」；你可以 `Thm(prop)` 凭空造定理。原语方法（`transitive` / `combination` / `implies_elim` …）仍做机械校验，但**绕过原语直接 `Thm(...)` 即可伪造**。对比 HOL Light：`thm` 是完全抽象类型，外部连 `Sequent(...)` 都看不见，只能经 8 原语 + 两个信任入口产生。

- **`check_proof` 是「可选信任」，不是强制。** 真正校验逻辑在 `check_proof`（`kernel/theory.py:436`）：① 原语步骤（在 `primitive_deriv` 中）**真校验**；② 宏按 `level <= check_level` 决定「信任跳过(eval) 还是展开校验」；③ `sorry` 造成的 gap 默认放行（`no_gaps=False`）。而生产路径的 `unchecked_extend` 连 `check_proof` 都不调——定义 / 公理直接信任。（注：`checked_extend` 实现了「有 prf 则 check_proof、无则当公理」的逻辑，但**生产路径不使用**，仅在 `kernel/tests` 中调用。）HOL Light 没有 `check_proof` 概念（其内核原语在 OCaml 中直接执行、证明即运行时调用序列）。

**结论**：holpy 的「严肃性」来自「证明最终可展开为 15 条原始规则 + 已证定理，且能独立重验」，不来自「定义被强制保证一致」。定义 / 归纳类型的一致性，由 `unchecked_extend` 信任加载器与用户自律（递归必须明显终止）保证；内核层不提供等价 HOL Light 的保守扩展保证（`define` 的良基性检查、`define_type` 的 `*_RECURSION` 预制）。

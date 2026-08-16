# 内核：类型、项、定理与原语

> 代码事实以 `kernel/` 目录为准。本章覆盖 `kernel/type.py`、`kernel/term.py`、`kernel/thm.py`、`kernel/proof.py`、`kernel/proofterm.py`、`kernel/theory.py`、`kernel/report.py`、`kernel/extension.py`。

逻辑理论见 [`01_hol_logic.md`](01_hol_logic.md)。本章讲 holpy 如何用 Python 实现。

## 1. 类型（kernel/type.py）

### 1.1 类层次

```
Type
├── STVar(name)              schematic 类型变量，打印 ?'a
├── TVar(name)               类型变量，打印 'a
└── TConst(name, *args)      类型构造器，args 为参数元组
```

`Type(arg)` 构造器：若 `arg` 已是 `Type` 则直接复制；若是字符串则调 `type_parser`（默认在 `syntax/parser.py` 中设置）。

### 1.2 预定义类型

| 名字 | 含义 |
|---|---|
| `BoolType` | `TConst("bool")` |
| `NatType` | `TConst("nat")` |
| `IntType` | `TConst("int")` |
| `RealType` | `TConst("real")` |

`TFun(*args)`：构造函数类型 `arg₁ ⇒ arg₂ ⇒ … ⇒ argₙ`（右结合）。

### 1.3 常用方法

| 方法 | 说明 |
|---|---|
| `is_stvar()` / `is_tvar()` / `is_tconst()` | 类型判断 |
| `is_fun()` | 是否函数类型 |
| `domain_type()` / `range_type()` | `A ⇒ B` 取 `A` / `B` |
| `strip_type()` | `A₁⇒…⇒Aₙ⇒B` 返回 `([A₁,…,Aₙ], B)` |
| `subst(tyinst)` | 按 `TyInst` 替换 schematic 类型变量 |
| `match(T)` / `match_incr(T, tyinst)` | 匹配，返回/累积 `TyInst` |
| `get_stvars()` / `get_tvars()` | 收集 schematic/普通类型变量 |

`TyInst` 是 `UserDict`，键为类型变量名，值为 `Type`。

## 2. 项（kernel/term.py）

### 2.1 六种项构造器

| 构造器 | 字段 | 说明 |
|---|---|---|
| `SVar(name, T)` | `name`, `T`, `_id` | schematic 变量，打印 `?name` |
| `Var(name, T)` | `name`, `T`, `_id` | 变量 |
| `Const(name, T)` | `name`, `T`, `_id` | 常量 |
| `Comb(fun, arg)` | `fun`, `arg`, `_id` | 函数应用 |
| `Abs(var_name, var_T, body)` | `var_name`, `var_T`, `body`, `_id` | λ 抽象（`var_name` 仅建议名） |
| `Bound(n)` | `n`, `_id` | de Bruijn 索引 |

每个项有 `_id = id(self)`，用于快速同一性比较与缓存。

### 2.2 相等与哈希

- `__eq__` 按 α-等价比较（忽略 `var_name`，比较 `var_T` 与 `body`）。
- `__hash__` 对 `CONJ`/`DISJ`/`LET` 链有专门优化（避免重复计算）。
- `__copy__` 深拷贝（类型共享）。

### 2.3 类型获取

| 方法 | 说明 |
|---|---|
| `get_type()` | 轻量类型获取（不做完整类型检查） |
| `checked_get_type()` | 完整类型检查，失败抛 `TypeCheckException` |
| `is_open()` | 是否含未绑定的 `Bound` |

### 2.4 函数应用与解构

| 方法/属性 | 说明 |
|---|---|
| `t(arg1, arg2, ...)` | `__call__`，构造 `Comb(Comb(t, arg1), arg2)` |
| `strip_comb()` | `f t₁…tₙ` 返回 `(f, [t₁,…,tₙ])` |
| `head` | 取 `f` |
| `args` | 取 `[t₁,…,tₙ]` |
| `arg1` | 二元运算的左参数（`f a b` 中的 `a`） |
| `arg` | 二元运算的右参数（`f a b` 中的 `b`） |
| `lhs` / `rhs` | 等式的左/右（要求 `is_equals()`） |

### 2.5 逻辑连接词识别

| 方法 | 识别的常量 |
|---|---|
| `is_implies()` | `implies`（2 参数） |
| `is_conj()` / `is_disj()` | `conj` / `disj`（2 参数） |
| `is_not()` | `neg`（1 参数） |
| `is_forall()` / `is_exists()` | `all` / `exists`（1 参数） |
| `is_equals()` | `equals`（2 参数） |
| `is_less()` / `is_less_eq()` / `is_greater()` / `is_greater_eq()` | 比较运算 |
| `is_let()` | `Let`（2 参数） |

`strip_implies()`：`s₁ ⟶ … ⟶ sₙ ⟶ t` 返回 `([s₁,…,sₙ], t)`。
`strip_forall()` / `strip_exists()` / `strip_quant()`：剥离量词。

### 2.6 替换与 β-变换

| 方法 | 说明 |
|---|---|
| `subst_type(tyinst)` | 替换类型变量 |
| `subst(inst)` | 替换项变量（`Inst`，先匹配类型再替换） |
| `incr_boundvars(inc)` | 提升松散 bound 变量 |
| `subst_bound(t)` | `Abs` 的 body 中用 `t` 替换 `Bound(0)`（β-变换的核心） |
| `beta_conv()` | `(λx. t₁) t₂` -> `t₁[t₂/x]` |
| `beta_norm()` | 完全 β-归一化 |
| `subst_norm(inst)` | `subst` + `beta_norm` |
| `abstract_over(t)` | 把 `t` 在 self 中替换为 `Bound`（`Lambda` 的辅助） |

`Inst` 含三层：`tyinst`（类型）、`var_inst`（普通变量）、`abs_name_inst`（绑定变量改名）。

### 2.7 数字与算术

二进制表示：`zero`、`one`、`bit0`、`bit1` 四个常量。`Binary(n)` 把 Python 整数转为二进制项（不套 `of_nat`）。`Number(T, x)` 按类型 `T` 构造数字项（套 `of_nat`、处理分数与负数）。

`Nat(n)` / `Int(n)` / `Real(r)` 是 `Number` 的类型特化。

运算符重载：`__add__`/`__sub__`/`__mul__`/`__truediv__`/`__neg__`/`__pow__`/`__le__`/`__lt__` 等，自动按 `get_type()` 选择常量类型，Python 数字自动提升为项。

### 2.8 预定义常量

`true`、`false`、`neg`、`conj`、`disj`、`implies`、`equals(T)`、`forall(T)`、`exists(T)`、`plus(T)`、`minus(T)`、`times(T)`、`less(T)` 等，以及辅助构造函数 `Eq`、`Not`、`And`、`Or`、`Implies`、`Lambda`、`Forall`、`Exists`、`Let`。

## 3. 定理（kernel/thm.py）

### 3.1 Thm 类

```python
class Thm:
    prop: Term          # 命题
    hyps: Tuple[Term]   # 假设（元组，视为集合）
```

构造器 `Thm(prop, *hyps)`：`hyps` 中每项可为 `Term` 或 `tuple`，自动去重。

- `assums` / `concl`：从 `prop` 用 `strip_implies` 取假设列表与结论。
- `lhs` / `rhs`：结论为等式时的左右。
- `__eq__`：`set(hyps)` 相同且 `prop` 相同。
- `can_prove(target)`：`prop` 相同且 `set(hyps) ⊆ set(target.hyps)`（**子集语义**，关键）。
- `check_thm_type()`：校验所有 hyps 与 prop 类型为 `bool`。

### 3.2 15 条原始推理规则

全部为 `Thm` 的 `@staticmethod`。参数不合法时抛 `InvalidDerivationException`。

| # | 规则 | 签名 | 说明 |
|---|---|---|---|
| 1 | `assume(A)` | `Term -> Thm` | `A ⊢ A` |
| 2 | `implies_intr(A, th)` | `Term, Thm -> Thm` | `th` 去掉 `A` 得 `⊢ A ⟶ th.concl` |
| 3 | `implies_elim(th1, th2)` | `Thm, Thm -> Thm` | MP：`th1=A⟶B`, `th2=A` 得 `B` |
| 4 | `reflexive(x)` | `Term -> Thm` | `⊢ x = x` |
| 5 | `symmetric(th)` | `Thm -> Thm` | `x=y` 得 `y=x` |
| 6 | `transitive(th1, th2)` | `Thm, Thm -> Thm` | `x=y`, `y=z` 得 `x=z` |
| 7 | `combination(th1, th2)` | `Thm, Thm -> Thm` | `f=g`, `x=y` 得 `f x = g y` |
| 8 | `equal_intr(th1, th2)` | `Thm, Thm -> Thm` | `A⟶B`, `B⟶A` 得 `A=B` |
| 9 | `equal_elim(th1, th2)` | `Thm, Thm -> Thm` | `A=B`, `A` 得 `B` |
| 10 | `subst_type(tyinst, th)` | `TyInst, Thm -> Thm` | 类型变量替换 |
| 11 | `substitution(inst, th)` | `Inst, Thm -> Thm` | 项变量替换 |
| 12 | `beta_conv(t)` | `Term -> Thm` | `⊢ (λx.t₁) t₂ = t₁[t₂/x]` |
| 13 | `abstraction(x, th)` | `Term, Thm -> Thm` | `t₁=t₂` 得 `(λx.t₁)=(λx.t₂)`，`x` 不在 hyps |
| 14 | `forall_intr(x, th)` | `Term, Thm -> Thm` | 得 `∀x. th.concl`，`x` 不在 hyps |
| 15 | `forall_elim(s, th)` | `Term, Thm -> Thm` | `∀x.t` 得 `t[s/x]` |

`primitive_deriv` 字典：规则名 -> `(函数, 参数签名)`，用于 `check_proof` 分发。

### 3.3 其他 Thm 方法

- `mk_VAR(v)`：构造内部命题 `_VAR(v)`（用于声明变量）。
- `convert_svar(th)`：把 `Var` 转为 `SVar`（用于定理的 schematic 版本）。

## 4. 线性证明（kernel/proof.py）

### 4.1 ItemID

`ItemID` 表示证明项的层级编号，如 `"1.2.0"` -> `(1, 2, 0)`。支持：

- `incr_id_after(start, n)`：在 `start` 前插入 `n` 行时的编号调整。
- `decr_id(id_remove)`：删除一行时的编号调整。
- `can_depend_on(other)`：当前项能否依赖 `other`（同一父级且编号更大）。

### 4.2 ProofItem

```python
class ProofItem:
    id: ItemID
    rule: str           # 规则名（原语名/宏名/theorem/sorry/variable/空串）
    args                # 规则参数
    prevs: List[ItemID] # 输入 sequent 的编号
    th: Optional[Thm]   # 该步得到的定理（校验时填充或检查）
    subproof: Optional[Proof]  # 展开宏时的子证明
```

### 4.3 Proof

```python
class Proof:
    items: List[ProofItem]
```

- `Proof(*assums)`：初始化时为每个假设生成一条 `assume` 项。
- `add_item(id, rule, args=, prevs=, th=)`：追加。
- `find_item(id)`：按 `ItemID` 查找（支持跨层）。
- `insert_item(item)`：按 `item.id` 插入到正确位置。
- `get_sorrys()`：返回所有 `sorry` gap。

## 5. 证明项（kernel/proofterm.py）

### 5.1 ProofTerm

```python
class ProofTerm:
    rule: str
    args
    prevs: List[ProofTerm]
    th: Thm
    gaps: List[Thm]      # 证明中的 sorry 列表
    checked: bool
```

构造器 `ProofTerm(rule, args, prevs, th)`：
- `rule == 'atom'`：直接用 `th`（用于引用已有证明项）。
- `rule == 'sorry'`：`th` 为 gap，`gaps = [th]`。
- `rule == 'variable'`：声明变量，`th = Thm.mk_VAR`。
- `rule == 'theorem'`：从 `theory.get_theorem(args)` 取。
- `rule in primitive_deriv`：调原语函数算 `th`。
- 否则：调宏的 `eval` 或 `get_proof_term` 算 `th`。

**不可变**：所有组合方法返回新 `ProofTerm`。

### 5.2 原语对应方法

`ProofTerm` 上有与 15 原语一一对应的方法：`assume`/`reflexive`/`theorem`/`sorry`（静态）、`symmetric`/`transitive`/`combination`/`equal_intr`/`equal_elim`/`implies_intr`/`implies_elim`/`subst_type`/`substitution`/`abstraction`/`forall_intr`/`forall_elim`/`beta_conv`。

`transitive` 和 `implies_elim` 支持多参数链式调用。`equal_elim`/`transitive` 遇到 reflexivity 会自动跳过。

### 5.3 转换应用 API

| 方法 | 作用 |
|---|---|
| `on_prop(*cvs)` | 对 `th.prop` 依次应用 conv |
| `on_arg(*cvs)` | 对 `th.prop.arg` 应用 |
| `on_lhs(*cvs)` | 对等式左端应用 |
| `on_rhs(*cvs)` | 对等式右端应用 |

### 5.4 策略应用 API

| 方法 | 作用 |
|---|---|
| `tac(tactic)` | 对首个 gap 应用策略 |
| `tacs(*tactics)` | 依次应用多个策略 |

### 5.5 export

`export(prefix=None, prf=None, subproof=True)`：把 ProofTerm 树转为线性 `Proof`。用 `seq_to_id` 字典去重（相同 `th` 只导出一次）。

### 5.6 check

`check(check_level=0, rpt=None)`：递归展开宏校验。`rpt` 为 `ProofReport`。

## 6. 理论（kernel/theory.py）

### 6.1 Theory 类

```python
class Theory:
    data: dict   # 七张表（见下）
```

七张表：

| 键 | 值 | 说明 |
|---|---|---|
| `type_sig` | `{name: arity}` | 类型构造器的元数 |
| `term_sig` | `{name: Type}` | 常量的最一般类型 |
| `theorems` | `{name: Thm}` | 已证定理（`Var` 版） |
| `theorems_svar` | `{name: Thm}` | 已证定理（`SVar` 版，缓存） |
| `attributes` | `{name: (attr,...)}` | 定理属性 |
| `overload` | `{name: True}` | 重载常量 |
| `thm_status` | `{name: status}` | 证明状态 |

### 6.2 全局单例

`thy` 是全局 `Theory` 单例。`EmptyTheory()` 创建含 `bool`/`fun` 类型与 `equals`/`implies`/`all` 常量的最小理论。`fresh_theory()` 是上下文管理器，保存恢复 `thy`。

### 6.3 关键方法

| 方法 | 说明 |
|---|---|
| `check_type(T)` / `check_term(t)` | 良构性检查 |
| `check_proof(prf, rpt, no_gaps, compute_only, check_level)` | 校验线性证明 |
| `unchecked_extend(exts)` | 不校验地扩展（生产路径） |
| `checked_extend(exts)` | 校验地扩展（仅测试用） |
| `get_theorem(name, svar=True)` | 取定理（默认返回 SVar 版） |
| `get_overload_const_name(name, T)` | 重载常量的展开名 |

### 6.4 check_proof 流程

对 `Proof` 中每个 `ProofItem`：
1. `rule == ""`：空行，跳过。
2. `rule == "sorry"`：gap，记入 report（除非 `no_gaps`）。
3. `rule == "theorem"`：从理论取定理。
4. `rule == "variable"`：声明变量。
5. `rule in primitive_deriv`：调原语函数，真校验。
6. 否则为宏：若 `macro.level <= check_level` 则调 `eval` 求值（信任跳过）；否则调 `expand` 展开为子证明递归校验。

最后检查 `res_th.can_prove(seq.th)`（子集语义）与 `check_thm_type`。

## 7. 宏的注册与查找（kernel/theory.py + kernel/macro.py）

`global_macros` 字典：宏名 -> `Macro` 实例。

- `register_macro(name)`：装饰器，注册宏类（幂等，支持重载）。
- `has_macro(name)`：宏存在且其 `limit` 定理已在理论中。
- `get_macro(name)`：取宏实例。

宏的 `level`/`sig`/`limit` 字段见 [`03_macro.md`](03_macro.md)。

## 8. 扩展（kernel/extension.py）

五种 `Extension`：

| 类 | 说明 |
|---|---|
| `TConst(name, arity)` | 添加类型构造器 |
| `Constant(name, T, ref_name=)` | 添加常量（`ref_name` 为重载展开名） |
| `Theorem(name, th, prf=None)` | 添加定理（`prf=None` 为公理） |
| `Attribute(name, attribute)` | 给定理加属性 |
| `Overload(name)` | 标记常量为可重载 |

`unchecked_extend` 遍历 `exts`，按类型分发到 `extend_type`/`extend_constant`/`add_theorem` 等。

## 9. 报告（kernel/report.py）

### 9.1 ProofReport

| 字段 | 说明 |
|---|---|
| `steps` | 总步数 |
| `thm_steps` | 调用已有定理的次数 |
| `prim_steps` | 原语步数 |
| `macro_steps` | 宏步数 |
| `th_names` | 用到的定理名集合 |
| `macros_eval` / `macros_expand` | 求值/展开的宏名集合 |
| `gaps` | sorry 列表 |

### 9.2 ExtensionReport

记录 `checked_extend` 时添加的公理列表。

## 10. 项序（kernel/term_ord.py）

`fast_compare(t1, t2)` / `fast_compare_typ(T1, T2)`：先按 size、再按 ty、再按结构的字典序比较。用于多项式归一化等需要对项排序的场景。

## 11. 信任模型要点

1. **15 原语是唯一凭空构造定理的入口**，但 `Thm` 构造器本身不强制走原语（比 HOL Light 的抽象 `thm` 类型宽松）。
2. **`check_proof` 是可选的**：生产路径 `unchecked_extend` 不校验，直接信任定义与公理。
3. **定义合法性检查**：`Fun`（`def.ind`）须通过**结构递归**检查（恰一个构造器模式参数、递归调用限于模式子项），`Datatype`（`type.ind`）须通过**严格正性**检查（类型不出现于函数定义域、不嵌套于其他归纳类型），否则解析失败拒收。通过检查的等式/类型必存在实现/模型，作为公理加入是一致的。`Definition` 与其他显式公理直接信任。
4. **宏的信任级别**：普通宏永远展开（最可信）；可信宏（带 `level`+`eval`）可跳过展开换效率；oracle（如 Z3，level 0）不可展开，依赖外部求解器。
5. **证明可独立重验**：任何 `ProofTerm` 可 `export` 为线性 `Proof`，由 `check_proof` 独立校验。

---

**下一章**：[`03_macro.md`](03_macro.md) -- 宏系统的详细机制与信任级别。

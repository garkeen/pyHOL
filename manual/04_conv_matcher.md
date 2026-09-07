# 转换与匹配

> 代码事实以 `core/conv/core.py`（转换）、`core/matcher.py`（匹配）、`kernel/term.py`（替换）为准。

转换（Conversion）与匹配（Matching）是自动化的基础设施。转换做"等价变换"，匹配做"模式实例化"。

## 1. 转换（Conv）

### 1.1 定义

**转换**是一个函数：输入项 `t`，返回定理 `|- t = t'`（即把 `t` 重写为等价的 `t'`）。

```python
class Conv:
    def eval(self, t: Term) -> Thm:
        return self.get_proof_term(t).th

    def get_proof_term(self, t: Term) -> ProofTerm:
        raise NotImplementedError
```

转换与宏的关系：转换是"参数为单个项、无输入证明项"的宏。因其有良好的组合性质，单独抽象为 `Conv` 类。

### 1.2 基础转换

| 转换 | 说明 |
|---|---|
| `all_conv()` | 恒等：`refl(t)`，返回 `|- t = t` |
| `no_conv()` | 总是失败：`raise ConvException` |
| `beta_conv()` | 单步 β 归约：`|- (λx. t₁) t₂ = t₁[t₂/x]` |
| `beta_norm_conv()` | 完全 β 归一化 |
| `eta_conv(thm_name='eta_conversion')` | Eta：`|- (λx. f x) = f` |

### 1.3 组合子

组合子是"接受一个或多个 conv，返回新 conv"的函数：

| 组合子 | 说明 |
|---|---|
| `then_conv(cv1, cv2)` | 先 cv1 再 cv2（`t = t1 = t2`） |
| `else_conv(cv1, cv2)` | cv1 失败则 cv2 |
| `try_conv(cv)` | cv 或恒等（`else_conv(cv, all_conv())`） |
| `combination_conv(cv1, cv2)` | 对 `f a` 的 f 用 cv1、a 用 cv2 |
| `comb_conv(cv)` | 对函数与参数都用 cv（`combination_conv(cv, cv)`） |
| `arg_conv(cv)` | 只转换参数（右）：`combination_conv(all_conv(), cv)` |
| `fun_conv(cv)` | 只转换函数（左）：`combination_conv(cv, all_conv())` |
| `arg1_conv(cv)` | 转换第一个参数：`fun_conv(arg_conv(cv))` |
| `binop_conv(cv)` | 转换二元运算的两个参数：`combination_conv(arg_conv(cv), cv)` |
| `argn_conv(n, cv)` | 转换第 n 个参数（从 0 数） |
| `every_conv(*cvs)` | 依次应用（`then_conv` 的多参数版） |
| `repeat_conv(cv)` | 重复直到失败 |
| `abs_conv(cv)` | 进入 λ 体：`|- (λx. body) = (λx. body')` |
| `assums_conv(cv)` | 对 `A₁ ⟶ … ⟶ Aₙ ⟶ C` 的每个 `Aᵢ` 应用 cv |
| `sub_conv(cv)` | 对直接子项（comb 或 abs）应用 |

### 1.4 遍历语义

三个关键遍历组合子，区别在顺序：

| 转换 | 顺序 | 语义 |
|---|---|---|
| `top_conv(*cvs)` | 先 t 后子项（top-down，重复） | 先对 t 应用 cv，再递归子项。若 cv 作用后产生的新项还能被 cv 作用，会在一遍内继续 |
| `top_sweep_conv(cv)` | 自顶向下，命中即停 | 对 t 应用 cv，**成功则停**（不再递归子项）；失败才递归子项。ONCE 语义 |
| `bottom_conv(cv)` | 先子项后 t（bottom-up） | 先递归子项，再对 t 应用 cv |

**`top_conv` 的"先 t 后子项"顺序关键**：应用 cv 于 t 产生新项后，若新项的子项还能被 cv 作用，会在同一遍内继续。例如分配律 `a·((b+c)+d)`：先对整个项应用分配律得 `a·(b+c) + a·d`，再递归发现 `a·(b+c)` 还可分配，一遍到位得 `(a·b + a·c) + a·d`。

### 1.5 rewr_conv

`rewr_conv` 是最核心的转换：用等式定理重写项。

```python
rewr_conv(pt, *, sym=False, conds=None)
```

- `pt`：等式定理名（`str`）或 `ProofTerm`。
- `sym`：`False` 从左到右（匹配 lhs），`True` 从右到左（匹配 rhs）。
- `conds`：条件列表（`ProofTerm`），匹配等式定理的假设。

工作流程：
1. 取等式定理，分解为 `(As, C)`。`C` 须为等式。
2. 匹配 `As` 与 `conds` 的命题，匹配 `C.lhs`（或 `C.rhs` 若 `sym`）与 `t`。
3. 检查所有 schematic 变量已实例化。
4. 实例化等式定理，`implies_elim` 消除条件，`symmetric` 若 `sym`。
5. 若非一阶模式，做 `beta_norm`。
6. 若 lhs 不精确匹配 t，尝试 `eta_conv`。

### 1.6 has_rewrite

`has_rewrite(th, t, *, sym=False, conds=None)`：预检查 th 能否在 t 的某个子项上重写。用于 `simp` 等方法决定是否建议重写。

### 1.7 replace_conv

`replace_conv(pt)`：直接用已有 `pt`（`|- lhs = rhs`）替换，要求 `t == pt.prop.lhs`。不做匹配。

### 1.8 ProofTerm 式 API

除了函数式组合，`ProofTerm` 提供命令式 API：

| 方法 | 作用 |
|---|---|
| `pt.on_prop(*cvs)` | 对 `pt.th.prop` 依次应用 cv，用 `equal_elim` 传递 |
| `pt.on_arg(*cvs)` | 对 `pt.th.prop.arg` 应用 |
| `pt.on_lhs(*cvs)` | 对等式左端应用（`symmetric + transitive`） |
| `pt.on_rhs(*cvs)` | 对等式右端应用（`transitive`） |

**不可变**：这些方法返回新 `ProofTerm`，不修改原对象。

示例：重写 `(a+b)+c` 到 `(a+c)+b`：
```python
# swap: (a+b)+c = a+(b+c) = a+(c+b) = (a+c)+b
pt = refl(t).on_rhs(
    rewr_conv('add_assoc'),
    arg_conv(rewr_conv('add_comm')),
    rewr_conv('add_assoc', sym=True),
)
```

### 1.9 领域转换

算术归一化等转换分散在 `theories/{nat,integer,real,function,logic}/conv.py`。这些是领域相关的，见 [`07_system.md`](07_system.md)。

## 2. 匹配（Matcher）

### 2.1 Inst 与 TyInst

`Inst` 是替换的载体，含三层：

| 字段 | 键 | 值 | 说明 |
|---|---|---|---|
| `self`（dict 主体） | schematic 变量名 | `Term` | schematic 变量的实例化 |
| `tyinst` | schematic 类型变量名 | `Type` | 类型变量的实例化 |
| `var_inst` | 普通变量名 | `Term` | 普通变量的实例化 |
| `abs_name_inst` | 绑定变量建议名 | 新建议名 | 匹配 abstraction 时的改名 |

`TyInst` 是 `UserDict`，键为类型变量名，值为 `Type`。

### 2.2 替换

| 方法 | 说明 |
|---|---|
| `Term.subst_type(tyinst)` | 替换类型变量（只影响 `T` 字段） |
| `Term.subst(inst)` | 替换项变量（先匹配 schematic 变量的类型到 `inst.tyinst`，再递归替换） |
| `Term.subst_norm(inst)` | `subst(inst) + beta_norm()` |

替换不自动 β-归一。若需要归一，用 `subst_norm`。

### 2.3 first_order_match

```python
first_order_match(pat, t, inst=None) -> Inst
```

一阶匹配：判断模式 `pat`（含 schematic 变量）能否实例化为 `t`，返回赋值 `Inst`。失败抛 `MatchException`。

核心逻辑：
- `pat` 是 `SVar`：赋值或检查一致性。
- `pat` 的 head 是 `SVar`（函数位）：
  - 若 head 未实例化且参数都是 bound/已匹配的 schematic：抽象出函数赋给 head。
  - 否则启发式：把 head 赋为 `t.fun`，递归匹配 `pat.arg` 与 `t.arg`。
- `pat` 是 `Var`/`Const`：名字与类型须匹配。
- `pat` 是 `Comb`：递归匹配 `fun` 与 `arg`（顺序可能调整，见 `is_pattern`）。
- `pat` 是 `Abs`：匹配绑定变量类型，改名，递归匹配 body。

### 2.4 is_pattern

`is_pattern(t, matched_vars, bd_vars)`：判断 `t` 是否为"可匹配模式"--即 head 是未匹配的 schematic 变量时，参数须为 bound 或已匹配的 schematic，且参数互异。

`is_fo_pattern(t)`：无 schematic 变量在函数位（纯一阶模式）。

匹配顺序受 `is_pattern` 影响：若 `pat.fun` 是模式则先匹配 fun 再 arg，否则先匹配 arg 再 fun。

### 2.5 first_order_match_list

`first_order_match_list(pats, ts, inst)`：匹配模式列表与项列表。顺序敏感：若 `pats[0]` 不是模式，先匹配 `pats[1:]` 再匹配 `pats[0]`（因为 `pats[0]` 的匹配可能依赖后面的结果）。

### 2.6 can_first_order_match

`can_first_order_match(pat, t, inst=None)`：尝试匹配，返回 `True`/`False`（不抛异常）。

## 3. 匹配与定理应用

`apply_theorem` 宏（见 [`03_macro.md`](03_macro.md) §9）用 `first_order_match` 自动实例化定理：
1. 匹配结论 `C` 与目标。
2. 匹配假设 `As[i]` 与输入事实 `prevs[i].prop`。
3. 检查所有 schematic 变量已实例化。

`rewr_conv` 用 `first_order_match_list` 匹配等式的 lhs 与条件。

---

**下一章**：[`05_tactic.md`](05_tactic.md) -- 策略系统。

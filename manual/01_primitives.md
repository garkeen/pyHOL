# 第一层：内核原语与宏

## 概述

内核是可信计算基。15 条原始规则 + ~100 个宏。所有证明最终归结到原始规则。

## 数据结构

```
Type:  STVar | TVar | TConst
Term:  SVar | Var | Const | Comb | Abs | Bound
Thm:   (hyps: Tuple[Term], prop: Term)
Proof: List[ProofItem]
ProofTerm: 树形证明（rule, args, prevs, th, gaps）
```

## 15 条原始规则 (`kernel/thm.py`)

| 规则 | 参数类型 | 签名 | 说明 |
|------|----------|------|------|
| `assume` | Term | `A \|- A` | 假设 |
| `implies_intr` | Term | `A \|- B` → `\|- A --> B` | 蕴含引入 |
| `implies_elim` | — | `\|- A-->B, \|- A` → `\|- B` | MP |
| `reflexive` | Term | `\|- x = x` | 自反性 |
| `symmetric` | — | `\|- x=y` → `\|- y=x` | 对称性 |
| `transitive` | — | `\|- x=y, \|- y=z` → `\|- x=z` | 传递性 |
| `combination` | — | `\|- f=g, \|- x=y` → `\|- f x = g y` | 同余 |
| `equal_intr` | — | `\|- A-->B, \|- B-->A` → `\|- A=B` | 等价引入 |
| `equal_elim` | — | `\|- A=B, \|- A` → `\|- B` | 等价消除 |
| `substitution` | Inst | 项替换 | |
| `subst_type` | TyInst | 类型替换 | |
| `beta_conv` | Term | `\|- (%x.t1) t2 = t1[t2/x]` | Beta |
| `abstraction` | Term | `\|- t1=t2` → `\|- (%x.t1)=(%x.t2)` | 抽象 |
| `forall_intr` | Term | `\|- t` → `\|- !x. t` | 全称引入 |
| `forall_elim` | Term | `\|- !x. t` → `\|- t[s/x]` | 全称消除 |

## 全部宏（~100 个）

### 核心宏 (`logic/macros/core.py`, 通过 `global_macros.update` 注册)

| 宏名 | 类 | 说明 |
|------|-----|------|
| `beta_norm` | `beta_norm_macro` | Beta 归一化 |
| `intros` | `intros_macro` | 引入变量和假设 |
| `apply_theorem` | `apply_theorem_macro` | 应用定理（最核心） |
| `apply_theorem_for` | `apply_theorem_macro(with_inst=True)` | 带显式实例化的应用定理 |
| `apply_induct` | `apply_induct_macro` | 应用归纳原理 |
| `resolve_theorem` | `resolve_theorem_macro` | 消解 |
| `apply_fact` | `apply_fact_macro` | 应用已有事实 |
| `apply_fact_for` | `apply_fact_macro(with_inst=True)` | 带实例化的应用事实 |
| `rewrite_goal` | `rewrite_goal_macro` | 重写目标 |
| `rewrite_goal_sym` | `rewrite_goal_macro(sym=True)` | 反向重写目标 |
| `rewrite_goal_with_prev` | `rewrite_goal_with_prev_macro` | 用已有事实重写目标 |
| `rewrite_goal_with_prev_sym` | `rewrite_goal_with_prev_macro(sym=True)` | 反向 |
| `rewrite_fact` | `rewrite_fact_macro` | 重写事实 |
| `rewrite_fact_sym` | `rewrite_fact_macro(sym=True)` | 反向重写事实 |
| `rewrite_fact_with_prev` | `rewrite_fact_with_prev_macro` | 用事实重写事实 |
| `forall_elim_gen` | `forall_elim_gen_macro` | 通用全称消除 |
| `trivial` | `trivial_macro` | 平凡证明（C 在假设中） |

### `@register_macro` 注册的宏

**`logic/macros/core.py`:**
| 宏名 | 说明 |
|------|------|
| `imp_conj` | 蕴含合取 |
| `imp_disj` | 蕴含析取 |
| `resolution` | 命题消解 |

**`logic/macros/nat.py`:**
| 宏名 | 说明 |
|------|------|
| `nat_eval` | 自然数计算 |
| `nat_norm` | 自然数归一化 |
| `nat_const_ineq` | 自然数常量不等式 |
| `nat_const_less_eq` | 自然数常量 <= |
| `nat_const_less` | 自然数常量 < |

**`logic/macros/z3.py`:**
| 宏名 | 说明 |
|------|------|
| `z3` | Z3 SMT 求解器 |

**`logic/auto.py`:**
| 宏名 | 说明 |
|------|------|
| `auto` | 自动证明（分发到 solve/norm） |

**`data/integer.py`:**
| 宏名 | 说明 |
|------|------|
| `int_eval` | 整数计算 |
| `int_eq_macro` | 整数等式 |
| `int_ineq` | 整数不等式 |
| `int_ineq_mul_const` | 整数乘常数不等式 |
| `int_const_ineq` | 整数常量不等式 |
| `int_multiple_ineq_equiv` | 整数多不等式等价 |
| `omega_norm_int_ineq` | Omega 归一化 |
| `int_eq_comparison` | 整数等式比较 |

**`data/real.py`:**
| 宏名 | 说明 |
|------|------|
| `real_eval` | 实数计算 |
| `real_norm` | 实数归一化 |
| `real_const_eq` | 实数常量等式 |
| `real_compare` | 实数比较 |
| `real_const_ineq` | 实数常量不等式 |
| `real_eq_comparison` | 实数等式比较 |
| `non_strict_simplex` | 非严格 Simplex |

**`data/function.py`:**
| 宏名 | 说明 |
|------|------|
| `fun_upd_eval` | 函数更新计算 |

**`data/expr.py`:**
| 宏名 | 说明 |
|------|------|
| `prove_avalI` | 表达式求值证明 |

**`imperative/imp.py`:**
| 宏名 | 说明 |
|------|------|
| `eval_Sem` | 语义求值 |
| `vcg` | 验证条件生成 |

**`prover/simplex.py`:**
| 宏名 | 说明 |
|------|------|
| `simplex_macro` | Simplex 线性规划 |
| `integer_simplex` | 整数 Simplex |

**`prover/simplex_strict.py`:**
| 宏名 | 说明 |
|------|------|
| `simplex_delta_macro` | Delta Simplex |
| `simplex_norm_form` | Simplex 归一化 |
| `strict_simplex_macro` | 严格 Simplex |

**`prover/sympywrapper.py`:**
| 宏名 | 说明 |
|------|------|
| `sympy` | SymPy CAS 集成 |

**`sat/zchaff.py`:**
| 宏名 | 说明 |
|------|------|
| `disj_force` | 析取强制 |
| `disj_false` | 析取假 |

**`smt/veriT/verit_macro.py`** (57 个)：veriT 证明重建宏，前缀 `verit_`。

**`smt/veriT/la_generic.py`** (4 个)：`verit_norm_lia`, `verit_norm_lra`, `verit_round_lia`, `verit_la_generic`

## ProofTerm 操作

```python
# 构造
ProofTerm.assume(A)            # A |- A
ProofTerm.reflexive(x)         # |- x = x
ProofTerm.theorem('conjI')     # 查找定理
ProofTerm.sorry(th)            # 创建 gap
ProofTerm.atom(id, th)         # 引用已有证明行

# 组合
pt.implies_intr(A)             # 蕴含引入
pt.implies_elim(pt2)           # 蕴含消除
pt.symmetric()                 # 对称
pt.transitive(pt2)             # 传递
pt.equal_intr(pt2)             # 等价引入
pt.equal_elim(pt2)             # 等价消除
pt.substitution(inst)          # 替换
pt.subst_type(tyinst)          # 类型替换
pt.forall_intr(x)              # 全称引入
pt.forall_elim(s)              # 全称消除
pt.abstraction(x)              # 抽象
pt.on_prop(*convs)             # 对命题应用转换
pt.on_rhs(*convs)              # 对右侧应用转换
pt.on_lhs(*convs)              # 对左侧应用转换
pt.tac(tac)                    # 对第一个 gap 应用策略
pt.tacs(*tacs)                 # 对多个 gap 依次应用策略

# 导出
pt.export()                    # 转为线性 Proof
pt.th                          # 结果 Thm
pt.gaps                        # 所有 sorry gap
```

## Theory 数据

```python
theory.thy.data['type_sig']    # {name: arity}
theory.thy.data['term_sig']    # {name: Type}
theory.thy.data['theorems']    # {name: Thm}
theory.thy.data['attributes']  # {name: (attr, ...)}
theory.thy.data['overload']    # {name: True}
theory.thy.data['thm_status']  # {name: status}
```

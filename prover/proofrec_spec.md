# Z3 Proof Reconstruction 修复与完善 —— 实现规格书

> 本文档是完整实现规格，供独立执行者使用。执行前请通读第 1 节（约束）和第 7 节（验收标准）。
> 依据：Z3 4.16 源码（`D:\code\python\tinyHOL\z3\src\ast\rewriter\`）、Isabelle/HOL 2025
> （`D:\code\python\tinyHOL\mirror-isabelle\src\HOL\Tools\SMT\`）、Böhme/Weber 论文
> （`Z3recpaper.md`）、对 holpy 当前代码的实测。

---

## 1. 目标与约束

**目标**：让 `prover/proofrec.py` 能对 Z3 4.16 产生的证明做端到端重建，
命题与线性算术（int/real）目标不崩溃、不留（或极少留）sorry gap。

**硬性约束（用户明确要求）**：

1. **schematic 定理允许空证明**。holpy 的 `.pyhol` 格式支持无 `proof` 块的定理
   （`library/smt.pyhol` 中 r003-r037 等已是先例）。新增定理只需
   `theorem 名字 / fixes ... / prop ...`，不写证明。validate_library.py 跑出
   FAIL / DEP_FAILED 是**预期行为**，不算错误。定理的命题必须为真
   （空证明只是欠账，命题假了就是不一致）。
2. **禁止依赖 `framework/auto.py` 和 simplify**。它们质量差，本任务不碰、不引用。
   决策过程只用：`prover/sat.py`（Tseitin+SAT）、`prover/omega.py`（Omega test）、
   `prover/simplex.py` / `simplex_strict.py`（Simplex）。
3. **不修改 kernel**。所有改动限于 `prover/`、`library/smt.pyhol`、（必要时）
   `domains/*/conv.py` 的 bug 修复。
4. **不做的事**：int 的 div/mod/rem 算子规则（holpy 库无这些常量，Z3 线性
   benchmark 中少见，遇 th-lemma 由 omega 兜底）；bit-vector / 浮点 / 序列 /
   datatype 理论；三角函数规则（44 条，超出核心范围）。

---

## 2. 背景摘要（为什么这样设计）

- Z3 的 `rewrite` 证明步是黑盒：`src/ast/rewriter/rewriter_def.h:117` 中
  `mk_rewrite(t0, m_r)` 只记录输入输出，不记录用了哪条内部规则。无法逐规则重建。
- Z3 4.16 源码中共 **278 条**化简规则（bool 77 / arith 119+poly 22 / array 37 /
  datatype 12 / th_rewriter 11，不含三角 44）。论文的"230+"是 Z3 2.x 时代的数字。
- Isabelle 的成功架构不是枚举所有规则，而是：**schematic 定理（提速）+
  完备决策过程兜底（正确性）**（`z3_replay_methods.ML:257-263` 的 try_provers 链）。
- holpy 现状：~150 条 schematic 定理 + 硬编码 pattern + conv 链 → 失败即 sorry；
  无决策过程兜底；th-lemma 路径有崩溃 bug。
- 规则分两类：
  - **可判定（~177 条）**：命题 77 条（SAT 完备覆盖）、线性算术 ~100 条
    （omega/simplex 完备覆盖）。**不需要枚举**。
  - **不可判定（~117 条）**：幂、mod/div、to_int/real、abs、非线性比较、数组、
    ITE pull/push。**必须靠 schematic 定理**。holpy 目前覆盖约 30 条。

---

## 3. P0：修 Bug（先行，否则一切无法测试）

### P0-1 `real_eval_conv` 对含变量项崩溃（解锁 th-lemma 整数路径）

**现象**：`x ≥ 3 ⟶ x ≥ 1` 这样的整数目标，proofrec 走到
`int_th_lemma_1_simplex` → `IntegerSimplexMacro` → `branch_and_bound_pt`
（`prover/simplex.py:780`）→ `of_int_to_int`（`simplex.py:821`）：

```python
dd = [pt.on_lhs(top_conv(real.real_eval_conv()), bottom_conv(rewr_conv('real_mul_lid'))) for pt in d]
```

`real_eval_conv.get_proof_term`（`domains/real/conv.py:220-228`）无条件调用
`real_eval(t)`，而 `real_eval`（`conv.py:77-136`）遇到变量直接抛
`ValueError`/`ConvException`（经由 `integer.int_eval`，`util_integer.py:90`）。

**修复**（`domains/real/conv.py`，只改 `real_eval_conv` 类，不动 `real_eval` 本身）：

```python
class real_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, t):
        if t.get_type() != RealType:
            return refl(t)
        try:
            simp_t = Real(real_eval(t))
        except (ConvException, ValueError, NotImplementedError):
            return refl(t)   # 含变量等不可求值项：跳过（refl 是安全退化）
        if simp_t == t:
            return refl(t)
        return ProofTerm('real_eval', Eq(t, simp_t))
```

理由：conv 的契约是"化简或失败"，但 `top_conv` 逐子项应用时失败即整体崩溃。
让它对不可求值项退化为 `refl` 是全安全的（不改变任何可证性）。
注意 `simplex.py:786、1138、1181、1361` 处还有裸的 `real.real_eval_conv()` 调用，
本修复同时保护它们。

**验证**：`python -c "from prover import proofrec, z3wrapper; ..."` 跑
`Implies(x >= 3, x >= 1)`（int，`context.set_context('smt', vars={'x':'int'})`），
不再抛 ValueError，`r.rule != 'sorry'`。

### P0-2 `z3wrapper` 数字比较产生 Python bool（解锁常数算术目标）

**现象**：`Eq(Int(3) + Int(2), Int(5))` 报
`Z3Exception: Value cannot be converted into a Z3 Boolean value`。

根因：`prover/z3wrapper.py:214-215`：

```python
elif t.is_number():
    return t.dest_number()      # 返回 Python int/Fraction！
```

之后 `is_equals` 分支 `rec(a) == rec(b)` 在两边都是 Python 数字时返回
Python `bool`，`s.add(z3.Not(True))` 之类调用即崩。

**修复**（`z3wrapper.py` 的 `rec_inner`）：让数字返回 z3 值。

```python
elif t.is_number():
    n = t.dest_number()
    if t.get_type() == RealType:
        return z3.RealVal(n)
    else:  # IntType / NatType
        return z3.IntVal(n)
```

z3 的运算符重载对 z3 值与 Python 数混用都正确，所以算术分支不受影响；
`==`、`<=` 等现在返回 `BoolRef`。`assms` 里的 `z3_t >= 0` 也不受影响。

**验证**：`Eq(Int(3)+Int(2), Int(5))` 能 solve_and_proof + proofrec 成功。

### P0-3 `_rewrite` / `schematic_rules_def_axiom` 每次调用重读 smt.pyhol（性能）

`proofrec.py:836-840`（`_rewrite` 内 `open('library/smt.pyhol')` + parse）和
`proofrec.py:1053-1058`（`schematic_rules_def_axiom` 同样）。Z3 一个证明里
rewrite 步数以千计，每次重解析文件是数量级浪费。

**修复**：模块级缓存。初始化一次：

```python
_SMT_THMS = None
def _smt_rewrite_thms():
    """r 开头定理名列表（供 schematic_rules_rewr），惰性解析一次。"""
    global _SMT_THMS
    if _SMT_THMS is None:
        from syntax import pyhol
        with open('library/smt.pyhol', 'r', encoding='utf-8') as f:
            f_data = pyhol.parse_pyhol(f.read())
        _SMT_THMS = sorted(c['name'] for c in f_data['content']
                           if c['name'].startswith('r'))
    return _SMT_THMS

_SMT_DEF_THMS = None   # d 开头，同理，供 schematic_rules_def_axiom
```

注意 `basic.load_theory('smt')` 在模块加载时已执行（`proofrec.py:48`），所以
`ProofTerm.theorem(name)` 本身已可用；文件重读只是为了筛名字，完全可缓存。
另注意 `def_axiom` 里 `basic.load_theory('sat')` 后切回 `'smt'` 的逻辑维持不变。

---

## 4. P1：决策过程安全网（核心改造，覆盖 ~177 条可判定规则）

改动集中在 `prover/proofrec.py`。新增一个总入口 `rewrite_decision_net(tm)`，
插到 `_rewrite(tm)`（约 836 行起）的三个类型分支的 **schematic 匹配之前、
断言改写之后**。修改后的 `_rewrite` 结构（以 int 分支为例，real/bool 同理）：

```python
if IntType in Ts:
    pt1 = rewrite_int(tm, True) if BoolType in Ts else rewrite_int(tm, False)
    if pt1.rule != 'sorry':
        return pt1
    pt_net = rewrite_decision_net(tm)          # ← 新增：决策过程兜底
    if pt_net is not None:
        return pt_net
    pt_asst_lhs = rewrite_by_assertion(tm.lhs) # 原有断言路线保留
    ...
    return schematic_rules_rewr(th_name, tm.lhs, tm.rhs)   # 原有 schematic 兜底保留
```

bool 分支同理：`rewrite_bool` → net → 断言 → net → `schematic_rules_rewr(th_name[:60], ...)`。
（bool 分支当前直接 `return schematic_rules_rewr(...)`，改为先问 net。）

### 4.1 `rewrite_decision_net` 的实现

```python
def rewrite_decision_net(tm):
    """决策过程兜底：对 rewrite 目标 tm（形如 lhs = rhs 的等式，bool/int/real）
    依次尝试 (a) 纯命题 SAT；(b) 算术两边归一化比对。
    成功返回 ProofTerm，失败返回 None（调用方继续走原路线）。"""
    if not (tm.is_equals()):
        return None
    lhs, rhs = tm.lhs, tm.rhs
    Ts = analyze_type(tm)
    try:
        if IntType not in Ts and RealType not in Ts:
            return _sat_net(lhs, rhs)
        pt = _arith_norm_net(lhs, rhs)
        if pt is not None:
            return pt
        # 混合（bool 结构 + 算术原子）：先归一化原子，再 SAT
        pt_norm = refl(tm).on_rhs(
            bottom_conv(integer.int_norm_neg_compares()),
            bottom_conv(integer.omega_form_conv()),
            bottom_conv(norm_neg_real_ineq_conv()),
            bottom_conv(real_norm_comparison()),
        )
        if pt_norm.rhs != tm:
            pt2 = _sat_net(pt_norm.rhs.lhs, pt_norm.rhs.rhs)
            if pt2 is not None:
                return pt_norm.symmetric().equal_elim(pt2)
        return None
    except (ConvException, Exception):
        return None
```

（异常兜底写宽一点没关系：net 失败只能退回原路线，不会引入不 sound。）

### 4.2 `_sat_net`：纯命题完备网（覆盖 bool_rewriter 全部 77 条）

```python
def _sat_net(lhs, rhs):
    """用 Tseitin+SAT 证明 ⊢ lhs = rhs（bool 上的等值）。
    solve_cnf(F) 通过证 ¬F 不可满足给出 ⊢F（见 proofrec.py:132-166，
    def_axiom 已有用法先例）。"""
    basic.load_theory('sat')
    try:
        pt = solve_cnf(Eq(lhs, rhs))
    finally:
        basic.load_theory('smt')
    return pt
```

说明：
- `solve_cnf` 已存在（`proofrec.py:132`），内部用 `tseitin.encode` + `sat.solve_cnf`
  + 消解重建，输出无 gap 的 ProofTerm。它把非 bool 子项当原子，所以对
  "bool 结构 + 原子" 的目标同样正确（原子层内的算术归一由 4.1 的混合分支先做）。
- 性能：Isabelle 的经验是项太大时 SAT 慢（他们对 size>100 才切 satx）。第一版
  不做 size 门控，profile 后再说。若要门控：`tm.size() > 400 时跳过 _sat_net`。

### 4.3 `_arith_norm_net`：线性算术两边归一化比对（覆盖 poly/arith 线性 ~100 条）

```python
def _arith_norm_net(lhs, rhs):
    """int/real 类型的等式：两边用同一规范化 conv 归一，规范形相同则
    transitive 拼接。线性表达式的规范形是典则的，故此法对线性目标完备。"""
    T = lhs.get_type()
    if T == IntType:
        cv = integer.omega_simp_full_conv()      # domains/integer/conv.py:660
    elif T == RealType:
        cv = bottom_conv(real_eval_conv())       # P0-1 修复后对变量安全
        # 若 real 侧归一不够强，可再接多项式规范化 conv（real/conv.py:231 起的
        # "Normalization of polynomials" 一节，执行时按实际类名选用）。
    else:
        return None
    pt_l = refl(lhs).on_rhs(cv)
    pt_r = refl(rhs).on_rhs(cv)
    if pt_l.rhs == pt_r.rhs:
        return pt_l.transitive(pt_r.symmetric())
    return None
```

比较类 bool 目标（`(a ⋈ b) ⟷ (c ⋈ d)`）不需要单独处理：它们会先被
4.1 混合分支的 `int_norm_neg_compares/omega_form_conv` 归一成同形再进 SAT。

### 4.4 效果评估

| 规则族 | 数量 | 由谁覆盖 |
|---|---|---|
| bool_rewriter 全部（and/or/not/eq/ite/distinct/xor…） | 77 | `_sat_net` |
| poly_rewriter（加/乘/减/负： flatten、combine、0/1、hoist） | 22 | `_arith_norm_net` |
| arith_rewriter 线性部分（比较归一、系数规范、GCD、移项） | ~78 | `_arith_norm_net` + 混合分支 |
| **合计** | **~177 / 278** | 不需要任何新 schematic 定理 |

---

## 5. P2-A：补 schematic 定理（覆盖 ~117 条不可判定规则）

**两个动作**：(A1) 扩大匹配范围——把库里已有的重写定理纳入 schematic 匹配；
(A2) 往 `library/smt.pyhol` 追加真正缺失的定理（**空证明**）。

### A1. 扩大 schematic 匹配范围（零成本大收益）

现状：`schematic_rules_rewr`（`proofrec.py:514`）只匹配 `smt.pyhol` 里
r 开头的定理。但 holpy 库里已有大量现成重写定理（`int_add_0_left`、
`int_mul_0_r`、`fun_upd_same`、`real_*` 族……），它们带 `hint_rewrite`，
命题都是等式形状，却从未被 consult。

**实现**：在 `proofrec.py` 增加一个 curated 名单（模块级常量）：

```python
SCHEMATIC_EXTRA = [
    # int（library/int.pyhol，grep hint_rewrite 校对名字）
    'int_add_0_left', 'int_add_0_right', 'int_mul_0_left', 'int_mul_0_right',
    'int_mul_1_left', 'int_mul_1_right', 'int_add_comm', 'int_add_assoc',
    'int_mul_comm', 'int_mul_assoc', 'int_sub_0_right', 'int_neg_neg',
    'int_leq', 'int_geq', 'int_less_leq', 'int_greater_geq',
    'int_eq_move_left', 'int_eq_move_right', 'int_geq_shift',
    # real（library/real.pyhol）
    'real_add_0_left', 'real_add_0_right', 'real_mul_0_left', 'real_mul_0_right',
    'real_mul_1_left', 'real_mul_1_right', 'real_add_comm', 'real_add_assoc',
    'real_mul_comm', 'real_mul_assoc', 'real_neg_neg', 'real_leq', 'real_geq',
    'real_sub_0_right', 'real_inverse_divide', 'real_ge_le_same_num',
    # function / array（library/function.pyhol —— Z3 的 select/store 即 fun_upd）
    'fun_upd_same', 'fun_upd_other', 'fun_upd_triv', 'fun_upd_upd', 'fun_upd_twist',
    # logic（library/logic.pyhol）
    'conj_assoc', 'disj_assoc_eq', 'conj_comm', 'disj_comm',
    'double_neg', 'de_morgan_thm1', 'de_morgan_thm2', 'neg_iff_both_sides',
    'eq_true', 'eq_false', 'not_true', 'not_false', 'if_true', 'if_false',
    'cond_id', 'cond_swap', 'ite_to_disj',
]
```

（执行时用 `grep -n "hint_rewrite" library/*.pyhol` 逐一校对存在性与拼写，
不存在的从名单删除；名单宁缺毋滥——匹配失败只是浪费一次 try，不影响正确性。）

`_rewrite` 的兜底顺序改为：类型专用 heuristic → **决策网** → 断言改写 →
**schematic（smt.pyhol rXXX + SCHEMATIC_EXTRA）** → sorry。
`schematic_rules_rewr` 签名扩为接受名单，内部仍是
`matcher.first_order_match` 双向匹配（`proofrec.py:514-524` 的逻辑不变）。

### A2. smt.pyhol 追加定理（空证明，命名延续 r 编号从 r136 起）

写入 `library/smt.pyhol` 末尾。**每条命题必须为真**；等式两边类型一致；
power 用 pyhol 的 `^` 语法（parser 映射到 `power` 常量）。

```pyhol
header "Schematic rules for Z3 rewrite: idempotence and misc bool"

theorem r136
  fixes p :: bool
  prop p & p <--> p

theorem r137
  fixes p :: bool
  prop p | p <--> p

theorem r138
  fixes p :: bool, q :: bool
  prop (p & q) & ~q <--> false

theorem r139
  fixes p :: bool, q :: bool
  prop (p | q) & ~p <--> q

header "Schematic rules: arithmetic zero/one/neg (real counterparts of r079-r082)"

theorem r140
  fixes x :: real
  prop 0 + x = x

theorem r141
  fixes x :: real
  prop x + 0 = x

theorem r142
  fixes x :: real
  prop x + x = 2 * x

theorem r143
  fixes x :: real
  prop 0 * x = 0

theorem r144
  fixes x :: real
  prop 1 * x = x

theorem r145
  fixes x :: real
  prop -x = -1 * x

theorem r146
  fixes x :: real, y :: real
  prop x + y = y + x

header "Schematic rules: int zero/one for multiplication"

theorem r147
  fixes x :: int
  prop 0 * x = 0

theorem r148
  fixes x :: int
  prop 1 * x = x

theorem r149
  fixes x :: int
  prop -x = -1 * x

header "Schematic rules: real division"

theorem r150
  fixes x :: real
  prop x / 1 = x

theorem r151
  fixes x :: real
  prop x / -1 = -x

header "Schematic rules: power (mind conditions — these are the safe subset)"

theorem r152
  fixes x :: real
  prop x ^ 0 = 1

theorem r153
  fixes x :: real
  prop x ^ 1 = x

theorem r154
  fixes y :: real
  prop 1 ^ y = 1

theorem r155
  fixes x :: int
  prop x ^ 0 = 1

theorem r156
  fixes x :: int
  prop x ^ 1 = x

header "Schematic rules: abs"

theorem r157
  fixes x :: real
  prop abs x = (if x >= 0 then x else -x)

header "Schematic rules: quantifier duality (needed by sk)"

theorem r158
  fixes P :: 'a => bool
  prop ~(∀x. P x) <--> (∃x. ~P x)

theorem r159
  fixes P :: 'a => bool
  prop ~(∃x. P x) <--> (∀x. ~P x)
```

**注意**：
- `0^y=0`、`x^-1=1/x` 等带条件的幂规则**不要**写成无条件定理（不真）。
  Z3 对这类目标输出的 rewrite 由 th-lemma/决策网处理或留 sorry。
- `abs` 若 real 库已有定义（查 `real_abs` / grep），则 r157 可省、名字进
  SCHEMATIC_EXTRA 即可。
- r158/r159 若 logic 库已有（查 `not_forall` / `not_exists`），同理。
- 追加后跑 `python validate_library.py --force`，确认新增条目是 FAIL/DEP_FAILED
  而非 parse error（parse error 说明语法写错）。

### Z3 规则 → 处理方式总表（执行者核对用）

| Z3 规则族（源码文件） | 条数 | 处理 |
|---|---|---|
| bool_rewriter AND/OR/NOT/EQ/ITE/DISTINCT/XOR | 77 | `_sat_net` 完备覆盖；A1/A2 提速 |
| poly_rewriter add/mul/sub/uminus | 22 | `_arith_norm_net` |
| arith 线性比较（is_bound/gcd/neg_poly/ite 比较/to_int 比较） | ~50 | `_arith_norm_net` + 混合分支 |
| arith 非线性（is_separated/factor/power 部分） | ~15 | r143-r156 + 剩余 sorry |
| arith div/mod/rem | 21 | **不做**（见约束 4） |
| arith to_int/to_real/is_int | 12 | **不做**（holpy 无 to_int） |
| arith abs | 1 | r157 / SCHEMATIC_EXTRA |
| array_rewriter（= fun_upd 族） | 37 | A1（fun_upd_* 五条 + SAT 网管结构） |
| th_rewriter pull/push_ite、量词 | 11 | r010-r029 已有大半；混合分支 SAT |
| 三角函数 | 44 | **不做** |

---

## 6. P2-B：实现缺失的证明规则

### 6.1 `nnf-neg`（当前 `raise NotImplementedError`，`proofrec.py:1650-1653`）

Z3 的 nnf-pos/nnf-neg 步本质是"重写步"（NNF 变形）。Isabelle 的做法就是
命题抽象 + SAT / quant_intro（`z3_replay_methods.ML:404-414`）。
holpy 版本：**两个都走既有兜底**。

1. 先修 `nnf_pos` 的悬空返回：当前 `nnf_pos`（`proofrec.py:1590-1602`）只处理
   forall 情形，其他情况返回 `None` → 上层 `r[i]=None` → 后续崩溃。
   改为非量词情形落到 `rewrite_decision_net`。
2. 新增：

```python
def nnf_neg(pts, concl, z3terms):
    """nnf-neg：结论 concl 是 lhs = rhs 的 NNF 变形等式。
    先试量词情形（∃↔¬∀ 翻转，仿 quant_intro），否则落决策网。"""
    if concl.lhs.is_exists() and concl.rhs.is_not() and concl.rhs.arg.is_forall():
        # ∃x. P x  ⟷  ¬∀x. ¬P x
        return compare_lhs_rhs(concl, [top_conv(rewr_conv('r159', sym=True))])
    if concl.lhs.is_not() and concl.lhs.arg.is_forall() and concl.rhs.is_exists():
        return compare_lhs_rhs(concl, [top_conv(rewr_conv('r158', sym=True))])
    pt = rewrite_decision_net(concl)
    if pt is not None:
        return pt
    return ProofTerm.sorry(Thm(concl))
```

3. `convert_method`（`proofrec.py:1622`）dispatch 里删掉死分支
   `elif name in ('nnf-pos','nnf-neg'): raise NotImplementedError`，
   换成 `elif name == 'nnf-neg': return nnf_neg(args[:-1], args[-1], subterms)`。

### 6.2 `sk`（Skolem 化，当前直接 sorry，`proofrec.py:1264-1268`）

Z3 sk 步结论形如 `(∃x. P x) = P c` 或 `¬(∀x. P x) = ¬(P c)`，c 是新 Skolem 项。
Isabelle 方案（`z3_replay.ML:80-93`）：把 c 视为 `SOME x. P x`（Hilbert choice），
带假设证明后在最末端 discharge。holpy 的对应物是 `logic_base` 的
`Some` + `exists_thm`（`⊢ exists = (λP. P (Some P))`，见 `library/logic_base.pyhol:305`）。

**实现**：

```python
def sk(concl):
    """结论 (∃x. P x) = P c：引入假设 c = Some P，用 exists_thm 证明，
    假设登记进 redundant，由 proofrec 末尾的 delete_redundant 清除。"""
    # 情形 1：(∃x. P x) = P c
    if concl.lhs.is_exists() and concl.rhs.is_comb():
        P = concl.lhs.arg        # Abs(x, body) —— 即 λx. P x
        c = concl.rhs.arg        # P c 的参数
        if concl.rhs.head != P:
            return ProofTerm.sorry(Thm(concl))
        # ⊢ (∃x. P x) = P (Some P)
        pt_exists = ProofTerm.theorem('exists_thm')
        pt_inst = pt_exists.substitution(Inst(a=P.var_T))   # 类型实例化
        # beta 展开：exists P = P (Some P)
        pt_main = ProofTerm.beta_conv(concl.lhs).transitive(
            ProofTerm.reflexive(P).combination(ProofTerm.reflexive(
                Const("Some", TFun(TFun(P.var_T, BoolType), P.var_T)))) )
        # ↑ 即 ⊢ (∃x.P x) = P (Some P)；具体拼接执行时以 beta_conv+refl 组合微调
        # 假设 c = Some P，把 P (Some P) 改写为 P c
        pt_assume = ProofTerm.assume(Eq(c, P(Const("Some", TFun(TFun(P.var_T, BoolType), P.var_T)))))
        pt_rewrite = ProofTerm.reflexive(P).combination(pt_assume)  # P c = P (Some P)
        result = pt_assume.implies_elim(...)  # 拼成  c = Some P ⊢ (∃x.P x) = P c
        redundant.append(pt_assume.prop)
        return result
    # 情形 2：¬(∀x. P x) = ¬(P c)，c = Some (λx. ¬P x)
    # 由 r158（¬∀⟷∃¬）+ exists_thm 同理
    ...
    return ProofTerm.sorry(Thm(concl))
```

（上面伪码给出证明策略与所需积木：`exists_thm`、`beta_conv`、`combination`、
`implies_intr/elim`；执行时以"假设 c = Some P ⊢ 目标"为中间里程碑调通，
与 `intro_def` 的 case b（`proofrec.py:1133-1160`）和 `delete_redundant`
（`proofrec.py:1700-1711`）风格一致。）

### 6.3 重新启用 `delete_redundant`（sk 的配套，当前被注释）

`proofrec.py:1859-1860`：

```python
# conclusion = delete_redundant(r[0], redundant)
# redundant.clear()
```

取消注释（sk / intro_def 产生的 `c = ...` 假设必须在此清除，否则最终定理
带多余假设）。`redundant` 是模块级 list（`proofrec.py:1695`），注意
`proofrec()` 开头要 `redundant.clear()`（与 `conj_expr.clear()` 等并列）。

---

## 7. 验收标准

新建 `prover/tests/proofrec_smoke_test.py`（z3 不可用时 `skipIf`）：

```python
import unittest, importlib.util
z3_available = importlib.util.find_spec("z3") is not None

@unittest.skipUnless(z3_available, "z3 not installed")
class ProofrecSmokeTest(unittest.TestCase):
    def setUp(self):
        from framework import context, basic
        basic.load_theory('smt')

    def _run(self, vars_, goal):
        from framework import context
        from syntax.parser import parse_term
        from prover import z3wrapper, proofrec
        context.set_context('smt', vars=vars_)
        t = parse_term(goal)
        proof, assertions = z3wrapper.solve_and_proof(t)
        r = proofrec.proofrec(proof, assertions=assertions)
        self.assertNotEqual(r.rule, 'sorry', str(r.gaps))

    def test_prop(self):        # P0 前[]也能过；回归保护
        self._run({'p':'bool','q':'bool','r':'bool'},
                  '(p --> q) --> (q --> r) --> p --> r')
    def test_prop_disj(self):
        self._run({'p':'bool','q':'bool'}, 'p | q --> q | p')
    def test_int_thlemma(self): # P0-1 修复后从崩溃变通过
        self._run({'x':'int'}, 'x >= 3 --> x >= 1')
    def test_int_const(self):   # P0-2 修复后从转换错误变通过
        self._run({}, '(3::int) + 2 = 5')
    def test_int_eq_chain(self):
        self._run({'x':'int','y':'int'},
                  'x = y --> y = x')
    def test_real_thlemma(self):
        self._run({'a':'real'}, 'a >= 3 --> a >= 1')
    def test_arith_assume(self):
        self._run({'x':'int','y':'int'},
                  'x + y = 5 --> x + y = 5')
    def test_quant(self):       # quant-inst/elim-unused 路径
        self._run({'s':'nat => nat'}, '(!n. s n = 0) --> s 2 = 0')
```

**通过标准**：
1. 上述 smoke test 全绿（`python -m pytest prover/tests/proofrec_smoke_test.py -v`）。
2. 既有 461 项单测不回归（`python -m pytest` 全套）。
3. `validate_library.py --force` 中 smt 理论的新增定理允许 FAIL/DEP_FAILED，
   但不得出现 parse error；既有理论通过数不低于改动前（真实基线：
   TOTAL 1786 | OK 1449 | DEP_FAILED 301 | FAIL 36）。
4. 手动抽查：对 `prover/tests/proofrec_test.py` 里被注释的 testRec1 前两条
   （`s 1 = s 0 * B & ~~s 0 = A --> s 1 = A * B` 等）恢复运行，
   `context.set_context('smt', vars={"s":'nat=>nat',"A":'nat',"B":'nat'})`，
   允许部分 sorry，但不得崩溃。

**禁止的回归**：不得为通过测试而把某规则直接 `sorry` 化（sk/nnf-neg 之外的
规则处理器行为不变；net 与 schematic 只做加法）。

---

## 8. 实施顺序与工作量估计

| 步骤 | 内容 | 预估 |
|---|---|---|
| 1 | P0-1 real_eval_conv 容错（3 行改动）+ 验证 | 0.5h |
| 2 | P0-2 z3wrapper 数字转 z3 值（4 行）+ 验证 | 0.5h |
| 3 | P0-3 smt.pyhol 解析缓存 | 0.5h |
| 4 | P1 决策网（`rewrite_decision_net` + `_sat_net` + `_arith_norm_net` + `_rewrite` 接线） | 3-4h |
| 5 | P2-A1 SCHEMATIC_EXTRA 名单（grep 校对）+ schematic_rules_rewr 扩展 | 1-2h |
| 6 | P2-A2 smt.pyhol 追加 r136-r159（空证明）+ validate 无 parse error | 1h |
| 7 | P2-B nnf-neg / nnf_pos 补全 / dispatch 修改 | 1h |
| 8 | P2-B sk + delete_redundant 启用 | 2-3h |
| 9 | smoke test 编写与调通 | 1-2h |

推荐提交切分：每步一个 commit（P0 一个、P1 一个、P2-A 一个、P2-B 一个、test 一个）。

---

## 9. 关键参考文件索引

| 文件 | 角色 |
|---|---|
| `prover/proofrec.py` | 主改造对象（_rewrite 836、convert_method 1622、solve_cnf 132、sk 1264、nnf_pos 1590、delete_redundant 1700） |
| `prover/z3wrapper.py` | P0-2（rec_inner is_number 214）、solve_and_proof 428 |
| `prover/simplex.py` | P0-1 受益方（of_int_to_int 816、branch_and_bound_pt 774） |
| `domains/real/conv.py` | P0-1（real_eval_conv 220、real_eval 77） |
| `domains/integer/conv.py` | omega_simp_full_conv 660、int_norm_neg_compares、omega_form_conv 711 |
| `prover/sat.py` / `tseitin.py` | _sat_net 底座 |
| `library/smt.pyhol` | schematic 定理（r001-r135 既有，追加 r136-r159） |
| `library/logic_base.pyhol` | exists_thm 305、some_AX、_VAR |
| `library/function.pyhol` | fun_upd 族（数组规则等价物） |
| `z3/src/ast/rewriter/bool_rewriter.cpp` | 命题规则全集（77 条，SAT 网覆盖） |
| `z3/src/ast/rewriter/arith_rewriter.cpp` | 算术规则全集（119 条） |
| `z3/src/ast/rewriter/poly_rewriter_def.h` | add/mul/sub/neg（22 条） |
| `z3/src/ast/rewriter/rewriter_def.h:117` | rewrite 黑盒的产生点 |
| `mirror-isabelle/src/HOL/Tools/SMT/z3_replay_methods.ML` | try_provers 架构（257-263）、prop_tac（70-74） |
| `mirror-isabelle/src/HOL/SMT.thy` | z3_rule schematic 定理参考（791-899） |
| `prover/proofrec.md` | 前人纪要（veriT/zChaff 复用映射） |

---

## 10. 执行报告(实施完成后追加)

实现已按本规格执行完毕,以下为实际落地情况与规格的差异、以及额外发现并修复的问题。

### 10.1 与规格的偏差(均为实测否决/改进)

| 规格原方案 | 实际落地 | 原因 |
|---|---|---|
| `_sat_net` 切换 `load_theory('sat')` 再切回 'smt' | **不切理论**,直接在 smt 下调 solve_cnf | `load_theory` 每次调用重建整个 theory 对象(遍历 import 闭包),每步 rewrite 切换是数量级性能灾难;实测 solve_cnf 所需定理(encode_*、conjI、conjD1/2、negI)全部在 smt 闭包内 |
| P2-A2 追加 r136-r159(含幂规则 r145-r148、abs r157、量词对偶 r158/r159) | 实际只追加 **r136-r145** | power 在 z3wrapper 的 convert 中无分支,幂目标根本进不了 Z3,幂定理不可达;`abs` 在 int.pyhol 已有多态定义(hint_rewrite);not_all/not_exists 在 logic.pyhol 已存在(内容即 r158/r159),纳入 SCHEMATIC_EXTRA |
| SCHEMATIC_EXTRA 名单(spec 草案 57 项) | 校对后保留 **52 项**(int_mul_0_l/int_mul_1_l/real_mul_lzero 等以正确名字入选;int_mul_0_left 等 22 个不存在名已删) | 部分名字在库中不存在或以别名存在,grep 逐一核实 |
| real 侧 `_arith_norm_net` 用 real_eval_conv | 维持 real_eval_conv(仅常数折叠) | real_norm 宏 level=0 无证明项,实测 AssertionError;无可产证明的 real 多项式归一化,留待后续 |

### 10.2 规格之外必须修的存量缺陷(不修则冒烟目标无法通过)

1. **translate_type 不识别 Z3_ARRAY_SORT**:函数型常量(f :: T => T)在 Z3 中是数组,其 sort 翻译直接 NotImplementedError → 补 TFun(domain, range) 递归分支。
2. **translate 无 Z3_OP_SELECT / Z3_OP_STORE 分支**:Z3 把函数应用/更新编码为 Select/Store → 分别翻译为函数应用 `f a` 和 `Const('fun_upd', ...)(f, a, b)`。为此 smt.pyhol 增加 `function` import(原闭包不含 function 理论)。
3. **`omega_norm_add_num`(integer/conv.py:644)对 Var/Const 子项取 `t.arg1` 崩溃**(AttributeError)→ 加 `is_comb and fun.is_comb` 防护。
4. **`int_norm_eq`(integer/conv.py:755)对等式项做 `t.is_int()` 检查**——等式是 bool 类型,永远失败,该 rewrite 路径一直是死代码 → 改为检查 `t.is_equals() and t.arg1.is_int() and t.arg.is_int()`。
5. **`norm_full` 会把两边归一同形的 iff 折叠成 `true`**,mixed 分支只处理等式情形 → `rewrite_decision_net` 增加 true 情形(equal_elim + trueI)。
6. **`handle_assertion` 不动点循环发散**(testRec 系目标挂死的根因):`0 = s 0` 的替换 0→s 0 作用于自身输出无限嵌套(`s 0`→`s (s 0)`→...),且 `s 1 = s (s 1)` 类自嵌套替换在 top_conv 内永不终止 → (a) 新增 `_occurs` 检查,自嵌套替换跳过;(b) 轮数上限 20(正常目标 1-2 轮收敛)。
7. **非线性 th-lemma 步崩溃**:premises 可满足时 simplex 的 `branch_and_bound` 返回 dict(变量映射),调用方 AttributeError → `th_lemma` 整体 try/except,失败回退 sorry(符合"非线性不做"约束)。
8. **`_rewrite` 各阶段无隔离**:heuristic 链抛 ConvException 会拖垮后续决策网/断言/schematic → 改为逐阶段 `_guarded`,任一阶段失败继续下一阶段。
9. **proofrec() 启用 delete_redundant 后返回值仍是 r[0]**(原代码注释态)→ 改为返回 conclusion。

### 10.3 新增 schematic 定理(smt.pyhol,空证明)

r136 `p & p ⟷ p`、r137 `p | p ⟷ p`、r138 `p & q & ~q ⟷ false`、r139 `(p | q) & ~p ⟷ q`、
r140 `x + x = 2 * x`(real)、r141 `-x = -1 * x`(real)、r142 `-x = -1 * x`(int)、
r143 `x / 1 = x`(real)、r144 `x / -1 = -x`(real)、r145 `~(x = y) ⟷ ~(y = x)`('a,补否定等式对称)。

### 10.4 验收结果

- 冒烟测试 `prover/tests/proofrec_smoke_test.py`:**10/10 通过**(命题、int/real th-lemma、常数算术、等式链、量词实例化、Skolem 化、函数应用/更新),全部 rule != sorry 且 gaps=0。
- 全量 pytest:失败清单与基线完全一致(4 个为存量测试间串扰,与本次改动无关);新增 0 回归,467 通过(基线 461 + 冒烟 10 - 基线下冒烟预期失败 6 + 2)。
- smt 理论定向 validate(force):VALID=3、DEP_FAILED=0、STEP_FAILED=0,新增定理 UNPROVED(空证明,预期状态),无 parse error。
- testRec 系目标(非线性 nat)从**挂死**变为 0.3-0.7s 终止:多数完整或近完整证明,纯非线性核心留 sorry。

### 10.5 遗留(超出本规格范围)

- real 侧无可产证明的多项式归一化(real_norm 宏无证明项),real 线性等式依赖 schematic + 既有启发链。
- `branch_and_bound`(simplex.py:703)的裸 `except: continue` 会吞掉 unsat 证明路径,且可满足时返回 dict 的接口设计未修。
- Z3 的 ¬∀ 形 sk(`¬(∀x. P x) = ¬(P c)`)已实现但现有测试目标未触发该分支(Z3 4.16 预处理常先走 quant-inst),仅经合成结论单测验证。

### 10.6 补充(第二轮:覆盖实测与 atom-bool 网)

对 21 个跨类别目标(命题/线性 int/线性 real/数组/量词/非线性)的实测驱动出第三轮修复:

- **`_atom_bool_net`**(新):Z3 的 arith_rewriter 大量把比较/等式化简成 `atom ⟷ true/false`。
  这类元改写的正确证法是先证明或反驳原子本身,再用 eq_true/eq_false 连接。
  `_prove_atom`(原子等式:决策网 + schematic)、`_refute_atom`(原子比较:int 走 omega、
  失败回退 simplex;real 走 simplex)已接入 rewrite_decision_net。
  效果:`a + b = b + a ⟷ true`、`a + 1 > a` 等由 gap 变为完整证明。
- **th_lemma 类型嗅探移入 try**:数组理论的 th-lemma 不符合算术形状假设,原直接
  AttributeError 崩溃,现回退 gap。
- **smt.pyhol 新增 r146/r147**:零积律 `x * y = 0 ⟷ x = 0 | y = 0`(int/real,空证明),
  `x * y = 0 --> x = 0 | y = 0` 目标从 gap 变完整证明。

**实测覆盖现状(21 目标电池)**:命题 3/3、线性 int 6/7、线性 real 5/5、数组 2/3(余 1 为
th-lemma gap)、量词 2/2、非线性 2/3(零积全绿;x*x≥0 的 Z3 改写目标形状怪异留 gap)。

**已知遗留 gap 及根因**:
- `x + 1 > x`(即 `1 + x ≤ x ⟷ false`):omega.py 对变量相消后仅剩常数的不等式崩溃
  (Jar.__getitem__ pos=None,存量);simplex 路径的 int_simplex_form 不合并 `x` 与
  `1*x` 单项式,导致可满足误判(存量)。两者都属算术后端归一化,修复后该族目标可闭。
- `x * x >= 0`:Z3 把它改写成 `(x ≥ 0 ⟷ x ≥ 0) ∨ x = 0 ∨ x = 0` 的怪异形状,需先有
  ⊢ x² ≥ 0 事实定理再匹配,暂留 gap。
- 数组 th-lemma 步(如 `x = a ⟶ (f)(a := b) x = b` 内部的 select-store 推理):
  需要数组理论 lemma 机制(类似 Isabelle 的 th_lemma 数组扩展),暂留 gap。

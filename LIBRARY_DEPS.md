# holpy 库依赖图与债务优先级

本文由 `library/*.pyhol` 的 `imports` 与解析后的定理引用关系生成。

- **§2 是开工前基线快照**（`.cache/*.json`，2026-09-09），随证明推进需用
  `python validate_library.py`（或对单理论的 `validate_theory`）刷新。
- **§3/§4 由当前 `.pyhol` 源码直接解析**，反映已开工进度。

## 1. 依赖图（拓扑序，地基在前）

```
logic_base
  └─ logic
       ├─ nat
       │    ├─ set
       │    │    ├─ list
       │    │    │    ├─ int  (另需 order，见 `library/int.pyhol` 的 imports)
       │    │    │    │    ├─ rat
       │    │    │    │    │    └─ real  (另需 order，同上)
       │    │    │    │    │         ├─ realset
       │    │    │    │    │         │    └─ floor
       │    │    │    │    │         ├─ limits
       │    │    │    │    │         └─ iterate  (另需 set)
       │    │    │    │    │              └─ sums
       │    │    │    │    │                   └─ products
       │    │    │    │    │                        └─ card
       │    │    │    │    │                        └─ gcd
       │    │    │    │    │                             └─ prime
       │    │    │    │    │                                  └─ lcm
       │    │    │    └─ string
       │    │    └─ topology
       │    ├─ function
       │    │    ├─ expr
       │    │    ├─ gcl ─ german / mutual_ex
       │    │    └─ (mem 另需 nat)
       │    ├─ class
       │    ├─ order（序谓词 preorder/order/linorder/linorder_lt + nat 实例，
       │    │         见 PROGRAM_VERIFICATION_PORT §1.5）
       │    │    └─ lists_ex（strict_sorted / ordered_insert / remove_elt_list / sorted；另需 list，见 §12–13）
       ├─ sat (另需 int)  └─ smt
       └─ hoare (另需 int)

real 下游：metric←misc←(floor,card)；integral←(real,metric)；transcendentals←(real,metric)
            realanalysis←(transcendentals,metric,function,integral)
            realderivative←(realanalysis,transcendentals,misc) → realseries → realintegral
            realgamma←realintegral → trig_series → trig_atn/trig_exp_log
            realgamma → trig_sin_cos / interval_arith
```

## 2. 各理论债务快照

**int / real 两行已于 2026-09-14 用 `validate_one --force` 刷新**（序层实例落地，
见 `library/real.pyhol`）；其余各行仍是 2026-09-09 的基线，刷新要跑
`python validate_library.py`。

| 理论 | 直接依赖 | 反向传递依赖数 | VALID | UNPROVED | DEP_FAILED | STEP_FAILED | AXIOM |
|---|---|---|---|---|---|---|---|
| logic_base | - | 43 | 37 | 0 | 0 | 0 | 19 |
| logic | logic_base | 42 | 53 | 39 | 0 | 0 | 0 |
| nat | logic | 40 | 55 | 37 | 132 | 1 | 1 |
| set | nat | 33 | 7 | 23 | 8 | 0 | 21 |
| list | set | 31 | 10 | 0 | 0 | 0 | 0 |
| int | list, order | 29 | 17 | 181 | 0 | 0 | 0 |
| rat | int | 26 | 0 | 4 | 0 | 0 | 0 |
| real | rat, order | 25 | 110 | 110 | 120 | 0 | 0 |
| iterate | set,real | 20 | 14 | 52 | 14 | 0 | 10 |
| sums | iterate | 19 | 5 | 55 | 136 | 0 | 1 |
| products | sums | 18 | 3 | 14 | 44 | 0 | 0 |
| card | products | 14 | 0 | 9 | 2 | 0 | 0 |
| function | nat | 17 | 17 | 0 | 0 | 0 | 0 |
| expr | function | 0 | 2 | 2 | 0 | 0 | 0 |
| realset | real | 15 | 4 | 12 | 13 | 0 | 0 |
| floor | realset | 14 | 1 | 38 | 4 | 0 | 0 |
| gcd | products | 2 | 12 | 6 | 72 | 0 | 0 |
| gcl | function | 2 | 0 | 2 | 0 | 0 | 0 |
| german | gcl | 0 | 0 | 1 | 0 | 0 | 0 |
| hoare | function,int | 0 | 10 | 6 | 1 | 0 | 0 |
| misc | floor,card | 13 | 11 | 14 | 6 | 0 | 0 |
| metric | misc | 12 | 5 | 23 | 22 | 0 | 0 |
| integral | real,metric | 10 | 1 | 132 | 2 | 0 | 0 |
| transcendentals | real,metric | 10 | 1 | 104 | 240 | 0 | 0 |
| realanalysis | transcendentals,metric,function,integral | 9 | 5 | 213 | 34 | 0 | 0 |
| realderivative | realanalysis,transcendentals,misc | 8 | 0 | 168 | 115 | 0 | 0 |
| realseries | realderivative | 7 | 0 | 105 | 32 | 0 | 0 |
| realintegral | realseries | 6 | 4 | 152 | 153 | 0 | 0 |
| realgamma | realintegral | 5 | 0 | 28 | 12 | 0 | 0 |
| interval_arith | realgamma | 0 | 0 | 56 | 1 | 0 | 0 |
| prime | gcd | 1 | 6 | 13 | 122 | 1 | 0 |
| lcm | prime | 0 | 1 | 0 | 33 | 0 | 0 |
| limits | real | 0 | 1 | 2 | 1 | 0 | 0 |
| mem | nat,function | 0 | 3 | 1 | 0 | 0 | 0 |
| mutual_ex | gcl | 0 | 0 | 1 | 0 | 0 | 0 |
| sat | logic,int | 1 | 0 | 5 | 0 | 0 | 0 |
| smt | logic_base,int,real,sat,function | 0 | 3 | 169 | 0 | 0 | 0 |
| topology | set | 0 | 0 | 2 | 0 | 0 | 0 |
| trig_series | realgamma | 2 | 3 | 16 | 43 | 0 | 0 |
| trig_atn | trig_series | 0 | 2 | 1 | 25 | 0 | 0 |
| trig_exp_log | trig_series | 0 | 0 | 0 | 16 | 0 | 0 |
| trig_sin_cos | realgamma | 0 | 0 | 5 | 10 | 0 | 0 |

## 3. blocker：被引用的 UNPROVED 定理（地基理论）

「被引用次数」= 有多少个已写证明的步骤以该定理为 `theorem=` 参数（代理其解锁的 DEP_FAILED 规模）。

| 理论 | UNPROVED 总数 | 其中是 blocker | blocker（按引用次数） |
|---|---|---|---|
| logic | 39 | 6 | imp_false_iff(1), exists_false(1), conj_iff_left(1), disj_iff_left(1), exists_eq(1), exists_disj_conj_distrib(1) |
| nat | 34 | 17 | not_le(32), less_eq_exist(17), eq_mult_lcancel(16), le_antisym(9), let_trans(7), mult_Suc_right(6), less_exist(5), lte_trans(5), mult_eq_1(4), nat_minus_suc(4), even_exists_lemma(2), lt_trans(1), exp_mono_lt_imp(1), nat_MAX(1) |
| set | 23 | 6 | subsetE(11), union_comm(4), subset_trans(2), subset_diff(1), lfp_fix_upper(1), lfp_fix_lower(1) |
| list | 0 | 0 | - |
| int | 181 | 0 | - |
| rat | 4 | 0 | - |
| real | 122 | 28 | （本行是 2026-09-09 基线：`real_le_trans`、`real_le_mul`、`real_lt_le` 等序引理已于 2026-09-14 证掉，见 `library/real.pyhol`；引用计数需刷新。仍 UNPROVED 的序外条目：real_mul_linv(18)、real_inv_0(14) —— 它们的 z3 证明受"该项在文件中的位置"影响，见 `library/real.pyhol` 的 NOTE）real_mult_comm(58), real_mul_lid(51), real_not_lt(39), real_of_nat_eq(13), real_of_nat_lt(10), sqrt_works_gen_2(10), real_of_nat_le(8), real_of_nat_add(8) |
| iterate | 52 | 33 | finite_natseg(31), iterate_empty(7), card_natseg(5), natseg_add_split(4), iterate_union(4), iterate_eq(4), iterate_superset(4), support_support(3), iterate_closed(3), iterate_related(3), iterate_eq_neutral(3), iterate_closed_nonempty(3), iterate_related_nonempty(3), iterate_delete(3) |
| sums | 55 | 25 | nsum_const(5), sum_clauses_right(5), sum_lmul(4), sum_const(4), nsum_le(3), nsum_sing(3), sum_le(3), nsum_lmul(2), nsum_lt(2), nsum_swap(2), sum_lt(2), sum_abs(2), sum_swap(2), real_of_nat_sum(2) |
| products | 14 | 8 | nproduct_sing(2), nproduct_pos_lt(1), nproduct_eq_0(1), nproduct_le(1), nproduct_mul(1), nproduct_const(1), product_pos_le(1), product_pos_lt(1) |
| card | 9 | 2 | countable_subset(2), nat_countable(1) |
| function | 0 | 0 | - |
| realset | 12 | 10 | sup(4), inf(3), has_inf(3), has_sup(3), inf_finite(2), sup_finite_lemma(1), has_inf_inf(1), sup_exists(1), has_inf_approach(1), has_sup_approach(1) |
| floor | 38 | 7 | integer_add(3), floor(2), real_floor_eq(2), real_abs_integer_lemma(1), integer_sub(1), floor_unique(1), real_frac_eq_0(1) |
| misc | 14 | 7 | from_0(11), real_interval_open_subset_closed(4), in_from(3), finite_inter_natseg(2), from_inter_natseg_gen(1), infinite_enumerate_eq_alt(1), convergent_bounded_increasing(1) |
| gcd | 6 | 4 | divides_exp2(1), divides_fact(1), divides_rexp(1), finite_special_divisors(1) |
| prime | 13 | 4 | prime_divexp(4), index_1(3), primepow_divisors_divides(2), index_fact_alt(1) |
| lcm | 0 | 0 | - |

## 4. 建议工作序（严格自底向上，先解 blocker）

1. **logic**（39）：`imp_false_iff, exists_false, conj_iff_left, disj_iff_left, exists_eq, exists_disj_conj_distrib` 先解。
2. **nat**（36）：`not_le(32), less_eq_exist(17), eq_mult_lcancel(16), le_antisym(9), let_trans(7), mult_Suc_right, less_exist, lte_trans, mult_eq_1, nat_minus_suc, lt_trans…`
3. **set**（23）：`subsetE(11), union_comm, subset_trans, subset_diff, lfp_fix_upper, lfp_fix_lower`。
4. **int**（181）：无外引用但为 rat/real 的地基，需整体补齐。
5. **rat**（4）→ **real**（122，其中 28 个 blocker）→ **realset/floor/misc**。
6. **iterate(52)/sums(55)/products(14)/card(9)**：`finite_natseg(31)` 优先。
7. **gcd(6)/prime(13)/lcm** 收尾。

> 纪律：不用 z3 / norm / auto / simp；全部手写 `rewrite`/`rule`/`intro`/`induct`/`cases` 等步骤。

---

## 5. 进度与遗留（2026-09-12，nat 专项）

nat 现状（`python .cache/validate_one.py nat`，trust=LIBRARY_ORACLES）：
**VALID 156 / 226，UNPROVED 9，DEP_FAILED 59，STEP_FAILED 1**（开工基线
VALID 55 / UNPROVED 34 / DEP_FAILED 132 / STEP_FAILED 1）。

已解 blocker（全部手工，无 z3）：`mult_Suc_right`、二进制位加乘 8 条、
`less_eq_exist(17)`、`less_exist(5)`、`less_lesseqI`、`less_lesseq(9)`、
`le_antisym(9)`、`lt_antisym`、`let_antisym`、`lt_trans`、`let_trans(7)`、
`lte_trans(5)`、`not_le(32)`、`not_lt`、`eq_mult_lcancel(16)`、`eq_mult_rcancel`、
`nat_norm_test1`；并修复预存 STEP_FAILED 的 `le_1_1`。

声明的顺序调整（必要，因为证明不能前向引用）：
- `less_lesseqI` 前移到 `less_lesseq` 之前（后者反向直接用前者）。
- `eq_mult_lcancel` / `eq_mult_rcancel` 前移到 `not_le` 之后（它们原来在
  `less_eq` 定义之前，无法使用序关系引理；更早引用仅在二者内部，其余在
  6463/6737 之后）。

剩余 UNPROVED（13）：`mult_eq_1(4)`、`bit0_neq`、`bit1_neq`、`bit0_bit1_neq`、
`bit0_neq_one`、`bit1_neq_one`、`nat_minus_suc(4)`、`even_exists_lemma(2)`、
`exp_mono_lt_imp(1)`、`nat_MAX(1)`、`divmod_uniq_lemma`、`div_le`、`div_mult_add4`。

剩余 z3（约 27 条，当前借 trust 判 VALID，需改手工）：
`le_mult_rcancel, lt_mult_rcancel, left_sub_distrib, not_even, not_odd,
even_add, even_mult, even_exp, odd_add, lt_exp, le_exp, divmod_exist,
divmod_uniq, mod_cases, mod_le_twice, mod_exists, div_mono, div_mono_lt,
mod_eq_0, div_eq_self, odd_mod, mod_add_mod, div_add_mod, div_le_exclusion,
div_div, div_mod, div_exp`。

已知难点：`mult_eq_1` 的正向需要一个 goal 假设（`0=1`）作为事实参与
`negE_gen` 造矛盾，而当前管线不把 goal 的 hyp 暴露为可引用事实
（见 `repl-client.md` §8.2）；可改结构（例如先用 `mult_nonzero` 反向证
`m≠0`/`n≠0` 再用 `Pre`）绕开。

### 5.1 第二轮补充（2026-09-12）

再补证：`mult_eq_1(4)`、`nat_minus_suc(4)`、`bit0_neq_one`、`bit1_neq_one`
（后者解锁 `nat_const_ineq` 方法）、`nat_norm_test1`。

**已修复**：`sub_eq_0`（`x - y = 0 <-> x <= y`）。它此前是 DEP_FAILED
（依赖未证的 `nat_minus_suc`），`nat_minus_suc` 证好后回放存量证明发现其
证明不完整。已重写：反向 `x<=y -> x-y=0` 用 `less_eq_exist` 取见证后对见证
归纳证 `x-(x+p)=0`；正向用 `cases "x<=y"` + `not_le`/`less_exist` 取
`x = y + Suc d`，借 `nat_plus_minus_2` 得 `Suc d = 0` 造矛盾。
`add_subr2` / `add_subr` / `sub_add` 随之 VALID。

**跨分支别名（重要）**：`StableProofState` 按命题值去重分配 sid，而
`apply_method` 用 `ItemID.can_depend_on` 限制事实必须与目标同分支且在前，
所以两个兄弟分支里字面相同的命题不能互相引用（报
`apply_method: illegal dependence`）。`mult_eq_1` 的解法是把共享的
`~(1=0)` 在 `type_cases` 之前 `forward` 出来当共同祖先，并让两支导出的
矛盾命题字面不同（一支 `1=0`、一支 `0=1`）。详见 `repl-client.md` §8.2。

**剩余 UNPROVED（9）**：`bit0_neq`、`bit1_neq`、`bit0_bit1_neq`（0 引用，
可用 `eq_mult_lcancel` + `mult_2` + `2!=0` 证；注意它们声明在
`eq_mult_lcancel` 之后需先整体后移）、`even_exists_lemma(2)`、
`exp_mono_lt_imp(1)`、`nat_MAX(1)`、`divmod_uniq_lemma`、`div_le`、
`div_mult_add4`。**剩余 z3：27 条**（同上轮清单）。

# pyHOL 地基债务清单

手工维护。基线快照见 `.cache/*.json`（`validate_library.py` / `.cache/validate_one.py <theory>`）。

参考库：HOL Light（`../hol-light`，边界 = `hol_lib.ml` 的 `loads` 列表）、
Isabelle/HOL（`../mirror-isabelle`，边界 = `src/HOL/Main.thy` 的 import 闭包）、
Mathlib（`/d/code/lean/MyTactics/.lake/packages/mathlib/Mathlib`）、
HOL Zero（`../holzero`，最小可信 HOL 的对照）。

---

## 1. set 定义化留下的

已完成（提交 `b5808ea1`、`375857ee`）：`set 'a` → `typeabbrev set 'a = 'a ⇒ bool`；
17 个操作定义化；21 条公理降到 1 条；`finite` 由公理常量改成最小性定义，`finite_empty` 证成。

| 债务 | 位置 | 说明 |
|---|---|---|
| `set_equal_iff` 仍是公理 | `library/set.pyhol` | `A = B ⟷ (∀x. x ∈ A ⟷ x ∈ B)`。`library/logic_base.pyhol:91` 的 `extension` 只有单向 `(∀x. f x = g x) ⟶ f = g`。在 logic_base 补一条外延性 iff 即可消掉。 |
| `finite_insert` 未证 | `library/set.pyhol` | 语句是 iff `finite (insert a A) ⟺ finite A`。正向由 `finite_def` 展开即得；反向需 P-技巧（取 `Q B = P B ∧ P (insert a B)` 证其封闭）加 insert 交换律。 |
| `finite_induct` 缺失 | — | 从 `finite_def` 展开可证，是下面 6 条的前提。 |
| `finite_subset` `finite_union_imp` `finite_inter` `finite_image` `finite_delete` `finite_diff` 未证 | `library/set.pyhol` | 6 条 gap，依赖 `finite_induct`。 |
| `card` 未定义 | `library/set.pyhol` | 仍是 `const`。需有限集计数开发（双射 + 唯一性）。对照 HOL Light `Library/card.ml`、Isabelle `Finite_Set.thy`。 |
| `countable` 未定义 | `library/set.pyhol` | 仍是 `const`。可用 `image`/`nat` 的满射刻画定义。 |
| `subsetE` 未证，拖累 `subset_antisym`/`lfp_unfold` | `library/set.pyhol` | 后两者原就是 DEP_FAILED，非本次引入。 |

## 2. 仍是公理式的类型（`TConst` + 断言，不是定义）

| 类型 | 位置 |
|---|---|
| `int` | `int.pyhol:6` |
| `rat` | `rat.pyhol:5`（该文件仅 4 条未证环律，无逆元/除法/序/floor） |
| `real` | `real.pyhol:6` |
| `topology` | `topology.pyhol:7` |
| `net` | `metric.pyhol:5` |
| ~~`set`~~ | 已改为 `typeabbrev`（提交 `b5808ea1`） |

对照：三个参考库里只有 Isabelle 的 `Set.thy` 是公理 bootstrap（两条），
`int`/`rat`/`real` 在 Isabelle 与 Mathlib 都是构造的；HOL Light 连 `real` 都是
`nadd`（子类型）→ `hreal`/`real`（商）构造的，`realax.ml` 全文 0 条 `new_axiom`。

## 3. z3 步 = 缺失的定理，待手工重建

`grep -cE '^\s*[←→]\s*z3'`：全库 **861 步，分布在 23 个文件**（本次实测，2026-09-12）。

这些 z3 步是「当年找不到的引理」的直接证据：每一步都要换成手写证明
（`z3`/`auto`/`simp`/`norm` 在基础库里禁用；`nat_norm` 这类 level-10 有证明项的
领域计算允许）。**`nat.pyhol` 已经是 0**，是全库唯一清零的，可作为替换范式参考
（提交 `07fc8d04` 手工替换了它的全部 39 个 z3 步）。

| 文件 | 步数 | 文件 | 步数 |
|---|---|---|---|
| transcendentals | 193 | realanalysis | 19 |
| real | 132 | lcm | 18 |
| trig_series | 76 | products | 14 |
| realseries | 59 | misc | 12 |
| prime | 54 | iterate | 12 |
| realderivative | 53 | trig_sin_cos | 11 |
| trig_atn | 42 | realset | 6 |
| trig_exp_log | 37 | int | 3 |
| sums | 37 | hoare | 2 |
| realintegral | 34 | floor | 1 |
| metric | 25 | card | 1 |
| gcd | 20 | **合计** | **861** |

替换时要注意：`.cache/check.py` 不注入 z3 后端，是真正能卡住显式 z3 步的校验方式；
`validate_theory(trust=...)` 对显式 `← z3` 步无效（显式 level-0 宏步自我授权）。
跑实验注意 `.cache/*.json` 会被写入（例如用 `--no-z3 --force` 跑一次会把状态污染成
STEP_FAILED），实验后要清理。

## 4. 机制缺口

- **类型定义原语**（HOL Light `fusion.ml:86` `new_basic_type_definition` 的对应物）——未加。
  当前类型只能公理式声明（`kernel/extension.py:77` `TConst`）；`set` 走类型同义词已经够用，
  商类型走 core 层的 `Quotient` item（产出公理，不是派生）。
- **良基递归**（Isabelle `Wellfounded.thy`/`Wfrec.thy`、HOL Light `wf.ml`）——没有。
- **一般递归定义**：`fun` 只支持结构递归（`core/defcheck.py:168`
  `check_fun_recursion`），没有一般递归/良基递归定义的合法性检查。

## 5. 缺失的理论（要新增的 `.pyhol`）

按依赖顺序 + 必要性排。**必要** = 不加就挡住别的；**补充** = 内容缺口。

- **P0 解锁现有 gap**：`logic_base` 补外延性 iff（消 `set_equal_iff` 公理）；
  `set.pyhol` 补 `finite_induct`/`finite_insert`；`card.pyhol` 扩写有限集基数
  （现只有 11 条可数定理）；`countable` 定义。参考 HOL Light `Library/card.ml`、
  Isabelle `Finite_Set.thy`、Mathlib `Data/Finset/Card.lean`。
- **P1 结构性大缺口（pyHOL 完全空白）**：
  序（Isabelle `Orderings.thy`/`Order_Relation.thy`、Mathlib `Order/Defs/`）——
  **谓词层已完成**：`'a::C` 类型类糖（一个类可贡献多条前提）+ `library/order.pyhol` 的
  `preorder`/`order`/`linorder`/`linorder_lt` 谓词、层级与严格序引理、`nat` 实例
  都已就位（见 `PROGRAM_VERIFICATION_PORT.md` §1.5）；auto2 `Lists_Ex.thy` 的列表层
  （`strict_sorted`、`ordered_insert`、`remove_elt_list`）与 Isabelle 的 `sorted`
  （≤ 版）连同各自的成员/集合/保序引理已在 `library/lists_ex.pyhol`；`lt`/`le` 桥接引理
  （`library/order.pyhol` 的 `linorder_lt_le`）与 `int`/`real` 的序类实例（`library/int.pyhol`、
  `library/real.pyhol`，
  两个理论因此各多一条 `imports order`）都已完成，只差 Quicksort 专用的
  `sublist` 刻画（归阶段 5，见 `PROGRAM_VERIFICATION_PORT.md` §4）与
  格（`Lattices.thy`/`Complete_Lattices.thy`/`Conditionally_Complete_Lattices.thy`/
  `Lattices_Big.thy`、Mathlib `Order/Lattice.lean`/`Order/CompleteLattice/`）、
  关系（`Relation.thy`/`Transitive_Closure.thy`/`Equiv_Relations.thy`、
  HOL Light `Library/rstc.ml`）、
  良基与递归（`Wellfounded.thy`/`Wfrec.thy`/`Zorn.thy`、HOL Light `wf.ml`/`Library/wo.ml`）
  仍缺。
- **P2 数据结构**：list 补全（已补 take/drop/sublist/last/butlast/map/filter/foldr/foldl/
  concat/zip/itrev/list_update/list_swap/remdups 的定义与 take/drop/map 骨架引理，见
  `PROGRAM_VERIFICATION_PORT.md` §1.4 与 `library/list.pyhol`；`sorted`/`strict_sorted`/`insort` 需序，归入 P1 序）；
  `option` 已建（`library/option.pyhol`）；`sum`（`Sum_Type.thy`）；
  `record`（`Record.thy`、HOL Light `Library/records.ml`）；`map`（`Map.thy`）；
  `finset`/`multiset`（`multiset` 已建：`library/multiset.pyhol`，用计数函数
  `'a ⇒ nat` 表示，避开缺失的类型定义原语；`mset`/单点/并/置换律已证）；`vector`/`tree`。
  有限集（`set` 理论）：`finite_induct`/`finite_insert`/`finite_subset`/`finite_union_imp`/
  `finite_inter`/`finite_image`/`finite_delete`/`finite_diff` 与 `lfp_*` 均已证
  （见 `library/set.pyhol`），**P0 有限集债清除**。
  基数层（同文档 §10，2026-09-13 续轮）：在 `card_empty`/`card_insert` 两条公理上
  证出 `card_image_inj`/`card_mono`/`card_image_le`/`card_subset_eq`、
  鸽子洞引理 `surjective_imp_injective` 与 `surjective_iff_injective`——
  **set 理论除 3 条故意留的公理外全部 VALID**。
- **P3 数系与代数**：`rat` 补全（现仅 5 条，无逆元/除法/序/floor；
  对照 `Rat.thy`、Mathlib `Data/Rat/`）；`binomial`/`factorial`；
  `Euclidean_Rings`/`GCD`；抽象代数 `group`/`ring`/`field`
  （`Groups.thy`/`Rings.thy`/`Fields.thy`、Mathlib `Algebra/`）；
  `Set_Interval` 风格区间求和。
  **待定决策**：`int`/`rat`/`real` 是否从公理化改成构造式（决定环律能否成为真定理）。
- **P4 补充**：`filter`（`Filter.thy`）、`cardinal`（HOL Light `Library/card.ml`）、
  `topology` 补全（现 2 条）、`string` 补全（现 2 条）。

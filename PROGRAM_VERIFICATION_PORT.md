# 复刻 auto2 程序验证：现状与交接

> 面向接手此任务的 AI。本文件只讲**表达能力移植**（把 auto2 的定义与命题写得出来），
> 不涉及自动化移植。素材：`../auto2`（Isabelle 源码，权威）、`../mirror-isabelle`、
> `../hol-light`。仓库现状契约见 `ARCHITECTURE_AUDIT.md`、`FOUNDATION_DEBT.md`，
> 工作方式见 `AGENTS.md`，本文件只负责**移植进度与库层面经验**。

## 0. 任务边界

- **要什么**：让 pyHOL 写得出来 auto2 `HOL/Program_Verification/` 的定义与命题。那份开发共
  **941 个声明**（datatype 20 / definition 161 / fun 105 / abbreviation 7 / function 5 /
  partial_function 30 / instantiation 6 / typedef 1 / inductive 2 / lemma 539 / theorem 65），
  分布在 28 个 `.thy`（Functional 13 个约 144KB，Imperative 15 个约 100KB + 1600 行 ML 分离逻辑胶水）。
- **不要什么**：auto2 的证明自动化（约 1.5 万行 ML 的饱和式证明器）。
- **地基**：`def`/`datatype` 落到 `Thm.axiom`（`core/items.py` 的 `Definition/Datatype.get_extension`
  → `defcheck.mk_axiom`），类型与常量只是签名扩展；`fun` 已改成展开成**派生条目**（§2）。
  `undefined`（`logic_base`）是"不覆盖的输入"的出口，与 Isabelle 的
  `axiomatization undefined :: 'a` 同义。

---

## 1. 现状

### 1.1 auto2 六个阶段

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | 基础库：`prod` 积类型 + `relation` | 完成 |
| 2 | 逻辑基础库：`option`、list 补全、`multiset`、有限集/基数、关系演算 | 完成（余量见 §1.4） |
| 3 | 序：`linorder` 谓词化 + `int`/`real` 实例 | 完成 |
| 4 | 良基与递归：`wf`/`acc`/`wfrec` + 关系归纳 + `function` 前端 | 完成（余量见 §1.4） |
| 5 | Functional 领域库：`Mapping_Str`、`Union_Find`、`Interval`、`Arrays_Ex`、`Indexed_PQueue`、Quicksort… | 未开始，清单见 §3 |
| 6 | Imperative：堆模型 + 分离逻辑基座 + 12 个实例 | 未开始，清单见 §3 |

### 1.2 递归前端（`fun`）对齐伊莎贝尔 Function 包

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | 覆盖证明器（`pat_completeness.ML`） | 完成 |
| 2 | `f.induct`（`induction_schema.ML`） | 完成 |
| 3 | 算术引擎：AC / 乘法 / 减法归约（`core/measure.py`） | 完成 |
| 4 | 模式减法 / 带洞定义（`pattern_split.ML`） | 完成 |
| 5 | 组合度量：`size_list f` 这类候选（`measure_functions.ML`） | 完成 |
| 6 | 互递归 `fun … and …` | **达成**（§2.2）：五样齐，N 个函数 / 多参数 / 多调用 / 结果类型不同 / 参数类型不同全部由输入算出；块的 order 三条路（推断度量、每函数一条 `measure` 链、组自己的 `relation`） |
| 7 | `f.cases` / `f.elims` / `fun_cases` | 部分：`<c>_cases`/`<c>_elims` 已发射（§2.3）；`fun_cases` 与布尔特化未做 |
| 8 | `partial_function` | 未做（§2.4） |
| 9 | `size_change`（scnp） | 未做（§2.5） |

### 1.3 已知缺口（真未实现）

- **家族上的递归 `fun`**（互递归 datatype 的下降）。`datatype … and …` 已经能写、能注册
  （家族声明、每成员的互归纳规则 / `_cases` / 区别性 / 单射性 / 析构子，§2.2 缺口三），
  但**家族的 subterm 关系与 size 没有生成**：跨成员的下降不是单个成员上的结构递归，关系要建在
  所有成员的和类型上（与 `fun` 的编码同款），家族的 size 本身又是互递归的。因此**递归**的 `fun`
  落在家族类型上时仍走公理；非递归定义、`type_cases` 分裂、互归纳证明都可用。
  边界由 `library/tests/mutual_datatype_test.py` 与 `core/tests/items_test.py::DatatypeFamilyTest`
  钉住（`<成员>_size` / `<成员>_wf_subterm` 不存在）。
- **度量路径里嵌套模式的调用重命名不完整**（`core/fungen.py` 的 `ren_call` 一带）。最小复现：
  `fun tdepth :: tri list ⇒ nat | tdepth (TriS t # xs) = Suc (tdepth (t # xs))`——模式里元素被
  拆开、递归调用重新组装列表——发出的目标条件写成 `tri_TriS_1 (TriS t) # xs`，而 mlex 链文本写成
  `t # xs`，重放必失败。这个形状恰好是"元素度量（`tri_size`）唯一能让下降严格"的场合，所以组合
  度量目前只覆盖"容器自身构造子"的降序。修法二选一：补全重命名，或诚实 `FunGenError` 退回公理
  （**不允许发出重放不过的条目**）。
- **参数化 datatype 的 size 族归纳**：`wfrec_example/seq_size_induct`、`gcl/varType_size_induct`
  两条重放失败（与 `fun` 前端各阶段的改动无关，是既有问题），症状是 `rewrite` 步失败。
- **`int`/`real` 的两条未证引理**（`real_inv_0`、`real_mul_linv`）：交互可证、重放不可证——z3 的
  归一化按 `has_theorem` 决定用哪些重写规则，重放时 `real_inverse_divide` 还不在作用域。结论与
  两种修法写在 `library/real.pyhol` 的 NOTE 里。

### 1.4 库层面余量（非阻塞）

- **list**：`nth_list_update_diff`；`foldr`/`foldl`/`concat`/`zip`/`remdups` 只有定义无引理；
  `sublist_*` 属阶段 5（auto2 放在 `Arrays_Ex`）。
- **multiset**：`mset_list_swap`、`set_list_swap`（要先有 `count` 对 `list_update` 的逐点刻画）。
- **set**：基数层已收口，只剩 3 条刻意留的公理（`set_equal_iff` 与两条 `card` 递归）。
- **`int`/`real`**：实例已完成；其余算术/除法/幂等引理属 `FOUNDATION_DEBT.md` 的 P3 数系债。

### 1.5 已实现的前端机制（其它文档引用的锚点）

- **类型类糖**：类型变量可带类注解（`'a::linorder`），一个类贡献**一条或多条前提**；类条目写成
  `class <name> = <pred> (<op> :: <type>, …), …`（`syntax/pyhol.py`），与 `typeabbrev` 同款处理。
  类前提在**每个分支各引入一份**（§4.7 第 48 条）。
- **序的谓词层**：`library/order.pyhol` 的 `preorder`/`order`/`linorder`/`linorder_lt` 与桥接类前提
  `linorder_lt_le`；`nat` 实例 + `int`/`real` 实例（两个理论因此各多一条 `imports order`）。
- **`-` 的集合实例**：`minus` 在 `'a set` 上有方程（在此之前它是未解释常量，§4.1 第 9 条）。
- **`fun` 的四条规则与子句**：见 §2.1；`<c>_exhaustive`/`_cases`/`_elims`/`_induct` 的命名与形状
  见 §2.1 与 §4.8。

---

## 2. 递归前端：已落地与边界

### 2.1 单函数 `fun`

`fun` 展开成**派生条目**（`core/fungen.py`）：`<c>_H` 体函数、`<c>_rel` 递归关系、`<c>_in` 不动点，
方程由良基性证明；每个定义还得到 `<c>_exhaustive`（覆盖析取）、`<c>_cases`（自己的 case 规则）、
`<c>_elims`（消去规则）、`<c>_induct`（关系归纳）。规则形状的样例在 `library/rules_example.pyhol`
（无变量子句、多参数多子句、布尔值）。

- **终止**：先由度量引擎（`core/measure.py`）找字典序链（各参数位一列）；找不到就退回 datatype 的
  subterm 关系。文件可以用 `measure "%m n. m"` 直接给链，或给 `relation` + `wf` + `descent`
  （关系写在两个**元组**参数上，obligation 由命名引理结清；`measure` 与 `relation` 不可同时给，
  `wf`/`descent` 缺一即报错）。
- **补全**（`_complete_equations`）：被前一条覆盖的规则做**模式相减**（`osum n 0` → `osum (Suc n) 0 = Suc n`），
  洞补 `= undefined`；单函数路径与互递归块同一套。一条子句被前面的完全覆盖时诚实报错
  （`covered by the equations before it`）。
- **样本与测试**：`library/{measure_example,wfrec_example,rules_example,fungen,...}.pyhol`、
  `library/tests/{fungen,measure_example,...}_test.py`、`core/tests/{fungen,measure}_test.py`。

### 2.2 互递归块 `fun … and …`（阶段 6，验收达成）

**编码**（伊莎贝尔 `mutual.ML` + `sum_tree.ML`）：N 个函数编成单个 `fsum : ST ⇒ RST`，交给单函数
机制定义并证明，再把定义、方程、`_exhaustive`/`_cases`/`_elims`/`_induct` 投影回各函数。

- **参数侧**：各函数参数元组类型的**平衡和树**（`_sum_split` 对半切，形状只由 N 决定，深度
  O(log N)，不镜像调用图）。注入 / 投影 / 谓词树（`mk_sumcases`）/ 步进序列都沿路径走。
- **结果侧**：结果类型**去重后**取和；每个函数的定义是结果投影，子句右端放到自己那侧，表达式里的
  调用写被调方的投影。
- **地基在 `library/either.pyhol`**（不叫 `sum`：那个名字是 `library/sums.pyhol` 的集合求和，
  它手写的 `sum_cases` 会让同名 datatype 的 cases 公理被加载器静默跳过；`'a + 'b` 这种中缀写法也
  解析不了）：`datatype either 'a 'b = Left 'a | Right 'b`、`either_case`（Isabelle 的 `sum_case`）、
  `either_rel`（每侧一个关系提升到和上）与 `wf_either_rel`，外加六条关系引理（两侧的注入 / 反推 /
  互不相容）。该理论的 `imports` 要带 `prod`（多参数定义走元组，`_require_in_scope` 要 `fst_def_1`）。
- **块的 order 三条路**（`fungen._block_order`，同一块只走一条）：
  1. **推断度量**：每个参数位一列（`_sum_column`）——各叶子在该位的度量用 `either_case` 串起来，
     缺的给 `zero_measure`；跨函数调用比较的是"被调方在调用点的度量 < 调用方在模式上的度量"。
     `measure.CaseRule` 让引擎认识 case 组合子的归约（名字由发射器给，引擎不认识任何具体常量）。
  2. **块级 `measure`**：写在**各函数自己那一段**里，一组函数各一条链，链内多条即多条度量。
  3. **组自己的 `relation`**：写在编码的和类型上（`((A1×A2),(B1×B2)) either ⇒ … ⇒ bool`，与
     Isabelle 互递归 `function` 同款），配 `wf` 与每条调用一条 `descent`；义务在**编码调用**上结清
     （`R (Right (Pair n m)) (Left (Pair (Suc m) n))`）。**不建列、不发 `<f>_m<k>`**。
- **子句补全**：块也先跑 `_complete_equations`（`_complete_group`），编码与全部投影同一份补全后的列表；
  相减/补洞出来的方程文本由发射器打印（含类型标注）。
- **逐步计数静态算出**：每步产生几个条目由模板决定（会提前关门的步骤在代码里 `if` 判定），
  投影引用的定理名取自实际发射出的条目（`get_overload_const_name` 可能给带后缀的名字）。
- **命名**：编码名 `<a>_<b>_sum`（查重）。函数名撞已有常量会静默出事——`nat` 自带 `even`/`odd`，
  `def` 条目被加载器静默跳过，`even_def` 解析到 nat 的那条，整个证明跑偏。

**库样本**（每个块都整文件强制重放 VALID）：

| 文件 | 覆盖 | 条数 |
|---|---|---|
| `mutual_example.pyhol` | `even2`/`odd2`，`even2_or_odd2` 用一次互归纳 | 22 |
| `mutual_examples.pyhol` | 三函数（和树两层）+ 双调用子句；双参数（每参数位一列）；两种结果类型（结果侧取和）；参数类型不同（`nat` 与 `nat list`）；块级 `measure`（`coll`/`done_coll`） | 115 |
| `mutual_completion.pyhol` | 洞（补 `= undefined`）与重叠（相减） | 48 |
| `mutual_relation.pyhol` | 组自己的 `relation`：`swapf`/`swapg` 每次对调参数，和减一而任一参数都不减（推断度量带不动，和类型也不是结构递归） | 31 |

**测试**：`library/tests/{mutual_example,mutual_examples,mutual_completion,mutual_relation,prod_size}_test.py`
与 `core/tests/fungen_test.py` 的 `MutualEncodingTest`/`CoverageVariableTest`（和树与路径、注入/投影、
谓词树、列文本、重复命题的 ID、缺和类型时报错、洞/重叠/完全覆盖被拒、relation 的规则与拒绝条件、
`<c>_exhaustive` 的自由名不被模式变量捕获）。

**验收**：一个两函数互递归的样本拿到方程、`_exhaustive`、`_cases`、`_elims`、`_induct` 五样，且归纳
规则能在库里用一次——**达成**，且是在一般实现上达成的。

**缺口三（部分）：`datatype … and …`**

已落地：语法（`and` 续块；单个类型仍是扁平形状，多个类型一个条目带 `groups`）、注册（成员一起登记，
构造子可拿兄弟当参数）、每成员的构造子区别性 / 单射性 / `_cases` / 析构子，以及**互归纳**：每个成员
一条 `<ty>_induct`，语句带全家族的谓词 `P1…Pn`，`MNode l f` 分支拿到 `P2 f`。这一类规则**不挂**
`var_induct`（`induct` 方法要把唯一谓词实例化成目标，家族规则没有那唯一谓词），用
`rule <ty>_induct param_P1=… param_P2=… param_x=…` 手写实例化。
样本 `library/mutual_datatype.pyhol`（`mtree`/`mforest`），两条定理各用一条家族规则证完。

未落地：**家族的 subterm 关系与 size**（见 §1.3），所以**递归**的 `fun` 落在家族上时仍走公理。

### 2.3 阶段 7：`f.cases` / `f.elims` / `fun_cases`

已落地 `<c>_cases` 与 `<c>_elims`（每个展开的 `fun` 的两条规则，与 `_exhaustive`/`_induct` 并列；
`library/tests/fungen_test.py` 的不变量测试要求四条齐）。

- **`<c>_cases`** 形状与 datatype 的 `<ty>_cases` 同款：`(⋀v̄₁. P P₁) ⟹ … ⟹ (⋀v̄ₙ. P Pₙ) ⟹ P p`，
  `P`/`p` 是自由变量。因此不需要新 tactic：`type_cases x cases_thm="<c>_cases"` 直接可用。
- **`<c>_elims`** 是伊莎贝尔的 `f.elims` 去掉域条件（pyHOL 没有 `dom`）：
  `f x̄ = y ⟹ (⋀v̄₁. T = P₁ ⟹ y = R₁ ⟹ P) ⟹ … ⟹ P`。用法是 `rule <c>_elims facts=[<方程>]`。
- 两条规则都比 datatype 的构造子更细：嵌套模式（`dbl (Suc (Suc n))`）与补 `undefined` 的洞都是一个分支。
- 命名：谓词/分支变量避开方程自己的变量名（`filter` 的模式变量就叫 `P`，于是谓词取 `P1`）、避开
  `_elims` 里 RHS binder 的绑定名（`strict_sorted` 的 RHS 是 `(∀y. …) ∧ …`）。
- **用法坑**：`type_cases … cases_thm=` 的分割要在 `intro` 之前（已 `intro` 出来的事实不代入分支）；
  `type_cases` 要一个**变量**，多参数定义得给元组变量。
- 验收（已过）：`library/gcl.pyhol` 的 `scalar_of_nat_id`/`scalar_of_bool_id` 原是两条公理，现在用
  `type_cases` + `cases_thm` 证明；消去规则的用法见 `library/rules_example.pyhol` 的 `gz_value_shape`。
- 余下（可选）：`fun_cases`（把 elim 特化到给定实例）在 pyHOL 里不必要——`rule` 直接吃
  `facts=[<方程>]`；布尔返回类型的两条特化规则同理（通用规则对布尔定义同样工作）。

### 2.4 阶段 8：`partial_function`

另一个顶层命令，严格说不属于 `fun` 对齐；auto2 有 30 处 `partial_function (heap)`，都是堆单子不动点
（与 §3 的堆模型绑定）。**依赖**：ccpo/不动点库（`option.fixp_fun`、`mono_body`、`fixp_induct_uc`）与
`partial_function_mono` 规则集；单调性自动化还依赖对 datatype case 表达式分情形的 tactic。
**成本最高，且与阶段 6/7/9 正交**——建议与 Imperative 堆模型一起评估。
**验收**：至少一条 `partial_function`（非堆，如 `option` 上的不动点）能定义出方程 + 归纳规则。

### 2.5 阶段 9：`size_change`

`scnp_solve.ML` + `scnp_reconstruct.ML` 共 604 行；求解算法自包含，重建深度绑定伊莎贝尔。
**缺的库比代码多**：`library/multiset.pyhol` 的 26 条定理全是代数（`count`/`union_mset`/`filter_mset`/`mset`），
**没有多重集序**（无 `mult`/`mult1`/`wf_mult`）；`reduction_pair`、集合的 `max_ext`/`min_ext`、`acc` 与
SCC 分解（`termination.ML:342` 的 `decompose_tac`）也都 grep 不到。
**它只决定"更难的终止性能不能自动证出来"，不影响能证的集合**：`relation` + 用户下降引理已覆盖同一批
定义。**放在最后做**。**验收**：一个现有 `relation`+`descent` 样本定义，去掉手写子句后仍能自动终止。

---

## 3. auto2 六阶段里剩下的两块

### 阶段 5：Functional 领域库

按依赖顺序补（文件大小是规模参考）：

1. `Mapping_Str.thy`（9.2KB）：`datatype ('a,'b) map = Map "'a ⇒ 'b option"`（函数类型字段，正性检查放行）
   empty/update/delete/keys_of/map_of_alist/map_of_aset/unique_keys_set。
2. `Partial_Equiv_Rel.thy`（2.4KB）：**已完成**。
3. `Union_Find.thy`（6.3KB）：`rep_of` 递归、`ufa_invar`、`ufa_α`。
4. `Interval.thy`（3.0KB）：`datatype 'a interval`、`idx_interval`、自定义序。
5. `Arrays_Ex.thy`（8.3KB）：`list_swap`、`sublist`、`list_update_set`、`array_copy`。
6. `Indexed_PQueue.thy`（18.3KB）：堆不变量。
7. 算法：`Lists_Ex` → `BST` → `RBTree`；`Quicksort`；`Interval_Tree` → `Rect_Intersect`；`Connectivity`；`Dijkstra`。

这些定义大量是**索引驱动递归**（`part1`/`quicksort`/`idx_bubble_down_fun`/`rect_inter` 用
`measure (λ(_,l,r,_). r - l)` 之类），终止性依赖用户给的引理——pyHOL 侧就是 `fun` 的
`measure`/`relation` + `descent`（已支持），或 §1.3 的组合度量。

### 阶段 6：Imperative

**最大的一块，也是唯一需要重建"堆模型"的阶段。** auto2 建立在 Isabelle 的 Imperative_HOL 上：
带类型 ref/array、`lim`、堆单子（`return`/`bind`/`effect`/`execute`）。pyHOL 只有裸 `nat⇒nat` 堆
（`library/mem.pyhol` 是雏形）。

1. **堆模型**：`heap`/`addr`/`lim`/`refs`/`arrays` + `Ref`/`Array` + 堆单子。可选用无类型堆规避
   `'a::heap` 类（auto2 有 92 处 `::heap`，那是序列化类，不是序），代价是堆里存不了任意类型。
2. **分离逻辑**：`pheap`/`in_range`/`relH`/`assn`。`SepAuto.thy:75` 的 `typedef assn = "Collect proper"`
   是全仓唯一一处 typedef——用 `datatype assn = Assn (pheap ⇒ bool)` + 显式 `proper` 前提替代，
   或声明类型 + 公理。`emp`/`*` 定义成普通常量，`assn_one_left` 之类代数律本来就要手证。
   另：`'a node ref option` 这类"自身嵌进别的类型构造子"会被正性检查拒（§4.1 第 3 条），要么手工声明
   类型 + 公理（`core/items.py::Quotient` 是先例），要么改无类型堆。
3. **12 个实例**：`Arrays_Impl` → `DynamicArray` → `LinkedList` → `BST_Impl` → `RBTree_Impl` →
   `IntervalTree_Impl` → `Indexed_PQueue_Impl` → `Union_Find_Impl` → `Quicksort_Impl` →
   `Connectivity_Impl` → `Dijkstra_Impl` → `Rect_Intersect_Impl`。
4. 自动化胶水（`sep_steps.ML` 824 行、`assn_matcher.ML` 324 行）**不在范围内**。

---

## 4. 写 pyHOL 证明：坑与配方

全部实测。按主题分组，编号只为引用方便。

### 4.1 语言与解析

1. **datatype 构造子行漏写 `|` 会静默产出零构造子**：`_parse_datatype` 在第一个非 `|` 行 break，
   `constrs = []`，随后 `datatype_axioms` 生成空的 `X_induct`/`X_cases`。防身：声明后查定理名齐不齐
   （单构造子应得 `X_<C>_inject`、`X_induct`、`X_cases`；多构造子还有 `X_A_B_neq`）。
2. **字段名不能取投影函数名**：字段名会被 `_cases`/`_induct` 当绑定变量，`Pair (fst :: …, snd :: …)`
   会遮蔽 `fst`/`snd`，`rule prod_cases` 的子目标没法用。改名 `left`/`right`，投影单独 `fun`。
3. **正性检查**（`core/defcheck.py`）拒绝"自身嵌进别的类型构造子"：`datatype 'a node = Node (val :: 'a)
   (nxt :: 'a node ref option)` 直接拒。绕过：`TConst` + `Constant` + 公理手工声明，或改无类型堆。
4. **多参数类型的两种写法不同**：声明后缀 `datatype prod 'a 'b =`；类型表达式前缀 `('a,'b) prod`
   （`prod 'a 'b` 不解析）。
5. **`imports` 逗号分隔**（`imports set, prod`）；写成空格报 `KeyError: 'set prod'`。
6. **`#[N]` 注解可省**：`.pyhol` 里它是纯文档，replay 不验证命题；`goal=`/`facts=` 的数字才是硬约束。
7. **`facts=[...]` 在文件里只吃数字**（REPL 另有语义引用，见 §5）。写了命题文本会得到
   `fact sid '[' not found` 这类费解报错。
8. **定义里的类型注解只是标记**：`fun ordered_insert :: 'a ⇒ 'a list ⇒ 'a list` 的体里 `x < y` 解析成
   通用重载常量，不需要也不接受前提注入。
9. **重载常量在缺实例时是未解释常量**：`A - B` 在集合上曾能通过类型检查、打印也与集合差一样，但没有
   任何方程（`refl` 关不掉、`rewrite` 也打不上）。遇到"看起来对但推不动"的算术/集合符号，先查实例。

### 4.2 稳定 ID 与依赖

10. **sid 按 Thm 分配**（`method/stable_state.py::_ensure_sid`），`Thm.__eq__` 比的是**假设集合 + 命题**：
    命题相同、假设集合不同 = 两个条目。
11. **依赖按位置判定**（`ItemID.can_depend_on`）：同分支且位置在前。兄弟 `cases` 分支的事实、被
    `cut`/`rule` 展开后位于其后的行，都用不了（`apply_method: illegal dependence`）。
12. **重复命题共享 sid，会封死跨分支引用**：同一命题在多个分支出现时只有一个 sid，属于最早的位置。
    要跨分支用的命题必须在**进入 `cases` 之前**展开，或拆成单分支引理（§4.6）。
13. **不能前向引用**：`validate_theory` 把理论截断到该定理之前再 replay。引用声明在自己后面的定理/定义，
    探针里能过、独立 replay 必 `STEP_FAILED`。
14. **定义体引用未声明的常量会被静默丢弃**：item 解析失败只记 `item.error` 并跳过，常量根本没注册；
    下游症状是解析期"变量未声明"，`inst` 用变量代入"侥幸"通过而生成的定理毫无意义。排查：翻
    `theory_cache[f]['content']` 里的 `.error`。
15. **sid 会随证明增长重排**：中间插一步，其后 sid 全部平移。REPL 里用语义引用（`goal=@`、
    `facts=["<命题>"]`），最后一次性把字面 sid 写进文件。
16. **`cut "P" goal=N` 的 N 必须是开口目标**。指到一条事实（如守卫）上不报错、`check` 也照 VALID，
    但完整重放报 `CheckProofException: output does not match`（新定理的假设集成了那条事实的兄弟分支）。
    **最容易翻车的一处**：改一个数字即通过。
17. **`cut` 的可用事实 sid 是"证明 P 之后新出来的那个"**，不是 cut 行编号；用 `all` 看一眼再引用。
18. **`intro` 后目标不一定保持 sid**：第二次 `intro` 可能撞上已出现的同命题而合并，目标换 sid。每步之后
    看 `all`，用最后一条 open goal，别按"上一步 +1"推算。

### 4.3 重写

19. **`rewrite` 不带 `loc` = 先定位（最外层优先）再替换*全部*同形项**：`set_def_1` 一步会把目标里两处
    `set []` 同时换掉；`insert_comm` 会把等式两边同时交换，只想动左边要写 `loc=0.1`。
20. **`loc` 按项树算**：`A ⟷ B` 的左/右操作数是 `0.1`/`1`，`f a` 的参数是 `1`。没把握就先小范围试。
21. **重写必须有效果**（`has_rewrite`），否则 `InvalidDerivationException: rewrite_fact using X`。
    展开链因此有顺序约束：外层的展开要等内层先打开。
22. **对事实重写时，事实里的变量必须在上下文里声明**：`intro`/`elim` 引进的变量会让重写直接失败。
    对策是把这类 iff 前向化下沉成带 `fixes` 的辅助引理。
23. **带前提的重写定理可以直接带 `facts=[<条件…>]` 重写目标**，省掉"先 forward 出等式事实"的一步。
24. **`sym=true` 是反向用等式**：定义用 `sym=false` 展开，`[] @ xs = xs` 反向才是 `xs → [] @ xs`。
25. **iff 定理改写目标会产生"转换子目标"**（被改写子项的那条等式成为新目标），要再用定理或引理关掉；
    左右两边恰好互为实例的情形会自动关门。

### 4.4 `rule` / `forward` / `inst`

26. **`rule` 只吃不超过前提数的 facts**；多前提定理要么全给、要么显式给 `param_*`（元变量从目标推不出来
    时只报 `ParameterQueryException`）。
27. **`rule` 匹配的是定理的结论**。带前提的引理用之前要先把目标 `intro` 成结论形态，再
    `facts=[<前提…>, <假设事实>]`。
28. **`rule` 对否定式定理会报 `too many previous facts`**（`¬` 是独立常量，`strip_implies` 看不到前提）。
    形状 `~A` 的定理配事实 `A` 用 `resolve`。
29. **∀-形式的命题不是重写规则**，`rule`/`rewrite`/`accept` 都对它报错。用法只有 `forward`（给全
    `param_*`）→ `inst <项>` → `apply_prev`；含空格的实参要加引号。**只用 `fixes` 声明、命题里不写
    `!` 的定理才是可重写的等式。**
30. **∀-形式且带蕴含的定理，`forward` 也用不了**（`strip_implies` 看不进 ∀）。唯一配方：`cut` 出原命题 →
    `accept <thm>` 得 ∀-事实 → `cut` 出实例 → `apply_prev facts=[∀-事实, 实证]`。
31. **`forward` 的 facts 要按定理前提顺序给全**，否则 matcher 拿第一条前提去比，报类型不匹配。
32. **推导结果与目标同命题时 `forward` 不新增条目**（可能直接关门）；没关门时用
    `apply_prev facts=[<∀/蕴含事实>, <参数事实>]`。`assumption` 只认目标自身的假设集，不认兄弟事实。

### 4.5 归纳与分情况

33. **`induct` 必须作用在整条蕴含上**：先 `intro` 把假设变成事实，ih 会退化成"结论 ⇒ 结论"而完全无用。
    正确顺序：`induct <var>` → `intro` 进分支。
34. **自由变量分情况用 `type_cases <var> goal=N`**，`rule <ty>_cases` 匹配不上自由变量；`type_cases` 后
    子目标常带 `!x.` 前缀，要 `intro` 再关。
35. **`type_cases` 不代入已 `intro` 出来的事实**（行不可变模型）。带守卫的引理要**把守卫重新折回目标**：
    `intro xs` → `cut "<守卫> --> <结论>"` → `type_cases xs` → 各分支收口 →
    `apply_prev facts=[<cut 事实>, <守卫事实>]`。
36. **索引驱动的递归函数**（`take`/`drop`/`nth`/`list_update`）的一般引理只能是 ∀-形式（对任一个参数归纳，
    ih 的另一个参数都对不上），代价见 §4.4 第 29 条。对策：另证"列表作参数、索引作模式"的展开特化引理
    （`take_cons`/`drop_cons`/…）供重写，∀-形式的总结论只偶尔 `forward`+`inst` 引一次。

### 4.6 常用配方

37. **把定义展开固定成一条引理**（如 `per_union_iff`、`remove_elt_list_mem`）：先证成员/展开刻画，打
    `[hint_rewrite]`，此后下游引理只依赖它。**每个用 `{p. …}`/`∪`/`image` 定义的集合算子都该这样。**
38. **按分支拆引理**：跨分支共享 sid 会 `illegal dependence`（§4.2），把 3×3 这类情况拆成 9 条单分支
    引理，主引理只留骨架。
39. **`forward` 做传递链**：`→ forward goal=N facts=[<传递事实>, <前提1>, <前提2>]` 一步得结论
    （事实本身排第一）。
40. **消析取**：出析取后用 `disj_comm` 换序 + `force_disj_true1/true2` 消掉已知为假的一支（注意朝向：
    `true1` 消第二个析取项，`true2` 消取反的第二个；要消第一个先换序）。矛盾支用 `negE_gen`
    （结论可与任意目标合一，不必先转 `false`）。
41. **"存在量词套等式"用 `exists_flatten`** 清理；`comp_fun_def` 展开产生的 β-redex 由重写器自动约简。
42. **常量引理的左右形式要看清楚**：`conj_false_left` 是 `P & false`、`conj_false_right` 是 `false & P`
    （`conj_true_*` 同理）。写反只报 `rewrite: unable to apply theorem`，先 `thm <名字>` 确认。
43. **集合等式先降到成员层**：先在成员层面归纳（`remove_elt_list_mem`），集合等式退化成 `set_equal_iff` +
    成员引理重写；直接对集合等式归纳会让命题级推理翻倍。
44. **`all_mem_elim`**：`(∀z. z ∈ B ⟶ P z) ⟹ y ∈ B ⟹ P y`——把"有界全称 + 成员事实"固定成一步。

### 4.7 库层面的约定

45. 基础库**禁 `simp`/`auto`/`norm`/`z3`**（见 `FOUNDATION_DEBT.md`）：用展开与显式规则写。
46. **证明一律用常驻 REPL + `repl/client`**（`AGENTS.md` §4），一条条 `item NAME` 导出、整段替换回文件；
    不要写每次重载理论的临时脚本。
47. **改了 `syntax/`、`repl/`、`.pyhol` 要换端口重起 server**（端口被占会明确报错退出 2）。
48. **类前提是每个分支各自一份**（同一命题在不同分支有不同 sid）：加一条类前提不能让脚本做全局编号平移，
    要按创建顺序分段偏移或干脆重证（`method/stable_state.py` 还要求注解条数 == 新建条目数）。
49. **`item NAME` 输出的是"当前证明"**：会话停在别的证明上时它会写出那条证明。导出后立刻核对 `prop` 行。

### 4.8 和类型编码与生成的名字

50. **一次消一个见证**：`elim "u,v"`（k≥2 个名字）会失败（方法把 ∃ 事实连同 k 个变量塞进外层 `intros` 行，
    而 `intros` 只用一次 `exE`）。配方：`elim "u"` 再 `elim "v"`。另注：这次失败**会留下半截条目**，
    失败后要么 `undo`，要么用 `all` 重读 sid。
51. **∀-绑定的变量不能 `type_cases`**（要"上下文里的变量"，而 `intro` 一次引进所有嵌套 ∀ 与 ⟹，守卫一
    变成事实就不再代入分支）。两条出路：(a) 让目标成为某个**有 ∀ 结论的定理**的实例，用 `rule` 配高阶
    谓词；(b) 展开定义自身的析取 → `disjE` → 每支 `elim` 见证 + `conjD1/conjD2` → 用析取项给的等式把目标
    改写成见证的样子。
52. **`rule` 能对 ∀-目标做高阶匹配**：`rule wf_induct goal=<!x. P (Left x)> facts=[<wf R1>]` 一步把
    `?P` 配成 `%z. P (Left z)`。前提是定理结论本身是 ∀，否则 §4.4 第 29 条适用。
53. **收口步（`rule ... facts=[...]`／`resolve`）落不落新行，取决于事实的假设集合**：落新行 ⇔ 事实们的
    假设并集 ≠ 被关那一行的假设集合。发射器静态算不出事实的假设集合，但知道自己走的是哪条路
    （`_refute_equality` 的 `extended` 参数就是为此）。症状：`replay failed at step: cut` 或后续
    `goal sid N not found`。**仍未修**：`_condition_negation` 末尾那处 `negE_gen`（没有触发它的样例，
    暂按计数 1）。
54. **稳定 ID 数的是命题，不是行**：同一份证明里第二次落同一条命题不占新号，写出来的 ID 还是第一次那个，
    而且这一步常常顺带 `auto_close`。触发条件与形状无关，两个递归调用走到同一个比较就会踩
    （`f (Suc n) = g n + h n`；`cycle3c (Suc n) = cycle3a n + cycle3c n`）——单函数路径同样有。
55. **同一条链的第二步要指上一步新开的目标**（`rewrite` 落下的新目标有自己的号），路径深度 ≥2 才会踩。
56. **`intro` 的多个变量用逗号分隔**（`data['names'].split(',')`），空格写的 `intro n1 m2` 会被当成一个
    名字，报 `strip_all_implies: not enough names input`。
57. **链式 `=` 是右结合**：`pos (Suc n) = cnt n = 0` 解析成 `(pos (Suc n) = cnt n) = 0`，报
    `Unable to unify bool with nat`。要写括号。
58. **生成的规则语句里，自由变量与子句模式变量同名会被捕获**（`<c>_exhaustive` 的 `p`）。语句是
    `p = P₁ ∨ …`，每个析取项绑定该子句的模式变量——模式里叫 `p` 的方程，它的析取项 `∃p. p = …` 里的
    `p` 就是外层那个自由 `p`：同名同类型静默写错命题，同名不同类型直接在 `abstract_over` 抛异常
    （发射器读成"超出支持范围"，整条定义掉回公理）。发射器的修法是让自由名避开方程变量
    （`_exhaustive_var`）并 `_reserve` 方程变量；**手写这类语句时同理**。
59. **只有 `and` 能续块**（`fun` 与 `datatype` 都是）：两个连着写的 `datatype` 是两个独立的类型
    （`string.pyhol` 的 `char` 后面跟 `string`），续块头按名字单独认。
60. **家族规则（互递归 datatype 的 `<ty>_induct`）的结论不指明是哪个谓词**，所以不能自动匹配：要
    `rule <ty>_induct param_P1="%t. …" param_P2="%f. …" param_x=t` 手写实例化；这类规则不挂
    `var_induct`。
61. **分支里引入的变量名要挑没出现过的**：变量行的定理是 `VAR(name, type)`，同名同类型就是**同一条**
    稳定 ID——内层再 `intro` 同一个名字不落新行，之后所有字面 ID 都错位（`_Names` 就是为此存在的）。
    手写证明同理：`library/mutual_datatype.pyhol` 的归纳证明用 `l1`/`f1`、`t2`/`f2`。

---

## 5. 工具链

```bash
# 常驻 REPL（理论只加载一次；改完 .pyhol 换端口重起）
python -m repl.repl --serve --port 5598 --theory relation &
python -m repl.client --port 5598 --stdin < steps.txt      # 或 "cmd1" "cmd2" ...

# 单理论独立验证（贵；日常只重放相关条目）
python .cache/validate_one.py relation
python .cache/check_item.py relation per_union_is_trans    # 重放指定条目（含 `fun` 派生项）
```

- **REPL 的 `check`/`VALID` 是 `compute_only`，不做独立重放**：最终必须用 `validate_one.py` 复核。
- **语义引用是内建功能**：`goal=@`/`goal=@N`/`goal="<命题>"`、`facts=[@]`/`facts=[别名]`/
  `facts=["<命题>"]`、`let NAME <引用>`；REPL 在应用前解析成字面 ID 并回显 `resolved: ...`，
  `item NAME` 输出可粘贴条目。事实引用按依赖规则预检，指到父目标/兄弟分支会直接报 `cannot depend on`。
  用法见 `repl-client.md` §4.1。
- **验收顺序**：定义先单独加载确认 → 逐条在 REPL 造证明 → 追加进文件 → 独立重放 → 补测试与回归 → 提交。
- 单条命令/单个测试/单次验证 ≤ 2 分钟（`AGENTS.md` §2）；全量 library 验证走 `.cache/` 缓存。

---

## 6. 纪律

工作方式以 `AGENTS.md` 为准（**禁止简化与特判**、报错清晰、两种测试、架构分离、常驻 REPL、
禁止探针与手算 sid）。本文件只负责移植进度与库层面经验；仓库现状契约归 `ARCHITECTURE_AUDIT.md`
与 `FOUNDATION_DEBT.md`，改动相应内容时要同步更新它们。

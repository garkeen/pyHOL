# 复刻 auto2 程序验证：现状与交接

> 面向接手此任务的 AI。本文件只讲**表达能力移植**（把 auto2 的定义与命题写得出来），
> 不涉及自动化移植。素材：`../auto2`（Isabelle 源码，权威）、`../mirror-isabelle`、
> `../hol-light`。仓库现状契约见 `ARCHITECTURE_AUDIT.md`、`FOUNDATION_DEBT.md`，
> 工作方式见 `AGENTS.md`。

---

## 0. 任务边界

**要什么**：让 holpy 能表达 auto2 `HOL/Program_Verification/` 里的定义与命题。那份开发共
**941 个声明**（datatype 20 / definition 161 / fun 105 / abbreviation 7 / function 5 /
partial_function 30 / instantiation 6 / typedef 1 / inductive 2 / lemma 539 / theorem 65），
分布在 28 个 `.thy`（Functional 13 个约 144KB，Imperative 15 个约 100KB + 1600 行 ML 分离逻辑胶水）。

**不要什么**：不移植 auto2 的证明自动化（约 1.5 万行 ML 的饱和式证明器）。

**地基**：holpy 里 `def` / `fun` / `datatype` 全部落到 `Thm.axiom`（`core/items.py` 的
`Definition/Fun/Datatype.get_extension` → `defcheck.mk_axiom` → `kernel/thm.py:Thm.axiom`），
类型与常量只是签名扩展。所以 **Isabelle 的每种声明都存在 holpy 对应物**，移植是全函数，
只存在"用什么方式引入"和"定理是证还是公理"两个选择。`undefined`（`logic_base`）是那条
"不覆盖的输入"的出口，与 Isabelle 的 `axiomatization undefined :: 'a` 同义。

---

## 1. 现状

### 1.1 auto2 移植的六个阶段

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | 基础库：`prod` 积类型 + `relation`（集合版偏等价关系） | 完成 |
| 2 | 逻辑基础库：`option`、list 补全、`multiset`、有限集/基数、关系演算 | 完成（余下引理见 §1.4） |
| 3 | 序：`linorder` 谓词化 + `int`/`real` 实例 | 完成 |
| 4 | 良基与递归：`wf`/`acc`/`wfrec` + 关系归纳 + `function` 前端 | 完成（尾部见 §1.4 与 §3） |
| 5 | Functional 领域库：`Mapping_Str`、`Union_Find`、`Interval`、`Arrays_Ex`、`Indexed_PQueue`、Quicksort… | 未开始 |
| 6 | Imperative：堆模型 + 分离逻辑基座 + 12 个实例 | 未开始 |

阶段 5、6 的具体清单与规模见 §4。

### 1.2 递归前端（`fun`）与伊莎贝尔 Function 包

`fun` 现在**展开成派生条目**（`core/fungen.py`：`<c>_H` 体函数、`<c>_rel` 递归关系、
`<c>_in` 不动点、方程由良基性证明），不再当公理注入；每个定义还得到
`<c>_exhaustive`（覆盖析取）、`<c>_cases`（定义自己的 case 规则）、`<c>_elims`
（消去规则）与 `<c>_induct`（关系归纳），带洞的定义靠模式减法补
`= undefined` 兜底方程后同样齐全。规则形状的样例在 `library/rules_example.pyhol`
（无变量子句、多参数多子句、布尔值——别处的定义覆盖不到的三种）。对齐伊莎贝尔 Function 包的九个阶段里，1–5 已完成：

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | 覆盖证明器（`pat_completeness.ML` 的 `prove_completeness`） | 完成 |
| 2 | `f.induct`（`induction_schema.ML`） | 完成 |
| 3 | 算术引擎：AC / 乘法 / 减法归约（`core/measure.py`） | 完成 |
| 4 | 模式减法 / 带洞定义（`pattern_split.ML`） | 完成 |
| 5 | 组合度量：`size_list f` 这类候选（`measure_functions.ML`） | 完成 |
| 6 | 互递归 `fun … and …` | 部分完成：`library/either.pyhol`（和类型地基）已落地；语法与编码见 §3 |
| 7 | `f.cases` / `f.elims` / `fun_cases` | 部分完成：`<c>_cases` 与 `<c>_elims` 已发射；`fun_cases` 那层与布尔特化见 §3 |
| 8 | `partial_function` | 未做，见 §3 |
| 9 | `size_change`（scnp 终止证明器） | 未做，见 §3 |

### 1.3 已知缺口

- **度量路径里嵌套模式的调用重命名不完整**（发射器缺陷，`core/fungen.py` 的
  `ren_call` 一带）。最小复现：`fun tdepth :: tri list ⇒ nat | tdepth (TriS t # xs) =
  Suc (tdepth (t # xs))`——模式里元素被拆开、递归调用重新组装列表——发出的证明目标条件
  写成 `tri_TriS_1 (TriS t) # xs`，而 mlex 链文本写成 `t # xs`，重放必失败。这个形状
  恰好是"元素度量（`tri_size`）唯一能让下降严格"的场合，所以组合度量目前只覆盖
  "容器自身构造子"的降序。修法二选一：补全重命名，或在发射器里诚实 `FunGenError`
  退回公理（**不允许发出重放不过的条目**）。
- **参数化 datatype 的 size 族归纳**：`wfrec_example/seq_size_induct`、
  `gcl/varType_size_induct` 两条重放失败（已确认与 `fun` 前端各阶段的改动无关，
  是既有问题），症状是 `rewrite` 步失败。

### 1.4 库层面的余量（非阻塞）

- **list**：`nth_list_update_diff`（双索引骨架）；`foldr`/`foldl`/`concat`/`zip`/`remdups`
  只有定义无引理；`sublist_append`/`sublist_Cons`/`nth_sublist` 归阶段 5（auto2 放在 `Arrays_Ex`）。
- **multiset**：`mset_list_swap`、`set_list_swap`（要先有 `count` 对 `list_update` 的逐点刻画）。
- **set**：基数层已收口，只剩 3 条刻意留的公理（`set_equal_iff` 与两条 `card` 递归）。
- **`int`/`real`**：实例已完成；`int` 其余算术/除法/幂等引理属 `FOUNDATION_DEBT.md` 的 P3 数系债。

### 1.5 已实现的前端机制（其它文档引用的锚点）

- **类型类糖**：类型变量可带类注解（`'a::linorder`），一个类贡献**一条或多条前提**；
  类条目写成 `class <name> = <pred> (<op> :: <type>, …), …`（`syntax/pyhol.py`），
  与 `typeabbrev` 同款处理——领域数据搬出核心，实例是普通定理。类前提在**每个分支各引入一份**
  （§5.7 第 48 条）。
- **序的谓词层**：`library/order.pyhol` 的 `preorder`/`order`/`linorder`/`linorder_lt`
  与桥接类前提 `linorder_lt_le`（`<` 与 `<=` 互推）；`nat` 实例 + `int`/`real` 实例
  （两个理论因此各多一条 `imports order`）。
- **`-` 的集合实例**：`minus` 在 `'a set` 上有方程，`A - B` 可照 auto2 原文写
  （在此之前它是未解释常量，见 §5.1 第 9 条）。
- **`int`/`real` 的两条未证引理**（`real_inv_0`、`real_mul_linv`）：交互可证、重放不可证——
  z3 的归一化按 `has_theorem` 决定用哪些重写规则，重放时 `real_inverse_divide` 还不在作用域。
  结论与两种修法写在 `library/real.pyhol` 的 NOTE 里，不在这里重复。

---

## 2. 怎么用这份文档

- **要写新理论**：先读 §5（坑与配方）与 §6（工具链），照 §5.7 的库约定写。
- **要动递归前端**：读 §3。
- **要对齐 auto2 进度**：读 §4。

---

## 3. 递归前端剩下四个阶段（6–9）

锚点都是伊莎贝尔的对应实现；依赖与验收按 holpy 自己的机制写。

### 阶段 6：互递归 `fun … and …`

锚点是伊莎贝尔的 `mutual.ML`（318 行）与 `sum_tree.ML`（62 行）：把 N 个函数编码成单个
`fsum : ST ⇒ RST`——参数侧各函数参数元组类型取和、结果侧返回类型去重后取和——交给现有的
单函数机制定义并证明，再把方程 / 归纳 / cases 投影回各函数（`mk_partial_rules_mutual`）。
那棵树**不镜像调用图**，只按 `fixes` 顺序对半切，形状只由 N 决定（平衡树而非右嵌套平铺
是为了深度 O(log N)）。

**已落地：和类型地基 `library/either.pyhol`**（不叫 `sum`：那个名字是 `library/sums.pyhol`
的集合求和，它手写的 `sum_cases` 会让同名 datatype 的 cases 公理被加载器静默跳过；
`'a + 'b` 这种中缀写法解析不了——`_parse_datatype` 把第一个 token 当类型名）。

- `datatype either 'a 'b = Left 'a | Right 'b`：datgen 自动给出析构子（`either_Left_1`/`either_Right_1`
  与各自的规则）、子项关系（**没有** `either_wf_subterm`：没有构造子递归地取自己，`subterm_pairs`
  为空，这是对的）与 size 族（`either_size`；也没有 `either_size_less`，同理）。
- `either_case`：伊莎贝尔的 `sum_case`，展开成五条派生条目 + 四条规则，全部重放 VALID——
  顺便它是**三参数**定义的第一个样例，暴露出 `_require_in_scope` 要 `fst_def_1`（多参数走元组），
  所以理论的 imports 必须带 `prod`（这里用 `imports nat`，它已经带上）。
- `either_rel`：每侧一个关系提升成一个和上的关系，`mk_sumcases` 那条路要用。
- **关系上的六条引理**（全部证出来、由 `check_item.py` 独立重放 VALID）：
  `either_rel_LeftI`/`either_rel_RightI`（注入：`R1 x y ⟹ either_rel R1 R2 (Left x) (Left y)`，
  即下降义务的形状）、`either_rel_LeftD`/`either_rel_RightD`（反推：
  `either_rel R1 R2 (Left x) (Left y) ⟹ R1 x y`）、`either_rel_Left_Right_neq`/
  `either_rel_Right_Left_neq`（两侧之间没有关系）。反推那两条的证明形状：展开定义 →
  `disjE` → 跨侧那支是 `Left = Right`（`Right` 侧要先用 `eq_sym_eq` 转向）→ `resolve
  either_Left_Right_neq`；本侧那支 `elim` 出见证、`conjD1/conjD2` 取合取项、
  `either_Left_inject` 把 `Left x = Left u` 化成 `x = u`，再用等式把目标改写成见证的样子。
- **`wf_either_rel`**（`wf R1 ⟹ wf R2 ⟹ wf (either_rel R1 R2)`）——编码的终止证明走它。
  证明形状与伊莎贝尔的直觉不同：**不在和类型上做归纳**，而是每侧各用一次自己的 `wf_induct`
  （`P ∘ Left` 配 `wf R1`、`P ∘ Right` 配 `wf R2`），每侧的步进从和上的那一步
  （`wf_def` 展开 `either_rel`，当成事实 `!y. either_rel R1 R2 y (Left a) --> P y` 用）推出来；
  和上的关系跨侧的分支是**空**的（上面两条 `_neq` 关掉），所以证一侧时完全不需要另一侧的结论——
  这正是互递归终止证明能拆成两份递归调用的原因。和元素的分情形走**定义自身的析取**而不是
  `type_cases`（原因见 §5.8 第 51 条）。

**已落地：`fun … and …` 的语法与条目 schema**

- `_parse_fun`（`syntax/pyhol.py`）把 `and NAME :: TYPE` 当作同一个块的续行：一个函数仍是
  原来的扁平形状（`name`/`type`/`rules`/子句在顶层，缓存与所有读 `data['name']` 的地方不变），
  两个以上则是一个条目带 `groups`（每个 group 的键与扁平形状同款）。`_export_fun` 反向输出
  （`fun` 起头、`and` 续行），**单函数导出逐字节不变**。`syntax/tests/pyhol_test.py` 锁住
  往返与"单函数不长出 `groups`"。
- `items.Fun` 读 `groups`：**所有 group 的类型都在作用域里**（跨函数的递归调用才解析得了），
  每条的方程仍检查"等式的头是本函数的常量""右端不多变量"。条目名字取 `even and odd`
  （状态表里一眼看出是个块）。
- **不发射**：块自己报告 `not emitted yet`，`get_extension` 也显式拒绝（`emitted, not
  axiomatized`）——`check_fun_recursion` 的结构判据问的是"某个函数的子项"，跨函数的调用不是
  任何东西的子项，所以这里**没有**可退守的公理路径（`core/tests/items_test.py` 的
  `MutualFunTest` 六例：报错、不注册、拒公理、头不对要拒、块不接 `measure`/`relation`、
  单函数形状不变）。`fungen.expand_item` 见到 `groups` 直接返回 None（唯一的判据在条目层）。
- 实测：临时 `.pyhol` 里放一个 `even2 and odd2` 块，加载后是**一条 error 条目**、理论里既没有
  `even2` 常量也没有 `even2_def_1`（验完已删除该临时文件）。
- 块的 `measure`/`relation`/`wf`/`descent` 子句暂不接受（终止是对整个组证一次，写法与
  单函数不同），报错而不是静默忽略。

**未做**：

1. 编码本身：`mk_inj`/`mk_proj`（沿平衡树走 `Left`/`Right` 与析构子）、`mk_sumcases`、
   每个函数用投影定义、方程翻译成 `fsum` 的方程、终止关系搬到和上（用 `wf_either_rel`）、
   再把方程 / cases / elims / induct 投影回各函数——**投影那步是 holpy 侧的真正工作量**：
   伊莎贝尔用 `EqSubst`+`simp_tac`，这里得写成显式步骤（形态与现有 `_def_entry` 模板同款）。
   `basic._load_group` 的分发也在这步接上（现在靠 `expand_item` 返回 None 走到条目层的报错）。

**编码的探路结果**（会话内实测，缺的只剩「把它写成生成器」）：

- **编码后的定义就是一条普通的 `fun`**：`even`/`odd` 编成
  `fun even_odd_sum :: (nat,nat) either ⇒ bool`（四条方程 `Left 0`/`Left (Suc n)`/
  `Right 0`/`Right (Suc n)`，递归调用写成 `even_odd_sum (Right n)` 这种）。结果类型只有一种时
  结果侧不用取和；参数侧每函数一个槽位。
- **终止走度量引擎**，不用显式 `relation`：`_measure_order` 自己找出 `[Measure(0, size)]`
  （`either_size id id`）。为此放宽了 `_expand` 里「有调用就要求子项关系」的前置门。
- **一次 `_expand` 出 14 条**（`m1/H/rel/in`、常量定义、`rel_wf`、四条方程、
  `exhaustive`/`cases`/`elims`/`induct`），其中 **9 条定理重放全部 VALID** ✓（曾卡在两处，
  都已修：收口步计数见 §5.8 第 53 条；模式叶子类型的析构子不在归约表里 ——
  `Left (Suc n)` 里的 `nat` 也要，否则义务里留 `Pre (Suc n)` 与事实对不上）。
- **投影的三条配方（都已验证，可直接抄成模板）**：
  1. 每个函数的定义：`def f :: T = f x̄ = <sum> (inj x̄)`（`inj` 是 `Left`/`Right`）。
  2. **方程**（`f_def_k`）：`← rewrite f_def goal=0`（把 `f p̄` 摊成 `<sum> (inj p̄)`，
     顺带摊掉 RHS 里的自调用）→ `← rewrite <sum>_def_k goal=1` → RHS 里出现别的函数名时
     再来一步 `← rewrite <g>_def goal=<当前目标>`，两条边相等时这一步**自动关门**
     （实测：`even2 (Suc n) = odd2 n` 三步即完，不要额外的 `refl`）。
  3. **互归纳规则**（`f_induct`）：前提是整个组的（按子句顺序），结论是本函数那一侧。
     证明把编码的归纳在 `either_case P1 P2` 上实例化，再逐条把 `either_case` 用它的方程归约。
     实测模板（`even2_induct`，id 就是发射器的静态计数）：
     ```
     ← intro goal=0                                  -- 前提（n 条）+ 目标
     ← intro a goal=<目标>                            -- 变量行 + 目标（2 条）
     cut "!p::ST. either_case P1 P2 p" goal=<目标>
     ← rule <sum>_induct goal=<cut>                  -- 编码的 n 条前提成为子目标
     每条前提：
       非递归子句：← rewrite either_case_def_<i> goal=<前提>        （关门，0 条）
       递归子句：  ← intro <模式变量> goal=<前提>                   （变量+假设+目标）
                  → rewrite either_case_def_<被调侧> target=fact goal=<目标> facts=[<假设>]
                  ← rewrite either_case_def_<本函数侧> goal=<目标>
                  ← inst <模式变量> goal=<目标> facts=[<第 k 条前提事实>]
                  ← apply_prev goal=<目标> facts=[<刚 inst 的>, <归约后的假设>]
     结论：← inst "<inj_j> a" goal=<目标> facts=[<cut 出来那条 !p. …>]
          → rewrite either_case_def_<本函数侧> target=fact goal=<目标> facts=[<刚 inst 的>]
     ```
     （实测 20 步、无效条目 0 条，`even2_induct` 重放 VALID ✓。变量名要**每条前提各一批**
     ——同名同类型的变量行第二次不落行，后面的 id 全错。）
- **命名坑**：函数名与已有常量撞名（`nat` 自带 `even`/`odd`！）时，`def` 条目被加载器
  静默跳过（`except TheoryException: pass`），于是 `even_def` 解析到 nat 的那条、整个证明
  悄悄跑偏。样本与生成器都要避开重名（生成器的编码名用 `<a>_<b>_sum` 并查重）。
- **还没做**：把上面三条写成 `fungen._expand_mutual`（`expand_item` 的 `groups` 分支接上它）、
  再补三条规则的投影（`_exhaustive`/`_elims` 用同一套「实例化到注入 + 归约 + 另一侧用不相交性
  排除」的写法；`_cases` 可以复用现成的 `_cases_entry`，它只依赖 `<c>_exhaustive` 与子句模式）、
  最后接一个两函数互递归的库样本（五样规则齐、归纳规则用一次）与测试。

**验收**：一个两函数互递归的样本（如 `even`/`odd` 的互递归版）拿到方程、`_exhaustive`、
`_cases`、`_elims`、`_induct` 五样，且归纳规则能在库里用一次。

### 阶段 7：`f.cases` / `f.elims` / `fun_cases`

**依赖**：阶段 2（已有）与一套归纳包风格的 case 化简。

**已落地：`<c>_cases` 与 `<c>_elims`**（每个展开的 `fun` 的两条新规则，与
`<c>_exhaustive`/`<c>_induct` 并列；`library/tests/fungen_test.py` 的不变量测试现在要求四条齐）。

- **`<c>_cases`** 形状刻意与 **datatype 的 `<ty>_cases` 同款**（`defcheck.datatype_axioms`）：
  `(⋀v̄₁. P P₁) ⟹ … ⟹ (⋀v̄ₙ. P Pₙ) ⟹ P p`，`P` 与 `p` 是**自由变量**（`fixes`）。
  因此 **不需要新 tactic**：`type_cases x cases_thm="<c>_cases"` 走的就是 `datatype_cases`
  那条路（`P := λx. 目标`、`p := 分情况的表达式`），每子句一个子目标。
- **`<c>_elims`** 是伊莎贝尔的 `f.elims` 去掉域条件（holpy 没有 `dom`，部分性不是谓词）：
  `f x̄ = y ⟹ (⋀v̄₁. T = P₁ ⟹ y = R₁ ⟹ P) ⟹ … ⟹ P`。首前提是消去方程，每子句的
  前提给出该子句下参数的样子（`T = P_k`，模式自己的变量作分支变量）与右端（`y = R_k`）。
- 两条规则都是**证明出来的**：读 `<c>_exhaustive` 的析取（`disjE` 逐层、`elim` 取见证与
  等式、每支把自己的前提 `inst` 到分支变量上再让重写/`apply_prev` 收口）。`_elims` 多一条
  桥：方程说的是柯里化应用，子句说的是模式的变量，靠柯里化常量的定义
  （`f x̄ = <c>_in T`）在两者之间走；这条桥里**与子句无关的那一步提到分叉之前**——
  分支里它是上一条分支的同命题，而"命题已是条目"的步不落行，后面的字面 ID 就全错。
- 子句比 datatype 的构造子更细：嵌套模式（`dbl (Suc (Suc n))`）与补 `undefined` 的洞
  （`drop2 (Suc 0)`、`the None`）都是一个分支，这正是它们比 `type_cases` 多出来的东西。
- 命名：谓词/分支变量避开方程自己的变量名，也避开 `elim` 会拿到的名字（`filter` 的模式变量
  就叫 `P`，于是谓词取 `P1`、消去拿 `P2`），`_elims` 还避开 RHS 里 binder 的绑定名
  （`strict_sorted` 的 RHS 是 `(∀y. …) ∧ …`）。文件若自己写了同名规则，发射器让位。
- **用法上的坑**：`type_cases … cases_thm=` 的分割要在 `intro` 之前——已 `intro` 出来的事实
  不代入分支（行不可变），守卫必须留在目标里（§5.5 第 35 条同一个道理）；
  `type_cases` 要一个**变量**，多参数定义得给元组变量。

**验收（已过）**：`library/gcl.pyhol` 的 `scalar_of_nat_id` / `scalar_of_bool_id` 原是两条公理，
现在用 `type_cases s cases_thm=scalar_of_{nat,bool}_cases` 分割后证明；消去规则的用法是
`rule <c>_elims facts=[<方程>]`（`library/rules_example.pyhol` 的 `gz_value_shape`），
两条都由 `check_item.py` 独立重放 VALID。

**余下（可选）**：

- `fun_cases`（`fun_cases.ML`，62 行）在伊莎贝尔里是把 elim 规则**特化到一条给定实例**上，
  因为那边的 `cases` 方法要一条现成规则；holpy 的 `rule` 直接吃 `facts=[<方程>]`（上面那条验收），
  所以这层不需要——真要做，也只是把它包成一条 `fun_cases` 方法。
- 布尔返回类型的两条**特化**规则（`f x̄` 与 `¬ f x̄` 作前提，`mk_bool_elims` 用 `eq_boolI`
  特化）：通用规则对布尔值定义同样工作（`rules_example` 的 `gb_elims` 在重放清单里），
  特化只是省掉用户自己把 `f x̄` 化成 `f x̄ = true`。

### 阶段 8：`partial_function`

**这是另一个顶层命令**，严格说不属于 `fun` 对齐；auto2 有 30 处 `partial_function (heap)`，
都是堆单子不动点（与 §4 阶段 6 的堆模型绑定）。

**依赖**：ccpo/不动点库（`option.fixp_fun`、`mono_body`、`fixp_induct_uc`）与 `partial_function_mono`
规则集；单调性自动化还依赖对 datatype case 表达式分情形的 tactic。**成本最高，且与阶段 6/7/9 正交**——
建议与阶段 6 的 Imperative 堆模型一起评估。

**验收**：至少一条 `partial_function`（非堆、如 `option` 上的不动点）能定义出方程 + 归纳规则。

### 阶段 9：`size_change`

`scnp_solve.ML` + `scnp_reconstruct.ML` 共 604 行。求解算法本身自包含（输入是纯组合的
size-change 图，输出是证书），但重建深度绑定伊莎贝尔。

**缺的库比代码多**：`library/multiset.pyhol` 有 26 条定理但全是**代数**（`count`/`union_mset`/
`filter_mset`/`mset`），**没有多重集序**（无 `mult`/`mult1`/`wf_mult`）；`reduction_pair`、
集合的 `max_ext`/`min_ext`、`acc` 与 SCC 分解（`termination.ML:342` 的 `decompose_tac`）也都
grep 不到。

**它只决定"更难的终止性能不能自动证出来"，不影响能证的集合**：`relation` + 用户下降引理已经覆盖
同一批定义（`fun` 的 `measure` / `relation` / `wf` / `descent` 子句）。**放在最后做**。

**验收**：一个现有 `relation`+`descent` 样本定义，去掉手写子句后仍能自动终止（即自动判出同样的度量）。

---

## 4. auto2 六阶段里剩下的两块

### 阶段 5：Functional 领域库

按依赖顺序补（文件大小是规模参考）：

1. `Mapping_Str.thy`（9.2KB）：`datatype ('a,'b) map = Map "'a ⇒ 'b option"`（函数类型字段，正性检查放行）。
   empty/update/delete/keys_of/map_of_alist/map_of_aset/unique_keys_set。
2. `Partial_Equiv_Rel.thy`（2.4KB）：**阶段 1 已完成**。
3. `Union_Find.thy`（6.3KB）：`rep_of` 递归、`ufa_invar`、`ufa_α`。
4. `Interval.thy`（3.0KB）：`datatype 'a interval`、`idx_interval`、自定义序（阶段 3 的条件实例）。
5. `Arrays_Ex.thy`（8.3KB）：`list_swap`、`sublist`、`list_update_set`、`array_copy`。
6. `Indexed_PQueue.thy`（18.3KB）：堆不变量。
7. 算法（依赖上述）：`Lists_Ex` → `BST` → `RBTree`；`Quicksort`；`Interval_Tree` → `Rect_Intersect`；
   `Connectivity`；`Dijkstra`。

注意：这些定义大量是**索引驱动递归**（`part1`/`quicksort`/`idx_bubble_down_fun`/`rect_inter`
用 `measure (λ(_,l,r,_). r - l)` 之类），递归同时消耗索引与列表，终止性依赖用户给的引理——
holpy 侧就是 `fun` 的 `measure` / `relation` + `descent` 子句（已支持），或 §1.3 的组合度量。

### 阶段 6：Imperative

**最大的一块，也是唯一需要重建"堆模型"的阶段。**

auto2 建立在 Isabelle 的 Imperative_HOL 上：带类型 ref/array、`lim`、堆单子
（`return`/`bind`/`effect`/`execute`）。holpy 只有裸 `nat⇒nat` 堆（`library/mem.pyhol` 是雏形）。

1. **堆模型**：`heap`/`addr`/`lim`/`refs`/`arrays` + `Ref`/`Array` + 堆单子。可选用无类型堆规避
   `'a::heap` 类（auto2 有 92 处 `::heap`，那是序列化类，不是序），代价是堆里存不了任意类型。
2. **分离逻辑**：`pheap`/`in_range`/`relH`/`assn`。`SepAuto.thy:75` 的
   `typedef assn = "Collect proper"` 是全仓唯一一处 typedef——用 `datatype assn = Assn (pheap ⇒ bool)`
   + 显式 `proper` 前提替代，或声明类型 + 公理。`emp`/`*` 定义成普通常量，`assn_one_left` 之类代数律
   本来就要手证。**另**：`'a node ref option` 这类"自身嵌进别的类型构造子"会被正性检查拒（§5.1），
   要么手工声明类型 + 公理，要么改无类型堆。
3. **12 个实例**：`Arrays_Impl` → `DynamicArray` → `LinkedList` → `BST_Impl` → `RBTree_Impl` →
   `IntervalTree_Impl` → `Indexed_PQueue_Impl` → `Union_Find_Impl` → `Quicksort_Impl` →
   `Connectivity_Impl` → `Dijkstra_Impl` → `Rect_Intersect_Impl`。
4. 自动化胶水（`sep_steps.ML` 824 行、`assn_matcher.ML` 324 行）**不在范围内**——那是自动化。

---

## 5. 写 holpy 证明：坑与配方

全部实测。按主题分组；编号只为引用方便。

### 5.1 语言与解析

1. **datatype 构造子行漏写 `|` 会静默产出零构造子**。`_parse_datatype` 在第一个非 `|` 行 break，
   `constrs = []`，随后 `datatype_axioms` 给空构造子的 datatype 生成 `X_induct`/`X_cases`——**空公理**。
   防身：声明后看定理名齐不齐（单构造子应得 `X_<C>_inject`、`X_induct`、`X_cases`；多构造子还有 `X_A_B_neq`）。
2. **字段名不能取投影函数名**。字段名会被 `_cases`/`_induct` 当绑定变量，`Pair (fst :: …, snd :: …)`
   会遮蔽 `fst`/`snd`，`rule prod_cases` 出来的子目标没法用。改名为 `left`/`right`，投影函数单独 `fun`。
3. **正性检查**（`core/defcheck.py:127`）拒绝"自身嵌进别的类型构造子"：`datatype 'a node =
   Node (val :: 'a) (nxt :: 'a node ref option)` 直接拒。绕过：手工用 `TConst` + `Constant` + 公理声明
   （`core/items.py::Quotient` 是先例），或改无类型堆。
4. **多参数类型的两种写法不同**：声明后缀 `datatype prod 'a 'b =`；类型表达式前缀 `('a,'b) prod`
   （`prod 'a 'b` 不解析）。
5. **`imports` 逗号分隔**（`imports set, prod`）；写成空格报 `KeyError: 'set prod'`。
6. **`#[N]` 注解可省**：`.pyhol` 里它是纯文档，replay 不验证命题；`goal=`/`facts=` 的数字才是硬约束。
7. **`facts=[...]` 在文件里只吃数字**（REPL 另有语义引用，见 §6）。写了命题文本会得到
   `fact sid '[' not found` 这类费解报错。
8. **定义里的类型注解只是标记**：`fun ordered_insert :: 'a ⇒ 'a list ⇒ 'a list` 的函数体里
   `x < y` 解析成通用重载常量，不需要也不接受前提注入。
9. **重载常量在缺实例时是未解释常量**：`A - B` 在集合上曾能通过类型检查、打印与集合差一样，
   但没有任何方程（`refl` 关不掉、`rewrite member_diff` 也打不上）。给类型加实例后才可用——
   遇到"看起来对但推不动"的算术/集合符号，先查实例。

### 5.2 稳定 ID 与依赖

10. **sid 按 Thm 分配**（`method/stable_state.py::_ensure_sid`），`Thm.__eq__` 比的是**假设集合 + 命题**
    （`kernel/thm.py:105`）。所以"同命题共号"的条件比命题相等更严：命题相同、假设集合不同 = 两个条目。
11. **依赖按位置判定**（`ItemID.can_depend_on`，`kernel/proof.py:71`）：同分支且位置在前。
    兄弟 `cases` 分支的事实、被 `cut`/`rule` 展开后位于其后的行，都用不了
    （`apply_method: illegal dependence`）。
12. **重复命题共享 sid，会连带封死跨分支引用**：同一命题在多个分支出现时只有一个 sid，
    而它属于最早的位置。所以要跨分支用的命题，必须在**进入 `cases` 之前**展开，
    或者拆成**单分支引理**（§5.7）。
13. **不能前向引用**：`validate_theory` 用 `context.set_context(thy, limit=('thm', name))` 把理论截断到
    该定理之前再 replay。引用声明在自己后面的定理/定义，探针里能过、独立 replay 必 `STEP_FAILED`
    （报错只说"某 step failed"，不说前向引用）。
14. **定义体引用未声明的常量会被静默丢弃**：item 解析失败只记 `item.error` 并跳过，常量根本没注册；
    下游症状是解析期"变量未声明"，于是 `inst` 用变量代入"侥幸"通过，生成的定理毫无意义。
    排查：翻 `theory_cache[f]['content']` 里的 `.error`。
15. **sid 会随证明增长重排**：中间插一步，其后 sid 全部平移。REPL 里用语义引用（`goal=@`、
    `facts=["<命题>"]`），最后一次性把字面 sid 写进文件。
16. **`cut "P" goal=N` 的 N 必须是开口目标**。指到一条事实（如守卫）上不报错、REPL 的 `check`
    也照样 VALID，但完整重放报 `CheckProofException: output does not match`（新定理的假设集成了
    那条事实的兄弟分支）。**这是最容易翻车的一处**：改一个数字即通过。
17. **`cut` 的可用事实 sid 是"证明 P 之后新出来的那个"**，不是 cut 行编号；用 `all` 看一眼再引用。
18. **`intro` 后目标不一定保持 sid**：第二次 `intro` 可能撞上已出现的同命题而合并，目标换 sid。
    每步之后看 `all`，用最后一条 open goal，别按"上一步 +1"推算。

### 5.3 重写

19. **`rewrite` 不带 `loc` = 先定位（最外层优先）再替换*全部*同形项**。`set_def_1` 一步会把目标里
    两处 `set []` 同时换成 `{}`；`insert_comm` 会把等式两边同时交换，只想动左边要写 `loc=0.1`。
20. **`loc` 按项树算**：`A ⟷ B` 的左/右操作数是 `0.1` / `1`，`f a` 的参数是 `1`。所以
    `z ∈ insert x A ∪ B` 里 `z ∈ insert x A` 的路径是 `0.1.0.1`——**没把握就先小范围试**。
21. **重写必须有效果**（`has_rewrite`），否则 `InvalidDerivationException: rewrite_fact using X`。
    展开链因此有顺序约束：外层的展开要等内层先打开。
22. **对事实重写时，事实里的变量必须在上下文里声明**：`intro`/`elim` 引进的变量会让重写直接失败。
    对策是把这类 iff 前向化下沉成带 `fixes` 的辅助引理。
23. **带前提的重写定理可以直接带 `facts=[<条件…>]` 重写目标**，省掉"先 forward 出等式事实"的一步。
24. **`sym=true` 是反向用等式**：定义用 `sym=false` 展开，`[] @ xs = xs` 反向才是 `xs → [] @ xs`。
25. **iff 定理改写目标会产生"转换子目标"**（被改写子项的那条等式成为新目标），需要再用定理或引理关掉；
    左右两边恰好互为实例的情形会自动关门。

### 5.4 `rule` / `forward` / `inst`

26. **`rule` 只吃不超过前提数的 facts**；多前提定理（`disjE2` 等）要么全给、要么显式给 `param_*`
    （元变量从目标推不出来时只报 `ParameterQueryException`）。
27. **`rule` 匹配的是定理的结论**。带前提的引理用之前要先把目标 `intro` 成结论形态，
    再 `facts=[<前提…>, <假设事实>]`。
28. **`rule` 对否定式定理会报 `too many previous facts`**（`¬` 是独立常量，`strip_implies` 看不到前提）。
    形状 `~A` 的定理配事实 `A` 用 `resolve`。
29. **∀-形式的命题不是重写规则**，`rule`/`rewrite`/`accept` 都对它报错。用法只有
    `forward`（给全 `param_*`）→ `inst <项>` → `apply_prev`；含空格的实参要加引号。
    所以：**只用 `fixes` 声明、命题里不写 `!` 的定理才是可重写的等式**。
30. **∀-形式且带蕴含的定理，`forward` 也用不了**（`strip_implies` 看不进 ∀）。唯一配方是
    `cut` 出原命题 → `accept <thm>` 得 ∀-事实 → `cut` 出实例 → `apply_prev facts=[∀-事实, 实证]`。
31. **`forward` 的 facts 要按定理前提顺序给全**，否则 matcher 会拿第一条前提去比，报类型不匹配。
32. **推导结果与目标同命题时 `forward` 不新增条目**（可能直接关门）；没关门时用
    `apply_prev facts=[<∀/蕴含事实>, <参数事实>]`。`assumption` 只认目标自身的假设集，不认兄弟事实。

### 5.5 归纳与分情况

33. **`induct` 必须作用在整条蕴含上**：先 `intro` 把假设变成事实，ih 会退化成"结论 ⇒ 结论"而完全无用。
    正确顺序：`induct <var>` → `intro` 进分支。
34. **自由变量分情况用 `type_cases <var> goal=N`**，`rule <ty>_cases` 匹配不上自由变量；
    `type_cases` 后子目标常带 `!x.` 前缀，要 `intro` 再关。
35. **`type_cases` 不代入已 `intro` 出来的事实**（行不可变模型）。带守卫的引理要**把守卫重新折回目标**：
    `intro xs` → `cut "<守卫> --> <结论>"`（`goal=` 指开口目标）→ `type_cases xs` → 各分支收口 →
    `apply_prev facts=[<cut 事实>, <守卫事实>]`。
36. **索引驱动的递归函数**（`take`/`drop`/`nth`/`list_update`）的一般引理只能是 ∀-形式
    （对任一个参数归纳，ih 的另一个参数都对不上）。代价见 §5.4 第 29 条。
    对策：另证"列表作参数、索引作模式"的展开特化引理（`take_cons`/`drop_cons`/…）供重写，
    ∀-形式的总结论只偶尔 `forward`+`inst` 引一次。

### 5.6 常用配方

37. **把定义展开固定成一条引理**（如 `per_union_iff`、`remove_elt_list_mem`）：先证成员/展开刻画，
    打 `[hint_rewrite]`，此后所有下游引理只依赖它。**每个用 `{p. …}`/`∪`/`image` 定义的集合算子都该这样。**
38. **按分支拆引理**：跨分支共享 sid 会 `illegal dependence`（§5.2），把 3×3 这类情况拆成 9 条
    单分支引理，主引理只留骨架。
39. **`forward` 做传递链**：`→ forward goal=N facts=[<传递事实>, <前提1>, <前提2>]` 一步得结论
    （事实本身排第一）。
40. **消析取**：`member_insert` 之类出析取后，用 `disj_comm` 换序 + `force_disj_true1/true2`
    消掉已知为假的一支（注意朝向：`true1` 消第二个析取项，`true2` 消取反的第二个；
    要消第一个先换序）。矛盾支用 `negE_gen`（结论可与任意目标合一，不必先转 `false`）。
41. **"存在量词套等式"用 `exists_flatten`** 清理；`comp_fun_def` 展开产生的 β-redex 由重写器自动约简。
42. **常量引理的左右形式要看清楚**：`conj_false_left` 是 `P & false`、`conj_false_right` 是 `false & P`
    （`conj_true_*` 同理）。写反只报 `rewrite: unable to apply theorem`，先 `thm <名字>` 确认。
43. **集合等式先降到成员层**：先在成员层面归纳（`remove_elt_list_mem`），集合等式退化成
    `set_equal_iff` + 成员引理重写；直接对集合等式归纳会让命题级推理翻倍。
44. **`all_mem_elim`**：`(∀z. z ∈ B ⟶ P z) ⟹ y ∈ B ⟹ P y`——把"有界全称 + 成员事实"固定成一步。

### 5.7 库层面的约定

45. 基础库**禁 `simp`/`auto`/`norm`/`z3`**（见 `FOUNDATION_DEBT.md`）：用展开与显式规则写。
46. **证明一律用常驻 REPL + `repl/client`**（`AGENTS.md` §4），一条条 `item NAME` 导出、整段替换回文件；
    不要写每次重载理论的临时脚本。
47. **改了 `syntax/`、`repl/`、`.pyhol` 要换端口重起 server**（端口被占会明确报错退出 2）。
48. **类前提是每个分支各自一份**（`class linorder` 那条前提下，同一命题在不同分支有不同 sid）：
    加一条类前提不能让脚本做全局编号平移，要按创建顺序分段偏移或干脆重证
    （`method/stable_state.py` 还要求注解条数 == 新建条目数）。
49. **`item NAME` 输出的是"当前证明"**：会话停在别的证明上时它会写出那条证明。
    导出后立刻核对 `prop` 行再落盘。

### 5.8 和类型编码：`elim`、∀-目标与分情况

50. **一次消一个见证**。`elim "u,v"`（k≥2 个名字）会失败：方法把 ∃ 事实连同 k 个变量塞进外层
    `intros` 行，而 `intros` 宏只用一次 `exE` 消化 `∀x. P x ⟹ C`；k≥2 时续行是
    `∀x1…xk. B ⟹ C`，匹配器报 `When matching implies (?P a) with (all::…)`。
    配方：`elim "u"` 再 `elim "v"`——第二次的 ∃ 正是第一次留下的假设行，两个单见证的 `exE`
    在反序重放里各吃一个，恰好对上。
    另注：k≥2 的这次失败**会留下半截条目**（变量行、假设行都在，gap 数不变），所以失败后要么
    `undo`，要么用 `all` 重读 sid——按旧 sid 手抄的 `goal=` 会指空。
51. **∀-绑定的变量不能 `type_cases`**。`type_cases` 要"上下文里的变量"
    （`Apply type_cases: extra variable`），而 `intro` 一次引进**所有**嵌套 ∀ 与 ⟹
    （`logic.strip_all_implies`），守卫一变成事实就不再代入分支（第 35 条）。
    所以 `!y. 守卫 y ⟹ 结论 y` 既不能 `intro y` 后 `type_cases y`（守卫已僵在事实里），
    也不能直接 `type_cases`（y 不在上下文），两条出路：
    (a) 让目标成为某个**有 ∀ 结论的定理**的实例，用 `rule` 配高阶谓词（下一条）；
    (b) 展开定义自身的析取：`→ rewrite <def> target=fact goal=… facts=[<守卫>]` → `rule disjE`
    → 每支 `elim` 见证 + `conjD1/conjD2` → 用析取项给的等式把目标改写成见证的样子。
    `wf_either_rel` 的跨侧分支走 (b)，本侧分支走 (a)。
52. **`rule` 能对 ∀-目标做高阶匹配**：`wf_induct`
    （`wf ?R ⟹ (!x. (!y. ?R y x ⟹ ?P y) ⟹ ?P x) ⟹ !x. ?P x`）上，
    `← rule wf_induct goal=<!x. P (Left x)> facts=[<wf R1>]` 一步把 `?P` 配成 `%z. P (Left z)`，
    留下 `<步进>` 子目标——比 `rewrite wf_def` 再 `inst` 写 λ 项省事（λ 项还带类型注解的坑）。
    前提是定理结论本身是 ∀（`?P ?x` 与 `!x. 目标 x` 之间的匹配），否则 §5.4 第 29 条适用。
53. **收口步（`rule ... facts=[...]`／`resolve`）落不落新行，取决于事实的假设集合。**
    **实测规律**：收口结果是一条新行 ⇔ 事实们的假设并集 ≠ 被关那一行的假设集合。三次测量：
    关 `elim` 出来的 `false` 行（行假设 = ∃ 与它的体，事实的假设并集 = 体）→ 落一条；
    关 `intro` 交下来的行（行假设 = 那条等式，剥一层后的事实假设也都是它）→ 不落；
    同上但用 `resolve` 替 `rule` → 同样不落（所以「换个收口步」不是修法）。
    发射器静态算不出事实的假设集合，但**知道自己走的是哪条路**：
    `_refute_test` 的存在式测试分支会 `elim`（行的假设变两条）→ 计数 1；
    `_pattern_neq` 的普通等式分支不 `elim`（事实的假设就是行的那条）→ 计数 0。
    这一点已按上述规则修进 `_refute_equality`（新增 `extended` 参数，沿剥离递归传递），
    core fungen 28 例、library fungen 16 例（重放 13 个理论）通过。
    **仍未修**：`_condition_negation` 末尾那处 `negE_gen`（多条件测试的合取否定路）——
    按规律它的计数也该随「被反驳的测试是不是存在式」变，但没有触发它的样例，暂按原样（计数 1）。
    症状与判别：`replay failed at step: cut`（差在 cut 的 `goal=` 上）或后续
    `goal sid N not found`。

---

## 6. 工具链

```bash
# 常驻 REPL（理论只加载一次；改完 .pyhol 换端口重起）
python -m repl.repl --serve --port 5598 --theory relation &
python -m repl.client --port 5598 --stdin < steps.txt      # 或 "cmd1" "cmd2" ...

# 单理论独立验证（贵；日常只重放相关条目）
python .cache/validate_one.py relation --force
python .cache/check_item.py relation per_union_is_trans    # 重放指定条目（含 `fun` 派生项）
```

- **REPL 的 `check` / `VALID` 是 `compute_only`，不做独立重放**：最终必须用 `validate_one.py`
  或重放测试台（`StableProofState.create(...)` 逐条 `apply_method_dict` 看 `num_gaps`）复核。
- **语义引用已是内建功能**：`goal=@` / `goal=@N` / `goal="<命题>"`、`facts=[@]` /
  `facts=[别名]` / `facts=["<命题>"]`、`let NAME <引用>`；REPL 在应用前解析成字面 ID 并回显
  `resolved: ...`，`item NAME` 输出可粘贴条目（`theorem` + `fixes` + 原文 `prop` + `proof..qed`）。
  事实引用按引擎的依赖规则预检，指到父目标/兄弟分支时直接报 `cannot depend on`。
  用法见 `repl-client.md` §4.1。
- **验收顺序**：定义先单独加载确认 → 逐条在 REPL 造证明 → 追加进文件 → 独立重放 → 补测试与回归 → 提交。

---

## 7. 纪律

工作方式以 `AGENTS.md` 为准（报错清晰、两种测试、架构分离、常驻 REPL、禁止探针与手算 sid）。
本文件只负责**移植进度与库层面经验**；仓库现状契约归 `ARCHITECTURE_AUDIT.md` 与
`FOUNDATION_DEBT.md`，改动相应内容时要同步更新它们。

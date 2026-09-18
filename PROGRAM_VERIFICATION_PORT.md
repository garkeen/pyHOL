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
`<c>_exhaustive`（覆盖析取）与 `<c>_induct`（关系归纳），带洞的定义靠模式减法补
`= undefined` 兜底方程后同样齐全。对齐伊莎贝尔 Function 包的九个阶段里，1–5 已完成：

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | 覆盖证明器（`pat_completeness.ML` 的 `prove_completeness`） | 完成 |
| 2 | `f.induct`（`induction_schema.ML`） | 完成 |
| 3 | 算术引擎：AC / 乘法 / 减法归约（`core/measure.py`） | 完成 |
| 4 | 模式减法 / 带洞定义（`pattern_split.ML`） | 完成 |
| 5 | 组合度量：`size_list f` 这类候选（`measure_functions.ML`） | 完成 |
| 6 | 互递归 `fun … and …` | 未做，见 §3 |
| 7 | `f.cases` / `f.elims` / `fun_cases` | 未做，见 §3 |
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

**依赖**：先有 `sum` 类型（holpy 没有；`datatype 'a + 'b = Inl 'a | Inr 'b` 用现成的 datatype 机制即可定义，
`core/datgen.py` 会自动给它子项关系、析构子与 size）。

**做法**（照 `mutual.ML`）：把 N 个函数编码成单个 `fsum : ST ⇒ RST`——参数侧各函数参数元组类型取和、
结果侧返回类型去重后取和——交给现有的单函数机制定义并证明，再把方程 / 归纳 / cases 投影回各函数
（`mk_partial_rules_mutual` 那一步）。`sum_tree.ML` 的 62 行是纯构造（`mk_inj`/`mk_proj`/`mk_sumcases` +
平衡树访问），可直接照搬；那棵树**不镜像调用图**，只按 `fixes` 顺序对半切，形状只由 N 决定
（用平衡树而非右嵌套平铺是为了深度 O(log N)）。

**验收**：一个两函数互递归的样本（如 `even`/`odd` 的互递归版）拿到方程、`_exhaustive`、`_induct` 三样，
且归纳规则能在库里用一次。

### 阶段 7：`f.cases` / `f.elims` / `fun_cases`

**依赖**：阶段 2（已有）与一套归纳包风格的 case 化简。

- `f.cases` 基本是免费的：它就是覆盖定理（`<c>_exhaustive`）的包装，改个名字、按构造子/方程组织。
- `f.elims` 走 `function_elims.ML`（157 行）：`cases` + `psimps` + `dom` 再加一次 case 化简，
  **不需要内核新能力**；最容易漏的是布尔返回类型的两条特化规则（`f x̄` 与 `¬ f x̄`）。
- `fun_cases.ML`（62 行）是最薄的一层，前提是前面那套 case 化简已存在。

**验收**：`hd`/`the` 这类带洞定义（方程集已补 `undefined`）能给出 case 名与 elim 规则，并在一条用例里关掉目标。

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

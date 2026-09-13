# 复刻 auto2 程序验证：阶段 1 完成报告与交接

> 面向接手此任务的 AI。本报告只讲**表达能力移植**（把 auto2 的定义与命题写得出来），
> 不涉及自动化移植。已验证的事实给出来源，未验证的明确标注。
>
> 起点提交：`bb44aa5f`。工作树干净。

---

## 0. 任务边界（先读这段，避免走错方向）

**要什么**：让 holpy 能表达 auto2 `HOL/Program_Verification/` 里的定义与命题。
auto2 那份开发共 **941 个声明**（datatype 20 / definition 161 / fun 105 / abbreviation 7 /
function 5 / partial_function 30 / instantiation 6 / typedef 1 / inductive 2 / lemma 539 / theorem 65），
分布在 28 个 `.thy`（Functional 13 个约 144KB，Imperative 15 个约 100KB + 1600 行 ML 分离逻辑胶水）。

**不要什么**：不要移植 auto2 的证明自动化（约 1.5 万行 ML 的饱和式证明器）。用户明确排除。

**为什么工作方式是这样**：holpy 里 `def` / `fun` / `datatype` 全部落到 `Thm.axiom`
（`core/items.py` 的 `Definition/Fun/Datatype.get_extension` → `defcheck.mk_axiom` → `kernel/thm.py:Thm.axiom`），
类型与常量只是签名扩展、不产定理。因此 **Isabelle 的每种声明都存在 holpy 对应物**，
移植是全函数，不存在"表达不出来"，只有"用什么方式引入"和"定理是证还是公理"两个选择。
这一条是全部后续判断的地基，别丢。

**参考素材**：本地 `../auto2`（Isabelle 源码，权威）、`../hol-light`、`../mirror-isabelle`。

---

## 1. 阶段划分（本报告的定义；若你的编号不同，按内容对应）

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | 基础库与关系：`prod` 积类型 + `relation` 关系与偏等价关系 | **完成**（本次） |
| 2 | 逻辑基础库补齐：`option`、`list` 补全、`multiset`、关系演算扩展 | 未动 |
| 3 | 序：显式关系参数的 `preorder`/`linorder` 谓词与引理 | 未动 |
| 4 | 良基与递归：`wf`/`acc`/`wfrec` + 关系归纳 + `function` 前端 | 未动 |
| 5 | Functional 领域库：`Mapping_Str`、`Partial_Equiv_Rel`、`Union_Find`、`Interval`、`Arrays_Ex`、`Indexed_PQueue` | 未动 |
| 6 | Imperative：堆模型 + 分离逻辑基座 + 12 个数据结构实例 | 未动 |

依赖：1 → 2 → {3, 4} → 5 → 6。3 与 4 可并行（都只依赖 2）。

---

## 2. 阶段 1 交付物

### 2.1 `library/prod.pyhol`（新）

```
datatype prod 'a 'b =
  | Pair (left :: 'a) (right :: 'b) :: ('a,'b) prod

fun fst :: ('a,'b) prod ⇒ 'a
  | fst (Pair a b) = a

fun snd :: ('a,'b) prod ⇒ 'b
  | snd (Pair a b) = b

theorem Pair_fst_snd: Pair (fst p) (snd p) = p
```

验证：1 条 VALID。

### 2.2 语法层三处

- `syntax/parser.py`：类型语法加 `×` 中缀。优先级**比类型应用松、比 `⇒` 紧**：
  `'a × 'b ⇒ bool` = `(('a,'b) prod) => bool`；`'a × 'b × 'c` 右结合。
  项语法加 `(a, b)`，右嵌套展开为 `Pair a b`。
- `syntax/pprint.py`：`prod` 在 unicode 下打印成 `×`，ascii 退回 `('a,'b) prod`。
- `syntax/pyhol.py`：**修 bug**。`fixes` 原来按裸逗号切分，`fixes p :: ('a,'b) prod`
  会被切成 `('a` 和 `'b) prod`，多参数类型根本写不出来。改为只切括号外的逗号。

### 2.3 `library/relation.pyhol`（重写）

从 curried 谓词 `'a ⇒ 'a ⇒ bool` 改成集合 `('a × 'a) set`，与 auto2 的
`Partial_Equiv_Rel.thy` 对齐。4 个定义 + **20 条定理，全部 VALID**：

- 定义：`sym`、`trans`、`part_equiv`、`per_union`。
  `per_union R a b = R ∪ ({p. (fst p, a) ∈ R ∧ (b, snd p) ∈ R} ∪ {p. (fst p, b) ∈ R ∧ (a, snd p) ∈ R})`
- `per_union_iff`：成员展开引理，见 §4.2，是重写版的骨架。
- 对应 auto2 的 9 条：`part_equivI`/`D1`/`D2`、`per_union_memI1`/`I2`/`I3`、`per_union_memD`、
  `per_union_is_trans`、`per_union_is_part_equiv`。
- 另加：`per_union_is_sym`、9 条 `per_union_case_ij`（见 §4.3）。

### 2.4 测试

- `library/tests/relation_test.py`：主动验 20 条定理全 VALID 且 API 名字齐；
  被动验 per_union 成员推不出 R 成员且 gap 数不变。
- `library/tests/prod_test.py`：验 `×` 解析、打印往返、元组项、带逗号的 `fixes`、坏类型被拒。
- `library/tests/__init__.py`（新建，使 pytest 可发现）。

### 2.5 验证结果

```
library+syntax+core+util = 183 passed
relation 20 VALID / 0 非绿        prod 1 VALID
logic 91 VALID / 0 非绿           function 17 VALID / 0 非绿
set 25 VALID / 24 非绿（存量 UNPROVED/DEP_FAILED，无 STEP_FAILED，未被本次改动影响）
```

---

## 3. 已知的坑（按踩过的代价排序，全部实测）

### 3.1 datatype 构造子行漏写 `|` 会**静默产出零构造子**

`datatype prod 'a 'b =` 下面必须每行写 `  | Pair (left :: 'a) (right :: 'b) :: ('a,'b) prod`。
写成 `  Pair (...)` 不带管道，`_parse_datatype`（`syntax/pyhol.py:647`）会在第一个非 `|` 行 break，
产出 `constrs = []`，**不报错**，然后 `datatype_axioms` 给一个空构造子的 datatype 生成
`prod_induct`/`prod_cases` —— 那是**空公理**。我因此一度宣称"prod 端到端通过"，是错的。

**防身**：声明后检查 `datatype_axioms` 产出的定理名。单构造子应得 `X_<C>_inject`、`X_induct`、`X_cases`；
多构造子还有 `X_A_B_neq`。名字缺失就是解析没吃到构造子。

### 3.2 字段名不能取投影函数名

`datatype_axioms` 只在 `name == 'state'` 时才把字段名注册成投影常量
（`core/defcheck.py:254` 起的注释说明了原因）。生成的 `_cases`/`_induct` 会把字段名当**绑定变量名**，
所以 `datatype prod 'a 'b = | Pair (fst :: 'a) (snd :: 'b)` 会让 `prod_cases` 出现
`!fst. !snd. P (Pair fst snd)`，遮蔽 `fst`/`snd` 函数，`rule prod_cases` 出来的子目标没法用。
**改名字段为 `left`/`right`，投影函数单独 `fun` 定义。**

### 3.3 正性检查拒绝"自身嵌进别的类型构造子"

`_check_positive`（`core/defcheck.py:127`）：类型名出现在函数定义域 → 拒；出现在**其他 tconst 的参数里** → 拒。
所以 auto2 的 `datatype 'a node = Node (val: 'a) (nxt: 'a node ref option)`
（`node` 嵌在 `ref` 里）**holpy 直接拒**。
绕过办法：不加 `datatype` 项，直接用 `TConst` + `Constant` + distinct/inject/induct 公理手工声明
（`core/items.py::Quotient` 已是这个做法），或改无类型堆（`nat⇒nat`，见 `library/mem.pyhol`）。
阶段 6 一定会撞上这个，别到时候才发现。

### 3.4 多参数类型的两种写法不同

- **声明**：`datatype prod 'a 'b =`（后缀，`_parse_type_args` 按空格切）
- **类型表达式**：`('a,'b) prod`（Isabelle 前缀式），**`prod 'a 'b` 不解析**（实测报错）

### 3.5 `#[N]` 注解可省

`.pyhol` 证明里的 `#[N] prop` 行是纯文档，`_parse_thm_body` 不要求它们，replay 也不验证命题。
写文件时去掉即可；`goal=` / `facts=` 的数字是**自动编号**，必须写对。
（用户明确提过这一点，别再花力气生成注解。）

### 3.6 `facts=[...]` 只接受数字

REPL 的 `_parse_step_line`（`syntax/pyhol.py`）用 `^facts=\[([\d,\s]*)\]$` 匹配，
里面不能放命题文本。传了非数字会得到 `fact sid '[' not found` 这类费解报错。

### 3.7 `imports` 是逗号分隔，不是空格

`imports set, prod`。写成 `imports set prod` 会报 `KeyError: 'set prod'`。

### 3.8 稳定 ID 的重复命题与跨分支依赖

- `th2sid` 按**命题相等**分配（`method/stable_state.py::_ensure_sid`），
  同一命题在多个分支出现时**共用 sid**；`sid2pos = {v: k for k, v in pos2sid.items()}` 保留**最后一个**位置。
- `apply_method` 有 `assert goal_id.can_depend_on(fact_id)`（`method/methods/core.py:1658`），
  `ItemID.can_depend_on`（`kernel/proof.py:71`）要求"同父级且编号更大"。
  **兄弟分支里派生的事实不能拿来给自己的目标用**。
- 后果：`per_union_is_trans` 的 3×3 情况**不能塞进一个证明**——每个分支都会重复派生
  `(x,a) ∈ R` 之类的命题，重复命题共享 sid，跨分支引用直接 `illegal dependence`。
- 解法：拆成 9 条**单分支** case 引理（§4.3），主引理用 `rule per_union_case_ij` 一步一步收口。
  这样每条引理内部只有一条分支，不会重名。

### 3.9 `intro` 的行为

- `intro x,y` 会引入**全称变量和蕴含前提**（一次做完），别再多写一步 `intro` 推前提。
- `intro` 不带名字会抛 `ParameterQueryException: ['names']`，必须写名字。
- 目标里的自由变量做归纳/分情况时，`rule <tyname>_cases` 匹配不上（会保留自由变量），
  要用 **`type_cases <var> goal=N` 方法**（`library/nat.pyhol` 里有大量先例）。
  用 `type_cases` 后子目标常带 `!left. !right.` 前缀，需要 `intro u,v` 再关。

### 3.10 `rewrite` 的两个行为

- `← rewrite <thm> goal=N` 与 `→ rewrite <thm> target=fact goal=N facts=[...]` 都用
  `top_sweep_conv`（`core/conv/core.py:322`，顶层失败则递归进 fun/arg/abs），**能重写子项**。
- `rewrite_fact_macro`（`core/macro/registry.py:385`）会检查 `has_rewrite` 且要求**重写必须有效果**，
  否则 `InvalidDerivationException: rewrite_fact using X`。所以展开链**顺序有约束**：
  比如 `member_collect` 必须等内层 `∪` 先用 `member_union_iff` 打开之后才有效（§4.2）。
- `→ rewrite target=fact` 在结果与目标相等时会**自动关门**，尾部常有多余的 `apply_prev` 需要删掉。

### 3.11 `rule` 只吃不超过前提数的 facts

`← rule disjI1 goal=N facts=[a,b]` 会报 `_backward_rule: too many previous facts`。
多前提结论要拆成多步或换引理。

### 3.12 REPL 里证出来的定理**不会**进理论

REPL 只维护证明状态。要入库必须把 `export` 出的 proof 块追加进 `.pyhol` 文件。
`per_union_is_sym` 之类依赖前面定理的证明，必须先把前面的追加进文件、**重启常驻 server**，
否则 `Theorem X not found`。

### 3.13 基础库禁用 simp / auto / z3

`FOUNDATION_DEBT.md` 的既有约定：基础库不写 `simp`/`auto`/`norm`/`z3`，要用展开与显式规则写。
`relation.pyhol` 全部是 `rewrite` + `rule` + `forward` + `conjD1/2` + `disjE` + `apply_prev`。

### 3.14 其它小项

- `goal` 命令**不带引号**：`goal sym R ⟶ sym (per_union R a b)`。
- `var NAME TYPE` 按**第一个空白**切分，类型串可以带空格与逗号。
- 定义了 `hint_rewrite` 的新常量不会影响其它理论：只有该常量出现时才触发。但
  `hint_backward`/`hint_forward` 会进全局搜索网，命名要避免与既有定理混淆。
- 改 `syntax/` 后必跑 `python -m pytest syntax/tests -q`（58 条）。

---

## 4. 证明经验与范式

### 4.1 总流程

1. 先只写**定义**，`python .cache/validate_one.py <theory> --force` 确认能加载。
2. 用**常驻 REPL + client** 逐条造证明（见 §5），每条 `export`。
3. 追加进 `.pyhol`，重跑 `validate_one.py`，只继续下一条。
4. 需要依赖前面定理时重启 server。
5. 最后补测试、跑回归、提交。

### 4.2 范式一：把定义展开固定成一条引理（`per_union_iff`）

集合版 `per_union` 的成员展开要 7 步（`per_union_def` → `member_union_iff` ×2 →
`member_collect` → `fst_def_1` → `snd_def_1`）。若每条引理都写这 7 步，19 条引理会全是噪音且容易错序。

做法：先证一条 `per_union_iff`：

```
theorem per_union_iff
  prop ((x,y) ∈ per_union R a b) ⟷ ((x,y) ∈ R ∨ ((x,a) ∈ R ∧ (b,y) ∈ R) ∨ ((x,b) ∈ R ∧ (a,y) ∈ R))
  [hint_rewrite]
```

证明是"两个方向各一条展开链"，方向 1 是对**事实**展开（`→ rewrite ... target=fact`），
方向 2 是对**目标**展开（`← rewrite ... goal=N`），后者最后一两步会自动关门。

此后所有引理只依赖 `per_union_iff`，读起来与 curried 版一致。**这个模式对阶段 2-6 的每个
"用 `{p. ...}`/`∪`/`image` 定义出来的集合算子"都适用：先把成员刻画固定成一条引理。**

### 4.3 范式二：按分支拆引理，避免重复命题

见 §3.8。9 条 case 引理的形式统一为
`trans R ⟶ D1_i ⟶ D2_j ⟶ (x,z) ∈ per_union R a b`，
每条内部单分支，证明套路固定：

```
← intro goal=0                      # 得 1=trans R, 2=D1, 3=D2, 4=goal
→ rewrite trans_def target=fact goal=4 facts=[1]    # 5 = ∀x y z 形式
→ forward conjD1 goal=4 facts=[2]                   # 拆合取
→ forward conjD2 goal=4 facts=[2 or 3]
→ forward goal=4 facts=[5, <两前提>]                 # 用 trans 串
← rule per_union_memI1|memI2|memI3 goal=4 facts=[...]
```

**注意 `trans_def` 展开要放在 intro 之后的第一位**，否则 id 与后续步骤错位（我在这上面浪费了两轮）。

哪些 case 需要 `trans`：`(2,2)` 和 `(3,3)` 不需要（合取里已直接给出目标析取项），其余都要。

### 4.4 范式三：`forward` 做传递链

`trans R` 展开成 `∀x y z. (x,y)∈R ⟶ (y,z)∈R ⟶ (x,z)∈R` 后，
`→ forward goal=N facts=[该事实, 前提1, 前提2]` 一步得到结论。注意 facts 里**事实本身排第一**。

### 4.5 结构骨架（主引理）

`per_union_is_trans` 的主证明是：`rewrite trans_def` → `intro x,y,z` →
对两个假设各做一次 `per_union_iff` 展开 → 两轮 `disjE` 拆成 3×3 →
每个叶子 `rule per_union_case_ij`。9 条 case 引理让主证明只剩 3×3 的骨架。

### 4.6 一个反直觉点

`per_union_var` 的集合展开**只在假设上做，不要做在 goal 上**（`per_union_is_sym` 的教训）：
goal 一旦展开成析取，`rule per_union_memI*` 就匹配不上（结论是成员、goal 是析取）。
保持 goal 为成员形式，用 `memI*` 收口。

---

## 5. 工具链

### 5.1 常驻 REPL（推荐）

```bash
python -m repl.repl --theory relation --serve --port 5598 &
python -m repl.client --port 5598 --stdin < steps.txt   # 退出码 0=无失败且无 open goal
```

`steps.txt` 形如：`var ...` / `goal ...` / 步骤行 / `export`。
改完 `.pyhol` 要**重启 server** 才能看到新定理。

### 5.2 单理论验证

```bash
python .cache/validate_one.py relation --force
```

### 5.3 已写的辅助脚本（都在 `.cache/`，**被 gitignore，不会进仓库**）

- `.cache/drive_rel.py`：进程内跑 REPL，支持**语义化 ID 解析**，是本次效率的关键。规则：
  - `goal=@` → 上一步新开的第一个仍开的子目标；否则上一步的目标（若仍开）；否则最大 sid。
  - `facts=[#PROP]` → 按打印形式匹配事实，**取 sid 最大的那个**（即同分支最近派生的一次）。
  - `facts=[#@]` → 最近派生的事实（做重写链时用）。
  - 调用：`python .cache/drive_rel.py CASES_FILE`，CASES 文件里定义 `THEORY`、`VARS`、`PROOFS`。
- `.cache/add_thm.py`：跑 client → 抽取 `proof..qed` → 去注解 → 追加定理 → 验证。
- `.cache/validate_one.py`：**仓库原有**（不在 .cache 的话见 `FOUNDATION_DEBT.md` 的说明）。

**给下一个 AI 的建议**：把 §5.3 的语义解析规则当作基础设施先重建一遍
（`.cache` 随时可能被清），比手算稳定 ID 快得多。手算 id 在 §3.9/§3.10 那些行为下极易错位。

### 5.4 抽取证明块的注意点

从 REPL 输出里抓导出块**必须按行判断** `l.strip() == 'proof'` 与 `== 'qed'`。
用 `text.split('proof')` 会撞上 REPL 的 `no open goals -- proof complete` 那行（我踩过）。

---

## 6. 阶段 2-6 的具体内容

### 阶段 2：逻辑基础库补齐

| 要补 | 位置 | auto2 用量 |
|---|---|---|
| `option`（`datatype option 'a = | None | SomeC 'a`，注意 `logic_base` 的 `Some` 是 Hilbert 选择算子，**重名**） | 新 `library/option.pyhol` | Mapping_Str 的 `'a ⇒ 'b option`、BST/RBTree search、Dijkstra map |
| list 补全：`take`/`drop`/`sublist`/`zip`/`concat`/`map`/`filter`/`foldr`/`butlast`/`list_update`/`list_swap`/`insort`/`remdups`/`sorted`/`strict_sorted` | `library/list.pyhol`（现仅 19 项） | Quicksort 用 `sublist` 19 次、`take/drop` 6 次；Rect_Intersect 用 nth 53 次 |
| `multiset`（全库为零）：`mset`/`count`/`set_mset`/`+`/`-`/置换 | 新 `library/multiset.pyhol` | Quicksort 3 处、Arrays_Ex 2、Indexed_PQueue 2 |
| 关系演算扩展：`rtrancl`/`trancl`/`equiv`/`refl_on`/`converse`/`Domain`/`Range` | `library/relation.pyhol` | Connectivity 的 `connected_rel` 用传递闭包 |
| 有限集收口：`finite_induct`、`card` 定义化、`range`/`Collect` 引理、`Min`/`Max` | `library/set.pyhol` | Dijkstra 的 `dist`、Union_Find 的 `[0..<n]` |

**注意**：`rtrancl` 用 `inductive` 定义（holpy 支持函数类型参数，`ll` 是先例），可得归纳原理。

### 阶段 3：序

auto2 的 `'a::linorder` 有 48 处，`instantiation` 3 处。**不做类型类**，改成：

```
def linorder :: ('a ⇒ 'a ⇒ bool) ⇒ bool = linorder le ⟷
  (∀x. le x x) ∧ (∀x y. le x y ⟶ le y x ⟶ x = y) ∧
  (∀x y z. le x y ⟶ le y z ⟶ le x z) ∧ (∀x y. le x y ∨ le y x)
```

函数与引理把 `le` 当显式参数/前提；实例是定理（`linorder (λx y. x ≤ y)` 之于 nat）；
自定义类型是**条件实例**（`linorder le ⟹ linorder (int_less le)`），正好对应
`instantiation interval :: (linorder) linorder`。

`fun` 的结构守卫允许函数类型的前导参数（`_classify_args` 只把带构造子模式的参数算 pattern，
其余必须是**普通变量**），所以 `fun insort :: ('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a list ⇒ 'a list` 合法。

参考：`Orderings.thy` 1557 行 + `Order_Relation.thy` 665 行，但**不要照抄**——
其中大半在伺候 Isabelle 的 class/locale 机制，holpy 用不上。只实现 auto2 实际引用到的。

### 阶段 4：良基与递归（**这一阶段是机制改动，风险最高**）

先读 `FOUNDATION_DEBT.md` §4：良基递归、一般递归合法性检查都没有。

顺序**不能反**：

1. 建 `library/wf.pyhol`：`acc R a` 用 `inductive` 定义；`wf R ⟷ ∀a. acc R a`；
   `wf_induct`、`wf_minimal`、`measure`、`measure_wf`。
2. `wfrec` 用 `SOME`/`The` 定义，配 `is_recfun`；核心定理 `wfrec_eq`。
3. tactic 层加**关系归纳**：`wf R ⟹ (∀x. (∀y. R y x ⟹ P y) ⟹ P x) ⟹ ∀x. P x`。
   没有它，函数定义了也证不了性质（auto2 的 `@fun_induct` 对应这个）。
4. 新增 `function` 项：用户给关系或 measure、证 `wf R`、给下降条件，**方程由 `wfrec_eq` 派生**。
5. **最后**才放宽 `fun` 守卫。

**关键约束**：现在 `fun` 的方程走 `mk_axiom`，一致性全押在结构守卫上。
守卫一松而不把方程改成派生，就等于把未检查的递归定义当公理注入。
这是"定义 ≡ 公理"这条地基的代价面，必须显式记账。

auto2 侧需要它的地方：`part1`、`quicksort`（`termination by measure`）、`idx_bubble_down_fun`、
`rect_inter`（4 处 measure 类）+ `rep_of`（`function (domintros)`，是不证终止的偏函数，
要的是域谓词而不是 wf）。命令式那 30 个 `partial_function (heap)` 是堆单子不动点，**第三套机制**，
别混进 wf。

参考：`Wellfounded.thy` 1513 + `Wfrec.thy` 145 + HOL Light `wf.ml` 440 行。

### 阶段 5：Functional 领域库

按 auto2 的依赖顺序补（对应文件大小是规模参考）：

1. `Mapping_Str.thy`（9.2KB）：函数式 map，`datatype ('a,'b) map = Map "'a ⇒ 'b option"`（函数类型字段，
   正性检查放行）。定义 empty/update/delete/keys_of/map_of_alist/map_of_aset/unique_keys_set。
2. `Partial_Equiv_Rel.thy`（2.4KB）：**阶段 1 已完成**。
3. `Union_Find.thy`（6.3KB）：`rep_of` 递归、`ufa_invar`、`ufa_α`。
4. `Interval.thy`（3.0KB）：`datatype 'a interval`、`idx_interval`、自定义序（阶段 3 的条件实例）。
5. `Arrays_Ex.thy`（8.3KB）：`list_swap`、`sublist`、`list_update_set`、`array_copy`。
6. `Indexed_PQueue.thy`（18.3KB）：堆不变量。
7. 算法（依赖上述）：`Lists_Ex` → `BST` → `RBTree`；`Quicksort`；`Interval_Tree` → `Rect_Intersect`；
   `Connectivity`；`Dijkstra`。

### 阶段 6：Imperative

**最大的一块，且是唯一需要重建"堆模型"的阶段。**

auto2 建立在 Isabelle 的 Imperative_HOL 上：带类型 ref/array、`lim`、堆单子
（`return`/`bind`/`effect`/`execute`）。holpy 只有裸 `nat⇒nat` 堆（`library/mem.pyhol` 是雏形）。

要做：
1. 堆模型：`heap`/`addr`/`lim`/`refs`/`arrays` + `Ref`/`Array` + 堆单子。可选用无类型堆规避
   `'a::heap` 类（auto2 有 92 处 `::heap`，那是序列化类，不是序）。代价是堆里存不了任意类型。
2. 分离逻辑：`pheap`/`in_range`/`relH`；`assn`。`SepAuto.thy:75` 的
   `typedef assn = "Collect proper"` 是全仓**唯一**一处 typedef —— 用
   `datatype assn = Assn (pheap ⇒ bool)` + 显式 `proper` 前提替代，或声明类型+公理。
   `emp`/`*` 定义成普通常量，`assn_one_left` 之类代数律本来就是手证的。
3. 12 个实例：`Arrays_Impl` → `DynamicArray` → `LinkedList` → `BST_Impl` → `RBTree_Impl` →
   `IntervalTree_Impl` → `Indexed_PQueue_Impl` → `Union_Find_Impl` → `Quicksort_Impl` →
   `Connectivity_Impl` → `Dijkstra_Impl` → `Rect_Intersect_Impl`。
4. 自动化胶水（`sep_steps.ML` 824 行、`assn_matcher.ML` 324 行）**不在范围内**——那是自动化。

---

## 7. 工作纪律（用户明确要求过的）

- **不要一次性写完整文件**。逐条驱动、追加、验证。
- 不要过度宣称。每个结论要么有命令输出，要么标注"未验证"。
- 改动后跑相关回归：
  ```bash
  python -m pytest library/tests syntax/tests core/tests util/tests -q
  python .cache/validate_one.py <改动的理论> --force
  ```
- `validate_library.py --force` 很贵，且脚本里明确写了未经许可不要跑。
- 提交在 `main`（仓库惯例，origin/main 长期落后，本地主干工作流）。提交信息写清改动与测试结果。
- 文档同步：`ARCHITECTURE_AUDIT.md`、`FOUNDATION_DEBT.md` 是本仓库的现状契约，
  动了相应内容要同步（例如阶段 2 补完 `multiset` 后要更新 `FOUNDATION_DEBT.md` 的 P2）。

---

## 8. 阶段 2 实测修订与进度（2026-09-13，接手者追加）

§6 的依赖清单是**按 Isabelle 库的完整面**估的，不是按 auto2 的实际用量。开工前先量了一遍，
下面每条都可复现：

```bash
cd holpy
for f in rtrancl trancl converse Domain Range refl_on equiv Id Image Restr Field \
         mset count set_mset card finite sum Min Max sorted strict_sorted insort \
         zip concat foldr foldl remdups take drop sublist nth list_swap list_update \
         butlast last map filter itrev distinct rev hd tl; do
  printf "%-14s %s\n" "$f" \
    "$(grep -ohE "\\b$f\\b" ../auto2/HOL/Program_Verification/Functional/*.thy \
        ../auto2/HOL/Program_Verification/Imperative/*.thy | wc -l)"
done
grep -ohE '@' ../auto2/HOL/Program_Verification/Functional/*.thy | wc -l   # 1299
grep -ohE '!' ../auto2/HOL/Program_Verification/{Functional,Imperative}/*.thy | wc -l  # 320
```

### 8.1 应当删掉的条目

| §6 里的条目 | 实测 | 结论 |
|---|---|---|
| 关系演算扩展 `rtrancl`/`trancl`/`equiv`/`refl_on`/`converse`/`Domain`/`Range` | **全部 0 次** | **不要做**。Connectivity 的 `connected_rel` 用的是它自己在 `Connectivity.thy` 里定义的归纳谓词 `has_path`/`is_path`，不是 `rtrancl`。`equiv` 的 8 次命中全是 Isabelle 的 `≡`（`\<equiv>` 定义记号），不是关系谓词 |
| `Min`/`Max` | 0 次 | 不要做 |
| `zip`/`concat`/`foldr`/`foldl`/`remdups`/`insort`/`sum` | 0 次 | 定义已给出（廉价），但不值得为它们写引理 |
| `multiset` 的 `count`/`set_mset`/`-` | 0 次 | 只需要 `mset`（16 次）与 `{#x#}`/`+` |
| `multiset` 类型名本身 | 0 次 | 只以 `mset _ = mset _` 的等式形式出现，即"置换" |

### 8.2 应该加重的条目

| 条目 | 实测 | 说明 |
|---|---|---|
| `@`（append） | 1299 | 最高频，`library/list.pyhol` 已有 |
| `length` | 347 | 已有 |
| `!`（nth） | 320 | 已有定义，但**引理几乎没有**——Rect_Intersect 与 Quicksort 大量依赖 `nth` 的追加/更新/交换律 |
| `set`（list→set） | 145 | 已有 |
| `hd`/`tl` | 41/12 | 已有 |
| `map` | 45 | 本次补：`length_map`/`map_append` |
| `sublist` | 57 | 本次补定义；引理（`length_sublist`/`nth_sublist`/`sublist_append`/`sublist_Cons`…）auto2 放在 Arrays_Ex，属阶段 5 |
| `last`/`butlast` | 35/15 | 本次补定义 |
| `list_swap`/`list_update` | 26/11 | 本次补定义 |
| `take`/`drop` | 16/10 | 本次补定义 + 骨架引理 |
| `strict_sorted`/`sorted` | 31/15 | **需要序**，见下 |
| `mset` | 16 | 待做（阶段 2.3） |
| `card`/`finite` | 9/1 | 待做（阶段 2.5） |

### 8.3 依赖顺序的一处修正

§1 的 `1 → 2 → {3,4}` 在 **`sorted`/`strict_sorted`/`insort`/`ordered_insert`** 上不成立：
这些函数的类型里带 `'a::linorder`，没有序就写不出来。也就是说 **§6 阶段 3（序）必须排在
阶段 2 的这一部分之前**，而不是之后。其余阶段 2 内容（`option`/list 原语/`mset`/`card`）确如
§1 所说是阶段 3、4 的前置。

### 8.4 本次已交付（两个提交）

- `9c338f69` 阶段 2.1：`library/option.pyhol`（`datatype option`、`the`、`not_None_iff`）+ 测试。
- `f46b15d0` 阶段 2.2 part 1：`library/list.pyhol` 补 15 个函数（take/drop/sublist/last/butlast/
  map/filter/foldr/foldl/concat/zip/itrev/list_update/list_swap/remdups）与 7 条定理
  （`take_nil`/`take_cons`/`drop_nil`/`drop_cons`/`append_take_drop_id`/`length_map`/`map_append`）+ 测试。
- 阶段 2.2 part 2（本次）：`nth_append_lt: !xs. i < length xs ⟹ nth (xs @ ys) i = nth xs i`
  ——第一条带 `< length` 守卫的列表引理，也是 `!`（320 次）引理族的范式样板（见 §8.5 第 6–9 条）。
- 阶段 2.2 part 3：`list_update` 的展开特化引理 `list_update_nil`/`list_update_zero`/
  `list_update_cons`（都 `[hint_rewrite]`，§4.2 范式）、`nth_list_update_same`、
  `length_list_update`、`length_list_swap`。`list_update` 的递归参数从 list 改成 nat
  （与 take/drop/nth 一致，去掉 `i - 1` 与 `Suc n = 0` 的算术摩擦）。
- 阶段 2.2 part 4：`nth_map`（`!`×`map` 交叉处的核心引理）、`sublist_0`。
- 阶段 2.3：新理论 `library/multiset.pyhol`（10 条定理，全 VALID）。多重集用
  `typeabbrev multiset 'a = 'a ⇒ nat`（计数函数）表示——**不需要商类型，也就不受
  "holpy 没有类型定义原语"的限制**。定义 `empty_mset`/`single_mset`/`union_mset`/`count`/
  `set_mset`/`mset`，并证 `count_union_mset`、`count_empty_mset`、`count_single_mset_same/other`、
  `union_mset_empty_left/right`、`union_mset_comm`、`union_mset_assoc`、`mset_append`、`mset_rev`
  （置换律）。集合层面的等式靠 `rule extension` + `intro` 转成逐点计数等式。
  回归 `pytest library/tests syntax/tests core/tests util/tests -q` → 189 passed；
  `validate_one.py list` → VALID 26、`multiset` → VALID 10，non-green 都是 0。

仍未做：list 的其余 `nth`/`update`/`swap`/`sublist` 引理族（2.2 part 2 续，
其中 `length_sublist`/`sublist_append` 之类需要 `≤` 的算术引理，见下）、
`mset_list_swap`（2.3 收尾，依赖 2.2 的 `list_update` 计数引理）、
`card`/`finite_induct` 收口（2.5），以及阶段 3–6。

**一处需要更正的前置依赖判断**：我先前以为 nat 缺 `Suc m ≤ Suc n ⟷ m ≤ n`，实测**它已经存在**，
叫 `le_suc`。真正缺的是更基础的两条，本次补入 `library/nat.pyhol`：
`lesseq_refl`（`n ≤ n`）与 `lesseq_zero`（`0 ≤ n`）——都是 `nat_induct` + `nat_less_eq_def_1/2`
各两步的短证明。补上之后 `length_filter_le`（`length (filter P xs) ≤ length xs`）顺利证出。
随后把这条链打通：`length_take_le`（`length (take n xs) ≤ n`）、`length_take`（`r ≤ length xs ⟹ length (take r xs) = r`）、`length_drop`（`l ≤ length ys ⟹ length (drop l ys) = length ys - l`）、`length_sublist`（`l ≤ r ⟹ r ≤ length xs ⟹ length (sublist l r xs) = r - l`），全部 VALID（list 现 31 条）。sublist 实测 57 次（Arrays_Ex），这条链是它的基础。
`length_drop` 用到 `nat_minus_suc`；`length_sublist` 把两个 ∀-形式引理引进来用，配方见 §8.5 第 13 条。
仍属阶段 3 前置的：`sorted`/`strict_sorted`（需要 `linorder`），以及 `sublist` 的其余引理（`sublist_append`/`sublist_Cons`/`nth_sublist` 等，auto2 放在 Arrays_Ex，属阶段 5）。

### 8.5 机制上的新经验（§3 之外）

1. **`fun` 只允许一个参数带构造子模式**（`core/defcheck.py::check_fun_recursion` 实测），
   所以 `take :: nat ⇒ 'a list ⇒ 'a list` 不能同时对 nat 和 list 做模式匹配。用
   「nat 作递归参数 + `if xs = []` 守卫」写，再把 `0`/`Suc` 与 `[]`/`#` 四种组合的展开式
   **各自证成 `[hint_rewrite]` 特化引理**（`take_nil`/`take_cons`/`drop_nil`/`drop_cons`）。
   这正是 §4.2「先把展开固定成一条引理」的用法，否则每条下游引理都要重做一遍 if 展开。
2. **`¬(x # xs = [])` 的来路**：datatype 只给 `list_nil_cons_neq: ~([] = ?x # ?xs)`，
   方向是反的。用 `← rule ineq_sym`（`~(x=y) --> ~(y=x)`）先翻方向，再 `← rule list_nil_cons_neq`
   关掉；随后 `← rewrite if_not_P ... facts=[<该事实>]` 消去守卫。
3. **`cut "P" goal=N` 产生的可用事实，sid 是"证明 P 之后 NEW 出来的那个"**，不是 cut 行编号
   （`cut` 建的是目标；`← refl goal=cut_sid` 之后会多出一个同命题的新 sid）。用 `all` 看一眼再引用。
4. **`rule` 对付否定式定理会报 `_backward_rule: too many previous facts`**，因为 `neg` 是独立常量、
   `strip_implies` 看不到前提。形状为 `~A` 的定理配事实 `A` 要用 **`← resolve <thm> facts=[A]`**。
5. **`type_cases` 不代入归纳假设**：在「已被 `intro` 拆出的 ih」上做 `type_cases`，ih 里的变量
   不会被替换，于是 ih 用不上。正确做法是把命题写成全称形式
   （`prop !xs::'a list. take n xs @ drop n xs = xs`），对 `n` 用 `induct`，让 ih 带 `∀xs`；
   之后 `→ inst "<项>" goal=N facts=[ih]` 实例化。`append_take_drop_id` 就是这么证的。
6. **`inductive` 允许非谓词前提**（先例 `library/mem.pyhol` 的 `ll_step: ¬(p = null) ⟶ ll (s p) s ⟶ ll p s`），
   且自动生成 `<name>_induct` 与 `<name>_cases`。若将来真要用传递闭包，这是可行入口（但见 §8.1：
   auto2 用不上）。
7. **带 `< length` 守卫的列表引理的标准配方**（`nth_append_lt` 用的，`!` 引理族都该照这个写）：
   定理写成 `prop !xs. i < length xs ⟹ …` 并对 `i` 做 `induct`（这样归纳假设带 `∀xs`，能实例化）。
   归纳步里 `xs` 是 ∀-绑定的、`type_cases` 够不着；而先 `intro` 出来又会把守卫变成事实、
   `type_cases` 不替换事实（行不可变模型，见 §8.5 第 5 条）。解法是**把守卫重新折回目标**：
   ```
   ← intro xs goal=N                      # 守卫成了事实，目标只剩结论
   cut "<守卫> --> <结论>" goal=N          # 注意 goal= 必须指当前开口目标，不是守卫事实！
   ← type_cases xs goal=<cut 目标>         # 此时 xs 自由、守卫在目标里，两者都替换
   ... 两个构造子分支各自收口 ...
   ← apply_prev goal=N facts=[<cut 事实>,<守卫事实>]
   ```
8. **`cut "P" goal=N` 的 N 必须是开口目标**。指到一个守卫**事实**上不会报错、REPL 的
   `check` 也照样 VALID，但完整重放会报
   `CheckProofException: output does not match`（产生的定理假设集成了那条事实的兄弟分支，
   而目标项的假设集不是）。**这是本次唯一一次真实翻车**，根因就是把第二个 `cut` 写成了
   `goal=24`（守卫）而不是 `goal=25`（目标）。改一个数字即通过。
9. **REPL 的 `check`/VALID 是 `compute_only`**，不做独立原语重放——报告 §5.3 已说过
   "REPL 通过后仍要 `validate_one.py` 复验"，这次实测确证：同一份 proof 块 REPL 说 VALID、
   `validate_one.py` 说 STEP_FAILED。**带守卫的引理务必走 `validate_one.py` 或重放测试台**
   （`StableProofState.create(...)` 逐条 `apply_method_dict` 并看 `num_gaps`/`get_open_goals`），
   不要只看 REPL 的 VALID。
10. **用归纳假设关闭被重写过的目标**：`← apply_prev goal=G facts=[impl,arg]` 在 REPL 里能过，
    但完整重放可能报 `output does not match`。稳妥写法是先 `→ forward goal=G facts=[impl,arg]`
    得到等式事实，再 `← apply_prev goal=G facts=[<新事实 sid>]`（`forward` 出来的事实 sid 顺延一位）。
    `← assumption` 不行——它只认目标自身的 `Thm.hyps`，不认兄弟事实。
11. **∀-形式的命题不是重写规则，`rule` 也吃不下**（实测）：
    `prop !xs::'a list. length (list_update xs i v) = length xs` 这种写法产生的是
    真全称命题；`← rewrite`/`← rule`/`← accept` 都对它报 MatchException 或 "unable to apply"，
    `[hint_rewrite]` 也没用。用法只有：
    ```
    → forward <thm> param_i=.. param_v=.. goal=N     # 得到 "!xs. …" 事实（schematic 参数必须给全）
    → inst <列表项> goal=N facts=[<该事实>]            # 得到实例事实（若实例与目标命题相同则不会新增 sid！）
    ← apply_prev goal=N facts=[<该事实>]              # 实例正好等于目标时直接关门
    ```
    注意 `param_v="(nth xs i)"` 这类含空格的参数**必须加引号**，否则客户端按空白切分。
    反过来，**只用 `fixes` 声明、命题里不写 `!` 的定理才是 `rewrite` 能用的等式**（Var 会被
    `get_theorem(svar=True)` 转成 schematic 变量）。所以：
12. **索引驱动递归的函数（`take`/`drop`/`nth`/`list_update`）的"一般引理"只能是 ∀-形式。**
    因为递归同时消耗索引和列表，无论对哪一个做 `induct`，归纳假设都是错的（ih 的索引/列表与
    递归调用的不一致）。只有把另一个参数写成 `!`（命题里），`induct` 才会给出带 ∀ 的 ih——
    这正是 `append_take_drop_id`/`nth_append_lt`/`nth_list_update_same`/`length_list_update`
    的写法。代价就是第 11 条：它们不能当重写规则用。
    **对策**：另证「list 作参数、索引作模式」的展开特化引理（`take_cons`/`drop_cons`/
    `list_update_zero`/`list_update_cons`），下游用这些做重写；∀-形式的总结论只偶尔用
    `forward`+`inst`/`apply_prev` 引一次（`length_list_swap` 就是这么证的）。
13. **∀-形式且带蕴含的定理（`!xs. 守卫 ⟹ 等式`），`forward` 也用不了**：`strip_implies` 看不进 ∀，
    所以 `forward` 认为它没有前提，传前提事实会报 `too many prevs`；不给类型信息又会报
    `unmatched type variable`（∀-绑定变量正是携带类型变量的那个）。可用的唯一配方是
    「把定理原命题 `cut` 成目标、再用 `accept` 关掉」得到 ∀-事实：
    ```
    cut "!xs::'a list. r <= length xs --> length (take r xs) = r" goal=N   # N 必须是开口目标
    accept length_take goal=<上面 cut 出来的目标>            # 得到 ∀-事实
    cut "length (take r xs) = r" goal=N                     # 要用的实例
    ← apply_prev goal=<该实例> facts=[<∀-事实>, r <= length xs]   # 实例化 + 消前提
    ```
    多层要用就先 `→ inst "<项>" goal=N facts=[<∀-事实>]` 得到蕴含式，再 `→ forward` 消前提。
    **顺序约束**：这些事实必须**在**用它们改写的那一步**之前**全部搭好，否则报
    `apply_method: illegal dependence`——线性证明只允许依赖同分支且位置在前的项
    （`length_sublist` 就是把 `sublist_def` 的展开放到最后一步才成功）。

---

## 9. 阶段 2.5 实测：set.pyhol 有限集块收口（本轮）

阶段 2.2/2.3 的 list/multiset 之后，本轮把 `library/set.pyhol` 的证明债收掉了
大头。**set 的非绿项从 22 条降到 2 条**。

### 9.1 结果

```
validate_one.py set
  AXIOM        1     set_equal_iff（故意留的公理）
  UNPROVED     2     card_image_inj / surjective_iff_injective
  VALID        58
non-green: 2
```

那 2 条用的是 `const card`（未解释常量，理论里没有任何 card 公理），属于
「可表达性移植」要保留的声明式命题，不打算证——真要证得先给 card 建公理体系。

本轮新证 26 条（含 3 条原为空壳的新增引理）：

| 组 | 引理 |
| --- | --- |
| 子集基础 | `subsetE`、`subset_refl`、`subset_trans`、`subset_diff`、`subset_insert`、`subset_delete`、`subset_inter_left`、`subset_inter_right` |
| 消 insert/delete | `subset_insert_imp`、`delete_subset_insert`、`subset_insert_delete`、`insert_delete` |
| 交并 | `inter_comm`、`union_comm`、`union_insert` |
| image | `image_insert`、`image_combine` |
| 有限集 | `finite_induct`、`finite_insert_imp`、`finite_fin_sub`、`finite_subset`、`finite_insert`、`finite_union_imp`、`finite_inter`、`finite_image`、`finite_delete`、`finite_diff` |
| 最小不动点 | `lfp_lowerbound`、`lfp_greatest`、`lfp_fix_upper`、`lfp_fix_lower`（连带 `lfp_unfold` 从 DEP_FAILED 变 VALID） |

### 9.2 有限集的核心：从 `finite_def` 里挤出事实

`finite` 在本仓库是定义而非归纳规则：

```
def finite :: 'a set ⇒ bool = finite A ⟷ (∀P. P {} ∧ (∀x B. P B ⟶ P (insert x B)) ⟶ P A)
```

于是**关于有限集的一切都得靠代入那个 P**。三条出口：

1. `finite_induct` —— 就是 `finite_def` 的直译（2 步）。
2. `finite_insert_imp` —— 由 `finite A` 造 `finite (insert a A)`：把 `finite_def`
   的 P 实例化成目标谓词，逐条消去前提。
3. `finite_subset`（子集封闭）—— 需要 P 是「一切子集都有限」这种**带 ∀ 的谓词**。
   holpy 没有 beta 化简通道，所以不能直接代入 λ：**把谓词写成命名定义**，
   再代入那个名字（`def fin_sub X ⟷ ∀Y. Y ⊆ X ⟶ finite Y`）。

第 3 条的证明形状（`finite_fin_sub`）：`cut` 出两条归纳前提的合取、`rule conjI` 分两
支证明、再 `apply_prev` 把合取喂给实例化的蕴含。insert 步里要对 `x ∈ Y` 做分叉，
分叉后 `x ∈ Y` 用 `insert_delete` 把 Y 还原成 `insert x (delete Y x)`、`x ∉ Y` 用
`subset_insert_imp` 把 `Y ⊆ insert x B` 收紧成 `Y ⊆ B`。

**偏应用代替 λ**：`finite_union_imp` / `finite_image` 用的谓词是
`def fin_union B X ⟷ finite (B Un X)`、`def fin_image f X ⟷ finite (image f X)`——
把归纳变量放在**最后一个参数**，于是 `fin_union A` / `fin_image f` 是偏应用
（类型就是 `'a set ⇒ bool`），代入时不需要 λ。副作用是 `fin_union` 的参数顺序
刻意反直觉（B 在前、归纳变量 X 在后），文件里写了注释。

### 9.3 新踩到的机制坑（§8.5 的补充）

14. **定理不能前向引用**。`validate_theory` 对每条定理用
    `context.set_context(filename, limit=('thm', name))` 把理论**截断到该定理之前**，
    再 replay。所以在 `.pyhol` 里引用声明在自己后面的定理（或定义），
    探针进程里能跑通，独立 replay 一定 `STEP_FAILED`。
    **表现极具误导性**：错误只是「某个 step failed」，不说是前向引用。
    本轮的 `subsetE`（原先在文件后部）、`finite_empty`（在 `finite_fin_sub` 之后）、
    `insert_delete`、`image_insert` 都因此挪过位置。
15. **定义体引用未声明的常量会被静默丢弃**。`def` 的 item 若解析失败（例如
    `def fin_image` 用了声明在其后的 `def image`），loader 只是把它记成
    `item.error` 并跳过，**常量根本没注册**。下游的症状是解析期
    「The variable(s) fin_image are not declared」——名字被当成变量，
    于是 `inst` 能"侥幸"通过（用变量代入），生成的定理却毫无意义。
    排查办法：`basic.theory_cache[f]['content']` 里翻该 item 的 `.error`。
16. **稳定 ID 会随证明增长重排**。往证明中间插一步，其后所有 sid 平移，
    早先记下的字面 sid 全部失效。REPL/探针里应当用「第几步产生的第几个新条目」
    之类的相对引用，最后再一次性把字面 sid 抄进文件。
    （`.cache/probe.py` 因此加了 `facts=[@step.k]` 与 `goal=autoN` 语法。）
17. **`rewrite`/`apply_prev` 的依赖合法性按位置判定**：
    `ItemID.can_depend_on` 要求「同一分支且位置在前」。跨 `cases` 分支引用兄弟支
    的事实、或引用被 `cut`/`rule` 展开后位于其后的行，都会报
    `apply_method: illegal dependence`。`cases` 之后要用的外部假设，
    位置必须在分叉点之前。
18. **`rule <thm> facts=[...]` 的前提必须与 facts 顺序对齐**，且 `rule` 是
    逐个 premise 匹配的：只给一个事实却想消掉第三个前提（如 `disjE2` 的
    `A ∨ B`）会报 `When matching implies with disj`。这时改用
    `rule <thm>` 后把析取前提当子目标关掉，或给全 `param_*`。
19. **`disjE2` 这类多前提定理要显式给 `param_*`**：元变量从目标推不出来时
    报 `ParameterQueryException: ['param_A', 'param_B']`，必须
    `← rule disjE2 param_A="finite A" param_B="finite B"`。
20. **消析取的实用配方**：`member_insert` 出析取后
    `disj_comm` 换序 + `force_disj_true1`（`A ∨ B ⟶ ¬B ⟶ A`）消掉已知为假的一支；
    矛盾支用 `negE_gen`（`¬A ⟶ A ⟶ C`，结论 C 可与任意目标合一，不必先转成 false）。
21. **带前提的等式/非等式假设**：`x = a` 直接 `← rewrite source=prev` 代入；
    `¬(x = a)` 要先 `→ rewrite target=fact eq_false ... facts=[h]` 得到
    `(x = a) ⟷ false`，再用 `rewrite source=prev` 把它当重写规则用。
    纯布尔事实（如 `a ∈ A`）**不能**当重写规则（`eq_false` 只吃 `¬P`）。
22. **`exists_flatten` 是"存在量词套等式"的专用清理器**：
    `(∃y. (∃z. P z ∧ y = Q z) ∧ R y) ⟷ (∃z. P z ∧ R (Q z))`。
    `image_combine`（`image f (image g A) = image (g ∘ f) A`）整个证明就是
    `set_equal_iff` → `intro` → 两次 `in_image` → `comp_fun_def` → `exists_flatten`。
    `comp_fun_def` 展开 `g ∘ f` 产生的 β-redex 由重写器自动约简，无需额外步骤。

### 9.4 阶段 2 明确剩余（未做，非阻塞）

- **list**：`nth_list_update_diff`（`i ≠ j` 时 update 不影响 nth）。需要
  「对 i 归纳 + 对 j 分 0/Suc 两支」的双索引骨架，比 `nth_list_update_same`
  （§8.5 的守卫重折配方，40 步）更重。`sublist_append`/`sublist_Cons`/`nth_sublist`
  一组 auto2 放在 `Arrays_Ex` 里，归阶段 5。
- **list 定义已备但无引理**：`foldr`/`foldl`/`concat`/`zip`/`remdups` 只有定义。
- **multiset**：`mset_list_swap`（`mset (list_swap xs i j) = mset xs`）、
  `set_list_swap`。需要「`count` 对 `list_update` 的逐点刻画」再让两次更新抵消，
  依赖上一条。
- **set（已收口，见 §10）**：基数层全部证完——`card_image_inj`、`card_mono`、
  `card_image_le`、`card_subset_eq`、鸽子洞引理 `surjective_imp_injective` 与
  `surjective_iff_injective` 都 VALID；set 只剩 3 条故意留的公理（`set_equal_iff`
  与两条 `card` 递归）。
- 阶段 3–6（序、良基递归、Functional 域库、指令式堆模型）未开始；阶段 3 是
  `sorted`/`strict_sorted`/`insort` 的前置。

## 10. 阶段 2.6：set 基数层（2026-09-13 续轮，全部经常驻 REPL 开发）

本轮把 §9.4 里「需要先给 card 建公理体系」的那一层做了。开发流程按
`AGENTS.md` §4：`repl.repl --serve --theory set` 起一次，所有步进走
`repl/client`，证完 `export` 出的证明块直接写回 `.pyhol`，最后
`.cache/validate_one.py set` 独立重放。

### 10.1 结果

```
validate_one.py set
  AXIOM        3     set_equal_iff / card_empty / card_insert
  VALID        73
non-green: 0
```

`surjective_iff_injective` 本身也证完了（见 §10.3），set 理论里除了那 3 条
故意留的公理之外**全部 VALID**。

新增定义（都只为给 `finite_induct` 提供**无 beta-redex 的 P**，varying 参数在最后）：

- `card_le_bound X ⟷ ∀A. finite X → A ⊆ X → card A ≤ card X`
- `card_img_le g X ⟷ finite X → card (image g X) ≤ card X`
- `card_faithful g X ⟷ finite X → card (image g X) = card X → inj on X`
  （本轮未用上，留给 §10.3 的备选路线）
- `card_inj f X`（`card_image_inj` 的 P，RHS 就是那条命题）

新增引理（全部 VALID）：

- `card_image_inj`：`finite s → inj on s → card (image f s) = card s`。
  由 `finite_induct` 实例化 `card_inj f` 归纳；归纳步分 `x ∈ B`（用
  `insert_absorb` 化归 IH）与 `x ∉ B`（`image_insert` + 反证 `f x ∉ image f B`：
  若 `f x = f y`（`y ∈ B`）则 `x = y ∈ B`，与 `x ∉ B` 冲突）。
- `card_le_bound_empty`、`insert_subset_imp`、`not_mem_delete_self`、
  `delete_subset_insert_imp`：元素层辅助（都带**非冗余前提**，见 `set_test.py`
  的被动用例）。
- `card_mono : A ⊆ B → finite B → card A ≤ card B`（`card_le_bound` 归纳）。
- `card_image_le : finite X → card (image g X) ≤ card X`（`card_img_le` 归纳）。
- `card_subset_eq : A ⊆ B → finite B → card A = card B → A = B`：反证 `y ∈ B \ A`，
  则 `insert y A ⊆ B`（`insert_subset_imp`），`card (insert y A) = Suc (card A)`
  与 `card_mono` 的 `≤ card B = card A` 冲突，经 `lesseq_Suc_less` + `less_irrefl`
  收口。**不依赖 `subset_antisym`**（它在文件后面，replay 截断会 STEP_FAILED）。

- **`surjective_imp_injective`**（鸽子洞辅助引理，见 §10.3）与
  **`surjective_iff_injective`**（`finite s → image f s ⊆ s → 满射 ⟷ 单射`）。

card 公理仍是 `card_empty`/`card_insert` 两条（§9 已论证：要定义化需要
pigeonhole 唯一性，库里没有，holpy 也没有类型定义原语）。

### 10.2 本轮新踩到的机制坑（§8.5/§9.3 的补充）

1. **对事实做重写时，事实里的变量必须是「上下文声明」的**：
   `has_rewrite` 内部对 `t.is_open()` 的子项不匹配，`intro`/`elim` 引进的
   变量让 `→ rewrite target=fact THEOREM facts=[f]` 直接
   `InvalidDerivationException`；同一命题在 `fixes` 声明变量下（例如
   写成独立的辅助引理）就能重写。所以元素层的 iff 前向化都下沉成
   带 `fixes` 的辅助引理。
2. **同一命题的条目按 Thm 结构去重**：`#[N]` 是「同命题共号」。于是
   (a) 在兄弟分支里引用先去重过的命题会 `illegal dependence`；
   (b) 在分支内「重做」一遍该推导得到的仍是旧位置，不能用来规避。
   对策：把归纳假设在**进入 `cases` 之前**展开一次（成为两支的共同祖先），
   或者用 `inst "<term>"` 现推出**新命题**再引用。
3. **`rule` 用定理名 + `facts=[...]` 只能给 sid**：定理名不能写在 facts 里；
   要先把定理 `forward` 成事实再用 `apply_prev`（`← apply_prev goal=G
   facts=[<thm事实>, <前提…>]` 会做 forall 消去）。
4. **定理里引用文件后面才声明的条目**：replay 在 `(thm, name)` 处截断理论，
   直接 `STEP_FAILED`（信息只显示「replay failed at step: rule」）。
   要用 `.cache/validate_one.py` 复核，别只看 `check`。
5. **`← rewrite THEOREM sym=false goal=G facts=[<条件…>]`** 很好用：
   带前提的重写定理可以直接重写目标（`card_insert` 的两个前提作为 facts），
   省掉「先 forward 出等式事实」的一步。

### 10.3 `surjective_iff_injective`（已证）

命题：`finite s → image f s ⊆ s → (满射) ⟷ (单射)`，用 `iffI` 分成两支。

- **单射 ⟹ 满射**：`card_image_inj` 给 `card (image f s) = card s`，
  `card_subset_eq` 配 `image f s ⊆ s` 给 `image f s = s`；对 `y ∈ s`
  用 `image f s = s` 把 `y Mem s` 改写成 `y Mem image f s`，再用
  `in_image` 取原像——注意 `in_image` 的右式是 `y = f x`，与目标里的
  `f x = y` 反向，用 `eq_sym_eq` 翻一次即可。
- **满射 ⟹ 单射**：鸽子洞，单独提成辅助引理

  ```
  theorem surjective_imp_injective
    fixes s :: 'a set, f :: 'a => 'a, x :: 'a, y :: 'a
    prop finite s --> image f s Sub s --> (!z. z Mem s --> (?w. w Mem s & f w = z))
         --> x Mem s --> y Mem s --> f x = f y --> x = y
  ```

  **元素变量用 `fixes` 声明而不是写成 λ/∀**，正是 §10.2 第 1 条的经验：
  这样元素层的等式重写（`eq_sym_eq`、`less_Suc_lesseq` 等）都能过
  `has_rewrite`。证明骨架（`cases "x = y"` 后只留 `x ≠ y` 一支）：

  1. `s' = delete s x`：`finite s'`、`~(x Mem s')`、`insert x s' = s`、
     `card s = Suc (card s')`（`card_insert`）、`card s' < card s`。
  2. `y ∈ s'`（用 `~(x = y)` 翻转 + `member_delete`）。
  3. `f x ∈ image f s'`（`in_image` 反向 + 见证 `y`，用 `f x = f y`）。
  4. 于是 `insert (f x) (image f s') = image f s'`（`insert_absorb`），
     配上 `image_insert` 与 `insert x s' = s` 得
     `image f s = image f s'`，进而 `card (image f s) = card (image f s')`
     （用 `cut` + `rewrite source=prev` 造出这条等式，因为库里没有 `arg_cong`）。
  5. `card_image_le` 给 `card (image f s') ≤ card s'`；用上面的等式换成
     `card (image f s) ≤ card s'`，再配 1 的 `card s' < card s`：
     先用 `less_Suc_lesseq sym=true` / `lesseq_Suc_less sym=true` 把
     `a ≤ b`、`b < c` 都抬到 `Suc` 层，`less_eq_trans` 拼，最后
     `lesseq_Suc_less sym=false` 落回 `card (image f s) < card s`
     （这一手避开了「`≤` + `≠` 推 `<`」那条更长的路）。
  6. 满射 → `s ⊆ image f s`（同 §10.3 第一支的取原像配方），配
     `image f s ⊆ s` 得 `image f s = s`（`set_equal_iff` + `iffI` + `subsetE`，
     **不用 `subset_antisym`**，它在文件后面），于是
     `card (image f s) = card s`，把 5 的结论改写成
     `card (image f s) < card (image f s)`，与 `less_irrefl` 冲突，
     `negE_gen` 收口。

## 11. 阶段 3 前置：类型类糖（2026-09-13，先做糖，按用户决定）

auto2 的 `'a::linorder` 共 50 处（`::linorder` 37 + `::ord` 11 + `::order` 2），
`instantiation` 6 处。**不做类型类**（理由见下方「边界」），改成两件事：
库里的序谓词 + 解析层的 `'a::C` 糖。

### 11.1 语义：注解就是前提

```
fixes x :: 'a::linorder
prop x <= x
```

在 item 层被存成

```
fixes x :: 'a
prop linorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶ x <= x
```

即**注解 = 前提**，`'a` 的类型不变。于是 item 层以下（步进、重放、内核）
完全不知道类；前提在**使用处**由实例定理消掉（`nat_linorder`）。
这条等价性来自 Isabelle 自己：Pure 内核没有类，`OFCLASS` 只是 meta 层假设，
类定律全是有条件假设。差别只在「谁来做实例解析」——糖版是显式的，
忠实类型类版交给 elaborator。

### 11.2 实现（约 130 行 + 测试）

| 位置 | 内容 |
|---|---|
| `syntax/parser.py` 文法 | `?typ_atom: "'" CNAME ("::" CNAME)? -> tvar`；transformer 丢掉注解，类型仍是 `'a` |
| `syntax/parser.py` 表 | `CLASSES`: 类名 → (谓词名, 运算表)，运算 = (常量名, 类型模板)；`add_class()` 是扩展点 |
| `syntax/parser.py` 函数 | `class_constraints()`（收集 + 报错）、`class_premises()`、`with_class_premises()` |
| `core/items.py` | `Axiom.parse`（`Theorem` 继承）里注入前提；`data` 是原始文本，所以 `'a::linorder` 留在源码里、导出回环保留 |
| `repl/repl.py` | `cmd_goal` 用同一条规则注入，所以 `var x 'a::linorder` + `goal x <= x` 与 item 的陈述一致 |
| `library/order.pyhol` | 新理论：`preorder`/`order`/`linorder` 谓词、6 条层级/投影引理、3 条 `nat` 实例、`linorder_refl/trans/antisym`、两条糖的端到端演示 |

### 11.3 边界（明确不做 / 留待增量 2）

- **datatype 参数上的约束**（`('a::linorder, 'b) tree`）暂不传播：holpy 的
  `datatype` 行只写参数名，没有 kind 注解。阶段 5 真需要时加一个 item 元数据
  + 传播（那时是「约束环境」，不是文本替换）。
- **定义（`def`/`fun`/`inductive`）只把注解当标记**：它们的方程对实例是均匀的
  （运算就是通用重载常量 `less_eq`），所以不注入前提；`fun tree_sorted ::
  ('a::linorder,'b) tree ⇒ bool` 这类签名照写即可。
- **不做忠实类型类**：`kernel/type.py` 的 `Type` 没有 sort；`kernel/theory.py:253`
  的 `get_overload_const_name` 明确要求实例类型是具体类型常量，所以「在类型变量上
  解析类运算」要改重载解析本身，再加超类闭包、重叠一致性、defaulting——2~5 天
  且动内核相邻代码，换来的只是 50 处的书写便利。
- **JSON/edit 面看到的是脱糖形态**：`.pyhol` 源码（和 `.pyhol` 回环）保留
  `'a::linorder`，而 `export_json`/`get_display` 给出的是去掉注解的 fixes +
  显式前提 `linorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶ ...`（两者语义相同，且不会
  二次注入——注解已经不在文本里了）。前端保存的文本因此是脱糖形态，这是可接受
  的规范形态。
- **实例解析暂不做自动化**：使用处手写 `rule <law> facts=[<约束事实>]`（约束事实
  来自注解或实例定理）。以后要自动化，加一张实例表让 solver 试即可，不动内核。

### 11.4 阶段 3 剩余

**转写 auto2 陈述时的一个文法语限制**：holpy 的 `∀` 只吃一个绑定变量，
`∀x y z. P` 必须写成 `∀x. ∀y. ∀z. P`（`∃` 同理）；`library/order.pyhol` 的定义
里就是这么写的。auto2/Isabelle 原文里的多变量量词照抄会解析失败。

谓词层（preorder/order/linorder + 层级引理 + nat 实例）已就位；
`sorted`/`strict_sorted`/`insort`/`ordered_insert` 与 `Min`/`Max` 仍待做，
它们建在 `linorder` 谓词上，语法照 auto2 写（`fixes xs :: ('a::linorder) list`）。
实例还需要 `int`/`real`（各自一条定理，料已在各自理论里）。

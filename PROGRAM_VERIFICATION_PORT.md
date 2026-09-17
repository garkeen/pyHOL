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

- `th2sid` 按 **Thm 相等**分配（`method/stable_state.py::_ensure_sid`），而
  `Thm.__eq__`（`kernel/thm.py:105`）比的是**假设集合 + 命题**——所以共号的条件比
  「同一命题」严：命题相同、假设集合不同是两个条目、两个 sid。同一 Thm 在多个分支
  出现时**共用 sid**；`sid2pos = {v: k for k, v in pos2sid.items()}` 保留**最后一个**位置。
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
python -m repl.repl --serve --port 5598 --theory relation &
python -m repl.client --port 5598 --stdin < steps.txt   # 退出码 0=无失败且无 open goal
```

`steps.txt` 形如：`var ...` / `goal ...` / 步骤行 / `item NAME`。
改完 `.pyhol` 要**换端口重起 server** 才能看到新定理（端口被占会明确报错退出 2，
不会像以前那样悄悄抢占端口、让客户端继续连旧进程）。

### 5.2 单理论验证

```bash
python .cache/validate_one.py relation --force
```

### 5.3 语义化 ID 现已内建（2026-09-13 补记）

§5.3 原先建议"把语义解析规则当基础设施重建一遍（`.cache` 随时可能被清）"。
现在它已经落在 `repl/` 里，不再是 `.cache` 的临时脚本：

- `goal=@` / `goal=@N` / `goal="<命题>"`；`facts=[@]` / `facts=[@N]` /
  `facts=["<命题>"]`；`let NAME <引用>` 起别名。REPL 在应用前解析成字面 ID
  并回显 `resolved: ...`，`export` / `item` 输出的永远是字面 ID。
- 事实引用按**引擎自己的依赖规则**（`ItemID.can_depend_on`）预检，指到父目标
  或兄弟分支时报 `CANNOT RESOLVE REFERENCE: ... cannot depend on`，
  而不是回放到一半才 `apply_method: illegal dependence`（§9.3 第 17 条）。
- `item NAME` 直接输出可粘贴的 `.pyhol` 条目（`theorem` + `fixes` +
  **保留 `'a::C` 的原文 `prop`** + `proof..qed`），写回文件不必手抄命题。
- `facts=[1, 2]`（逗号后带空格）现在与 `facts=[1,2]` 等价。

用法与匹配规则见 `repl-client.md` §4.1；测试在 `repl/tests/repl_test.py`
（`SemanticRefTest` / `ServerBindTest`）。

历史（已被上面的内建功能取代，`.cache` 里的脚本早就不在了）：
以前是 `.cache/drive_rel.py`（进程内 REPL + 语义 ID）、`.cache/add_thm.py`
（抽 proof 块追加定理）、`.cache/validate_one.py`（单理论验证，**仓库原有**，
不在 `.cache` 时见 `FOUNDATION_DEBT.md` 的说明）。

### 5.4 抽取证明块的注意点

从 REPL 输出里抓导出块**必须按行判断** `l.strip() == 'proof'` 与 `== 'qed'`。
用 `text.split('proof')` 会撞上 REPL 的 `no open goals -- proof complete` 那行（我踩过）。
现在不需要手写抽取器：`item NAME` 直接输出整段条目。

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
prop linorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶
     linorder_lt (less::'a ⇒ 'a ⇒ bool) ⟶ x <= x
```

即**注解 = 前提**，`'a` 的类型不变。每个类运算各贡献一条前提
（`preorder`/`order` 只有 `≤`，`linorder` 有 `≤` 与 `<`；Isabelle 的 `ord` 无法则，
贡献 0 条前提，只作标记）。**为什么 `<` 要单独一条**：holpy 的 `less` 与 `less_eq`
是**互相独立**的重载常量（nat 各自用递归定义），不像 Isabelle 的 `less` 由 `≤` 定义，
所以约束 `≤` 推不出 `<` 的任何性质，一条 `'a::linorder` 注解必须同时给出两者的法则。
于是 item 层以下（步进、重放、内核）完全不知道类；前提在**使用处**由实例定理消掉
（`nat_linorder`、`nat_linorder_lt`）。这条等价性来自 Isabelle 自己：Pure 内核没有类，
`OFCLASS` 只是 meta 层假设，类定律全是有条件假设。差别只在「谁来做实例解析」——
糖版是显式的，忠实类型类版交给 elaborator。

### 11.2 实现（约 150 行 + 测试）

| 位置 | 内容 |
|---|---|
| `syntax/parser.py` 文法 | `?typ_atom: "'" CNAME ("::" CNAME)? -> tvar`；transformer 丢掉注解，类型仍是 `'a` |
| `syntax/parser.py` 表 | `CLASSES`：**注册表**（初值为空，由库条目填充）。类的法则不在代码里：`library/order.pyhol` 用 `class` 条目声明「类名 → 若干 (谓词, 运算)」（见 §13.5） |
| `syntax/parser.py` 函数 | `class_constraints()`（收集 + 报错）、`class_premises()`（一条注册项 = 一条前提）、`with_class_premises()`、`add_class()` / `clear_classes()`（供 item 层与加载器调用） |
| `core/items.py` | `Axiom.parse`（`Theorem` 继承）里注入前提；`data` 是原始文本，所以 `'a::linorder` 留在源码里、导出回环保留 |
| `repl/repl.py` | `cmd_goal` 用同一条规则注入，所以 `var x 'a::linorder` + `goal x <= x` 与 item 的陈述一致 |
| `library/order.pyhol` | 新理论：`preorder`/`order`/`linorder`/`linorder_lt` 四个谓词、投影引理、`nat` 实例（`nat_linorder_lt` 由 `less_irrefl`/`lt_trans`/`lt_cases` 组成）、两条糖的端到端演示 |

`linorder_lt` 的法则 = 非自反 + 传递 + 三歧（`∀x.∀y. lt x y ∨ lt y x ∨ x = y`）；
下游 `<` 引理实际用到的派生引理也建在这一层：`linorder_lt_neq`（`lt x y ⟹ x ≠ y`）、
`linorder_lt_gt_of_not_lt`（`x ≠ y ⟹ ¬ lt x y ⟹ lt y x`，即 ordered_insert 的
else 分支要用的「既不等于也不小于就是大于」）。

### 11.3 边界（明确不做 / 留待增量 2）

- **datatype 参数上的约束**（`('a::linorder, 'b) tree`）暂不传播：holpy 的
  `datatype` 行只写参数名，没有 kind 注解。阶段 5 真需要时加一个 item 元数据
  + 传播（那时是「约束环境」，不是文本替换）。
- **定义（`def`/`fun`/`inductive`）只把注解当标记**：它们的方程对实例是均匀的
  （运算就是通用重载常量 `less_eq`/`less`），所以不注入前提；`fun tree_sorted ::
  ('a::linorder,'b) tree ⇒ bool` 这类签名照写即可。
- **不做忠实类型类**：`kernel/type.py` 的 `Type` 没有 sort；`kernel/theory.py:253`
  的 `get_overload_const_name` 明确要求实例类型是具体类型常量，所以「在类型变量上
  解析类运算」要改重载解析本身，再加超类闭包、重叠一致性、defaulting——2~5 天
  且动内核相邻代码，换来的只是 50 处的书写便利。
- **JSON/edit 面看到的是脱糖形态**：`.pyhol` 源码（和 `.pyhol` 回环）保留
  `'a::linorder`，而 `export_json`/`get_display` 给出的是去掉注解的 fixes +
  显式前提 `linorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶ linorder_lt (less::…) ⟶ ...`
  （两者语义相同，且不会二次注入——注解已经不在文本里了）。前端保存的文本因此是
  脱糖形态，这是可接受的正规形态。
- **实例解析暂不做自动化**：使用处手写 `rule <law> facts=[<约束事实>]`（约束事实
  来自注解或实例定理）。以后要自动化，加一张实例表让 solver 试即可，不动内核。

### 11.4 阶段 3 剩余（已于 §13 收尾）

**转写 auto2 陈述时的一个文法语限制**：holpy 的 `∀` 只吃一个绑定变量，
`∀x y z. P` 必须写成 `∀x. ∀y. ∀z. P`（`∃` 同理）；`library/order.pyhol` 的定义
里就是这么写的。auto2/Isabelle 原文里的多变量量词照抄会解析失败。

序谓词层已完整：`preorder`/`order`/`linorder`/`linorder_lt` + 层级与投影引理
+ `nat` 实例（20 条 VALID）。**`sorted`（≤ 版）要做**——它来自 Isabelle 的
List.thy，auto2 在 `Quicksort.thy`（4 处）、`LinkedList.thy`（4 处，指令式）、
`Rect_Intersect.thy`（区间序，1 处）里用；§8.1 说的「0 次」是 `insort`，
本条曾一度被误记成 sorted（2026-09-13 修正）。`strict_sorted` 已完成一半
（`library/lists_ex.pyhol`，对应 auto2 `Lists_Ex.thy`；该文件里依赖 Mapping_Str
的 `ordered_insert_pairs`/`remove_elt_pairs`/`map_of_alist_binary` 留到阶段 5，
`remove_elt_list` 只依赖 list/order，可归本阶段）。
实例还缺 `int`/`real`：`real` 只差 `real_le_trans`（UNPROVED）与几个 `<` 律；
`int` 整条序层都是 UNPROVED（该理论 184 条里也几乎全未证），属 P3 数系债。

以上各项（`strict_sorted_appendI`/`strict_sorted_distinct`/`ordered_insert` 一组/
`remove_elt_list` 一组/`sorted` 定义 + 基础引理）已在 **§13** 完成；
`int`/`real` 实例、三个 `_binary` 引理、`sorted` 的 sublist 刻画、以及混合
`<`/`≤` 的桥接引理仍然缺，边界见 §13.3。

## 12. 阶段 3：strict_sorted 层（2026-09-13 续轮，常驻 REPL）

### 12.1 交付物

| 位置 | 内容 | 验证 |
|---|---|---|
| `library/order.pyhol` | `linorder_lt` 谓词（非自反/传递/三歧）+ `linorder_lt_irrefl/trans/linear` + 派生 `linorder_lt_neq`、`linorder_lt_gt_of_not_lt` + 实例 `nat_linorder_lt` | VALID 20 / 0 非绿 |
| `syntax/parser.py` | `CLASSES` 改为「类名 → 若干 (谓词, 运算)」：`'a::linorder` 注入**两条**前提（`linorder less_eq` + `linorder_lt less`）；无公理的 `ord` 类 | 回归 349 → 见 §12.4（该表 2026-09-15 已搬进库，见 §13.5） |
| `library/logic.pyhol` | `disj_left_comm`（`A ∨ (B ∨ C) ⟷ B ∨ (A ∨ C)`） | VALID 92 / 0 非绿 |
| `library/set.pyhol` | `empty_union`、`insert_union`、`insert_comm`、`subset_union_left`、`subset_union_right`、`all_mem_elim` | VALID 79 / AXIOM 3 / 0 非绿 |
| `library/list.pyhol` | `set_append`、`member_set_append`、`member_set_append_left/right` | VALID 41 / 0 非绿 |
| `library/list.pyhol` | （补）`member_set_cons` | VALID 42 / 0 非绿 |
| `library/lists_ex.pyhol`（新） | `fun strict_sorted` + `strict_sorted_appendE1`、两个析构引理 `strict_sorted_append_head/tail`、`strict_sorted_appendE2` | VALID 4 / 0 非绿 |

`strict_sorted` 的定义照 auto2（`∀y. y ∈ set ys ⟶ x < y`），约束写成
`fixes xs :: 'a::linorder list`——注解注入三条前提（`linorder`、`linorder_lt`、
`linorder_lt_le`，见 §14），证明里用 `linorder_lt_*` / `linorder_lt_imp_le`。
`strict_sorted_appendE1`（33 步）与 `strict_sorted_appendE2`（36 步，auto2 的
`[forward]` 前缀-后缀性质）都已证成；`_head`/`_tail` 是把「`(x # xs) @ ys` 的
strict_sorted 拆开」固定下来的析构引理（见 §12.2 第 31 条）。

### 12.1.1 分支内命题去重（本轮最费时的一处）

`StableProofState` 按命题去重分配 sid（§3.8），于是**两个 `cases` 分支里如果
推导出同一条中间命题，它们共用同一个 sid，只对其中一个分支可达**——第二个分支
拿到的是"非法依赖"（`apply_method: illegal dependence`）。E2 的归纳步正好踩上：
两支都要先把 `strict_sorted ((x1 # xs) @ ys)` 展成
`(∀y. y ∈ set (xs@ys) ⟶ x1 < y) ∧ strict_sorted (xs @ ys)`，于是那一串中间命题
全被第一支占住。**对策（本轮采用）**：把两支各自需要的东西做成**不同命题**的
析构引理 `strict_sorted_append_head`/`_tail`，让两支从同一个假设出发各自推出
*互不相同* 的结论（head 支只要 `∀…`，tail 支只要 `strict_sorted (xs@ys)`），
分支内部再展开。这与 §4.3「按分支拆引理」是同一招，只是这里拆的是"同一个证明的
两个分支"。

另一条经验：**为某个目标 `goal=G` 派生的事实落在 G 的子树里**，`cases G` 之后
的两个分支看不到它们（可见的是 G 之前、同一层子证明里的事实，例如 `intro` 出来的
假设）。所以"进 cases 之前先 forward 出来当共同祖先"（repl-client §8.2 的建议）
要求那些 forward 的插入点在外层，而不是在被 split 的那个目标下面。

### 12.2 机制新发现（§8.5/§9.3/§10.2 的继续）

23. **`induct` 必须先作用在整条蕴含上**。auto2 那类 `strict_sorted (xs@ys) ⟹ …`
    的引理，若先 `← intro` 把假设变成事实，`induct` 只看到结论，归纳假设退化成
    「结论 ⇒ 结论」而完全无用。正确顺序：`← induct xs list_induct goal=0`（此时
    目标还是整条蕴含，ih 带假设），再 `← intro goal=1` / `goal=2` 进入两个分支。
24. **`rule <thm>` 匹配的是定理的结论**，所以对上条那种蕴含式引理，用之前要先把
    目标 `intro` 成结论形态，再用 `facts=[<两个类前提…>, <被 intro 出的假设>]`。
25. **`rewrite <iff 定理>` 作用在目标上会产生「转换子目标」**：被改写子项的那条
    等式会成为新的目标（例如 `union_comm` 把 `set ys = {} Un set ys` 变成
    `set ys = set ys Un {}`），要再用同一条定理或另一条引理关掉。同理
    `disj_assoc_eq`/`insert_union` 这类「恰好左右两边互为实例」的情形会自动关门。
26. **`loc` 路径要按项树算**：`A ⟷ B` 的左/右操作数是 `0.1` / `1`，而 `f a` 的参数
    是 `1`——所以 `z ∈ insert x A ∪ B` 里那个 `z ∈ insert x A` 的路径是
    `0.1.0.1`（`0.1` 是这个成员关系的左操作数 `z`、`z ∈ insert x A ∪ B` 整体在
    `0.1`，「集合」是 `member z` 的参数）。`insert_comm`/`insert_union` 全靠
    `loc` 精准落点。
27. **对事实做重写时，含 `intro`/`induct` 绑定变量的事实会被 `has_rewrite` 拒绝**
    （`InvalidDerivationException: rewrite_fact using X`，§10.2 第 1 条的实践版）。
    两条出路：(a) 改用**等式事实** + `→ rewrite target=fact source=prev sym=…`；
    (b) 不用重写，改用**投影/消去引理**（如新增的 `all_mem_elim`）。
28. **`all_mem_elim`**（set.pyhol）：`(∀z. z ∈ B ⟶ P z) ⟹ y ∈ B ⟹ P y`，
    把「有界全称 + 成员事实」的一步推理固定成一条可 `rule` 的定理——
    `strict_sorted` 那类证明里每处「头元素小于尾部每个元素」都只用一步。
29. **推导结果与目标同命题时 `forward` 不新增条目**，此时关门要用
    `← apply_prev goal=G facts=[<∀/蕴含事实>, <参数事实>]`（§8.5 第 10 条的确认），
    或者先 `→ inst` 出蕴含式再 `apply_prev`。
30. **`rewrite … sym=true` 是「等式反向用」**：`strict_sorted_def_2`（定义）要用
    `sym=false` 展开；`append_def_1`（`[]@xs = xs`）反向用才是 `xs → []@xs`。
31. **`forward <thm> facts=[…]` 要按定理的前提顺序把前提全给上**：带类前提的
    引理（如 `strict_sorted_append_tail`）若只给 `strict_sorted` 假设，matcher
    会拿第一条前提 `linorder less_eq` 去比，报 `linorder … --- strict_sorted …`。
    正确写法 `facts=[<P1>, <P2>, <假设>]`（`param_*` 可给可不给，给了也对）。
32. **`forward` 推出的命题与目标相同时会直接关门**（本轮 `strict_sorted_append_head`
    就是 `conjD1` 一步关门），不需要再 `apply_prev`；反之若目标没关（见第 29 条
    的 `all_mem_elim` 场景），才要 `apply_prev`。

### 12.3 阶段 3 剩余（已于 §13 完成，保留原文以对照）

`library/lists_ex.pyhol` 里还缺 auto2 `Lists_Ex.thy` 的其余陈述：
`strict_sorted_appendI`（`[backward]`）、`strict_sorted_distinct`（需要 cons 形式的
析构引理 + `linorder_lt_irrefl` + `negE_gen`，配方已明确）、`ordered_insert` 与
`ordered_insert_set`（要 `insert_comm`）/`ordered_insert_sorted`（要
`linorder_lt_gt_of_not_lt`）、`remove_elt_list` 一组（`_set`/`_sorted`/`_idem`，
BST 删除要用）。三个 `_binary` 引理（`ordered_insert_binary`、
`remove_elt_list_binary`、`ordered_insert_pairs_binary`）**在 Lists_Ex 之外无人引用**
（2026-09-13 实测），是 auto2 自己二分路径用的，属可选的收尾工作。

`sorted`（≤ 版）也要在本阶段补：定义 + Quicksort 用到的引理（
`sorted (sublist l (r+1) (quicksort xs l r))` 那类陈述要能用，
说明至少需要 `sorted` 对 `sublist`/`append` 的刻画）。它建在 `linorder`（≤）上，
与 `strict_sorted` 平行，可复用本轮的全套配方。
`remove_elt_list` 一组（BST 的删除用）与依赖 Mapping_Str 的
`ordered_insert_pairs`/`remove_elt_pairs`/`map_of_alist_binary` 归阶段 5。

## 13. 阶段 3 收尾（2026-09-14，常驻 REPL）

### 13.1 交付物

| 位置 | 内容 | 验证 |
|---|---|---|
| `library/list.pyhol` | `mem_set_cons_self`（`x ∈ set (x # xs)`）、`mem_set_cons_weak`（`z ∈ set xs ⟹ z ∈ set (x # xs)`） | VALID 44 / 0 非绿 |
| `library/set.pyhol` | `mem_insert_self`（`x ∈ insert x A`）、`insert_idem`（`insert x (insert x A) = insert x A`） | VALID 81 / AXIOM 3 / 0 非绿 |
| `library/lists_ex.pyhol` | `strict_sorted_cons_head`/`_cons_tail`（cons 析构）、`strict_sorted_appendI`（backward）、`strict_sorted_distinct` | VALID 18 / 0 非绿 |
| 同上 | `ordered_insert` 定义（`if x = y then … else if x < y … else …`）+ `ordered_insert_set`、`ordered_insert_sorted` | 同上 |
| 同上 | `remove_elt_list` 定义 + `remove_elt_list_mem`、`remove_elt_list_set`、`remove_elt_list_sorted`、`remove_elt_idem` | 同上 |
| 同上 | `sorted`（≤ 版）定义 + `sorted_cons_head`/`_cons_tail`、`sorted_appendI`、`sorted_appendE1` | 同上 |

`library/tests/lists_ex_test.py` 从 5 例扩到 10 例（4 个 nat 使用点主动用例 +
2 个被动用例）；`list_test.py`/`set_test.py` 的名字表同步。

### 13.2 本轮新发现的机制

33. **`rewrite` 不带 `loc` 时改写目标里*所有*匹配出现**，不是只看最外层一次。
    基例里 `insert x (set []) = {x} Un set []` 一条 `set_def_1` 就把两处
    `set []` 同时换成 `{}`；`insert_comm` 一步把等式两边同时交换（因此要
    `loc=0.1` 只动左边）。与 §8.5 第 3 条（rewrite 抓最外层匹配）合起来就是
    完整语义：**先定位（最外层优先），再替换全部同形项**。
34. **目标命题与作用域内某条定理相同时会被自动关闭**。`remove_elt_list_set`
    的证明在两次重写后正好得到 `remove_elt_list_mem` 的命题，那一步直接
    "no new items; goal closed"，导出里留下一条 `→ forward remove_elt_list_mem …`
    作为关门行的记录。库回放（`validate_one`）重现该行为，不是 REPL 特例。
35. **`intro` 后的目标不总是保持同一个稳定 ID**：同一分支里第二次 `intro`
    会遇到与已出现命题合并的情况，目标会换 sid。**每步之后看 `all`，
    用最后一条 `GOAL` 的编号**，不要按"上一步 +1"推算。
36. **`force_disj_true1`/`_true2` 只吃一种朝向**：`true1 : A | B ⟹ ~B ⟹ A`
    （消去第二个析取项），`true2 : A | ~B ⟹ B ⟹ A`（消去取反的第二个）。
    要消去**第一个**析取项时先 `→ rewrite disj_comm … target=fact` 把
    `A | B` 变成 `B | A`，再用 `true1`（appendI/E2 与 `remove_elt_list_mem` 都这么写）。
37. **`false` 常量引理的左右形式要看清**：`conj_false_left` 是 `P & false`、
    `conj_false_right` 是 `false & P`（`conj_true_left/right` 同理）。写反了
    报的是 `rewrite: unable to apply theorem`，不提示左右之别——查
    `thm <名字>` 再写。
38. **`A - B` 在集合上曾经是「静默的通用常量」**：解析器把 `A - B` 解析成
    重载常量 `minus`（`syntax/parser.py` 的 `minus` 方法），而在加实例之前
    `'a set` 上没有 `minus` 的方程，于是 `A - B` 能通过类型检查、打印出来也
    和集合差一模一样，但它是**未解释常量**（`← refl` 关不掉 `A - B = diff A B`，
    `rewrite member_diff` 也打不上）。集合差因此一度只有前缀写法 `diff A B`。
    §13.4 给 `minus` 加上了集合实例，现在 `set ys - {x}` 可以照 auto2 原文写。
39. **定义里的类型注解只是标记**（§11.3 的实践确认）：`fun ordered_insert ::
    'a ⇒ 'a list ⇒ 'a list` 的函数体里可以出现 `x < y`，此时 `<` 解析为通用
    重载常量（`strict_sorted`/`sorted` 同理），不需要也不接受前提注入。
40. **`remove_elt_list` 的集合刻画走「先证成员刻画、再对集合等式取 `set_equal_iff`」**：
    归纳步里 `if` 分支与 `delete`/`diff` 的交互（`insert x A - {x} = A - {x}` 之类）
    如果直接对集合等式归纳，命题级推理会翻倍；先在成员层面归纳（`remove_elt_list_mem`），
    集合等式就退化成 4 步 `set_equal_iff` + 成员引理重写。

### 13.3 阶段 3 之后仍缺的部分

- **`int`/`real` 实例**：**已完成（2026-09-14）**，见本节末尾"int/real 实例"
  一段；`int` 其余 181 条（算术/除法/幂等）仍是 P3 数系债，与本尾巴无关。
- **三个 `_binary` 引理**与 `ordered_insert_pairs`/`remove_elt_pairs`/
  `map_of_alist_binary`：前者 Lists_Ex 之外无人引用（可选），后者依赖
  Mapping_Str，归阶段 5。**本轮试做 `ordered_insert_binary`，被机制挡住**，
  见本节末尾"`_binary` 引理为什么没做"。
- **`sorted` 与 `sublist`/`append` 的 Quicksort 专用刻画**（`sorted (sublist l r
  (quicksort xs l r))` 那类）：留到阶段 5 与 Quicksort 一起做，那里才知道
  真正需要对 `sublist` 的哪几条重写。
- **混合 `<` 与 `≤` 的桥接引理**（Isabelle 的 `strict_sorted_imp_sorted`）：
  **已完成（2026-09-15，见 §14.6）：`class linorder` 现在带 `linorder_lt_le`。**
  下面保留"为什么缺了它就不可证"的反例与两条修法，供参考：
  本移植的 `linorder`/`linorder_lt` 是**互相独立**的谓词，缺
  `lt x y ⟶ le x y` 这条类公理，所以这类引理在抽象层面**不可证**。
  这不是猜测，有机器验证过的反例（2026-09-14，REPL 内证完，未落盘）：

  ```
  linorder (less_eq::nat ⇒ nat ⇒ bool) & linorder_lt (λa. λb. b < a)
    & (λa. λb. b < a) 1 0            -- 即 0 < 1
    & ¬(1 ≤ 0)
  ```

  即：把第二条前提里的 `less` 解释成**反向严格序**，两条类谓词都成立，而桥接律
  在该点不成立（`lt 1 0` 真、`le 1 0` 假）。取 `l = [1, 0]`，展开
  `strict_sorted`/`sorted` 的递归即得「前件真、后件假」，故抽象陈述不成立。
  关键中间引理 `linorder_lt lt ⟹ linorder_lt (λa. λb. lt b a)`（反向严格序仍是
  `linorder_lt`）也是在 REPL 里证过的一步，说明反例不是构造错误。

  两条修法（都走同一套糖机制）：
  1. **加第三条前提**：在 `library/order.pyhol` 的 `class linorder` 声明里增一条
     `linorder_lt_le (less_eq :: …, less :: …)`（**不是**改 `syntax/parser.py`，
     类数据已归库，见 §13.5），配
     `def linorder_lt_le le lt ⟷ (∀x y. lt x y ⟶ le x y)` 与实例定理
     （nat 用 `lt_imp_le`）。`linorder_lt_*` 现有引理签名不动。
     代价：所有 `'a::linorder` 陈述多一条前提；现有 14 条 lists_ex 陈述的证明里
     每处「逐条剥 IH 的类前提」要多剥一次（结构性改动，不是编号问题），
     所以要先重导出那批证明。
  2. **把桥接律并入 `linorder_lt`**（`linorder_lt le lt`，把 `≤` 一起约束）——
     语义上更贴近 Isabelle 的类（`<` 与 `≤` 本是一对），但 `order.pyhol` 里
     `linorder_lt_irrefl/trans/linear/neq/gt_of_not_lt` 与 `nat_linorder_lt`
     的签名全要改。

  注意实例层面不缺这条：nat 有 `lt_imp_le : ?m < ?n ⟶ ?m ≤ ?n`（反方向是
  `less_lesseqI : ?m ≤ ?n ⟶ ?(m = n) ⟶ ?m < ?n`），所以**按实例**证
  `strict_sorted_imp_sorted` 是能做到的，缺的只是抽象层的类公理。
  两条修法都属于「改类理论」，动之前先报备。

#### int/real 实例（2026-09-14 完成）

- **先要让这两个理论 import `order`**：类注册表只认本理论已载入的 `class` 条目，
  在此之前 `library/real.pyhol`/`library/int.pyhol` 里**连 `'a::linorder` 记法都
  解析不了**。改成 `real: imports rat, order`、`int: imports list, order`
  （`order` 只依赖 `nat`，不成环）。
- `real`/`int` 的序常量在这里是**未解释常量**（`type real`/`type int` 抽象；real 的
  `<` 还是 `x < y ⟷ ¬(y ≤ x)` 的定义），所以这一层只能走 z3 oracle——`LIBRARY_ORACLES`
  正是为 int/real/hoare 放行 z3 的，real 原有的序层（132 处 z3）就是这么证的。
  所有证明先在常驻 REPL 里证完再写入文件。
- `library/real.pyhol`：补上 12 条序引理的证明（`real_le_trans`、`real_le_ladd_imp`、
  `real_le_mul`、`real_ge_add`、`real_ge_mul`、`real_ge_divide`、`real_gt_add`、
  `real_gt_mul`、`real_lt_neq`、`real_gt_neq`、`real_gt_to_neq`、`real_lt_le`），
  新增 5 条实例 `real_preorder`/`real_order`/`real_linorder`/`real_linorder_lt`/
  `real_linorder_lt_le`（每条 2–4 步：展开类谓词定义后交给 z3），外加端到端用例
  `real_le_refl_via_linorder`（照 `nat_le_refl` 的写法）。
- `library/int.pyhol`：新增 8 条序引理（`int_le_refl`/`int_le_antisym`/`int_le_trans`/
  `int_le_total`/`int_lt_irrefl`/`int_lt_trans`/`int_lt_cases`/`int_lt_le`）、5 条实例
  `int_preorder` … `int_linorder_lt_le` 与用例 `int_le_refl_via_linorder`；int 的
  `<`/`≤` 同样被 z3 映射到 Int 的序，故连定义都不用展开。
- 验证：`validate_one real --force` → VALID 110 / DEP_FAILED 120 / UNPROVED 110
  （改前 VALID 85 / UNPROVED 122 / DEP_FAILED 127——**证掉序层还顺带解开了一批依赖
  它的 DEP_FAILED 条目**）；`validate_one int --force` → VALID 17 / UNPROVED 181
  （改前 VALID 3；181 条全是本尾巴之外的老债，未动）。
- **`real_inv_0`/`real_mul_linv` 故意保持 UNPROVED**：它们在 REPL 里 z3 一步就过，
  但库回放时这两条 item 排在 `real_inverse_divide`（约 1528 行）之前，而
  `solvers/z3wrapper.py:norm_term` 只在 `has_theorem` 成立时才用那条定理改写，
  oracle 看到不同的规范形就失败。**这是 REPL 与库回放的真实分歧**：z3 的可用改写
  规则取决于"此刻理论里有什么"，所以带 z3 的证明必须在**该 item 在文件中的位置**
  上验证，不能只在整理论已加载的 REPL 会话里验证。要证这两条得把它们移到
  `real_inverse_divide` 之后，或让规范化不依赖可选上下文。

#### `_binary` 引理为什么没做（2026-09-14 实测，结论：需要按分支拆引理）

`ordered_insert_binary` 的**基例**已在 REPL 里证完（外层 `cases "x < a"` + 分支内
`cases "x = a"`，靠 `linorder_lt_neq`/`_irrefl`/`_gt_of_not_lt` 与 `if_P`/`if_not_P`），
步进例卡在一个**引擎级限制**上，不是证明难度：

- `method/stable_state.py` 的 sid 表是 **Thm → sid**（按命题去重）。某命题一旦在证明里
  出现过（哪怕是兄弟分支 `forward` 推出来的），**之后把它当 `intro` 假设引入时不再产生
  独立的 fact 条目**——它只存在于 goal 的 hyps 里。
- 于是后面的分支里 `← rewrite if_P facts=[<该命题>]` 必然失败：字面 sid 报
  `apply_method: illegal dependence`；引号命题会被解析到别处（实测 `facts=["x < a"]`
  解析成基例分支的 `#[16]`，整步变成空转、只留下一条无用条目）。
- `ordered_insert_binary` 的步进例恰好要求：展开 LHS 的 `ordered_insert` if 链要
  `x`/`x1` 的比较，RHS 的 if 链又要 `x`/`a` 的比较——**同一个命题会在多个分支里既被
  推出又被假设**，正是 §12.1.1 记录的那个坑。
- 出路是按 §12.1.1 的办法把引理**按分支拆开**（`x < a`/`a < x`/`x = a` 各一条，再一条
  合并），使每条子引理内部的假设命题唯一；代价约 4 条引理 + 各自归纳（≈130 步 REPL
  步进），对一个"Lists_Ex 之外无人引用"的可选引理不成比例。本轮**没有落盘**：REPL 里
  的基例半成品既没写进 `.pyhol`，也没提交。


### 13.4 给 `-` 加集合实例（2026-09-14，用户选定方案 A）

holpy 的算术算子是**重载常量**：`library/nat.pyhol` 声明
`const minus :: 'a ⇒ 'a ⇒ 'a overloaded`（`plus`/`times`/`power`/`less`/`less_eq`/
`zero`/`one`/`of_nat` 同理），实例就是一条**写在实例类型上的普通定义**
（`fun plus :: nat ⇒ nat ⇒ nat`、`def one :: nat = 1 = Suc 0`、`def of_nat :: nat ⇒ nat`）。
item 层给实例算一个链接名 `cname = <类型构造子>_<算子>`（`nat_plus`、`int_minus`），
定义定理叫 `<cname>_def`。

项里**存的是通用名**（实测 `0 + Suc 0` 的常量名就是 `plus`，`has_term_sig('nat_plus')`
为 False）——holpy 不是「每个实例一个独立常量」，而是**一个通用常量 + 各实例上的方程**，
重写时按同名同类型匹配。所以给集合差加实例只需要一条：

```
def minus :: 'a set ⇒ 'a set ⇒ 'a set = A - B = diff A B      -- library/set.pyhol
```

几点确认（都是实测，不是推断）：

- 装载路径（`basic._apply_item`，会跑 defcheck）接受这条 item：它是对**已存在**常量
  在更窄类型上的定义，和 `def one :: nat` 是同一机制；注册出的定理是
  `?A - ?B = diff ?A ?B`。
- 定理名是 **`fun_minus_def`**（不是 `set_minus_def`）：`set` 是类型缩写
  （`library/set.pyhol` 的 `typeabbrev set 'a = 'a ⇒ bool`），类型构造子叫 `fun`，
  `get_overload_const_name` 因此拼出 `fun_minus`。内核/打印都不受影响，只是名字别扭。
- `def` 条目**不进状态表**（`core/verify.py` 只对 `thm`/`thm.ax` 记状态），所以
  set 的 `AXIOM 3` 不变（重验：VALID 81 / AXIOM 3 / 0 非绿）。
- **边界**：实例要求类型是已知的具体构造子（`'a set` = `'a ⇒ bool` ✓、`'a list` ✓）；
  **裸类型变量没有实例**，`x - y`（x,y :: 'a）仍是未解释的 `minus`——这与
  §11.3「类型变量上解析类运算」是同一条边界的两个面，也正是类型类糖要把
  `'a::linorder` 降级成前提 `linorder (less_eq::…)` 的原因。
- 用法上 `diff` 仍是原语：`← rewrite fun_minus_def` 把 `-` 展开成 `diff`（**故意不加
  `[hint_rewrite]`**，避免 `simp` 自动展开；要展开就显式写一行）。

落地效果：`remove_elt_list_set` 现在照 auto2 原文写成
`set (remove_elt_list x ys) = set ys - {x}`（证明只多一行 `rewrite fun_minus_def`），
`remove_elt_list_sorted` 里用到它的那一步同样多一行。新增陈述可以直接写
`A - B`，转写 auto2 时不必再改写。测试见 `library/tests/set_test.py`
（`-` 可用 + 裸类型变量上实例不生效两条）。

## 14. 领域数据搬出核心：`class` 条目类型（2026-09-15）

### 14.1 动机与规则

规则（用户 2026-09-15 定）：**核心（`kernel/` + `syntax/`）只准通用；领域扩展可以随便
硬编码。** 判据：改一条库法则/一个记法，只该动 `.pyhol`，不该动 `.py`。

按这条规则，`CLASSES`（类名 → 法则）当初写成 `syntax/parser.py` 里的 Python 常量就是
违例：数据的归属地是库（谓词住在 `library/order.pyhol`），映射却锁在核心代码里。

### 14.2 做法（照 `typeabbrev` 的现成模式）

| 位置 | 内容 |
|---|---|
| 语法 | 新条目 `class <name> = <pred> (<op> :: <type>, ...), ...`；续行按缩进（同 `datatype`），空体 = 无法则的类（`ord`） |
| `syntax/pyhol.py` | `_parse_class` / `_export_class` / 分派 + 文档行 |
| `syntax/parser.py` | `CLASSES` 变**注册表**（初值空）；`add_class()` / `clear_classes()`；`parse_class_body()`、`inst_class_type()`；`class_premises` 一条注册项生成**一条**前提（谓词应用到该项列出的全部运算），并把声明里的首个类型变量改写成被注解变量 |
| `core/items.py` | `Class` 条目：解析并注册，`get_extension()` 返回空（parser 侧状态，与 `typeabbrev` 同类） |
| `core/basic.py` | `_apply_item` 重放时重新注册 `class`；`load_theory` 开头 `clear_classes()`；**导入循环改用 `_apply_item`**（原来是裸 `unchecked_extend`，导入侧的 parser 状态——`typeabbrev` 与 `class`——不会登记，冷启动解析下游文件就会缺） |
| `library/order.pyhol` | 四个声明：`class ord =`、`class preorder = …`、`class order = …`、`class linorder = linorder (less_eq :: …), linorder_lt (less :: …)` |
| `syntax/tests/class_sugar_test.py` | 17 例：数据来源改为**装载库**（不再手造表），新增声明回环、多运算谓词、变量改写、畸形声明报错等 |

### 14.3 验证（这一步必须逐字等价）

改动前把 `order`/`lists_ex` 全部条目的解析命题存了一份快照，重构后逐条比对：
**49 条全部逐字相同**；`validate_one order --force` → VALID 22 / 0 非绿；
`validate_one lists_ex --force` → VALID 18 / 0 非绿。

### 14.4 两个工具层面的缺陷（2026-09-14 已修）

1. **`core/incremental.py: imports_epoch` 不含上游内容哈希**：它只把导入图的名字
   递归拼起来，所以**上游文件改了它也不变**，与它自己的 docstring（"a change to any
   upstream file changes this value"）矛盾。后果：只跑 `.cache/validate_one.py
   <下游>`（不带 `--force`）会拿到**假绿**——本轮把 `CLASSES` 搬走时，`lists_ex`
   的 14 条其实已经全挂，非 force 的验证仍然报 `VALID 18 / 非绿 0`，`--force`
   才暴露。全库 `validate_incremental` 那条路有「上游判定变了就下推」的补偿，
   但单文件入口没有。
   **已修**：`imports_epoch` 现在把每个 import 的 `source_hash` 连同名字、嵌套
   epoch 一起拼进指纹（`or ''` 兜住尚未载入内容的 metadata-only 条目）。代价是
   全库缓存一次性失效（旧指纹与新指纹天然不同），之后恢复正常。测试
   `test_incremental_validate.py::ImportsEpochSourceTest` 两例：上游 source_hash
   一变，下游 epoch 必须变、下游 `validate_theory_info` 必须报 `reused=False`；
   原有的 `testImportsEpochExcludesOwnSource`（自身 hash 不动 epoch）保持通过。
2. **`new_ids` 只在数量相等时生效**（`method/stable_state.py`
   `if len(ns.new_ids) == len(new_items)`，`apply_method_dict` 与
   `apply_method_new` 两处）：给一类陈述多注入一条前提后，旧注解的数量与新条目数
   不等，覆盖被整体跳过、退回自动编号——不只影响「加前提」，任何一步新建条目数与
   注解不等都会让该步（以及后续步骤引用的字面 ID）静默错位。
   **已修**：新的 `StableProofState._apply_new_ids` **按创建顺序对齐**（第 i 个新建
   条目拿注解的第 i 个 ID），注解没覆盖到的条目保留自动 ID（若已被占用则顺延到一个
   全新 ID，保证不会有两条命题共用一个 ID）。测试
   `method/tests/method_test.py::NewIdsAlignmentTest` 四例：短注解按序生效、长注解
   取前缀、冲突条目让位、数量相等时行为不变。
   注意：这修的是「不该整体丢弃」，**不是**「加前提后旧注解自动正确」——类前提是
   每个分支各一份，加一条前提仍然要按 §14.6 重证（本修复没有也不能取代它）。

   **已知边界（2026-09-17 实测）**：按创建顺序对齐只在一种情形会挪位——注解条数
   多于实建条目数，且被记下的那一条**已由本步之外的条目持有**。`logic.conj_iff_left`
   的 `intro goal=12` 就是：假设 `P` 已在作用域（`rule conjD1 goal=14` 派生的那条，
   #15），本步只新建 `P ∧ Q` 一个条目，而注解记着 `[15, 16]`；位置对齐把 `P ∧ Q`
   钉到 #15，后一步 `rule conjI goal=16` 就解析不到（症状是被点名的那一步失败，
   肇事步在它前面）。
   试过把规则改成「跳过已被本步未创建条目占用的记录 ID」，单测通过，但 `logic`
   从 92 VALID 掉到 **82 VALID / 10 非绿**——库里大量证明依赖位置对齐的这种补偿，
   所以**保留现行为**。这类过期注解按数据问题改正（`logic.pyhol` 那三条已按引擎
   真实导出改，见提交 `8c87294a`），改完 `logic` 92 VALID / 0 非绿。

### 14.5（已完成，见 §14.6）

`def linorder_lt_le`、定律 `linorder_lt_imp_le`、实例 `nat_linorder_lt_le` 先作为
独立条目写进 `library/order.pyhol` 并验证；随后把它挂进 `class linorder` 的声明，
14 条 `lists_ex` 陈述与 `order` 的端到端演示在 REPL 里重证——做法、代价与踩到的坑
见 §14.6。

### 14.6 相容律挂上类（2026-09-15，REPL 重证）

`library/order.pyhol` 的 `class linorder` 现在带第三条法则
`linorder_lt_le (less_eq :: …, less :: …)`，于是每条 `'a::linorder` 陈述的命题多一条前提，
`strict_sorted` / `sorted` 混用 `<` 与 `<=` 的桥接（`linorder_lt_imp_le`）在抽象层可用。

代价与做法（都按 AGENTS §4：**证明只用常驻 REPL**）：

- 受影响的 14 条 `lists_ex` 陈述 + `order` 里那条端到端演示 `linorder_le_refl`，
  全部在 REPL 里重证后 `item` 导出、整段替换回文件。重证的实质变化是三处：
  1. 类前提块多一条（每个**分支**各有一份，见下）；
  2. 消费类前提的 `rule`/`forward`（如 `facts=[3,4,10]`）要多喂那条事实
     （`facts=[3,4,5,11]`）；
  3. 「逐条剥 IH 类前提」的证明要多剥一步（`facts=[<imp>, 4]` 之后再
     `facts=[<imp'>, 5]`），此后编号再 +1。
- **不要试图用脚本做全局编号平移**：类前提是**每个分支各自引入一份**（同一命题在
  不同分支有不同 sid，只有引擎的解析会挑分支内那份），所以不存在"一个映射值"；
  而且 `method/stable_state.py` 的 `new_ids` 覆盖要求「注解条数 == 新建条目数」，
  多一条前提后旧注解整体失效。要么按创建顺序按段偏移，要么（本轮做法）重证。
- 踩过的坑：`item NAME` 输出的是**当前证明**的名字为 `NAME` 的条目——如果会话当前
  停在别的证明上，它会把那条证明写成 `NAME`。导出后要立刻核对 `prop` 行再落盘。
- 用语义引用（`goal=@`、`facts=["<打印出来的命题>"]`）可以完全绕开编号问题，
  重证时比手算 sid 稳得多（`ordered_insert_sorted` 的第二个分支就是这么过的）。

验证：`validate_one order --force` → VALID 22 / 0 非绿；
`validate_one lists_ex --force` → VALID 18 / 0 非绿（两边都是强制重放）。

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




## 审查结论（只查不改，未动任何实现代码）

**唯一落盘的东西**：`.cache/deadcode_scan.py`（gitignore 内的死代码扫描脚本，临时工具，不算项目代码）。没有修改、没有修复、没有跑测试。

---

# 一、严重：可信度/可靠性层面

| # | 位置 | 问题 |
|---|---|---|
| 1 | `core/macro/z3.py:44-56` | **`z3` 宏在求解器不可用时照样"证明"命题**。`eval` 只在 `backend.z3_loaded` 为真时调求解器；为假时仅 `print("Warning: Z3 is not installed")`，然后无条件 `return oracle_thm(self.name, args, ...)` —— 把目标当成 oracle 假设收下。而 `COMPUTATION_ORACLES`（`core/verify.py:74`）默认放行 `'z3'`，`backend.check_z3` 默认 `False`（`core/macro/z3.py:28`）。即：未安装 z3／未加载 `solvers/z3wrapper` 时，`z3` 步仍能通过校验。 |
| 2 | `core/basic.py:410-422` | `fungen.expand_item` 抛**任何**异常都被吞掉（只有 `PYHOL_FUNGEN_DEBUG=1` 才重抛），然后退回公理化路径。生成器内部 bug（AttributeError/TypeError 之类）会被静默降级成"方程变公理"，只在状态表里显示 AXIOM。 |
| 3 | `core/defcheck.py:368` | `if name == 'state':` —— 构造子投影函数的生成**只对硬编码类型名 `state` 生效**（注释说是为避免与归纳规则里的同名自由变量冲突）。换任何别的 datatype 名字都拿不到投影。 |
| 4 | `core/basic.py:386` | 生成器的"用户已自行声明过的定理名"是用**正则扫源码文本**得到的：`re.findall(r'^theorem\s+(\S+)', source_text)`。非结构化、对缩进/注释/条目形式敏感。 |
| 5 | `syntax/infertype.py:270-334` | 类型回填靠**给 Term 对象注入属性、把 `t.T` / `t.var_T` 置 None 再恢复**：`t.backupT`、`t.print_type = True`、`hasattr(t,'print_type')` 当状态位。恢复不在 `try/finally` 里 —— 中途抛异常会留下被改成 `None` 的项（项对象是共享的）。另有魔法上限 `for i in range(100)` + `assert i != 99`。 |
| 6 | `tactic/steps.py:103-107` | `_backward_rule` 里 `As, _ = th.prop.subst_norm(inst).strip_implies()` 后 `if len(goal.assums)>0: As = As[:-goal_Alen]` —— **按计数从末尾裁掉前提**，不与 goal 实际假设做匹配。前提顺序一变就裁错。 |

# 二、特判 / 硬编码（按样例形状写死）

- **互递归和类型编码**：`core/fungen.py:4113-4117` `_SUM_TY='either'`、`_SUM_CONSTRS=('Left','Right')` 写死库文件名与构造子名；`:4253` 用 `1 if side == _SUM_CONSTRS[0] else 2` 的索引魔法取 `_def_1/_def_2`。
- **析构子命名表**：`core/datgen.py:385-391` `_LIB_DESTRUCTORS`（`('nat','Suc',0)→('Pre','Pre_def_2')`、`list/cons→hd/tl`、`prod/Pair→fst/snd`）；另有 `core/fungen.py:147-161` 同一套写死（该函数见 §四，是死代码）。
- **度量引擎纯 nat**：`core/measure.py:89-110` `ARITH`/`CLOSING_LEMMAS`、`:631-640` `_PLUS_RULES/_TIMES_RULES/_MINUS_RULES` 全是 nat 定理名；`:135/140/363/372/623` 写死 `'Suc'/'plus'/'times'/'minus'/'Pre'`。文档也承认"每一步都是 nat 的引理"。`core/fungen.py:913` `measure.Measure(pos, arg_types, 'nat')` 写死 kind。
- **用 nat 定理名当生成闸门**：`core/datgen.py:702` `SIZE_LESS_DEPS = ['add_1_left','less_Suc_lesseq','lesseq_refl']`，`core/basic.py:473` 用它判断"size 族现在能不能生成"。
- **方法方向表**：`method/stable_state.py:33-53` `_SKIP_RULES`/`BACKWARD`/`FORWARD`/`_STRUCTURAL_METHODS` 硬编码方法名集合；`:77-81` 逻辑是"**不在 FORWARD 里就算 backward**"，所以任何新注册的 forward-only 方法会被默认判错方向。
- **程序验证编译器**：`imperative/imp_compile.py:341` 类型只认 `nat`/`nat[N]`/`ref`；`:411` `if e.name == 's'`（写死堆伪变量名）；`:480` `if e.fname == 'll'` 特判；`:841` 所有参数类型写死 `'nat'`。
- **打印层**：`syntax/pprint.py:230/256/262` 写死 `'prod'` 的二元组括号规则。
- **启发式上限**：`core/auto.py:190` `max_depth=6`、`core/search.py:54` `max_depth=6`、`syntax/pprint.py` 若干，`syntax/infertype.py:293` 100 轮。

# 三、静默失败（宽 except / 吞异常）

- `core/basic.py:412`（§一.2）、`core/basic.py:476/488`（size 族生成失败 → `derived=None` 直接跳过）。
- `core/datgen.py:568 / 613 / 630 / 723`：失败即 `return False/None`，无对外信号。
- `method/stable_state.py:343-346 / 394-396`：`apply_method_dict`（非 strict）和 `apply_method_raw` 捕获**一切**异常后返回 `False`/`None`，**原因被丢弃**；`:720 / 732` 搜索收集时同样吞掉。
- `method/methods/core.py:355-366`：用 `except AssertionError: pass` 把"该 gap 不是平凡的"当控制流。
- `core/macro/simp.py:56 / 64 / 68`：宽 `except Exception: continue`。
- **系统性**：全仓 hundreds of `assert` 同时承担输入校验和控制流（如 `method/methods/core.py:376`、`tactic/steps.py` 各处）；`python -O` 会直接改变语义（含 §一.6 那处裁剪的邻接断言）。

# 四、死代码（我已逐条在整仓核实引用次数）

**同文件重复定义、前一份被遮蔽（铁死）**，全在 `core/fungen.py`：
- `destructor` :147 与 :2207 重复 → **:147 那份写死 `Suc`/`cons` 的版本是死代码**
- `_typenames` :1349 与 :1441 重复 → :1349 死
- `_vars_dict` :1353 与 :1445 重复 → **两份都零引用**

**全仓零引用（只出现在自己的 def 行）**：`core/fungen.py` `plain_env:305`；`core/datgen.py` `_destructor_term:417`、`_printable_application:556`；`core/fungen.py` `_pattern_vars:1306`；`core/search.py` `lookup_net:166`；`core/auto.py` `solve_rules:237`、`cache_stats:438`、`clear_cache:441`；`core/basic.py` `is_cache_valid:212`、`clear_statuses:126`、`get_all_errors:140`、`user_dir:48`；`core/logic.py` `is_exists1:23`、`is_the:36`；`syntax/list_tools.py` `is_append:33`；`syntax/set_tools.py` `mk_image:56`；`syntax/numeral.py` `is_numeral_type:25`；`syntax/parser.py` `parse_var_decl:816`。

**仅测试引用、生产路径不用**：`core/fungen.py` `recursion_position:135`（它强制的"仅一个递归位"限制，与 emitter 已支持多递归位的实现脱节；`core/fungen.py:39` 的模块 docstring 还写着 "exactly one argument"，已过时）；`core/measure.py` `size_spec:310`。

# 五、判定为"有意为之/已文档化"，但值得你知道的

- `core/fungen.py:3762` "a definition without constructor patterns **is not emitted yet**"、`:3772` "recursion on argument N **is not supported**"（无模式/非 datatype 递归是能力边界，属于诚实失败）。
- `core/defcheck.py:139-146`：类型嵌套在别的类型构造子里直接拒（`is not supported`），比标准 HOL 窄。
- **两条路径能力不一致**：`core/defcheck.py:285-289`（结构检查仍只允许**一个**参数带构造子模式）vs `core/fungen.py` 的 emitter（已支持多递归位、字典序）。同一语言两种限制。
- `core/fungen.py:3860-3874`：度量机制不在作用域时**静默退回** subterm 关系 → 同一份源码在不同 `imports` 下生成不同条目。
- `core/basic.py:457-522`：size 族"反复重试直到能生成"，依赖生成顺序。
- `method/stable_state.py:747-754`：前向搜索对 facts 做**全排列 + 全子集**枚举（组合爆炸），只有 `method.no_order` 逃生。
- `core/verify.py:74-79`：`COMPUTATION_ORACLES` 是一张写死的 oracle 白名单（含 `z3`/`sympy`），库验证与 IDE 默认放行它。
- `syntax/pyhol.py:1232-1235`：`ast.literal_eval` 失败即 `new_items=[]`（静默丢数据）。
- `kernel/` 全部核心文件（type/term/thm/proof/proofterm/replay/report/theory/macro/extension/bootstrap/term_ord）我通读了，**没有发现特判或死代码**；`kernel/replay.py` 的规则集是闭合的（未知 rule 直接报错），这部分是干净的。

# 六、覆盖范围（诚实交代）

- **通读/大段读**：`kernel/*` 全部核心文件；`core/{basic,verify,incremental,context,matcher,search,items,defcheck}` 全文，`core/datgen.py`、`core/fungen.py`、`core/conv/core.py`、`core/macro/*` 的**关键段落**；`tactic/steps.py` 大部分；`method/stable_state.py` 大部分、`method/methods/core.py` 关键段落；`imperative/imp.py` 全文 + `imp_compile.py` 关键段落。
- **只做定向 grep、未通读**：`core/auto.py`、`core/measure.py`（除头部/命中点）、`core/fungen.py` 的其余约 4000 行分支、`core/logic.py`、`core/method.py`、`tactic/goal.py`、`method/init.py`、`method/methods/core.py` 的其余部分、`syntax/{pyhol,parser,pprint,numeral}.py`、`util/*`、`imperative/{expr,com,parser2}.py`。

**如果要我优先补哪一块，我建议 `core/fungen.py` 剩余分支 + `core/measure.py` + `method/methods/core.py`**——按已发现的问题密度看，特判与静默降级主要集中在这三处。
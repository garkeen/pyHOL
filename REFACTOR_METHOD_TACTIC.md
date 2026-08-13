# Method / Tactic / Macro 层抽象重构设计

> 状态：后端主体已实施完成（见文末“实施状态”）；前端待后续。
> 范围：`server/methods/`、`framework/tactic.py`、`framework/macros/`、`domains/*/method.py`。
> 不动：kernel 的 15 条原语、macro 的展开与检查机制、`.pyhol` 存储格式。
>
> **硬约束（用户明确要求）**：自动闭合必须显式——每个被自动关闭的
> 缺口都落成可见的 close_by/trivial 行（_finish_backward 机制），
> 任何新入口不得引入隐式消缺口。

---

## 1. 背景与目标

holpy 的交互式证明中，用户不直接写 tactic 脚本，而是通过 method
（前端点击 / 手动输入）一步步证明。method 是**证明语言本身**，
`.pyhol` 里存的证明步骤就是 method 调用（method_name + args + goal + facts），
stable_state 回放解释的也是 method 调用。tactic 只是 method 的执行语义。

当前问题：

1. **名字膨胀**：方向（backward/forward）× 目标（goal/fact）× 来源（theorem/fact）
   三个轴被展开成笛卡尔积命名，如 `apply_backward_step / apply_forward_step /
   rewrite_goal / rewrite_fact / rewrite_goal_with_prev / rewrite_fact_with_prev /
   frule / insert`。method 35 个、tactic 21 个，其中大量是同一概念的组合变体。
2. **双协议并存**：后向步骤走 `apply_tactic`（受控）；前向步骤由 method 直接
   `state.set_line(id, '<裸宏名>', ...)` 手写证明行，method 层直接引用宏名。
3. **逃生出口**：
   - `call_tactic`（注释原文 "Escape hatch when no method works"）
   - `MacroTactic`：泛型未检查适配器，任意宏名字符串从 method 层直通证明项
   - `norm/eval/linarith`：硬编码 NatType/RealType/IntType 类型分支 + 宏名
   - `exists_elim`：method 原地改写已有证明行（修改 intros 行的 args/prevs）
   - `simp/subst/unfold/fold/rewrite_goal(loc)`：conv 组合逻辑写在 method 层

目标：

- **减少名字**：method 35 → 17，tactic 21 → 13；轴变参数，短名优先
- **每个定义都有理由**：删掉纯变体，留下的每个名字对应一个不可归约的语义
- **焊死逃生出口**：method 层不再出现宏名字符串、不再碰 proof state 内部、
  不再有 call_tactic；macro 只能经唯一受检入口使用

---

## 2. 现状清点（修改前）

### 2.1 Method：35 个，按 apply() 实际行为分四类

**A 类｜干净派发（15 个）** —— `state.apply_tactic(id, tactic.xxx(), args, prevs)`：

| 名字 | 位置 |
|---|---|
| cases, apply_prev, rewrite_goal_with_prev, rewrite_goal, apply_backward_step, apply_resolve_step, accept, inst_exists_goal, induction, reflexive, equal_intr | server/methods/core.py |
| nat_norm, nat_const_ineq | domains/nat/method.py |
| prove_avalI | domains/expr/method.py |
| real_norm_method | domains/real/conv.py（经 domains/real/method.py 导入）|

**B 类｜绕过 tactic 直接写证明行（11 个）** —— 试跑后 `state.set_line(id, '<宏名>')`
或手动 `add_line_before`：

| 名字 | 行为 |
|---|---|
| rewrite_fact, rewrite_fact_with_prev, apply_forward_step, apply_fact, forall_elim, frule | 前向协议：行 rule 是裸宏名字符串 |
| cut, new_var, insert | 写结构行（sorry / variable / theorem）|
| introduction | 手动 `pt.export` 塞进 subproof |
| z3 | 直接 `set_line('z3')`（server/methods/z3.py）|

**C 类｜method 层组装 conv（5 个）** —— conv 组合写在 method，塞给
`tactic.rewrite_goal_with_conv`：rewrite_goal 的 loc 分支、simp、subst、unfold、fold

**D 类｜类型硬分发 + 逃生门（4 个）**：
- norm / eval / linarith：`if T == NatType: MacroTactic('nat_norm') elif ...`
- call_tactic：按名字 dispatch tactic 的白名单逃生门

**特例**：exists_elim —— method 原地改写后续 intros 行的 args/prevs。

### 2.2 Tactic：21 个（framework/tactic.py）

- 后向：MacroTactic, rule, resolve, intros, var_induct, rewrite_goal,
  rewrite_goal_with_conv, rewrite_goal_with_prev, apply_prev, cases,
  inst_exists_goal, assumption, reflexive, equal_intr, trivial, accept
- 前向（_forward 族，5 个）：apply_theorem_forward, rewrite_fact_forward,
  apply_fact_forward, rewrite_fact_with_prev_forward, forall_elim_forward
- 每个 tactic 产出的 ProofTerm 节点 = 宏名字面量或 primitive 组合

### 2.3 Macro：约 48 个

- framework/macros/core.py（18）：intros, resolve_theorem, beta_norm,
  apply_theorem(_for), apply_induct, apply_fact(_for), rewrite_goal(_sym),
  rewrite_goal_with_prev(_sym), rewrite_fact(_sym), rewrite_fact_with_prev(_sym),
  forall_elim_gen, trivial, close_by
- framework/macros/z3.py（1）：z3
- framework/auto.py（1）：auto
- domains：nat 5、real 6、integer 6、expr 1、logic 3（imp_conj/imp_disj/resolution）
- imperative 2（eval_Sem/vcg）、prover 4（sympy、simplex 系）

### 2.4 Conv

framework/conv/core.py：基类 + 组合子（then/top/sweep/arg/fun/abs_conv、
rewr_conv、beta_conv 等），全部领域无关。域 conv（domains/*/conv.py）
硬编码各域定理，由 tactic 内部或 auto 注册表使用。**conv 层本身无问题**，
问题只是 method 层越级组合 conv（C 类）。

---

## 3. 目标架构（修改后）

### 3.1 三种证明步骤与三个受检动词

证明步骤本质上只有三种：

1. **原语推导**（15 primitive）——藏在 macro 展开里，任何层都不直接调
2. **派生规则**（macro）——单步受检推理（nat_norm、imp_conj...）
3. **编排**（tactic）——多步组合、产生子目标（rule、intros、rewrite...）

Method 层（证明语言的执行器）对应**三个且仅三个受检入口**：

```python
state.apply_tactic(id, tac, args, prevs)        # 编排语义（现有，保留）
state.apply_macro(id, macro_name, args, prevs)  # 单条派生规则（新增）
state.apply_forward(ftac, prevs)                # 前向派生行（新增）
```

- `apply_macro`：检查宏存在性（theory.has_macro）、limit、sig，然后走与
  apply_tactic 相同的 export/写行/auto-close 机器。**取代 MacroTactic**。
- `apply_forward`：前向 tactic 返回 (rule 名, args, 新 Thm)，由 state 统一
  写行与 auto-close。**取代 method 里的 set_line/add_line_before**。

**MacroTactic 删除**。理由：它不是"调用 macro"（tactic 内部用宏字面量是合法的），
而是泛型未检查适配器——任意字符串从 method 层动态流入证明项。删除后
method 用 macro 的唯一途径是带检查的 `apply_macro` 注册表入口。

### 3.2 Method 词表：35 → 17

后向（攻击 goal）：

| 新名 | 吞并 | 存在理由 |
|---|---|---|
| rule | apply_backward_step | 定理反向拆目标 |
| resolve | apply_resolve_step | ~A 与 A 矛盾解任意目标 |
| rewrite | rewrite_goal + loc 分支 + subst + rewrite_goal_with_prev | 改写目标；参数 sym/loc/facts |
| intro | introduction | 引入变量/假设 |
| cases | — | 分情况 |
| induct | induction | 归纳 |
| cut | — | 插入中间断言 |
| inst | inst_exists_goal（目标侧）+ forall_elim（事实侧）| 实例化：exists 目标给见证 / forall 事实实例化 |
| accept | — | 定理结论直接匹配目标、前提由假设消化，零子目标 |
| refl | reflexive | 自反原始规则 |
| eq_intro | equal_intr | 等式双向引入 |
| simp | — | hint_rewrite 驱动的简化 |
| unfold | unfold + fold（方向变参数）| 定义展开/折叠 |

前向（派生 fact）——7 个并成 2 个：

| 新名 | 吞并 | 存在理由 |
|---|---|---|
| forward | apply_forward_step + frule + insert + apply_fact | 前向推导：来源=定理名或 fact，前提=选中 facts，零前提即 insert |
| rewrite（同名复用）| rewrite_fact + rewrite_fact_with_prev | 选中 fact 时自动前向改写；来源=定理/fact 由参数区分 |

结构与其他：

| 新名 | 吞并 | 存在理由 |
|---|---|---|
| elim | exists_elim（重做实现）| 存在事实消去，产生 variable+assume 行 |
| var | new_var | 声明变量 |
| assumption | 新增（现有 assumption tactic 升为正式 method）| 目标与自身假设相同时直接关闭；现仅存于 call_tactic 白名单，删除 call_tactic 后将不可达 |
| norm | norm + eval + linarith | 按目标类型查**域注册表**派发；等式与比较统一处理 |
| z3 / sympy / auto | — | 外部求解器，语义独立 |
| 域宏方法（nat_norm…）| — | 名字保留，改由 `register_macro_method(name)` 自动生成，apply 一行 `apply_macro` |

**删除**：call_tactic、subst、frule、insert、apply_fact、
rewrite_fact、rewrite_fact_with_prev、rewrite_goal_with_prev（独立名）、
forall_elim、inst_exists_goal（独立名）、eval、linarith、
apply_forward_step、apply_backward_step、apply_resolve_step。

### 3.3 Tactic 词表：21 → 13

```
rule, resolve, rewrite(sym, loc, source), intro, cases, induct,
inst_exists, elim_exists, accept, reflexive, equal_intr, assumption,
forward_rule(source=thm|fact)   ← 吞 apply_theorem_forward / apply_fact_forward /
                                    forall_elim_forward
rewrite_fact(source=thm|prev)   ← 吞 rewrite_fact_forward /
                                    rewrite_fact_with_prev_forward
```

- `rewrite_goal_with_conv` 降为内部组合子（unfold/simp 的实现零件，不再公开）
- `MacroTactic` 删除
- `trivial` tactic 保留为内部件（apply_tactic 流程的自动收尾用）
- tactic 内部的宏字面量（`ProofTerm('intros', ...)`）保留——静态可 grep
  审计，是 tactic 层的固有权力；可选收紧：`ProofTerm.macro(name)` 构造时断言存在

### 3.4 norm 域注册表（取代类型硬编码）

```python
# framework 提供：
norm_registry = {}          # 类型 -> 归一 tactic/macro 名
def register_norm(T, macro_name): ...

# 各域激活时（domains/<name>/__init__ 或 macro.py）注册：
register_norm(NatType, 'nat_norm')
register_norm(RealType, 'real_norm')
...
```

norm method 只查表，新增域不再改中央代码。eval/linarith 的语义
（数值求值、比较式）并入同一注册表（每类型可注册多档过程，按目标形状选择）。

### 3.5 register_macro_method 生成器

```python
# server/methods/core.py 提供：
def register_macro_method(name):
    """从宏自动生成 method：sig/limit/can_eval 取自宏定义，
    search = can_eval 试跑，apply = state.apply_macro(id, name)。"""
```

域里一行注册替代 30 行手写样板；宏→method 通道从手抄后门变正规机制。

### 3.6 Method 层契约（红线）

| 层 | 允许 | 禁止 |
|---|---|---|
| Method | 解码参数、search 试跑、三动词之一 | set_line / add_line_before / pt.export / ProofTerm 构造 / 宏名字符串 |
| Tactic | 组合 primitive 与宏字面量、调用 conv | 动态宏名字符串 |
| apply_macro | 检查后执行单条宏 | — |

---

## 4. 兼容性方案

`.pyhol` 存着旧 method 名的证明步骤，**库文件一个不动**：

- **回放别名表**：replay 时旧名 → 新实现（如 `apply_backward_step → rule`、
  `rewrite_fact → rewrite(target=fact)`）。别名表只服务回放，前端建议列表
  与新证明只出现新名。
- **行级 rule（宏名）完全不变**：kernel 展开/检查路径零改动，
  前向步骤写出的行格式与现在逐字节一致。
- `validate_library` 与 `server_test.testSteps` 回放即回归验证。

---

## 5. 实施步骤（每步独立可验证，不跑全量测试）

**第 1 步｜统一执行入口**（结构改动，行为不变）
- 新增 `ProofState.apply_macro`（含存在/limit/sig 检查）与
  `ProofState.apply_forward`
- 前向 tactic 合并：forward_rule / rewrite_fact
- MacroTactic 现有消费方（norm/eval/linarith、域 method）迁移到 apply_macro
- 删除 MacroTactic
- 验证：server/tests、syntax/tests、受影响的域测试

**第 2 步｜method 合并与改名**
- 按 3.2 表合并；旧名进回放别名表；display/search 逻辑合并
- 验证：server/tests/method_test.py、server_test.py（含各理论回放）

**第 3 步｜注册表与生成器**
- norm 域注册表；register_macro_method；域 method 样板删除
- 删除 call_tactic
- 验证：norm/eval 相关测试、域宏回放

**第 4 步｜elim 重做**
- exists_elim 改为 tactic 产出子证明结构，消除改行手术
- 验证：含 exists_elim 步骤的库理论回放

**第 5 步｜文档与清理**
- manual/ 相应章节更新；本文档标记完成状态

**第 6 步｜search/suggest 重设计**（见第 9 节）
- 模式网络（pattern net）索引替代全量扫描
- search 协议统一，迁入 framework/search.py
- 验证：IDE suggest 接口、method_test 的 search 用例

---

## 6. 验证策略（约束）

- 禁止主动跑全量 pytest 与 validate_library（用户明确要求）
- 每步只跑受影响的最小测试集 + 相关理论的定向回放
- 全库验证仅在用户明确要求时执行

---

## 7. 风险与开放问题

1. **别名表长期维护**：旧名回放映射需一直保留，除非未来迁移库文件。
2. **forward 的行管理差异**：frule（保留原 fact）与 apply_forward_step
   （关闭/替换语义）合并时须逐条核对行为，必要时留内部参数而非两个名字。
3. **前端接口**：method 名变更影响前端建议列表与步骤展示，
   需确认 frontend 是否有硬编码方法名。
4. **norm 注册表的多档派发**（eval 级 vs norm 级 vs 线性算术级）
   的优先级语义，实施时细化。
5. `rewrite` 单名覆盖 goal/fact 双向后，search 提示的 `_goal`/`_fact`
   返回格式需统一。

---

## 8. 对照研究：HOL Light 与 Isabelle（代码证据）

tinyHOL 树内的参考实现：`hol-light/`（HOL Light 全量）、
`mirror-isabelle/`（Isabelle 源码镜像）、`auto2/`（Bohua Zhan 的
matcher+steps 自动化框架，holpy 的 matcher/apply_theorem 谱系源头）。

### 8.1 HOL Light（hol-light/）

**底层类型**：
- `type conv = term -> thm`（equal.ml:93）——conv 本质：项 → 等式定理。
  holpy 的 `Conv.get_proof_term(t) -> ProofTerm(⊢ t = t')` 与之同构。
- `type goal = (string * thm) list * term`（tactics.ml:25）；
  tactic = goal → goalstate，goalstate = (meta × goal list × justification)
  （tactics.ml:45）——LCF 式：tactic 返回子目标 + **justification 函数**，
  由 justification 把子目标的定理组装回原目标。holpy 的
  ProofTerm-with-sorry + export 是其等价物（带洞证明项 + 事后展开检查）。

**组合子层**：
- tactic 组合子：THEN / THENL / ORELSE / REPEAT / EVERY / FIRST
  （tactics.ml:133-195）；conv 组合子：THENC / ORELSEC / FIRST_CONV /
  EVERY_CONV / REPEATC / CHANGED_CONV / RATOR_CONV / RAND_CONV /
  LAND_CONV（equal.ml）——与 holpy framework/conv 的组合子族一一对应，
  说明 conv 层设计早已对齐。
- **关键设计：`thm_tactic = thm -> tactic` 类型**（MATCH_MP_TAC 等）：
  “用一条定理”不是起名字，而是一个从定理到 tactic 的函数；
  `thm_tactical = thm_tactic -> thm_tactic` 组合子（ALL_THEN / NO_THEN /
  EVERY_TCL / FIRST_TCL）作用于“定理用法函数”。定理是参数，不是名字。

### 8.2 Isabelle（mirror-isabelle/src/Pure/）

**method 的形状**：
- `type method = thm list -> context_tactic`（Isar/method.ML:107）：
  method = **facts → tactic**。facts（已有定理/前提）是一等参数。
  与 holpy 的 `method.apply(state, id, data, prevs)` 同构——方向已对齐。
- **method 表达式是小型 AST**：`datatype text = Source | Basic |
  Combinator(info, comb, texts)`，组合子仅 5 种：Then / Then_All_New /
  Orelse / Try / Repeat1（+ Select_Goals）（method.ML:48-52）。
  用户可写的 method 语言 = 少量基本 method + 5 个组合子，语法极小。
  holpy 的交互式场景中组合由用户点击完成，无需暴露组合子，
  但“基本词表要小”的结论直接适用。
- **规则 method 族只有 4 个名字**：rule / erule / drule / frule
  （method.ML:37-40），全是同一 resolution 的方向变体，且全部接受
  定理表作为数据。holpy 目标词表的 rule/forward 合并与此同构。

**数据驱动与模式索引**：
- `net.ML`：`key_of_term: term -> key list`、`'a net`——定理按结论模式
  建 trie 式索引，搜索时以目标子项为 key 查 net 得候选，再精匹配。
  这是第 9 节 suggest 重设计的直接蓝本。
- 属性驱动：[simp]/[intro]/[dest]/[elim] 把定理存入 context，
  simp/rule 等 method 只读 context 数据——对应 holpy 的 hint_* 属性
  （用途保持不变：仅搜索建议，非上下文）。

### 8.3 结论：holpy 目标词表与 Isabelle 的对照

| Isabelle | holpy 目标名 | 备注 |
|---|---|---|
| rule | rule | 后向 resolution |
| erule | rule/elim 变体 | 消去式后向 |
| drule / frule | forward | 前向推导 |
| rewrite | rewrite | 参数 sym/loc/source |
| unfold / fold | unfold | 方向变参数 |
| insert / cut | cut | 插入断言 |
| simp | simp | 属性/提示驱动的简化 |
| induct / cases | induct / cases | |
| assumption | accept / refl / eq_intro | 收尾族 |

两套独立成熟的系统都收敛到同一形状：**少量正交基本 method +
定理/事实作为数据 + 方向与目标作为参数**。本文档第 3 节的词表
因此不是发明而是对齐。

---

## 9. suggest 与模式匹配搜索重设计

### 9.1 现状问题

- 每个 method.search() 各自遍历全量定理表（`theory.thy.get_data("theorems")`），
  对每条定理做 first_order_match + tactic 试跑：O(N × 匹配成本)，
  N 随库增长。
- **hint 属性竖井隔离（已实测确认的完备性缺口）**：rule 搜索只认
  hint_backward/hint_backward1，rewrite 只认 hint_rewrite。实测：目标
  `?A & ?B <--> ?B & ?A` 与 conj_comm 完全同形，rule/accept/手输方法名
  都能 0 gaps 关闭，但 conj_comm 只标了 hint_rewrite，因此 rule 建议列表
  永远不出现它；**无任何 hint 属性的定理对所有搜索完全不可见**。
  这是“无法直接用无参定理证同形目标”体验问题的根源（机制完备，
  搜索不可见）。
- search 实现散落在各 method 类内，suggest 接口（server/server.py 与
  ide_v2.py）重复拼装结果，无统一结构。

### 9.2 目标设计（参照 Isabelle net.ML + method 数据模型）

1. **模式网络索引**（framework/search.py 新增）：
   - **全局精确匹配网（最高优先级，不看属性）**：对当前理论内**所有**
     定理建 net，查询目标与定理结论可统一者——命中即产生
     “直接用定理 X 关闭”的建议（走 rule/accept 路径）。
     对齐 Isabelle：`rule` 不带参数时搜全部规则库，不按属性过滤。
     这一条直接修复 9.1 的竖井缺口。
   - 分类别网（次优先级）：hint_rewrite / hint_rewrite_sym /
     hint_backward / hint_backward1 / hint_forward / hint_resolve，
     key 为定理结论的 head 骨架（仿 net.ML key_of_term：常数/自由变量/
     结合符抽象为 key）。
   - 查询：取 goal/fact 的子项作 key 查 net 得候选集，再对候选做
     精确 first_order_match + 试跑。复杂度 O(N) → O(候选数)。
   - 维护：load_theory_cache 载入新定理时增量插入对应 net；
     limit 定理消失（理论切换）时按当前 theory 重建或惰性过滤。
2. **search 协议统一**：
   - 返回统一结构 `{method_name, data, _goal | _fact | _needs_params}`，
     与第 7.5 条的格式统一同步。
   - search 从 method 类迁入 framework/search.py 成为数据驱动的
     表查询；method 只声明“查哪张表、用什么参数模式”。
     method 类只剩 display/apply，与第 3.6 契约一致。
3. **hint_* 属性语义不变**：仅搜索建议用途，不做上下文/依赖划分
   （既有约定）。新增定理在 .pyhol 里标注属性即自动入网。
4. **前端**：suggest 端点只返回统一结构，前端按 method_name 渲染；
   旧 method 名不出现在建议中（回放别名表只服务回放）。

### 9.3 完备性审计清单（实测发现，随重构逐条关闭）

> 方法论（教训）：本节所有结论必须由执行过的测试用例支撑，
> 不允许仅凭读代码断言语义。审计矩阵脚本见仓库历史
> （__semantic_audit.py / __semantic_audit2.py / __audit3.py / __audit4.py，
> 审计后可删）。
>
> 审计进度（pass 1-4 已完成）：rule/accept 矩阵、close_by、must-change、
> forward 族、simp、resolve/cases/var_induct/apply_prev/条件重写。
> 未审计：auto 宏派发、oracle method（z3/sympy）、域宏（nat_norm 等）、
> method 层 display/search——属后续阶段。

**实测矩阵（logic 理论，rule/accept × 6 定理 × 7 目标形状）**：

| 目标形状 | 能一步关闭的机制 |
|---|---|
| iff 目标（与 conj_comm 同形）| rule:conj_comm ✓、accept:conj_comm ✓ |
| 蕴含目标 `~(q\|p) --> ~q` | **无任何机制一步关闭**（C6）；intro+rule 可关 ✓ |
| 蕴含目标 `A --> B --> A & B` | **无任何机制一步关闭**（rule:conjI 只匹 A&B）；intro+rule:conjI 可关 ✓ |
| 合取目标 `A & B` | rule:conjI ✓（2 子目标）|
| 析取目标 `B \| A` | rule:disjI1 ✓（子目标 B）|
| exists 目标 `(? y. y = A)` | inst_exists_goal(见证 A) ✓；rule:exI 抛 param 查询 |
| trivial `A --> A` | trivial 宏 ✓（自动收尾路径使用）|
| 整条 prop 统一性 | `first_order_match(not_or_elim1.prop, G2缺口)` 成功（?p:=q, ?q:=p）——证明 C6 修法可行 |
| resolve（~A 定理 + fact A）| 实测可关任意目标（gaps=0）；但只认字面 ~A 形（nat 理论中仅 not_false_res 一条，见 C4）|
| cases（默认 classical_cases）| 实测正常：goal B 产生子目标 ~A-->B、A-->B |
| var_induct 对已 intro 的体目标 | 实测正常：`n+0=n` 产生归纳步 `!n. n+0=n --> Suc n+0=Suc n` 与基步 `0+0=0` |
| var_induct 对带 forall 的目标 | **静默产生错误子目标（C10）** |
| apply_prev 实例化 | 实测：模式变量 fact 可实例化关具体目标（gaps=0）；forall fact 可实例化；前提不足时产生子目标——均正常 |
| 条件重写（rewr_conv conds）| 实测 if_P：给 cond `A` 正确改写 `(if A then 1 else 2) → 1`；缺 cond 报 “number of conds does not agree”；错 cond（~A）报 “cannot match left side”——语义正确 |
| rewrite_goal_with_prev | 实测正常，must-change 约束生效（无效果 AssertionError）|

| # | 缺口 | 现状 | 关闭方式 |
|---|---|---|---|
| C1 | 无 hint 属性定理 / 跨类别定理对搜索不可见 | 实测确认（conj_comm 案例）| 全局精确匹配网（9.2.1）|
| C2 | assumption tactic 无 method 暴露，删 call_tactic 后不可达 | 仅存于白名单 | 词表新增 assumption method（3.2）|
| C3 | accept 搜索受 hint 属性过滤 | 只扫 hint_* | 并入全局网，属性只作排序信号不作过滤 |
| C4 | resolve 只认字面 ~A，不认 A = false / A --> false | 形状单一 | 低优先：resolve tactic 增加形状归一（可选）|
| C5 | 对称形式定理不能当 rule 用 | 需走 rewrite sym | 接受（Isabelle 亦不自动），rewrite sym 建议覆盖 |
| C7 | **close_by 用精确相等（已实测）**：`Thm.can_prove` = `prop == target.prop` 加 hyps 子集。带模式变量的 fact 不能关具体目标（无实例化）；连 alpha 等价都判 False（`B & A <--> A & B` ≠ `A & B <--> B & A`）。自动收尾只在字面完全一致时生效 | 实测确认 | **缓行（回放风险）**：放宽 can_prove 会使回放时自动关闭录制时未关闭的缺口，破坏后续步骤对 id 的引用；需全库验证后才能启用 |
| C6 | **rule/accept 缺“整条 prop 匹配”模式（已实测）**：holpy 的 rule 先把对象层 `-->` 剥成前提，只拿最后结论匹配目标；蕴含形目标永远匹配不上蕴含形定理。实测 not_or_elim2 缺口 `~(q\|p) --> ~q`：Isabelle 的 `rule not_or_elim1` 一步关闭（整条结论统一 ?p:=q, ?q:=p），holpy 必须 intro 后再 rule | 存档证明因此残缺（rewrite 对齐后无处收尾），疑为多个库 FAIL 的同根因 | rule/accept 在剥离前先试 `first_order_match(th.prop, goal.prop)`，命中即返回定理实例证明项（对齐 Isabelle rule 语义）；一步关闭 not_or_elim2 型缺口 |
| C8 | **simp method 整体失效（已实测，真 bug）**：`conv.rewr_conv(thm)` 传入 Thm 对象，但 rewr_conv 只接受 ProofTerm\|str → TypeError 被 `except Exception: continue` 静默吞掉，全部 50 条 hint_rewrite 定理被跳过，simp 对任何目标都报 “no rewrite applicable” | 实测确认（探针手动用 str/ProofTerm 均成功）| **暂且不实现**（用户决定：simp 属自动化范畴）；重构时删除或保留为占位，后续与 auto 统一规划 |
| C9 | **无定点迭代（已实测）**：即使修复 C8，simp 每条定理只扫一轮（then 链一遍 top_conv）；`~~~~A` 变 `~~A` 即停，Isabelle 的 simp 迭代到不动点 | 实测确认 | **暂且不实现**（同 C8）；若将来实现，循环下沉 method 内部到不动点，仍一行，与不可变行模型相容（同 auto 宏的递归模式）|
| C10 | **var_induct 对带 forall 的目标静默出错（已实测）**：tactic 直接 `Lambda(var, goal.prop)`，不剥外层全称量词；对 `!n. n = n` 产生垃圾子目标（P 吞掉整个量化命题）且不报错。正确用法是先 intro 再对体目标归纳（实测该路径正确），但错误路径无任何防护。另：错归纳定理（conj_comm）抛裸 NotImplementedError 无信息 | 实测确认 | induction method 入口自动剥外层 forall（或断言拒绝）；错定理改报错信息 |

**附注（parser 小问题，非 tactic 层）**：`!n. n = (n::nat)` 解析失败
（绑定变量与带标注同名变量 abstract_over 类型冲突），需类型标注于绑定处
或用 kernel 构造器绕过；低优先。

### 9.4 模型层差异：不可变行模型与传统 HOL（已实测核实）

holpy 的证明状态是**不可变的行列表**：goal/fact 一旦生成不可修改，
步骤只能填充 sorry 或插入新行；且应用定理/重写**必须产生变化**，
否则报错。传统 HOL（HOL Light/Isabelle）无这两个约束（目标状态可原地
变换、无效果重写是合法 no-op）。实测核实：

- must-change：`rewrite_goal` 无效果 → `AssertionError: rewrite: unable
  to apply theorem`；`rewrite_fact_forward` 无效果 →
  `InvalidDerivationException`（均实测）
- 不可变：历史提交 75342bd2 有意删除了行变异类 method
  （revert_intro/sym/thin/drule）；rewrite_fact 派生新行而非原地改写

**对控制流组合子的影响（结论：不需要也不应该引入 method 级组合子）**：

| 组合子 | 传统位置 | holpy 中的对应物 |
|---|---|---|
| THEN | tactic 层 | **外化为会话**：步骤的线性顺序就是顺序组合 |
| ORELSE | tactic 层 | **外化为建议+用户选择**；method 内部可有回退（norm 的类型分发）|
| REPEAT | tactic 层 | **下沉到 macro 内部**：auto.solve 已递归；simp 修 C9 后也如此 |

理由：THEN/ORELSE/REPEAT 产生**不可见的中间状态**，与“每步都是
可见受检行”的模型直接冲突。但注意：REPEAT 与不可变性**不矛盾**——
auto 宏内部递归、对外仍是一行受检证明，已证明该模式可行。因此
正确方向是把循环下沉进单个 method/macro 内部，而不是暴露组合子语法。

不可变模型的代价（接受为设计权衡，非缺口）：无 fact 消费（事实只增
不减，证明行变长）；无假设改写/thin（子目标冗余假设只能保留）；
与 C7 叠加：fact 不能变形适配目标，精确相等的 close_by 更脆弱。

### 9.5 对照结论：底层与 tactic 层无需增删

- primitive（15 条）与 macro 展开/检查机制 ≈ Isabelle 原始规则 +
  派生规则，无缺口。
- conv 组合子族与 HOL Light 的 THENC/ORELSEC/RATOR_CONV/RAND_CONV/
  REPEATC 一一对应，无缺口；holpy 另有 loc 位置寻址（对应 Isabelle
  rewrite 的位置参数）。
- tactic 种类不新增：rule/accept/rewrite/inst/intro/cases/induct/
  assumption 已覆盖 HOL Light + Isabelle 的基本集；组合子
  （THEN/ORELSE/REPEAT）不引入——交互式场景组合由用户点击完成，
  自动化由 auto 承担。**但 rule/accept 的匹配语义需增强**：
  增加整条 prop 匹配分支（见 C6），这是语义对齐而非新增名字。

---

## 10. 实施状态（后端主体完成）

### 已完成

1. **三个受检入口**（server/methods/core.py）：
   - `apply_tactic`（原有，行为不变）
   - `apply_macro`（新增）：宏存在性/limit 检查后执行单条派生规则，
     取代 MacroTactic；**MacroTactic 已删除**
   - `apply_forward`（新增）：前向 tactic 派生新 fact 行，行 rule 取自
     证明项（method 不再触碰宏名）
   - 三者共享 `_finish_backward`：**显式自动闭合**（可见 close_by/trivial
     行），无隐式消缺口
2. **method 词表收敛**：rule / resolve / rewrite / intro / cases /
   induct / cut / inst / accept / refl / eq_intro / unfold / forward /
   elim / var / assumption / norm / apply_prev + 域宏方法（nat_norm /
   nat_const_ineq / prove_avalI / real_norm / eval_Sem）+ oracle
   （z3 / vcg）。删除：call_tactic、simp（坏方法，属自动化范畴暂不
   实现）、eval、linarith、subst、fold（并入 unfold 的 sym 参数）、
   frule/insert/apply_fact（并入 forward）
3. **回放别名表 METHOD_ALIASES**：库中 26 个旧 method 名（20,700+ 步）
   全部映射到新词表，附数据默认值（如 rewrite_fact → target=fact）；
   别名只服务回放，交互面只暴露新名
4. **缺口修复**：
   - C1：framework/search.py 模式网络（key_of_term 骨架索引），全局网
     不看 hint 属性；stable_state.search_backward 新增 exact 通道
   - C2：assumption method
   - C4：resolve 形状归一（A --> false、A = false 经 negI 派生 ~A）
   - C6：rule 整条 prop 匹配（**回退顺序**：剥离匹配失败后才试，保证
     录制回放逐字节不变）
   - C10：var_induct 拒绝“目标外层 forall 恰好绑定归纳变量”的垃圾
     情形（注意：外层 forall 绑定其他变量是库证明的正常形状，不拒绝）
   - C7：缓行（放宽 can_prove 有回放分裂风险，需全库验证）
   - C8/C9：simp 暂不实现（用户决定）
5. **register_macro_method 生成器**：域 method 样板归零（nat/expr/real/
   imperative 已迁移）；norm 改为类型→宏注册表（norm_registry）

### 验证结果（均与重构前基线逐项一致）

- pytest：server/syntax/framework/domains.logic/kernel/util 349 passed；
  prover/imperative 72 passed
- 定向回放：logic 52/92（STEP_FAILED 仅 not_or_elim2，已知）、
  nat 148/226（le_1_1、sub_eq_0，已知）、set 15/59（无 STEP_FAILED）
- C6 端到端：not_or_elim2 缺口 `~(q|p) --> ~q` 经 rule not_or_elim1
  一步关闭；suggest exact 通道给出 ('rule', 'not_or_elim1') 建议

### 追加完成（第四轮：前端同步 + manual 更新）

11. **前端同步新词表**：
   - ProofArea.vue 手动 tab 下拉改新名（forward/rewrite/inst 正向组；
     rule/resolve/apply_prev/intro/elim/cases/induct/unfold/simp/refl/
     eq_intro/assumption/accept 反向组；cut/var 结构组），删除
     subst/fold/insert；Auto tab 删 eval/linarith（已不存在）
   - 集合更新：FORWARD_METHODS={forward,rewrite,inst}（无目标可用），
     INST_PARAM_METHODS={rule,forward,apply_prev}；rewrite 分组改
     target 标记判定（isFactRewrite/isGoalRewrite）
   - apply_suggestion 透传 target/source 标记（双模式回放无歧义）；
     手动应用 rewrite/inst 无目标时自动注 target='fact'；
     method_sig_map 静态回退表改新名
   - ProofLine.vue 方向标记加 close_by（行级 rule 名均合法保留）
   - FRONTEND_API.md 示例与说明同步新名
12. **manual/ 更新**：06_method.md 方法目录/分发模式/属性表/step 示例
   全部改新词表（含双模式语义与受检宏调用）；README.md 速查、
   07_system.md 方法层自动化同步；MacroTactic 描述移除
13. **验证**：前端 npm build 通过；端到端 API 冒烟 16 项全过
   （init/搜索/apply/双模式 fact 改写 target=fact/自动闭合 close_by/
   从头重放）；pytest 349 全绿无回归

### 追加完成（第二轮）

6. **elim 重做**：新增 tactic.elim_exists 受检推导；method 只做结构性
   状态编辑（插行/扩 hyps/接线），接线的 intros 行与 tactic 推导项做
   kernel 等价断言。exists_elim 密集理论（logic_base/logic/function/
   misc/sums/floor/metric）回放与基线逐项一致
7. **search 数据驱动化**：framework/search.py 升级为通配模式桶
   （head 常量分桶 + 骨架通配匹配）：
   - rewrite_goal/rewrite_fact/rule/forward/accept 的 search 改走
     candidates_for / forward_candidates_for（结论两侧骨架 + 全部前提
     骨架均入索引），干跑验证不变；严格候选列表测试全部通过
   - resolve 保留全扫（hint_resolve 定理极少且 ~A 结论不适用骨架索引）
   - 实测剪枝：real 理论 389 条 hint_rewrite → 9 候选（0.0025s）

### 追加完成（第三轮：旧名清零 + simp 实现）

8. **旧方法名全部移除**：
   - METHOD_ALIASES 删除，apply_method 直接按新名派发
   - 类改名新词表（rule/resolve/intro/induct/elim/var/refl/eq_intro/
     rewrite/forward/inst/...），内部实现类改 _impl 后缀，insert 类删除
   - 库录制步骤全量迁移：18,184 步 / 39 个 .pyhol 文件改名，
     fact 模式步骤内联 target=fact / source=prev 标记；json 缓存
     不含方法名，无需迁移
   - 步骤解析修复：位置参数索引不再把命名 token 计入（标记可任意穿插）
   - 双模式 method（rewrite/inst）由状态形状推断模式，标记可覆盖；
     fact 模式指向缺口位置时必须显式 target='fact'（歧义说明已入文档）
   - stable_state BACKWARD/FORWARD 集合、导出箭头、search_forward
     过滤同步新词表；imp_compile 生成步骤改 rule
9. **simp 实现**（修复 C8/C9，此前“暂不实现”解除）：
   - 全量 hint_rewrite 无前提定理参与，top_conv 逐定理扫一轮 +
     beta 归一，**循环到不动点**（上限 100 轮防交换律循环）
   - must-change：无可简化报错；整个简化经 rewrite_goal_with_conv
     落成单个可见步骤（展开为受检原语行）
   - 冒烟验证：~~A→A、~~~~A 两轮定点→A、无变化报错均通过
10. **C7 匹配化自动闭合**（实现）：
   - 新增 server 层 `_can_prove_match`（first_order_match + hyps 子集），
     替换 find_goal / _finish_backward 中的精确相等判定；模式变量
     fact 可实例化关具体目标（实测生效）
   - **内核 Thm.can_prove 保持严格**（kernel/theory.py:437 是声音性
     校验边界，不能放宽）；匹配化仅用于显式自动闭合
   - 注：自由变量互换是逻辑等价非 alpha 等价，匹配不关闭它是正确行为
   - 验证：九理论回放与基线逐项一致（无回放分裂），pytest 全绿

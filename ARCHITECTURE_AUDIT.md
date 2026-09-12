# holpy 架构：目标态、铁律与现状契约

> 本文件原为 2026-09 架构重写的审计与迁移日志（563 行）。重写已完成，逐日/逐步的过程记录、
> 任务 A–H 的收尾叙述、已修复偏差的来龙去脉全部删除，只保留对将来有用的部分：目标架构、
> 铁律与 lint、信任模型、当前债务、以及改代码前必须知道的陷阱。过程对应提交见 `git log`。
>
> **文档同步状态（2026-09-12）**：本文件与代码一致。**`manual/` 与 `README.md` 落后于现状**
> ——仍写着重写前的 `framework`/`domains`/`server`/`app` 结构与旧 API，需要一次专门同步。
> 本次不动。

---

## 1. 组织定律：严格可剥离分层

全系统按**推理方向**切成一条全序。每一层都是独立可用的完整子系统；从顶上剥掉一层，下面照常工作。

| 剥掉 | 剩下仍然可用 |
|---|---|
| 外壳 repl / backend / frontend | method —— 证明语言完整，只是无交互入口 |
| L3 method | kernel + core + theories + tactic —— 程序化驱动 goal，无证明语言 |
| L2 tactic | kernel + core + theories —— 正向 conv+macro 写证明，无 goal |
| L1 conv + macro | kernel —— 裸原语，完整 HOL |
| （底）L0 kernel | 15 原语 + Thm |

全序：`kernel < conv < macro < tactic < method`。matcher / search / solvers 是**旁路服务**；
theories 是内容，按文件归属各层（内部同序 `conv < macro < tactic < method`）。

**互相调用不是要被运行时小聪明容忍的环，而是"职责切错"的症状。** 解法是把每个类别的职责切到
只剩一条，让反向调用在构造上不可能——不靠注入、不靠注册总线、不靠装配点。

---

## 2. 层级定义（每类一职责）

| 类别 | 唯一职责 | 形状 | 不许做 |
|---|---|---|---|
| **kernel** | 正向原子推理，Thm 唯一来源 | 15 原语 | 不识 goal；不执行上层代码 |
| **conv** | 等式的组合构造（同余闭包） | `Term + 显式前提定理 -> Thm(t ≡ ?)` | 不见宏名、不搜索、不见 goal |
| **macro** | 命名的正向一步（内核扩展） | `(args, prevs) -> Thm`，可记录可展开 | 不 import tactic |
| **tactic** | 逆向一步的翻译：goal 形状分析 → 宏名+参数 | `goal -> (子goal, 宏名+参数)` | 无推导逻辑、无组合子 |
| **method** | UI 通道：apply_tactic / apply_macro / apply_forward | 操作 ProofState | 不见 conv、不见原语 |
| **matcher** | 精确匹配：一阶匹配、模式判定（两步匹配第二步） | `Term -> Inst` | 不证任何东西 |
| **search** | 候选检索：模式网分桶、candidates_for（第一步） | `Term -> [候选名]` | 不证任何东西、不精确匹配 |
| **theories** | 领域特定内容（垂直切片） | 每领域 conv/macro/tactic 实例 | 不 import method |
| **solvers** | 纯算法核（sat/tseitin/congc/fologic/omega 算法核） | 只依赖 kernel+syntax+core | **不 import theories、不 import tactic** |

---

## 3. 目标文件架构

```
holpy/
├── kernel/              【L0】正向原语，Thm 唯一来源。独立 = 完整 HOL
│   ├── type.py term.py term_ord.py thm.py theory.py
│   ├── macro.py           Macro 基类 + global_macros（宏 = 内核扩展槽）
│   ├── proofterm.py proof.py   日志数据结构（构造时不再隐式 eval 宏）
│   ├── replay.py          带假设规则的纯原语重放：replay(prf, axioms) -> (Thm, holes)
│   └── bootstrap.py       纯 kernel 引导宏（intros/trivial）
│
├── core/                【L1】正向推理机器 + 服务。不识 goal。剥掉 L2/L3 仍可用
│   ├── conv/             等式构造：basic.py（Conv 协议 + 组合子）+ inst.py（原语链接助手）
│   ├── macro/            命名正向步骤：registry.py（注册+level+展开）/ logic.py（领域无关）/ simp.py
│   ├── matcher.py        精确匹配（两步匹配的第二/精确步）
│   ├── search.py         候选检索（两步匹配的第一/候选步）
│   ├── auto.py           global_autos 分发器
│   ├── items.py          .pyhol 条目模型
│   ├── defcheck.py       定义合法性检查（结构递归 + 严格正性）+ 归纳公理配方
│   ├── verify.py         verify 的 core 半边：展开器 + 信任集 + 信任报告 + 四态判定
│   ├── basic.py          .pyhol 加载 + theories 动态激活
│   ├── logic.py / context.py / method.py（注册表）
│
├── syntax/              【L0.5】语言层：parser/printer/pprint/numeral/operator/logicops/
│                        settings/pyhol。只依赖 kernel+util（数字与逻辑常量的语法糖在这里）
│
├── theories/            【内容】领域实例，垂直，镜像 library/*.pyhol DAG
│   ├── <theory>/         logic/ nat/ function/ integer/ real/ expr/
│   │   └── conv.py / macro.py / tactic.py / method.py（注册走 core 注册 API）
│   ├── integer/omega.py  omega 的证明装配 + auto 注册（算法核在 solvers/omega.py）
│   ├── real/simplex.py real/simplex_strict.py   实/整数线性算术的证明装配
│   ├── z3rec.py          Z3 证明重建引擎（跨域实验链；含 solve_and_reconstruct 桥）
│   └── poly.py           多项式项工具
│
├── tactic/              【L2】逆向翻译层。剥掉 L3 仍可用
│   ├── goal.py           Goal（goal 概念全系统唯一定义点）
│   └── steps.py          rule/cases/induct/intro/accept = 形状分析 + 宏名+参数
│
├── solvers/             旁路纯算法：sat / tseitin / congc / fologic / auto /
│                        sympywrapper / z3wrapper（纯 z3 桥）/ omega（纯 factoid 求解核）
│
├── method/              【L3】证明语言层
│   ├── methods/          method 通道：apply_tactic / apply_macro / apply_forward
│   ├── stable_state.py   稳定 ID 包装 + 行树 + gap
│   └── init.py           初始 state 解析
│
├── util/                纯工具：name / typecheck / unionfind（kernel 的合法伙伴）
├── imperative/          Hoare 逻辑子模块（theories 的第 7 个垂直切片）
├── backend/             HTTP API 层（Flask 薄壳，零逻辑）
├── frontend/            Vue 前端（不动）
├── library/             .pyhol 理论数据（不动）
└── repl/                【未建】自洽 REPL（见 §7.1）
```

---

## 4. 依赖律（全部由 lint 强制）

1. `kernel` 不 import 任何项目模块；`kernel + syntax` 独立即可正向证定理。
2. `core/` 任何文件不得出现 Goal 类型；`tactic/` 之外不存在 goal 概念。
3. `core/conv` 不得搜索、不得出现宏名；前提定理永远显式传入。
4. `core/macro` 不得 import `tactic`。
5. `tactic` 可用一切正向资产；正向层永不 import `tactic`。
6. 领域对框架的唯一入口是 `core/basic.py` 按 `.pyhol` 元数据动态加载 + 注册表按名解析。
7. `kernel/replay` 只识 15 原语与假设规则；`core/verify` 是唯一认识宏展开的验证入口。
8. Thm 构造白名单（§6.3）。
9. `repl`/`backend`/`frontend` 不含逻辑，只调 method 通道。

**lint 清单（白名单全部为空）**

| lint | 断住 |
|---|---|
| `kernel/tests/thm_priv_test.py` | kernel 外无裸 `Thm(` 构造（命名构造器 `Thm.sorry` 等是 Attribute 调用，放行） |
| `core/tests/test_import_direction.py` | tactic∌auto；macro 层∌tactic；core∌method；solvers∌method；solvers∌theories；solvers∌tactic；theories/imperative∌method；syntax 生产代码∌core/method/theories/solvers；Goal 消费面 |
| `util/tests/test_util_pure.py` | util 不 import kernel 以上任何层 |
| `core/tests/test_macro_invariant.py` | 有 gpt 的宏不得自定义 eval；宏模块 pyflakes 零 undefined name |
| `syntax/tests/pyhol_test.py` | pyhol 不 import method/core/theories；方向表与 stable_state 不漂移 |
| `kernel/tests/replay_test.py` | `import kernel` 不拉 framework（子进程检查） |

---

## 5. 设计原则

- **5.1 Thm 是唯一一等对象。** ProofTerm 是降级的日志（为点击式 UI 与 .pyhol 重放保留确定性记录），
  永远不许碰地基：kernel 不依赖它的求值、不认识宏，`replay.py` 只跑原语。
- **5.2 tactic 是逆向→正向的翻译器，不是证明语言。** 对外只见 goal；每步逆向编译成一次正向宏调用 +
  前提槽。**判断归 tactic，机械展开归 macro**。tactic 层无推导逻辑，无 THEN/ORELSE/REPEAT。
- **5.3 证明语言是声明式 have/by/with 的唯一组合机制。** 组合只发生在证明文本的显式行/分支里。
- **5.4 没有组合子的位置。** THEN/ORELSE/REPEAT 需要可回滚、失败即控制流、隐式 goal 状态三个前提，
  holpy 一个都没有（证明行不可改写、失败是原子拒绝、证明文本本身就是状态）。
- **5.5 互相调用靠职责消解，不靠运行时小聪明。** conv 不碰 macro 是构造使然。唯一保留的运行时按名
  解析是宏注册表（ProofTerm 按名、global_macros、global_autos）。
- **5.6 类别不许发明。** kernel/conv/macro/tactic/matcher/search/theories/method/solvers 就是全部。
- **5.7 名字对齐语义。** (1) 每个函数名对齐语义，改名与挪位同步，不留"历史名+注释"过渡态；
  (2) 目录名=类别名；(3) 一个抽象层一个职责，lint 能断的交给 lint，断不住的靠三重对齐让人一眼看出异常。
- **5.8 两个表面。** 程序员表面（conv/macro/tactic + kernel，供扩展者）；证明语言表面（method，供写证明者）。
  tactic 属程序员表面。REPL 是证明语言表面的交互终端。
- **5.9 增量校验要求宏是纯函数（memo 契约）。** `core/verify.py` 的
  `verify(..., compute_only=True, memo=...)` 在一条定理的回放内缓存宏展开：仅当一次宏调用的**全部
  输入**与上次相同时才复用（键 = `rule` + `args` + 各前提定理 + 该行自己的声明命题 `seq.th` +
  全局理论对象 `theory.thy`；后三者按对象身份比较，条目内钉住这些对象）。因此宏的 `get_proof_term`
  **不得**依赖这些之外的任何可变全局状态，特别是：(1) `context.ctxt` / `context.ctxt.vars`（回放中随
  `intro`/`elim` 增减）；(2) 模块级可变容器、计数器、缓存（除非它只是**加速**，且不缓存时结果逐位
  相同）；(3) 随机数 / 时间 / 环境变量；(4) `self` 上构造后写入的字段。理论对象身份已在键内
  （见 §7.4 的 z3rec 条目），宏作者无需自行处理；前四类是宏作者的责任。审计（2026-09-12）：58 个
  注册宏全部满足该契约。审计模式 `--selfcheck` 会重推并复核每个命中，恢复"每行每次都重推"的属性
  （代价回到记忆化之前）；常规开发默认关。

---

## 6. 信任模型

### 6.1 规则全集封闭

凭空产生定理的规则只有 **18 条** = 15 推理原语 + 3 假设规则（axiom / oracle / sorry）。TCB 就是这张
封闭规则表；replay 遇到这 18 条之外的任何东西都是错误，没有例外分支。每个证明的信任报告
（`rpt.axioms` / `rpt.oracles`）列出它实际用到的非原语规则。

`verify` 拆两半：`core/verify.py`（展开器：宏展开、信任集、报告、`compute_only` 全行 emit）+
`kernel/replay.py`（只跑原语）。kernel 永不执行上层代码。

### 6.2 三条假设规则

| 规则 | 假设了什么 | 守门机制 | 消费方政策 |
|---|---|---|---|
| **axiom** | 一条命题为真 | 理论装载：定义经结构递归/严格正性检查（`core/defcheck`），显式公理直接声明 | 库验证接受；信任报告列出 |
| **oracle** | 一个外部求解器的判定为真 | 具名 + 信任集：`oracle_thm(name, prop)` 是唯一构造点 | 缺省拒收；信任集按名放行 |
| **sorry** | 眼下这条还没证 | 仅限构造中的缺口；`Thm.sorry` 是机制原语 | no_gaps / 未完成判据 |

### 6.3 Thm 构造私有化：现状

Thm 的构造通道只有：kernel 内部（15 原语）、`ProofTerm` 存储字段、三个洞构造器
（`Thm.sorry` / `Thm.axiom` / `oracle_thm`）、`tactic/goal.py`（Goal 铸洞）、
`core/defcheck.mk_axiom`（axiom 装载的唯一入口）、syntax 前门（`parser.thm` 直用 `Thm.sorry`，
因 syntax 低于 tactic 不能 import goal）。

lint 只禁**裸 `Thm(` 调用**；上述通道都是命名构造器（Attribute 调用）或 kernel 内。新增 Thm 构造点
前先想清楚它属于哪条规则、守门在哪。

### 6.4 证明状态四态（只属于 theorem 条目）

axiom 条目（`thm.ax`）没有证明、没有状态。四态是验证管线的输出契约，后三态本质都是失败：

| 状态 | 语义 | 判据 |
|---|---|---|
| **VALID** | 成功：完整无洞的证明 | 重放完成，sorry 洞为 0，oracle 洞在信任集内 |
| **DEP_FAILED** | 依赖失败：本证明完整，但引用了失败态定理 | 引用的定理状态 ∈ {STEP_FAILED, DEP_FAILED, UNPROVED}；沿 import DAG 查缓存 |
| **STEP_FAILED** | 失败：证明存在但有洞，未完成 | 重放任一步抛错，或关洞后仍有 open goals |
| **UNPROVED** | 未证：根本没有证明 | 无 steps |

---

## 7. 当前债务

### 7.1 待做的工程债

- **"计算即 oracle" 推导化**（最大的一块）。6 个常数折叠/范型 conv——`nat_eval_conv`、`int_eval_conv`、
  `real_eval_conv`、`real_norm_conv`、`real_const_eq_conv`、`real_power_conv`——内部的 `auto_solve`
  前提仍在发射 level-0 oracle 宏节点。不是"有推导却用宏包装"（那类已消灭），而是**计算本身没有推导**：
  真推导化需先实现数值计算的重写推导（二进制数值计算），属独立机制工程；`norm_conv` 返回的推导里
  那些折叠节点随之消失。
- **REPL（repl/）**——未建。验收：不启 backend/frontend，纯交互走 method 通道 + verify 反馈完成一个
  库级定理的证明与验证。§5.8 定义了它的定位。
- **frontend/backend 需要一次大的 API 修复**——已明确推迟，本阶段不碰。`backend/tests/test_backend_api.py`
  目前是知识归档（0 个 test 函数，记录 12 个端点的载荷与断言意图）；原脚本有两病灶（12 个 pytest error；
  save round-trip 写真实 `library/`）。

### 7.2 内容债（不在架构范围）

`library/` 约 3675 条定理：**VALID 388 / UNPROVED 1813 / DEP_FAILED 1420 / AXIOM 52 / STEP_FAILED 2**
（仅 `nat.le_1_1`、`prime.distinct_prime_coprime`）。这是原作没证完的库内容，**不是机制 bug**——
DEP_FAILED 的瀑布正是"依赖失败"状态的正常传播。

验收基线不是"全绿"，而是**快照 + 零缩水**：任何原先 VALID 的定理必须仍 VALID（允许状态更精确，
不允许退化）；原先失败的允许重新归类，但每个状态翻转都要能归因到具体改动。**本仓库不负责补证它们**；
若发现某条失败是机制性的（策略/宏的 bug），按 AGENTS 修复并补"之前失败现在能过"的主动用例。

### 7.3 记录在案、按设计不动

- **`Thm.__init__` 的 hyps 去重四分支**：TCB 热路径上按原语规则的真实调用形态裁出的优化
  （单 Term / 整 tuple 免检 / 两 tuple 跨 tuple 去重 / 原地早退）。hyps 保序且参与 Term 判等与重放校验，
  统一成 set 会给最常见的 `Thm(prop, th.hyps)` 路径凭空加开销并可能改变顺序——**这是设计 feature**。
  前提约束：传 tuple 时调用方保证 tuple 内部已去重（构造函数只做跨 tuple 去重）。
- **`core/auto.py` 的 `if filename == 'hoare'` 硬编码**激活 imperative 包（它不是 theories/ 包）。
- **`first_order_match` 不做 `t` 无 SVar 的断言**：`auto` 拿定理 schema 去匹配 **schematic 子目标**，
  `t` 合法地含 SVar；加断言会改掉 auto 的 `TacticException` 失败契约。契约写在函数 docstring 里。

### 7.4 结构备注

- `theories/z3rec.py` 是内容层里的**跨域非域模块**（先例：`theories/poly.py`）。它和
  `theories/real/simplex*.py` 一起构成 z3 实验链，生产消费者为零；整体放在内容层是因为其"算法"
  本身就是领域证明构造，或跨域不可按域分文件。
- **`theories/z3rec.py::def_axiom` 会在回放中途替换全局理论**：它在 z3 证明重建里调用
  `basic.load_theory('sat'/'smt')`（对照 `theories/integer/omega.py` 的同类调用在模块级、导入期执行，
  无害）。所以增量校验缓存的键必须含理论对象身份（`core/verify.py::_memo_key`，与
  `core/auto.py::_cache_key` 同理）；理论一旦被换掉，旧条目自动全部失效并重推。
- **omega 的 auto 注册由 `theories/integer/__init__.py` 触发**（core/basic 不再 eager import 它）。
  依据：全库只有 `library/int.pyhol` 使用 omega，且它声明 `domains integer`。将来若有理论用 omega
  却不声明 integer 域，这个假设会被破坏。
- `theories/real/simplex*.py` 不被 `theories/real/__init__.py` 引入（刻意的懒装载与宏注册时机）。

---

## 8. 改代码前必读的陷阱

- **同名不同义**：`core/logic.py` 的 `strip_conj`/`strip_disj` 是**递归展平**，`syntax/logicops.py` 的是
  **只展右嵌套**的浅版。两者不可互换，跨文件 import 时用别名（`_strip_conj_shallow`）。
- **z3 的 `AstRef` 也有 `is_not`/`is_exists` 同名方法**：`theories/z3rec.py` 的 `translate`（z3→holpy）
  里 `term.is_exists()` 是 z3 方法，不是 holpy 谓词。批量改谓词时必须按 receiver 类型区分。
- **模块级缓存的键要含理论身份**：`core/auto.py` 的 `norm_record`/`solve_record` 若只以项为键，进程内
  换理论后会复用上一理论的证明项（其行按旧理论语境解析）。键用 `(id(theory.thy), t)`。
- **洞语句只在 kernel 之外经命名构造器**：`Thm.sorry`（下层/成洞）、`tactic/goal.py` 的 Goal（tactic 及以上）、
  `oracle_thm`（具名 oracle）、`core/defcheck.mk_axiom`（axiom）。裸 `Thm(` 会被 lint 拒绝。
- **conv 不得发射宏名、不得搜索**；前提定理永远显式传入（`core/conv/inst.py` 的原语链接助手）。
- **失败语义是契约**：`auto`/`solve`/`simp` 关不掉就诚实失败（`TacticException`），不留半截证明、
  不改 gap 计数；加断言/改异常类型前先看调用方是否依赖该契约。
- **证明行一旦生成不可改写**（无 thin/sym 这类行改写）；一次应用要么原子写入完整行，要么一行不写。
- **缓存键是文件 mtime**：改名/拆分会让理论"看起来变了"、缓存全失效一次（可接受）。改缓存格式要连
  `--force` 语义一起定义。
- **前端契约**：`/api/*` 路径与 `#[N]` 稳定 ID 格式是前后端共同契约，重写全程冻结。
- **`syntax/` 的生产代码不得 import core/method/theories/solvers**；数字/逻辑常量的语法糖住在 syntax，
  靠显式 import 装载（不再有 import 副作用把方法挂到 `Term` 上）。

---

## 9. 测试与验证惯例

- 测试跟模块走（`kernel/tests/`、`core/tests/`、`theories/<t>/tests/`…），跨模块的才放顶层。
  **不合并、不删改旧用例**（防回归是契约）。每个新功能至少一个"之前失败、现在能过"的主动用例；
  每个新入口至少一个被动用例（抛指定异常 / gap 不变 / 无副作用）。
- 宏用 `test_macro`（同时验 eval、get_proof_term、check_proof/verify）；method 用 `test_method` 或
  StableProofState（验关门、gap 数、行记录）。
- **全量 library 验证很贵**：结果走顶层 `.cache/` 缓存，命中即跳过，`--force` 才全量重验。
  日常只跑相关模块回归；改共用件（`simp_sweep`、`solve`、`basic.load_theory_cache`、matcher 等）
  才扩大回归范围。
- 改 import 方向、Thm 构造、Goal 消费面时，对应的 lint 会立即报错，白名单应保持为空。

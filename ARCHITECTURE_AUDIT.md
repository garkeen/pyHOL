# holpy 架构重写目标

本文件记录 2026-09-05 架构讨论的结论，作为 holpy 完全重写的目标参照。
原依赖审计的发现已并入第 6 节"当前贴错层的修正"。本文件只记录设计，未修改任何代码。

2026-09-06 增补（依 kernel/Thm/状态管线的源码核对）：
- `check_proof` 全链路更名 **verify**，语义升为"带洞的纯原语重放"（§7.1-7.2）；
- **Thm 构造私有化**（命名约定 + lint），kernel 外 ~100 处裸 `Thm()` 分类改造（§7.3）；
- **证明状态四态** 固定为验证管线输出契约（§7.4）；
- 第 6 节补入 syntax 层反咬、thm_status 住错层、monitor 死代码、eval 断言式等清单；
- 第 8 节步骤 0/5 扩充，新增步骤 8（验证管线收口）。

2026-09-06 第二轮增补（server 定位核查 + HOL 语义修正）：
- axiom / oracle / sorry 升为 15 原语之外的**假设规则**，规则全集封闭 = TCB（§7.2）；
- 证明状态修正：只属于 theorem 条目，axiom 无状态；后三态本质皆失败；记录两处现行偏差（UNPROVED 依赖漏判、跨文件依赖不查，§7.4）；
- **server 拆分**：items/defcheck/verify 归 core，剩余定名 `method/`（L3 证明语言层），`app` → `backend`，新增自洽 REPL（§2/§5.7/§6/§8 步骤 9）；
- 设计原则新增 §5.7：名字对齐语义、目录名=类别名、程序员表面与证明语言表面分离。

2026-09-06 第三轮增补（盲区调研）：
- 新增 §9 重写前置条件：**库验证债务的快照基线**（内容债非机制债，OK 集零缩水 + 逐翻转归因）、库文件清点、imperative 的 import 面、util 拆分（纯工具 vs 项工具）、syntax 内部分裂（语言 vs 序列化）、缓存契约、前端契约（#[N] 冻结）、测试搬家、更名无双名期；**search 归 core**（matcher=精确匹配、search=候选检索，两步匹配各自独立）；
- REPL 明确为**新功能、最后考虑**（§8 步骤 10 标注）。

---

## 0. 组织定律：严格可剥离分层

全系统按**推理方向**切成一条全序。每一层都是独立可用的完整子系统；从顶上剥掉一层，下面照常工作。

| 剥掉 | 剩下仍然可用 |
|---|---|
| 外壳 repl / backend / frontend | method —— 证明语言完整，只是无交互入口 |
| L3 method | kernel + core + theories + tactic —— 程序化驱动 goal，无证明语言 |
| L2 tactic | kernel + core + theories —— 正向 conv+macro 写证明，无 goal |
| L1 conv + macro | kernel —— 裸原语，完整 HOL |
| （底）L0 kernel | 15 原语 + Thm |

每一层只依赖下面；下面不知道上面存在。

**互相调用不是要被运行时小聪明容忍的环，而是"职责切错"的症状。** 解法是把每个类别的职责切到只剩一条，让反向调用在构造上不可能发生——不靠注入、不靠注册总线、不靠装配点。今天代码里 conv 发射 `apply_theorem`、宏定义塞在 conv 文件里、`auto_conv`、`simp_sweep` 住在 tactic.py——这些不是"要被聪明打破的环"，是贴错了层，挪回各自的位置即可。

---

## 1. 层级定义（每类一职责）

| 类别 | 唯一职责 | 形状 | 不许做 |
|---|---|---|---|
| **kernel** | 正向原子推理，Thm 唯一来源 | 15 原语：`... -> Thm` | 不识 goal；不执行 framework 代码 |
| **conv** | 等式的组合构造（同余闭包） | `Term + 显式前提定理 -> Thm(t ≡ ?)` | 不见宏名、不搜索、不见 goal |
| **macro** | 命名的正向一步（内核扩展） | `(args, prevs) -> Thm`，可记录可展开 | 不 import tactic |
| **tactic** | 逆向一步的翻译：goal 形状分析 → 宏名+参数（+显式分支） | `goal -> (子goal, 宏名+参数)` | 无推导逻辑、无组合子 |
| **method** | UI 通道：apply_tactic / apply_macro / apply_forward | 操作 ProofState | 不见 conv、不见原语 |
| **matcher** | 精确匹配：一阶匹配、模式判定（两步匹配的第二步） | `Term -> Inst` | 不证任何东西 |
| **search** | 候选检索：模式网分桶、candidates_for（两步匹配的第一步） | `Term -> [候选名]` | 不证任何东西、不精确匹配 |
| **theories** | 领域特定内容（垂直切片） | 每领域 conv/macro/tactic 实例 | 不 import server |
| **solvers** | 纯算法核（sat/omega/simplex/z3/tableau） | 只依赖 kernel+syntax | 不碰 Thm 构造以外的事 |

**全序**：kernel < conv < macro < tactic < method。matcher、solvers 是旁路服务。theories 是内容（按文件归属各层，内部同序 conv < macro < tactic < method）。

---

## 2. 目标文件架构

```
holpy/
├── kernel/              【L0】正向原语，Thm 唯一来源。独立 = 完整 HOL
│   ├── type.py  term.py  term_ord.py  thm.py  theory.py
│   │                Thm 构造私有化（§7.3）：15 原语/mk_VAR/oracle_thm 是仅有的凭空入口
│   ├── macro.py          Macro 基类 + global_macros 注册表（宏=内核扩展槽）
│   ├── proofterm.py  proof.py      日志数据结构（构造时不再隐式 eval 宏）
│   └── replay.py         带假设规则的纯原语重放（§7.1）：replay(prf) -> (Thm, holes)
│                         verify 的 kernel 半边就这一个函数
│
├── core/                【L1】正向推理机器 + 服务。不识 goal。剥掉 L2/L3 仍可用
│   ├── conv/            等式构造：Term + 显式前提定理 -> Thm(t≡?)
│   │   ├── basic.py     Conv 协议 + refl/beta/eta/rewr/then/top_sweep/arg/binop
│   │   └── inst.py      原语链接助手（替代 conv 里发射 apply_theorem 宏节点）
│   ├── macro/           命名正向步骤：(args, prevs) -> Thm。可用 conv
│   │   ├── registry.py  注册 + level + 展开器
│   │   ├── logic.py     intros/apply_theorem/resolution/rewrite_*（领域无关）
│   │   └── simp.py      simp_sweep + simp 引擎（从 tactic.py 迁回；它是宏展开机制）
│   ├── matcher.py       精确匹配（一阶匹配、is_pattern 判定）——两步匹配的第二步
│   ├── search.py        模式网候选检索（candidates_for、hint_* 分桶）——两步匹配的第一步，
│   │                    兼作 method 搜索建议的取候选引擎；只出候选，不证任何东西
│   ├── auto.py          global_autos 分发器
│   ├── items.py         .pyhol 条目模型（从 server 迁回，消掉 framework->server 反向）
│   │                    mk_axiom 收口（§7.3）：axiom 假设规则的唯一装载点
│   ├── defcheck.py      定义合法性检查（从 server/struct_recursion.py 迁回）：
│   │                    结构递归 + 严格正性——axiom 规则的守门人，属内核扩展，不属 server
│   │                    Datatype/Inductive 的公理配方（distinct/inject/induct/cases）也在这里
│   ├── verify.py        verify 的 core 半边：展开器 + 信任集 + 信任报告（§7.1）
│   │                    证明状态四态判定 + thm_status/thm_error 住这里（§7.4）
│   └── basic.py         .pyhol 加载 + theories 动态激活
│
├── theories/            【内容】L1/L2 的领域特定实例，垂直，镜像 library/*.pyhol DAG
│   └── <theory>/        logic/ nat/ function/ integer/ real/ expr/
│       ├── conv.py       该领域的等式构造（纯：不搜索、不发射宏名）
│       ├── macro.py      该领域的宏 + 注册（原 conv.py 里的宏定义挪回这里）
│       │                 eval 断言式全部清理（§7.3）：仅真 oracle 保留且具名
│       ├── tactic.py     该领域的拆法（可选）
│       └── method.py     注册走 core 注册 API（不 import server/method）
│
├── tactic/              【L2】逆向翻译层。彻底脱离：HOL 没它也工作。剥掉 L3 仍可用
│   ├── goal.py          Goal + goal 树（全系统唯一定义点；sorry 节点改吃 Goal，§7.3）
│   └── steps.py         rule/cases/induct/intro/accept = 形状分析 + 宏名+参数
│                        （无 THEN/ORELSE/REPEAT，无推导逻辑）
│
├── solvers/             纯算法核：sat/omega/simplex/z3/tableau。只依赖 kernel
│                        （omega 的项胶水 strip_plus 等回 theories/integer）
│
├── method/              【L3】证明语言层（原 server 拆分后的剩余）。剥掉它 tactic 系统仍可用
│   ├── methods.py       method 通道：apply_tactic/apply_macro/apply_forward（原 server/methods）
│   ├── proofstate.py    行树 + gap，have/by/with 唯一组合处（原 methods/core 的 ProofState 部分）
│   └── stable.py        稳定 ID 包装（原 server/stable_state.py）
│
├── repl/                自洽 REPL：交互驱动的读-证-验循环
│   └── repl.py          薄壳：解析输入 -> 调 method 通道 -> verify 反馈
│                        不含逻辑；有它，项目不依赖 backend/frontend 也可交互使用
│
├── backend/             HTTP API 层（原 app/ 更名）：Flask 路由薄壳
│                        只做 请求解码 -> method/repl 调用 -> JSON 编码，零逻辑
│
├── frontend/            Vue 前端（不动）
├── library/             .pyhol 理论数据（不动）
└── imperative/          Hoare 逻辑子模块（不动）
```

**命名**：原 `framework`（太抽象）→ `core`；原 `domains`（太抽象）→ `theories`；原 `server` 拆分——`items`/`struct_recursion`/monitor 的验证半边归 `core`（items/defcheck/verify），`server.py` 的初始化解析归 `tactic` 侧 goal 构造，剩余（methods/proofstate/stable_state）定名 `method/`，与类别名对齐；原 `app` → `backend`（名实相符：它只是 HTTP 薄壳，不是"应用本体"）。类别仍是现有的（kernel/conv/macro/tactic/matcher/method），不发明新类别。

**server 拆分的依据**（2026-09-06 核查 `server/items.py` 968 行、`struct_recursion.py` 217 行）：`Datatype.get_extension` 配方 distinct/inject/induct/cases 公理、`Inductive.get_extension` 生成 `_cases`/`_induct`、`Fun` 经结构递归检查后注册方程——这些是**归纳类型翻译与归纳公理注册**，真身是 axiom 假设规则的守门与装载，属内核扩展（core），与 UI/会话毫无关系。留在 L3 的只有真正面向证明语言的东西：method 通道、ProofState 行树、稳定 ID。拆分后名字对齐语义（§5.7）。

---

## 3. 依赖律

```
kernel（含宏注册表 = 内核扩展槽）
  ↑
core:  conv < macro           matcher / search / verify / items / defcheck  服务层，只依赖 kernel+syntax
  ↑
theories/<t>/conv.py, macro.py    L1 内容，镜像 .pyhol DAG
  ↑
tactic + theories/<t>/tactic.py   L2
  ↑
method + theories/<t>/method.py    L3 注册
                                    ↑
repl / backend / frontend           外壳，只调 method 通道

solvers  旁路纯算法，被 theories/*/macro.py 使用，不 import 任何领域
```

静态铁律（lint 强制）：

1. `kernel` 不 import 任何项目模块；`kernel + syntax` 独立即可正向证定理。
2. `core/` 任何文件不得出现 Goal 类型；`tactic/` 之外不存在 goal 概念。
3. `core/conv` 不得搜索、不得出现宏名；前提定理永远显式传入。
4. `core/macro` 不得 import `tactic`。
5. `tactic` 可用一切正向资产；正向层永不 import `tactic`。
6. 领域对框架的唯一入口是 `core/basic.py` 按 `.pyhol` 元数据动态加载 + 注册表按名解析。
7. `kernel/replay` 只识 15 原语与假设规则；`core/verify` 是唯一认识宏展开的验证入口。
8. Thm 构造白名单（§7.3）：kernel 内部原语、ProofTerm 存储字段、`oracle_thm` / `mk_axiom` 洞构造器、`tactic/goal.py` 之外不得构造 Thm。
9. `repl` / `backend` / `frontend` 不含逻辑，只调 method 通道；method 之下的层不知道它们存在。

---

## 4. 可剥离性（架构定律的兑现）

见第 0 节表。每一前缀都是可用系统：kernel ⊆ +conv ⊆ +macro ⊆ +tactic ⊆ +server。
theories/ 的文件按所属层遵守同一方向：`conv.py < macro.py < tactic.py < method.py`。

---

## 5. 设计原则

### 5.1 Thm 是唯一一等对象

ProofTerm 是降级的**日志**，不是货币。holpy 保留它是因为点击式 UI 与 `.pyhol` 重放需要确定性记录（重放是展开，不是重新搜索）；但它是仪器，永远不许碰地基。kernel 不依赖 ProofTerm 的求值、不认识宏——`replay.py` 只跑原语。

### 5.2 tactic 是逆向→正向的翻译器，不是证明语言

策略系统本质上是把逆向推理翻译为正向推理——它不是新东西，是正向推理的包装、架在 kernel 之上的完整抽象。

- 对外只见 goal；每一步逆向编译成一次正向 macro 调用 + 前提槽。
- goal 全部关闭时按记录正向重放出最终 Thm。最终交付给 kernel 的东西里没有任何逆向成分。
- **判断归 tactic，机械展开归 macro**（holpy 现有约定，提纯）：tactic 做 goal 形状分析、决定拆法、命名用哪条宏、算出参数；机械推导全在 macro。
- tactic 层不含推导逻辑，无 THEN/ORELSE/REPEAT。

### 5.3 证明语言是声明式 have/by/with，是唯一的组合机制

证明是 `have S by m with fs` 的显式断言序列。每一步显式陈述证了什么、用什么方法、用哪些前提。组合只发生在证明文本的显式行/分支里，不发生在 tactic 表达式里。tactic 不是证明语言，只是 `by` 后面的判定词汇。逆向结构（cases/induct 拆分支）显式化为一行一行的分支块，由用户逐块填写——不是被组合子驱动的隐式状态机。

### 5.4 没有组合子的位置

THEN/ORELSE/REPEAT 成立需要三个前提，holpy 一个都没有：

1. **可回滚**——ORELSE 的语义是"试一条，失败换一条"。但证明行一旦落盘就不可改写（`AGENTS.md` 第 3 条"证明行一旦生成不可改写"），一次应用要么原子地写入完整行，要么一行不写。先试再回滚在不可变行上没有定义。
2. **失败即控制流**——REPEAT 预设步骤幂等、有不动点；holpy 每次应用都追加新的不可变行，没有幂等，没有"状态不变"检测。而且失败语义是契约（`AGENTS.md` 第 1 条）——失败是原子拒绝，不是迭代终止信号。
3. **隐式 goal 状态**——组合子是"操作隐式状态的程序的控制流"。holpy 的证明文本本身就是状态，读者可见。在声明式语言上套组合子等于把显式步骤重新藏进隐式状态，和语言存在的目的直接冲突。

### 5.5 互相调用靠职责消解，不靠运行时小聪明

conv 不碰 macro 不是纪律使然，是构造使然：conv 的职责（从项组合地构造等式）本身就没有理由去碰一个命名的正向步骤。macro 碰 conv 才有理由（命名正向步骤需要等式机器）。方向由本质决定。simp↔auto 的真递归走宏注册表按名解析（holpy 现成机制：ProofTerm 按名、global_macros、global_autos），死结关在一个数据结构里——这是唯一保留的运行时按名解析，不是注入/装配点。

### 5.6 类别不许发明

kernel、conv、macro、tactic、matcher、search、theories、method、solvers 就是全部（matcher=精确匹配，search=候选检索，两者合成两步匹配，各自独立）。此前一度造出的 rules/steps/record/forward/backward 全是多余的，已废弃。

### 5.7 名字对齐语义：从文件架构就能读懂项目

架构的最终检验标准：**新人扫一眼目录树和函数名，就能不读实现地讲出每个部分是干什么的**。三条纪律：

1. **每个函数有一个对齐其语义的简单名字**。`check_proof` 名不副实（它不是检查一个证明，而是带假设的重放），故更名 verify（§7.1）；`load_json_data` 这类名随机制更替自然死亡；改名与挪位同步做，不留"历史名 + 注释解释"的过渡态。
2. **目录名 = 类别名**。`conv/` 里只有 conv，`macro/` 里只有 macro——conv 干 macro 的活（发射宏名）不是风格问题，是这个纪律被破坏的症状（§6）。反例即现行目录名：`framework`（太抽象）、`server`（装的是归纳公理注册和 ProofState，名实不符）、`app`（其实是 HTTP backend）。全部更名到位（§2）。
3. **一个抽象层只有一个职责，职责与名字互相锁定**。名字是职责的 API：名字改了 = 职责变了，反之亦然。lint 能断的东西（import 方向、裸 Thm 构造）交给 lint，lint 断不住的（一个模块"顺便"干了邻居的活）靠目录-类别-名字的三重对齐让人一眼看出异常。

### 5.8 两个表面：程序员的，与证明语言的

系统对外只有两个入口，面向两类使用者（分工与 Isabelle 的 ML 层 / Isar 层一致）：

| 表面 | 面向 | 词汇 | 层 |
|---|---|---|---|
| **程序员表面**：conv / macro / tactic（+ kernel） | 扩展 holpy 的人（写领域包、写求解器） | Python API：Conv 组合子、宏注册、策略类 | L0-L2 |
| **证明语言表面**：method | 写证明的人（点击式 / have-by-with 文本） | `have S by m with fs`——方法名是词汇，不是代码 | L3 |

- tactic 属于**程序员表面**：它是逆向推理到正向机器的翻译器，供扩展者实现新拆法；它不是用户证明语言的一部分。
- method 是**证明语言**的唯一词汇表：每个 `by m` 里的 m 是一个方法名。证明语言不暴露 tactic/conv/macro 的任何组合机制（§5.3/§5.4）。
- **REPL（repl/）是证明语言表面的交互终端**：读一行（声明或方法调用）→ 调 method 通道 → verify 即时反馈（状态四态、当前 goal、洞报告）。自洽 = 不依赖 backend/frontend 也能完整使用。它是"点式 IDE 的文本化孪生"：IDE 点按钮，REPL 敲命令，两者走同一条 method 通道、共享同一份验证语义——这本身就是 L3 薄壳的证明。

---

## 6. 当前贴错层的修正

> 原审计（2026-09-05 源码核对）结论：conv→tactic 无（干净）；conv→宏/原语 有；tactic→conv/宏/原语 三者皆有；宏→conv 大多数有，6 个宏是纯原语；宏→tactic 无 Tactic 调用但有 2 处 import 越界；Method→conv 无（唯一 import 是死代码）；Method→宏 5 处绕过受检入口手写宏名；Method→原语 1 处（assume）；跨层反向依赖 2 处。

贴错层清单（按真身归类，迁移即可，零行为变化为主）：

| 现状 | 真身 | 动作 |
|---|---|---|
| `auto_conv`（把 auto 包成 Conv） | 它在搜索，是 macro | 删；条件重写前提由调用方显式传入 |
| `simp_sweep` 住在 `framework/tactic.py:222` | 它是宏展开机制 | 迁到 `core/macro/simp.py` |
| conv 里发射 `apply_theorem` 宏节点（`framework/logic.py:143`，`domains/logic/conv.py` 8 处） | conv 在做 macro 的活 | 换成 `core/conv/inst.py` 原语链接（forall_elim+substitution+implies_elim） |
| `int_eval_macro` 等定义在 `domains/integer/conv.py:112` | 是宏，位置错 | 挪到同领域 `macro.py` |
| `domains/*/method.py` import `server.methods.core` | 注册目标错 | 改走 core 注册 API |
| `framework/basic.py:13` import `server.items` | 反向依赖 | items 下沉 `core/items.py` |
| `framework/tactic.py:235` 反向 import `auto` | 形成 tactic↔auto 双向延迟 import 环 | 随 `simp_sweep` 迁出而消解 |
| `server/methods/core.py` 5 处手写宏名（`rewrite_fact_sym` 等）绕过 `apply_forward` | 复制粘贴未走受检通道 | 换 `state.apply_forward(...)`（审计【B】） |
| `server/methods/core.py:1070` 手写原语 `assume` | 无 tactic 包装 | 加 ContextTactic 入口或规范开口子（审计【C】） |
| `server/methods/z3.py:35` 手写宏名 `z3`，无 tactic 包装 | level-0 oracle 宏 | 补 `z3_forward` 或明确 oracle 宏允许直连（审计【D】） |
| `domains/real/conv.py:31` import `server.methods.core` | 与其余 3 domain 不一致 | 挪入 `domains/real/method.py`（审计【F】） |
| `server/items.py`（968 行）：Datatype 配方 distinct/inject/induct/cases 公理、Inductive 生成 `_cases`/`_induct`、Fun 经检查注册方程 | 归纳类型翻译 + 归纳公理注册 = axiom 假设规则的守门与装载，属内核扩展 | items 下沉 core 时拆分：条目解析归 `core/items.py`，检查+公理配方归 `core/defcheck.py` |
| `server/struct_recursion.py`（217 行）：结构递归 + 严格正性检查 | 同上，是 axiom 规则的守门人，不是 server | 迁 `core/defcheck.py` |
| `server/monitor.py` 的 `validate_theory`（四态判定） | 验证管线输出，属 core | 迁 `core/verify.py`（§7.4，含两处状态判定偏差修正） |
| `server/server.py` 的 `parse_init_state`（74 行小文件） | 目标行/sorry 初始化 = goal 构造，属 tactic 侧 | 并入 `tactic/goal.py` 的初始 goal 构造 |

2026-09-06 增补的贴错层（源码核对新增）：

| 现状 | 真身 | 动作 |
|---|---|---|
| `framework/macros/z3.py:9` 模块级 import `prover.z3wrapper` | oracle 胶水住 L1 | 宏留在 core（oracle 槽位），wrapper 归 `solvers/`；注册时按名注入，不模块级 import 领域/求解器代码 |
| `syntax/json_output.py` import `framework.basic` + `server.items`；`syntax/pyhol.py:376` 延迟 import `server.stable_state`；`syntax/parser.py`/`infertype.py` import `framework.context`；`pprint.py` 延迟 import `framework.logic` | syntax 层反向咬住上层 | syntax 只许依赖 kernel(+util)；序列化/展示的编排逻辑上浮到 core/server（json_output 属导出服务，上下文解析属 core） |
| `framework/context.py`（Context，被 syntax 的 parser/infertype 与 server 共用） | 目标架构未给它定位 | 归 core（core/basic.py 旁）或独立 `core/context.py`；syntax 的 parser 依赖它则接口反转：parser 只收纯数据（名->类型表），Context 在 core 组装 |
| `thm_status` / `thm_error` 两张表注册在 `EmptyTheory`（`kernel/theory.py`） | 证明状态是验证管线的输出，不是内核数据 | 随验证管线迁出 kernel（见 §7.4） |
| `server/monitor.py` 的 `check_theory` / `__main__` 路径引用已不存在的 `basic.load_json_data`、`theory_cache['master']` | JSON 时代死代码 | 删除；唯一活路径 `validate_theory` 收口进 `core/verify`（见 §7） |
| 位置序（`util/`）：`util/lark_error.py` 依赖 lark 解析器报错形态 | 解析层错误翻译住 util | 挪入 `syntax/`，util 回归纯工具 |

回归范围：conv 纯净化（换 apply_theorem）改变导出证明形状，须全量 `validate_library.py`；更名与拆分步骤（server→method、app→backend、check_proof→verify）跑全量单测 + 库验证缓存未命中的理论；其余跑相关模块回归。

---

## 7. 信任模型

**规则全集封闭**：整个系统凭空产生定理的规则只有 18 条——15 条推理原语 + 3 条**假设规则**（axiom / oracle / sorry）。TCB = 这张封闭的规则表；每个证明的信任报告列出它实际用到了哪些非原语规则。这是"check_proof 只是 replay 的包装"成立的前提：replay 遇到这 18 条之外的任何东西都是错误，没有例外分支。

- kernel 永远不执行 framework 代码。
- `check_proof` 拆两半：core 侧的展开器（认识宏，把日志展开成纯原语流）+ kernel 侧的 `replay.py`（只跑原语；跑通则 Thm 合法——Thm 的抽象类型本身就是校验）。重命名后这分别是 `core/verify.py` 与 `kernel/replay.py`（§7.1）。
- 三条假设规则各有明确的守门机制（见 §7.2），守门之外的用途一律非法。

### 7.1 verify：check_proof 的更名与语义升级

**全链路统一更名 `check_proof` → `verify`**（kernel 的 `Theory.check_proof`、模块级 `theory.check_proof`、`ProofState.check_proof`、monitor 的同名包装、全部调用点）。

更名的理由不只是名字，而是语义修正：verify 不是"逐行执行一遍"的 replay，而是**带假设规则的纯原语重放**——sorry 和 oracle 在构造上就无法展开/重放，这不是缺陷，是证明语义的边界，必须成为显式数据而不是隐式分支。改造后 kernel 侧的契约：

```
replay(prf) -> (Thm, holes)
  holes = [(rule, label, Thm)]
    rule ∈ {'sorry', 'oracle', 'axiom'}   # 15 原语之外的假设规则
```

- 输入的每行只能是：原语 / theorem / variable / **假设规则**。replay 不再有任何"跑不了"的分支：假设是一等行类型，重放证明的是"**在全部列出的假设成立的前提下，最终 Thm 成立**"。
- replay 是纯函数：不回填 `seq.th`、不缓存 subproof、无 `compute_only` 跳过模式——这些杂务全部归 core 侧的展开器。现有 `_check_proof_item` 的三个非校验职责（回填、暂存、跳过）在 kernel 侧消失。
- no_gaps 政策 → 参数化为**信任集**：`verify(prf, trust={'z3', 'sympy'})`。缺省拒绝一切 oracle；sorry 规则在任何档位都使证明"未完成"（报告非空 sorry 列表）。
- 具名假设：oracle 行以 `('oracle', 'z3', th)` 形式落洞表，**缺省信任集里没有的名字直接拒收**（对比现状：z3 未安装时 eval 只打印 warning 然后照常 `Thm(args, ...)` 返回——verify 后这种情况是硬失败）。

### 7.2 三条假设规则（15 原语之外凭空产生定理的全部入口）

三条假设规则是一个统一概念——**假设**——的三个实例，区别只在假设的来源与守门政策：

| 规则 | 假设了什么 | 守门机制 | 消费方政策 |
|---|---|---|---|
| **axiom** | 一条命题为真 | 理论装载：定义经结构递归/严格正性检查（`core/defcheck`），显式公理直接声明 | 库验证接受；信任报告列出 |
| **oracle** | 一个外部求解器的判定为真 | 具名 + 信任集：`oracle_thm(name, prop)` 是唯一构造点 | 缺省拒收；信任集按名放行 |
| **sorry** | 眼下这条还没证 | 仅限构造中的缺口；`Thm.assume` 是其机制原语 | no_gaps / 未完成判据 |

要点：

- **"定理"的三种身份分开**：被 axiom 规则接纳的条目是理论内容（axiom 条目），不是待证对象；只有 theorem 条目才有证明状态（§7.4）。axiom 洞指的是重放视角下"该定理以 axiom 规则进入"这一事实。
- 守门是规则的一部分：axiom 规则只许经 `core/defcheck`/`core/items` 的受检装载进入（结构递归、严格正性——正是现 `server/struct_recursion.py` + `server/items.py` 里 Datatype/Inductive/Fun 的检查逻辑，真身是内核扩展的守门人，不是 server），oracle 规则只许具名进入。绕过守门直接造 Thm 的所有路径即 §7.3 清理的对象。
- 全量库验证敢声称"独立重验"，正是按依赖序重放后只剩 axiom 规则这一层假设——信任报告把每个定理的 axiom 依赖列全。

### 7.3 Thm 构造私有化（LCF 精神的修复）

**现状**：`Thm.__init__` 是公开构造函数，全库（kernel 外、非测试）约 100 处裸 `Thm()` 直调。LCF 风格要求"凭空构造定理只能经 15 原语"——今天 Python 侧没有这道墙，靠的是没人乱写。

**目标**：用命名约定强化——`Thm` 的构造通道只有三：

1. `kernel/thm.py` 内部（15 原语与 `mk_VAR`）；
2. `ProofTerm` 的定理存储字段（proof 数据结构持有已得 Thm）；
3. **洞的构造器**：`Thm.assume`（匿名洞的机制原语）与 `oracle_thm(name, prop)` ——具名洞的唯一构造点，任何宏 eval 若产出未经推导的 Thm，必须以洞的形式显式给出名字。

其余一律改为：判断/形状分析层不得 new Thm，只能**引用**已有 Thm 或经 ProofTerm 推导后取 `.th`。

**全库约 100 处裸 `Thm()` 的分类改造**（2026-09-06 逐类核对）：

| 类别 | 形态 | 例 | 改造 |
|---|---|---|---|
| 语句构造（最大类，~40 处） | `ProofTerm.sorry(Thm(new_goal, goal.hyps))` | `framework/tactic.py` 17 处、rewrite/unfold/cases 各处 | 真身是 **Goal**，不是 Thm——迁到 `tactic/goal.py` 的 Goal 构造，sorry 节点吃 Goal（这是 goal 概念全系统唯一定义点的兑现） |
| eval 断言式 | `return Thm(goal)`：把待证目标原样包成 Thm 扔回去 | `domains/nat/macro.py` 4 处、`rewrite_goal_macro.eval`（macros/core.py:418）、z3 宏 | 仅真 oracle 保留此形态且必须具名（`oracle_thm`）；`rewrite_goal.eval` 这类"断言即求值"改真推导（对照 `beta_norm_macro.eval` 走 conv 的正例）或直接删 eval 走展开 |
| 平行双实现 | eval 与 get_proof_term 两套独立逻辑（漂移风险） | `apply_theorem` 宏：eval 在 Thm 空间手拼匹配，get_proof_term 在 ProofTerm 空间 | eval 的默认实现（宏基类里 sorry prevs → get_proof_term → 取 th）已是安全形态；删平行实现，可信宏必须显式声明并提供一致性测试 |
| 数据装载（item→extension） | `extension.Theorem(name, Thm(prop))` | `server/items.py` 6 处 | 这是理论公理的装载点——正身是 **axiom 洞的构造**，收口到 `core/items.py` 的单一 `mk_axiom` 入口，与 §7.2 对齐 |

**执行机制**：import-lint 同一套 AST 扫描加一条规则——`kernel/` 之外出现 `Thm(` 构造调用（白名单：`tactic/goal.py`、`core/items.py` 的 mk_axiom、oracle 槽）即报错。命名约定靠 lint 变成构造上的强制。

### 7.4 证明状态：只属于 theorem 条目

**证明状态是 theorem 条目的属性**。axiom 条目（`thm.ax`）是被 axiom 假设规则接纳的理论内容——它没有"证明"，因此没有证明状态；`def`/`fun`/`datatype`/`inductive` 的衍生定理（`_def_N`/`_cases`/`_induct` 等）同样以 axiom 规则进入，不参与状态机。状态是**验证管线**（core 的 verify + 库验证器）对 theorem 条目的判定输出，不是逻辑内核的数据。

四态固定为契约，后三态本质都属于失败：

| 状态 | 语义 | 判据 |
|---|---|---|
| **VALID** | 成功：完整无洞的证明 | 重放完成，sorry 洞为 0，oracle 洞在信任集内 |
| **DEP_FAILED** | 依赖失败：本证明完整，但引用了失败态定理 | 步骤引用的定理状态 ∈ {STEP_FAILED, DEP_FAILED} |
| **STEP_FAILED** | 失败：证明存在但有洞，未完成 | 重放中任一步抛错，或关洞后仍有 open goals |
| **UNPROVED** | 未证：根本没有证明 | 无 steps |

- 现行实现（`server/monitor.py:validate_theory`）四态语义与此对齐，随验证管线迁 `core/verify`；`thm_status` / `thm_error` 两张表从 `EmptyTheory`（kernel/theory.py）一并迁出，kernel 的七张表回归纯逻辑数据。
- **两处现行偏差，重写时修正**（2026-09-06 核对 `validate_theory` 源码）：
  1. **UNPROVED 依赖漏判**：依赖检查只把 `STEP_FAILED`/`DEP_FAILED` 当失败；若本定理无 steps 而**它依赖的定理恰是 UNPROVED**，仍判 UNPROVED——按"后三态皆失败"的定义，这应记 DEP_FAILED（依赖了失败态）。
  2. **跨文件依赖不查**：依赖状态只查本文件内已判定的定理（`statuses` 字典）；import 来的定理若在别的文件验证失败，本文件引用它不会被判 DEP_FAILED。重写后依赖检查应沿理论的 import DAG 查询状态（含库验证缓存）。
- AXIOM 不是状态，是条目类型；在重放视角下是 axiom 假设规则（§7.2）。
- 库验证（`validate_library.py`）的缓存机制不变：命中即跳过、`--force` 全量。

---

## 8. 迁移顺序（小步，每步用可剥离性测试断住）

0. **内核断奶**（最痛但最本质，先做）【已完成 2026-09-06】：`Macro` 基类、`global_macros`、宏名解析、eval 校验若依赖 framework 则正名为"内核扩展槽"或迁出；`replay.py` 独立。验收测试：不 import framework/core，只用 kernel+syntax 证一个定理并通过纯原语 replay——此测试现在应为红。
   - **实际落点**：`kernel/replay.py`（带假设规则的纯原语重放，`replay(prf) -> (Thm, holes)`，规则集封闭，宏行/未知规则一律拒绝）；`kernel/bootstrap.py`（纯 kernel 的引导宏注册表 `bootstrap_macros`：intros/trivial，只产原语 ProofTerm，与 `global_macros` 扩展槽并存不互吃；`expand_macro_proof` 展开宏行为纯原语流并立即用 replay 验证）。验收测试 `kernel/tests/replay_test.py` 11 例（含"import kernel 不拉 framework"的守卫）。`kernel/tests/` 已全目录零 framework 依赖（proofterm_test 的 load_theory 残留清除）。后续 verify 拆半（§7.1）、Thm 私有化（§7.3）在此基础上继续。
   - **check_proof → verify 拆半与更名（§7.1）**：kernel 侧只留 `replay.py`（带洞、纯函数、无回填/无 compute_only）；宏展开、信任集、报告组装归 core/verify.py。`ProofTerm.__init__` 不再隐式调宏 eval（z3 构造点执行 prover 代码的反例在此斩断）——求值成为显式动作。
   - **Thm 构造私有化（§7.3）**：白名单之外全库改造——tactic 的 ~40 处 goal 语句构造等 Goal 迁移到位后自然消失；eval 断言式（nat/macro、rewrite_goal.eval）改真推导或具名 oracle；items 的 6 处 axiom 装载收口 mk_axiom。
   - **thm_status/thm_error 迁出 kernel**（§7.4），kernel 七张表回归纯逻辑数据。
1. **conv 纯净化**：原语链接助手替代 `apply_theorem`；删 `auto_conv`；宏定义从 conv.py 挪到 macro.py。【已完成 2026-09-06，提交 b947a8a7 + 步骤1收尾】
   - **上半（b947a8a7）**：`framework/conv/inst.py`（`inst_theorem` 原语链接助手）落地；logic/conv.py 全部 9 处、integer/conv.py conv 层 2 处迁移；integer 域 8 个宏搬到 macro.py；纯度测试 `domains/logic/tests/conv_pure_test.py` 先红后绿。
   - **收尾**：`auto_conv` 删除，替代者 `framework/auto.py:norm_conv`——`norm()` 本身就返回真推导，auto_conv 的 'auto' 宏节点包装纯属多余，且展开时要重跑求解循环（隐藏非确定性）；17 处消费点（real/conv 12、proofrec 2、simplex_strict 3）全部改挂 `norm_conv`，条件重写前提（conds）仍由调用方显式传入。real 域 7 个宏搬进 `domains/real/macro.py`（`register_macro_method('real_norm')` 归位 method.py，斩断 `real/conv.py:31` 的 server 反向依赖）；real 注册测试 3 例就位。integer `int_neq_false_conv`/`int_gcd_compares` 改前提注入：符号事实（`|- c > 0`/`|- g > 0`）由调用方以 `mk_premise` 工厂传入，发射点移至 prover 层（`proofrec.py:mk_int_const_ineq_pt`），conv 本体零宏名；死代码 `int_const_compares`（integer）/`real_const_compares`（real）删除；测试 `domains/integer/tests/test_conv_premise_injection.py` 7 例（含无工厂必须断言失败的被动用例）。**顺带修复**：b947a8a7 把 int_neq_false_conv 的 `apply_theorem` 换成 `inst_theorem` 时漏了 import，该路径一调用即 NameError——本步补上并先红后绿。步骤0守卫测试 `testNoFrameworkLoaded` 改 subprocess 检查（原实现查主进程 sys.modules，pytest 合跑必假红）。全量验证 1786 条与快照一致（OK 零缩水、零翻转）。
   - **遗留（"计算即 oracle"债务，非本步范围）**：常数折叠/范型 conv——`nat_eval_conv`、`int_eval_conv`、`real_eval_conv`、`real_norm_conv`、`real_const_eq_conv`、`real_power_conv` 内的 `auto_solve` 前提——仍发射 level-0 oracle 宏节点。这不是"推导存在而被宏包装"（那类已消灭），而是计算本身无推导：推导化需先实现数值计算的重写推导（二进制数值计算），属独立机制工程。宏节点收敛的另一面：`norm_conv` 返回的推导内部含上述折叠节点，随该工程一并消失。
2. **`simp_sweep` 进 `core/macro/simp.py`**，斩断 tactic↔auto 环。【已完成 2026-09-06】`framework/macro/simp.py`（包名 framework 待步骤 9 整包改名 core，子目录=类别名先兑现，同步骤 1 先例）；simp tactic 顶部下行 import，simp 宏（macros/core.py）与 auto 宏的延迟 import 改挂新址。tactic.py 对 framework.auto 的引用清零——环消解；auto ⇄ simp_sweep 的**函数级**互递归（求解-化简-重试）是同层机制内在联系，保留单侧延迟 import，步骤 9 后同住 core。import 方向 lint `framework/tests/test_import_direction.py` 落地（tactic 不得引 auto；macro 层不得引 tactic 层）。回归：framework+kernel+domains 250 例、server 128 例全绿；全量验证 1786 条与快照一致（OK 零缩水、零翻转）。
3. **宏类瘦身为适配器**：证明逻辑抽到 macro 模块普通函数，宏类只剩名字/level/sig/转调。eval 平行双实现（apply_theorem）在此步删除，eval 一律派生自展开结果或显式声明+一致性测试（§7.3）。【已完成 2026-09-06】
   - **eval 收敛为不变量**（用户拍板全删）：11 个自定义 eval 删除——core.py 4 个（`apply_theorem`【审计点名双实现】、`rewrite_goal`【断言即求值】、`beta_norm`【正例，默认 eval 同为派生故一并删】、`auto_close`【恒等式】）+ nat 3 个（`nat_norm`/`nat_const_ineq`/`nat_const_less_eq`）+ `int_norm` + logic `imp_conj`/`imp_disj` + expr `prove_avalI`；eval 统一走宏基类默认（sorry prevs → 展开 → 取 th）。level-0 oracle（nat_eval/int_eval/int_const_ineq/real 系 5 个/z3）eval-only 形态即"显式声明"，保持不动；`real_norm` 的死 gpt（只抛 NotImplementedError）删除使其成为干净 oracle。不变量 lint：`framework/tests/test_macro_invariant.py`——有 gpt 的宏不得自定义 eval（AST 扫描）+ 全部宏模块 pyflakes 零 undefined name。
   - **适配器化（重灾区优先，用户拍板）**：real `relax_strict_simplex`（230 行：4 个 stage 方法 + 主体 → `_min_positive_proof`/`_geq_bounds_proof`/`_max_negative_proof`/`_leq_bounds_proof`/`relax_strict_simplex_proof`）；integer omega 家族 6 个宏（int_eq_macro/int_ineq/int_ineq_mul_const/int_multiple_ineq_equiv/omega_norm_int_ineq/int_eq_comparison → 同名 `_proof` 函数）。nat/logic/expr 的中小函数体保持现状，随步骤 8 需要时再抽。
   - **顺带修复潜伏 NameError**（b947a8a7 遗留，pyflakes 抓出）：integer 8 宏搬入 macro.py 时 `refl`/`rewr_conv`/`matcher`/`ConvException` 未随迁——omega 系 gpt 一调用即 NameError，此前被 proofrec 的宽 except 吞掉走降级路径而未翻转验证状态。修复后 `domains/integer/tests/test_omega_macro_paths.py` 3 例先红后绿。
   - **验证**：framework+kernel+domains 255 例、server 128 例全绿；全量 1786 条与快照一致（OK 零缩水、零翻转——nat_norm 的 eval 派生化未暴露任何此前被盲断言掩盖的失败）。
4. **method 注册表下沉**：`domains/*/method.py` 改走 core 注册 API，method 层改为读者。【已完成 2026-09-06】`framework/method.py`（包名 framework 待步骤 9 改名 core）承载注册表全机制：`Method` 基类、`global_methods`、`has_method`/`get_method`/`get_all_methods`/`get_method_sig`/`get_method_list_params`/`register_method`、`register_macro_method`、`norm_registry`+`register_norm`（nat/real/int 三类型接线随迁）。`server/methods/core.py` 切出三块（-108 行），只 import 自用名字——不做 re-export shim（§5.7 纪律 1）；`stable_state.py`/`methods/z3.py`/`methods/__init__.py`/`tests/method_test.py` 与 `imperative/imp.py`（2 处）全部直接改读 framework.method。4 个 domain（nat/real/integer/expr）的 method.py 注册改走 framework API——domains→server 反向依赖清零。lint 新增规则 `testTheoriesDoNotImportServer`（AST 扫描 domains/ + imperative/ 全树；白名单一项：`imperative/tests/imp_compile_test.py` 调 `monitor.validate_theory`，步骤 8 迁 core/verify 时移除）。`get_method_sig`/`method_list_params` JSON 形状零变化（注册表内容逐字节相同，前端零改动，§9.7 隐藏验收面通过）。
5. **`items.py` 下沉 `core/`**，消掉 framework→server 反向（报备后动，波及 `load_theory_cache`）。连带：syntax 层反咬（json_output/pyhol:376/parser/infertype/pprint）与 Context 归位（§6 增补表）——syntax 只许依赖 kernel+util。【已完成 2026-09-07】本步做 5a：`server/items.py`（968 行）git mv → `framework/items.py`（821 行纯条目模型：parse/display/export/edit）；`server/struct_recursion.py`（217 行）git mv → `framework/defcheck.py` 并吸收公理配方——`datatype_axioms`（state 投影/distinct/inject/induct/cases）与 `inductive_case_induct_axioms`（_cases/_induct）从 items 的 get_extension 抽出，配方代码逐字迁移。**mk_axiom 收口（§7.3）**：defcheck 内 `mk_axiom` 成为 axiom 假设规则在 kernel 外的唯一装载点，原 items.py 的 6 处 `Thm(...)` 装载（Axiom/Definition/Fun 方程/Inductive 引入规则 + 配方 3 处）全部改走它，items.py 不再 import kernel.thm.Thm；mk_axiom 住 defcheck 而非审计树字母写的 items.py——items 已依赖 defcheck 的检查函数，配方在 defcheck 内装配，入口放守门人模块依赖方向才成立。**消费方改读**：`framework/basic.py:13`（审计点名的反向依赖；`load_theory_cache` 只改一行 import，逻辑/失败语义/缓存键零变化）、`server/monitor.py`、`app/ide.py`、`syntax/json_output.py`；`server/tests/items_test.py` git mv → `framework/tests/items_test.py`（14 例随模块走，旧用例原样保留）。lint 新增规则 `testFrameworkDoesNotImportServer`（framework/ 全树 AST 扫描）——framework→server 反向依赖从此构造上不可能。**孤儿 .pyhol 清点（§9.2 顺带项）**：`library/` 与 `imperative/programs/` 之外全库无散落 .pyhol/JSON 遗物，无需删除；`_lib_dirs` 搜索路径已只剩 `library/`。**遗留（5b，下轮）**：syntax 层反咬（json_output import framework.basic+items、pyhol:376 延迟 import server.stable_state、parser/infertype/pprint 反咬 framework）与 Context 归位。验证：framework+kernel+domains 271 例、server 114 例、imperative+syntax 74 例全绿；全量验证 2200 行与快照逐字节一致（OK 零缩水、零翻转）。
   - **5b【已完成 2026-09-07】syntax 反咬清理 + Context 归位**：
     - **json_output.py 删除**：`JSONTheory` 全库零引用（死代码），git rm；其“导出服务”职责不存在——现役导出走 `pyhol.export_pyhol`（app/ide.py:189 直调）。
     - **pyhol.py:376 断 server**：延迟 import `server.stable_state.BACKWARD/FORWARD` 改为 pyhol 自持方向表 `_BACKWARD_METHODS`/`_FORWARD_METHODS`（与 `_METHOD_POSITIONAL` 同模式的方法元数据自描述），一致性测试 `syntax/tests/pyhol_test.py` 锁死与 stable_state 的漂移 + AST 断言 pyhol 不 import server/framework/domains。
     - **pprint.py 断 framework.logic**：`logic.is_if`（两处，均为 `is_comb("IF",3)` 纯形状判断）改为本地谓词 `_is_if`；顺带删零引用的 `util_nat` 延迟 import。
     - **parser/infertype 接口反转（Context 归位）**：`type_infer`/`infer_printed_type`/`parse_term`/`parse_thm`/`parse_inst`/`parse_named_thm`/`parse_term_list`/`parse_args`/`parse_proof_rule` 全部加 `ctxt=None` 纯数据参数（svars/vars/defs 三表），syntax 内 `context.ctxt` 全局读点清零（infertype 9 处读点、parser vname、死 import `syntax.tests.parser_test` 一并删除）。**性能关键**：共享单例 Transformer + `_bind_ctxt` 换引用（O(1)）——绝不按 ctxt 重建 Lark 解析器（grammar 编译是秒级，每个 parse 重建曾把回归拖到分钟级，已修复并验证 10s/批）。**kernel Term(str) 钩子重绑**：`kernel/term.py:term_parser` 由 framework/context.py 重绑到 ctxt 感知包装器（framework→syntax 方向合法，syntax 不引 framework）；infer_printed_type 里零使用的 `from framework.context import Context` 死 import 删除；infertype 的 copy/Term/term/unionfind 四个死 import（HEAD 旧账）顺手清。
     - **framework 侧适配**：`framework/context.py` 提供 `parse_term`/`parse_thm`/`parse_inst`/`parse_named_thm`/`parse_term_list` 包装器（全局 ctxt 注入 parser）；items.py（4 处，fun 方程装载曾因此静默失败——`item.error` 吞掉后理论缺 `nat_plus_def_1`）、server/methods/core.py（12 处，全在 fresh_context 块内）、server/server.py（parse_init_state/parse_proof）、server/stable_state.py（create）、测试（parser_test/infertype_test/pprint_test/logic_test test_macro/method_test run_test）全部改走包装器。**Context 归位结论**：Context 类与全局单例仍住 framework/context.py（纯数据容器，syntax 不再读它）——完整迁移 `core/context.py` 留到步骤 9 整包更名时一并做，避免本轮再动 20+ import 点。
     - **遗留**：parser.py:374/`pprint.py` 的 `domains.nat.interval` 延迟 import（nat_interval 语法糖 + interval AST 打印）——需要把 mk_interval/is_interval 的纯形状半边下沉 syntax、conv 半边留 domain，属 interval 机制重构，随步骤 6 prover→solvers 一起处理。lint 规则 `syntax 只依赖 kernel+util` 因此**未在本轮落地**（interval 两处会立即红），记入步骤 6 完成项。
     - 验证（分批，每批 30s 内，用户约束）：syntax 50、framework 99、kernel 130、logic 27+conv_pure 5、integer 12、real 5、imperative 26、server method 69+server 35+trans_type_cases 10+items 14——全绿。全量 library 验证按用户指令跳过；理论装载经 nat spot-check（`nat_plus_def_1` 在位）+ server_test 35 例库级重放覆盖。
6. **prover→solvers 解散**：纯算法核留 `solvers/`，领域胶水回 `theories/`；z3 宏的 wrapper import 改按名注入。【已完成 2026-09-07】**整包 git mv `prover/` → `solvers/`**（含 tests、proofrec.md/proofrec_spec.md 文档，代码零逻辑改动），全库 import 改写（framework/basic 的 sympy/omega 装载、monitor、methods/z3、imp、imp_compile、solvers 内部互引、14 个测试文件、2 份 .md 的路径），sat_test 里硬编码的 `prover/tests/pelletier.json` 数据路径同修。**z3 按名注入（审计【§6 增补表】）**：`framework/macros/z3.py` 不再模块级 import 求解器——定义 `Z3Backend` 注入槽（z3_loaded/check_z3/solve），`solvers/z3wrapper.py` 末尾装载时回填（`_inject_z3_backend`）；宏 eval 读槽，`server/methods/z3.py` 同改读槽；monitor `__main__` 的 `check_z3=False` 开关改拨槽位；双向装载顺序验证（先宏后 solver / 先 solver 后宏均正确）；imp.py 的死 z3wrapper import（HEAD 已死）删除。**z3wrapper 定位（用户拍板）**：实验性，不接入真实 verify——solve_and_proof/proofrec 重建路径保持现状，只服务于 smoke 测试与后续实验。**fologic 纯化**：死 import（framework.logic/Term/Implies，HEAD 旧账）删除——fologic 从此不依赖任何上层。**lint 新增两条**：`testSolversDoNotImportServer`（solvers 全树）+ `testSyntaxDoesNotImportUpperLayers`（syntax 生产代码不得 import framework/server/domains/solvers，tests 豁免）。**步骤 5b 遗留填坑（用户否决新模块方案）**：不造 `syntax/interval.py`——parser 的 nat_interval 语法糖两行内联（`Const("nat_interval", TFun(...))`，同 comp_fun 风格）、pprint 的分支改 `t.is_comb('nat_interval', 2)` 一行形状判断；domains/nat/interval.py 原样不动；{m..n} 解析+打印冒烟验证（iterate 理论）。**遗留（记入步骤 9 决策）**：proofrec/omega/simplex/simplex_strict/sympywrapper 仍 import domains+framework（项胶水与推导装配未拆）——审计原案"领域胶水回 theories"需要把这 5 个文件的证明装配半边拆出，量级大且当前不阻塞依赖律（solvers 是旁路服务、无循环），按用户时间约束推迟到步骤 9 更名时一并评估。solvers/tests 8 个文件是 5b 接口反转的漏网模式（set_context+裸 parse_term），全部改走 context 包装器；simplex_test/proofrec_test/z3wrapper_test 为注释收藏夹（0 例）保持现状。验证（分批，每批<30s，用户约束）：solvers 批（fologic/sat/tseitin/congc 17、omega 17、auto 1、sympy 4、simplex_strict 1、proofrec_unit 6、smoke 10）、framework+kernel 231、domains 42、server 45+69、imperative 26、syntax 50、lint 6 条——全绿。全量 library 验证按用户指令跳过；z3 注入链以 logic_base 真求解冒烟覆盖（solve('A --> A') = True）。
7. **server 5 处手写宏名 + 原语入口**：走受检通道（审计【B】【C】【D】）。【已完成 2026-09-07】实际现状核对：手写宏名共 2 处（步骤 2/3 期间 methods 层已陆续收口过一批，非审计写作时的 5 处）。
   - **【B】`rewrite_fact`/`rewrite_fact_sym`**：`methods/core.py` 的 rewrite_fact 方法先 dry-run tactic 再手写 set_line 两分支——改为直接 `state.apply_forward(id, tactic.rewrite_fact_forward(sym=...), args=...)`：行规则取自 tactic 的 ProofTerm（`apply_forward` 的既有契约），dry-run 与落行合一，删掉复制的 set_line 双分支与手动 `_find_and_close`。
   - **【C】elim 的手写 `assume` 行**：`assume` 是 15 原语之一（`kernel/thm.py:primitive_deriv`），ProofState.set_line 本身走 check_proof 受检——审计要求的是"有规范的入口"，补 `ProofState.assume_line(id, prop)` 显式原语入口（文档注明：ProofState 外唯一写 assume 行的地方，set_line 的 check_proof 即内核校验），elim 改走它。无需 ContextTactic——assume 无搜索无匹配，包一层 tactic 只会重复 set_line 的校验。
   - **【D】z3 method**：`state.set_line(id, 'z3', ...)` 手写宏名改为 `state.apply_macro(id, 'z3', prevs=prevs)`——注册表校验 + _finish_backward 显式关门，z3 作为 level-0 oracle 宏走与其他宏同一受检通道（solve 检查仍留在 method 里：那是 oracle 的"求值前断言"，与落行无关）。**实测**：if_demo（1 处 z3）与 call_demo（3 处 z3，8/10 定理重放，余 2 个为库存故意留 sorry 的 UNPROVED VC，HEAD 同样不可回放——非回归）全走新通道重放通过。
   - 验证（分批，每批<30s）：method 69、server 45、imperative 26、framework 101 全绿。
8. **验证管线收口（§7.1/§7.4）**：`validate_theory` 四态判定迁 `core/verify`，monitor 死代码（check_theory/__main__ 引用 load_json_data、theory_cache['master']）删除，`validate_library.py` 对接 verify 的新洞报告（缓存机制不变）。同步修正 §7.4 的两处状态判定偏差。【已完成 2026-09-07】`framework/verify.py`：四态判定（VALID/DEP_FAILED/STEP_FAILED/UNPROVED）+ AXIOM 展示值 + 缓存读写（格式/键不变：.cache/<theory>.json 按源 mtime）。**重放注入**：steps→行的翻译住 method 层（StableProofState），framework 不得 import server——`set_replay_fn(fn)` 注入槽由 `server/stable_state.py` 模块级回填（`_verify_replay(item, name) -> gaps`），未注入时 validate_theory 诚实报错。**两处偏差修正（§7.4）**：(1) UNPROVED 计入失败态——依赖表 `_FAILED_STATES = {STEP_FAILED, DEP_FAILED, UNPROVED}`，无 steps 而依赖 UNPROVED 的定理现在正确判 DEP_FAILED（旧代码会继续重放）；(2) 跨文件依赖——`_import_statuses` 沿 import DAG 递归读已缓存理论的状态，引用别文件失败定理不再漏判。**实测**：nat/logic_base/set 三理论新旧四态分布逐类一致（nat: VALID 49/UNPROVED 37/DEP_FAILED 134/STEP_FAILED 5/AXIOM 1）；合成用例（临时理论引用 nat 的 UNPROVED `add_Suc_right`）判 DEP_FAILED 并给出 `depends on add_Suc_right which is UNPROVED`——两处修正均生效且不误伤健康依赖。**monitor.py 整文件删除**：唯活函数 validate_theory 已迁；check_proof/check_theory/__main__ 全为死路径（`basic.load_json_data`、`theory_cache['master']` 早不存在，一调即崩）。消费方改读：`app/ide.py`（verify.validate_theory）、`validate_library.py`（+stable_state 装载行）、`imperative/tests/imp_compile_test.py`。**lint 白名单**：步骤 4 承诺的 monitor 项已消失；imp_compile_test 因装配 import（server.stable_state 接 replay）重回白名单，注释更新为步骤 9 server→method 更名时移除。**遗留（§7.1 完整拆半，未做）**：`ProofTerm.__init__` 隐式调宏 eval 的显式化、check_proof→replay/verify 的 kernel/core 命名拆分、thm_status/thm_error 表迁出 EmptyTheory——这三项是 Thm 私有化与 Goal 迁移的前置，与步骤 9/Thm 私有化轮合并处理（本轮不动 check_proof，缓存格式不动）。验证（分批<30s）：framework 101、server 45+69、imperative 26、syntax 50、lint 6 条全绿；库验证按用户禁令跳过，三理论 force 抽样等价确认。
9. **server 拆分 + 更名（§2/§5.7）**：items/defcheck/verify 的逻辑已在步骤 5/8 下沉 core，此步做纯更名与拆分——`server` 剩余定名 `method/`（methods/proofstate/stable），`app` → `backend`，`server.py` 并入 tactic 侧 goal 构造。更名一步到位（改名与挪位同步，不留过渡态），全量单测 + 前端 API 路径核对。
10. **REPL 落地（§5.8）**：`repl/` 薄壳接 method 通道与 verify 反馈；验收 = 不启动 backend/frontend 也能交互完成一个库级定理的证明与验证。**新功能，最后考虑**——前 0-9 步全部完成、架构稳定后再动。

每步加 import 方向 lint（AST 扫描），白名单逐步缩短——这就是 `AGENTS.md` 第 4 条"新增引用先查 import 方向"的自动化。
lint 同时断住两条铁律：kernel 外无裸 `Thm(` 构造（白名单见 §7.3）、kernel 外不出现 Goal 类型（铁律 2 的镜像）。

信任模型全程不动：15 原语一行不碰，任何中间形态都有 `check_proof` 兜底。这是敢大改的底气。
（重命名落地后，兜底的名字就是 verify。）

---

## 9. 重写的前置条件与盲区（2026-09-06 第三轮调研）

第 0-8 节是目标态。本节记录**达成它之前必须回答的现实问题**——底层事实大都是原作（Bohua Zhan）遗留的：证明未完成、分层未切好，该分开的混在一起、该聚合的散在各处。重写的对象正是这团东西，但每一条都要在动第一行代码前想清楚怎么应对。

### 9.1 库验证债务：基线快照，而非待修清单

`validate_run.log` 现况（2123 条定理行）：**OK 1449，STEP_FAILED/DEP_FAILED 639，FAIL 36**。
失败按理论分布：trig_sin_cos 一家 STEP_FAILED 36 + DEP_FAILED 302（36 个失败根因雪崩出 302 个依赖失败）；transcendentals 151、gcd 40、nat 38……

**定性：这是内容债，不是机制 bug**——原作就没有证完这些理论（DEP_FAILED 的瀑布正是"依赖失败"状态的正常传播）。**重写不负责补证它们**。

因此验收基线不是"全绿"，而是**快照 + 零缩水**：

- 重写开始前，把当前每理论 × 每定理 × 状态的完整清单存档（`validate_run.log` 即快照）。
- 每步迁移的验收 = **OK 集不缩水**：任何原先 OK 的定理，迁移后必须仍 OK（允许状态更精确，不允许退化）；原先失败的定理**允许**因 proof 形状变化重新归类，但失败集合不减、不增不减地对照解释——每个状态翻转（无论变好变坏）都要能归因到本步的哪个具体改动。
- conv 纯净化（步骤 1）改变导出证明形状后，原先失败的定理可能换个原因失败——这是预期噪声，靠"逐翻转归因"消化，不追求全绿。
- nat/gcd 里的 STEP_FAILED 若在重写中被发现是**机制性**的（策略/宏的 bug 而非缺证明），按 AGENTS 规则修复并补"之前失败现在能过"的主动用例——这是重写的红利，不是义务。

### 9.2 库文件与理论名的分裂

`library/` 44 个 .pyhol 文件 vs 44 个理论名基本对应，但存在旧理论残留目录（`library/` 之外顶层散落的孤儿 .pyhol/JSON 遗物）。重写动 `load_theory_cache`（步骤 5）时**顺手清点**：删除孤儿文件、确认 `_lib_dirs` 搜索路径只剩 `library/`（`imperative/programs/` 隔离机制保持）。

### 9.3 imperative/ 的位置：计划说"不动"，但它依赖 domains

§2 树里 imperative 标"不动"，实际上 `imperative/imp.py` import `domains.nat`/`domains.function`/`domains.logic`、`framework.conv`、`framework.logic`——**framework→theories→imperative 三层更名它全要跟着改 import**。所谓"不动"只是"不重排它的内部结构"，import 面必须随步骤 1-9 一起更新。它是 `theories/` 的第 7 个垂直切片（hoare 领域），唯一特殊点是自带前端路由（`app/imperative.py` → `backend/`）。

### 9.4 util 的双向依赖：kernel 与 theories 各要一半

- `util/typecheck.py`、`util/name.py`：纯工具，kernel 依赖它们——这两个是 kernel 的合法伙伴。
- `util/function.py`、`util/list.py`、`util/poly.py`、`util/set.py`、`util/string.py`：依赖 kernel+syntax，**真身是 theories 层的项工具**（nat/real 的多项式、列表辅助）。
- **拆分**：纯工具留 `util/`（与 kernel 同级）；项工具下沉到使用它们的 `theories/` 对应包。否则铁律 1"kernel 不 import 任何项目模块"在 util 上留一个永久的解释成本。

### 9.5 syntax 的"只依赖 kernel+util"仍需内部清理

铁律 1 说 kernel+syntax 独立可用，但 syntax 现含两块不同的东西：
- **真语法层**：parser/printer/numeral/operator/settings——kernel+syntax 独立性靠它们。
- **序列化层**：`pyhol.py`（.pyhol 读写）、`json_output.py`（导出 JSON）——它们编排 items/stable_state，真身是 core 的服务。
- 拆分方向：序列化归 `core/`（`.pyhol` 的解析/导出走 `core/pyhol.py`），syntax 只留语言解析与打印。`settings.py` 的全局可变状态（`global_setting` 上下文管理器遍布全库）随迁——它是隐藏的跨层通道，kernel/thm.py 因 unicode 打印才 import 它，kernel 断奶时这根线必须断（打印函数住 syntax，kernel 内部断言消息不走 settings）。

### 9.6 缓存与状态的迁移契约

`.cache/*.json`（状态缓存）与 `theory_cache`（解析缓存）是重写期间每步的快验手段，但**缓存键是文件 mtime**——更名/拆分会让所有理论"看起来变了"，缓存全失效一次（可接受，一次性全量重验）。规则：迁移中间态**不动缓存格式**；步骤 8 收口 verify 时才允许换格式（连 `--force` 语义一起重定义）。

### 9.7 前端契约

backend 更名后 `/api/*` 路径**不变**（vite 代理 8080→5000 零改动）；但 method 注册表下沉（步骤 4）会改变 `get_method_sig`/`method_list_params` 的 JSON 形状，前端 ProofQuery 渲染依赖它——这是步骤 4 的隐藏验收面，须同步前端。`#[N]` 稳定 ID 格式是前后端共同契约，**重写全程冻结**。

### 9.8 测试基线的重组

AGENTS 规定"测试跟模块走"——目录更名即测试搬家。迁移每步的验收 = 新位置的测试全绿 + lint 白名单缩短；**不合并、不删改旧用例**（防回归是契约）。全量 library 验证仍然很贵：每步跑一次全量、对照 §9.1 快照（OK 集零缩水 + 逐翻转归因），日常开发只跑相关模块回归。

### 9.9 迁移期双名期

`framework`→`core`、`server`→`method` 等更名期间，git 历史/AGENTS.md/7 章手册里的旧名大量存在。处理：**代码一步到位不留兼容 shim**（§5.7 纪律 1），文档（AGENTS.md、manual/、README）在步骤 9 一次性同步更名，中间各步的 commit message 用"旧名（现 X）"标注。不写任何 `framework = core` 的别名过渡层——过渡层本身就是"运行时小聪明"。

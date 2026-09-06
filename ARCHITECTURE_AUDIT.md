# holpy 架构重写目标

本文件记录 2026-09-05 架构讨论的结论，作为 holpy 完全重写的目标参照。
原依赖审计的发现已并入第 6 节"当前贴错层的修正"。本文件只记录设计，未修改任何代码。

---

## 0. 组织定律：严格可剥离分层

全系统按**推理方向**切成一条全序。每一层都是独立可用的完整子系统；从顶上剥掉一层，下面照常工作。

| 剥掉 | 剩下仍然可用 |
|---|---|
| L3 server / method | kernel + core + theories + tactic —— 程序化驱动 goal，无 UI |
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
| **matcher** | 模式匹配服务：模式网取候选 + 精确匹配确认（两步） | `Term -> ...` | 不证任何东西 |
| **theories** | 领域特定内容（垂直切片） | 每领域 conv/macro/tactic 实例 | 不 import server |
| **solvers** | 纯算法核（sat/omega/simplex/z3/tableau） | 只依赖 kernel+syntax | 不碰 Thm 构造以外的事 |

**全序**：kernel < conv < macro < tactic < method。matcher、solvers 是旁路服务。theories 是内容（按文件归属各层，内部同序 conv < macro < tactic < method）。

---

## 2. 目标文件架构

```
holpy/
├── kernel/              【L0】正向原语，Thm 唯一来源。独立 = 完整 HOL
│   ├── type.py  term.py  term_ord.py  thm.py  theory.py
│   ├── macro.py          Macro 基类 + global_macros 注册表（宏=内核扩展槽）
│   ├── proofterm.py  proof.py      日志数据结构
│   └── replay.py         纯原语 replay（校验就这一个函数）
│
├── core/                【L1】正向推理机器 + 服务。不识 goal。剥掉 L2/L3 仍可用
│   ├── conv/            等式构造：Term + 显式前提定理 -> Thm(t≡?)
│   │   ├── basic.py     Conv 协议 + refl/beta/eta/rewr/then/top_sweep/arg/binop
│   │   └── inst.py      原语链接助手（替代 conv 里发射 apply_theorem 宏节点）
│   ├── macro/           命名正向步骤：(args, prevs) -> Thm。可用 conv
│   │   ├── registry.py  注册 + level + 展开器
│   │   ├── logic.py     intros/apply_theorem/resolution/rewrite_*（领域无关）
│   │   └── simp.py      simp_sweep + simp 引擎（从 tactic.py 迁回；它是宏展开机制）
│   ├── matcher.py       模式匹配服务（两步：候选网 + 精确确认）
│   ├── auto.py          global_autos 分发器
│   ├── items.py         .pyhol 条目模型（从 server 迁回，消掉 framework->server 反向）
│   └── basic.py         .pyhol 加载 + theories 动态激活
│
├── theories/            【内容】L1/L2 的领域特定实例，垂直，镜像 library/*.pyhol DAG
│   └── <theory>/        logic/ nat/ function/ integer/ real/ expr/
│       ├── conv.py       该领域的等式构造（纯：不搜索、不发射宏名）
│       ├── macro.py      该领域的宏 + 注册（原 conv.py 里的宏定义挪回这里）
│       ├── tactic.py     该领域的拆法（可选）
│       └── method.py     注册走 core 注册 API（不 import server）
│
├── tactic/              【L2】逆向翻译层。彻底脱离：HOL 没它也工作。剥掉 L3 仍可用
│   ├── goal.py          Goal + goal 树（全系统唯一定义点）
│   └── steps.py         rule/cases/induct/intro/accept = 形状分析 + 宏名+参数
│                        （无 THEN/ORELSE/REPEAT，无推导逻辑）
│
├── solvers/             纯算法核：sat/omega/simplex/z3/tableau。只依赖 kernel
│                        （omega 的项胶水 strip_plus 等回 theories/integer）
│
├── server/              【L3】UI 抽象。剥掉它 tactic 系统仍可用
│   ├── methods/         method 通道：apply_tactic/apply_macro/apply_forward
│   └── proofstate.py    行树 + gap，声明式 have/by/with 唯一组合处
│
├── library/             .pyhol 理论数据（不动）
└── imperative/  app/  frontend/    不动
```

**命名**：原 `framework`（太抽象）→ `core`；原 `domains`（太抽象）→ `theories`；`library` 保留。类别仍是现有的（kernel/conv/macro/tactic/matcher/method），不发明新类别。

---

## 3. 依赖律

```
kernel（含宏注册表 = 内核扩展槽）
  ↑
core:  conv < macro           matcher / search  服务层，只依赖 kernel+syntax
  ↑
theories/<t>/conv.py, macro.py    L1 内容，镜像 .pyhol DAG
  ↑
tactic + theories/<t>/tactic.py   L2
  ↑
server + theories/<t>/method.py   L3 注册

solvers  旁路纯算法，被 theories/*/macro.py 使用，不 import 任何领域
```

静态铁律（lint 强制）：

1. `kernel` 不 import 任何项目模块；`kernel + syntax` 独立即可正向证定理。
2. `core/` 任何文件不得出现 Goal 类型；`tactic/` 之外不存在 goal 概念。
3. `core/conv` 不得搜索、不得出现宏名；前提定理永远显式传入。
4. `core/macro` 不得 import `tactic`。
5. `tactic` 可用一切正向资产；正向层永不 import `tactic`。
6. 领域对框架的唯一入口是 `core/basic.py` 按 `.pyhol` 元数据动态加载 + 注册表按名解析。

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

kernel、conv、macro、tactic、matcher、theories、method、solvers 就是全部。此前一度造出的 rules/steps/record/forward/backward 全是多余的，已废弃。

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

回归范围：conv 纯净化（换 apply_theorem）改变导出证明形状，须全量 `validate_library.py`；其余跑 `server/tests/` + `framework/tests/`。

---

## 7. 信任模型

TCB = 15 条原语 + 每个证明显式列出的 oracle 名字。

- kernel 永远不执行 framework 代码。
- `check_proof` 拆两半：core 侧的展开器（认识宏，把日志展开成纯原语流）+ kernel 侧的 `replay.py`（只跑原语；跑通则 Thm 合法——Thm 的抽象类型本身就是校验）。
- z3/sympy 这类 oracle 永不展开，按名写进该证明的信任报告。oracle 是按名点名的信任扩展，报告里写清楚每个证明依赖哪些 oracle，诚实且可审计。

---

## 8. 迁移顺序（小步，每步用可剥离性测试断住）

0. **内核断奶**（最痛但最本质，先做）：`Macro` 基类、`global_macros`、宏名解析、eval 校验若依赖 framework 则正名为"内核扩展槽"或迁出；`replay.py` 独立。验收测试：不 import framework/core，只用 kernel+syntax 证一个定理并通过纯原语 replay——此测试现在应为红。
1. **conv 纯净化**：原语链接助手替代 `apply_theorem`；删 `auto_conv`；宏定义从 conv.py 挪到 macro.py。
2. **`simp_sweep` 进 `core/macro/simp.py`**，斩断 tactic↔auto 环。
3. **宏类瘦身为适配器**：证明逻辑抽到 macro 模块普通函数，宏类只剩名字/level/sig/转调。
4. **method 注册表下沉**：`domains/*/method.py` 改走 core 注册 API，server 改为读者。
5. **`items.py` 下沉 `core/`**，消掉 framework→server 反向（报备后动，波及 `load_theory_cache`）。
6. **prover→solvers 解散**：纯算法核留 `solvers/`，领域胶水回 `theories/`。
7. **server 5 处手写宏名 + 原语入口**：走受检通道（审计【B】【C】【D】）。

每步加 import 方向 lint（AST 扫描），白名单逐步缩短——这就是 `AGENTS.md` 第 4 条"新增引用先查 import 方向"的自动化。

信任模型全程不动：15 原语一行不碰，任何中间形态都有 `check_proof` 兜底。这是敢大改的底气。

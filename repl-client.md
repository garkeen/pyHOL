# holpy REPL 使用与设计说明（给 AI / 自动化使用）

本文件面向**用工具调用驱动的 AI**（不能保持交互式会话），也适用于人类。
REPL 位于 `repl/`，只依赖 `kernel/core/method/syntax`，**不 import 前后端**。

> 重要：REPL 是开发工具，不是固定契约。**你在使用中发现的痛点，可以直接改 `repl/`**
> 然后继续干活——本文件末尾列出的问题就是前几轮这么改出来的。改完请补
> `repl/tests/repl_test.py` 的用例。

---

## 1. 为什么需要非交互模式

AI 通过工具调用执行命令、等待结果。一旦程序停在 `input()` 等输入，整个流程会卡死。
因此 REPL 必须提供**非交互**路径；`holpy>` 交互提示符只给人用。
`main()` 用 `sys.stdin.isatty()` 判断：stdin 不是终端时**永不进入交互循环**。

三条可用路径（都不会阻塞）：

### 1.1 管道 / heredoc（一次性、最简单）

```bash
python -m repl.repl --theory nat <<'EOF'
var x nat
var y nat
goal x + Suc y = Suc (x + y)
← induct x nat_induct goal=0
← rewrite nat_plus_def_1 sym=false goal=1
← intro m goal=2
← rewrite nat_plus_def_2 sym=false goal=5
← rewrite source=prev goal=6 facts=[4]
check
export
EOF
```

退出码：`0` 无失败且无剩余目标；`1` 有步骤失败或还有 open goal。

### 1.2 脚本文件

```bash
python -m repl.repl --script steps.txt
```

### 1.3 常驻服务 + 客户端（推荐：理论只加载一次）

冷启动要加载理论（秒级），常驻可跨多次工具调用复用：

```bash
# 后台起一次（跨工具调用存活）
python -m repl.repl --serve --port 5599 --theory nat

# 之后每批命令一次客户端调用
python -m repl.client --port 5599 "var x nat" "goal x + Suc y = Suc (x + y)" "check"
python -m repl.client --port 5599 --stdin < batch.txt
```

- 服务端只绑 `127.0.0.1`，协议是一行一个 JSON 请求/回复。
- 客户端退出码：`0` 成功、`1` 有失败或剩余目标、`2` 连不上服务端。
- 实测第二次请求 ~0.27s（对比冷启动 ~4s）。
- **做完工作记得关掉后台服务**，不要留常驻进程。

---

## 2. 命令

| 命令 | 说明 |
|---|---|
| `theory NAME` / `load NAME` | 加载理论并设置解析上下文 |
| `var NAME TYPE` | 声明上下文变量；**类型可含空格**（`var P 'a => bool`） |
| `goal PROP` | 以 `PROP` 开始证明，稳定 id `#0` |
| `goals` / `g` | 显示 open goals |
| `all` | 显示全部 `#[N]` 项（fact 与 goal） |
| `methods [SUBSTR]` | 列出当前理论可用方法（受 `limit` 约束）；列出的名字就是步骤能用的名字 |
| `theorems [-v] [SUBSTR]` | 列出作用域内定理名；`-v` 附命题 |
| `thm NAME` | 显示一条定理的命题、假设、schematic 变量（→ `param_x=`） |
| `<步骤行>` | 直接粘贴 `.pyhol` 步骤，如 `← rule iffI goal=0` |
| `undo` | 撤销最后一步（从头重放重建，坏步骤不留痕） |
| `export` | 输出 `.pyhol` proof 块（**自动重新生成 `#[N]` 注解**） |
| `check` | 打印 `VALID` 或剩余目标数 |
| `trust NAME,...` / `trust +N` / `trust -N` | 设置/追加/移除会话信任集 |
| `help`、`quit`/`exit`/`q` | |

步骤行与 `.pyhol` 完全同构，可直接从库里复制粘贴。

---

## 3. 关键语义

### 3.1 trust 由 shell 显式传入

内核**不做任何按需加载**：`core/verify.py` 的 `verify(..., trust=...)` 默认空集，
调用方显式传入。REPL 默认空集，并在切换理论/新建 goal 时把它传给
`StableProofState`。

- **显式调用 level-0 oracle 方法（如 `← z3`）会自动授权**该名字：宏经受检通道
  `apply_macro` 进入，这一动作本身就是授权。
- `trust` 命令用于**回放**已存 oracle 行的场景。
- 库验证侧：`validate_library.py` 自己定义 `LIBRARY_ORACLES` 并
  `trust=LIBRARY_ORACLES` 传给 `validate_theory`——这是验证器自己的选择，不涉及内核。

### 3.2 `#[N]` 注解只是显示，但会强制 sid

注解在回放时变成 `new_ids`，**若与引擎自动编号不一致会强制覆盖 sid**，从而
挪动后续 `goal=` 的指向。不确定时**省略注解**最安全；`export` 会生成正确注解。

### 3.3 稳定 id 的坑

sid 按 **命题值（prop + hyps）去重**：不同分支里相同的命题会共用同一个 sid，
`next_sid` 不递增。所以手写 `goal=N` 时不要凭直觉递增，每步后看 `all` 输出。

### 3.4 `loc` 是项树路径

`rewrite ... loc="1"` 等：`"0"` 函数部分、`"1"` 参数部分、`"0.1"` 函数的参数。
对 `A ⟷ B`（内部是 `=`）而言，左操作数在 `"0.1"`、右操作数在 `"1"`。
**`loc` 无法进入 `λ` / 量词体**（抽象不是 `Comb`）。

### 3.5 `rewrite` 会抓最外层匹配

`(P⟷¬P)⟷false` 上直接 `rewrite iff_conv_conj_disj` 会把整个目标当 `A⟷B`。
需要 `loc` 指定子位置。

---

## 4. 常见技巧（手工证明）

- `intro` 会**一次引入所有嵌套蕴含**：`A ⟶ B ⟶ C` → 事实 `A`、`B`，目标 `C`。
- `rule` 是 stripped-conclusion 匹配；蕴含形目标要**先 `intro`** 再 `rule`。
- `cut "P" goal=N`：插入中间命题，它**同时是可引用 fact**（证明主目标时可用）。
- 用等式改事实：`→ rewrite target=fact <thm> goal=N facts=[eq, fact]`。
- 用已有等式改目标：`← rewrite source=prev goal=N facts=[eq]`（**不支持 `sym`**）。
- 条件重写 if 项：`← rewrite if_P goal=N facts=[<条件事实>]`。
- 显式 oracle / 自动化（`z3`/`norm`/`simp`/`auto`）在基础库中**禁止使用**。

---

## 5. 方法与证明管线（写证明前必读）

### 5.0 先查，不要猜

证明要用到依赖库的定理。**先查再写**：

```
methods rewrite              # 这个方法是否可用、参数是什么
theorems less_eq             # 作用域内有哪些名字含 less_eq
theorems -v less_exist       # 连命题一起看
thm less_exist               # 完整命题 + schematic 变量（param_m/param_n/param_d）
```

`theorems`/`thm` 查的是**当前理论闭包**里 `theory.thy` 真正登记的定理
（kernel 的定理表），即 `rule`/`forward`/`rewrite ... theorem=` 能引用的全集；
`methods` 查的是受检注册表，且已按每个方法的 `limit` 过滤掉当前理论还用不了的。
两者都是**能用什么**的真值来源，不要凭记忆拼名字或参数。

### 5.1 方法表（`.pyhol` 步骤能用的名字）

`params` 是步骤行的具名参数；`schematic vars` 用 `param_<名字>=...` 传入。

| 方法 | params | 语义 |
|---|---|---|
| `rule` | theorem | 逆向应用定理（结论与目标合一，前提生成子目标） |
| `forward` | theorem | 前向推理：新增一条事实行（省略 theorem 则用已有事实作用） |
| `resolve` | theorem | 由 `~A` 与事实 `A` 得 `false` |
| `accept` | theorem | 用定理直接关门（结论合一、前提匹配假设，无子目标） |
| `apply_prev` | - | 用之前的蕴含/forall 事实作用到目标 |
| `intro` | - | 一次引入所有嵌套蕴含的假设与 forall 变量 |
| `elim` | names | 消去 exists 事实，得到见证与实例 |
| `induct` | theorem, var | 归纳（`nat_induct` 等）；可带假设存在时使用 |
| `var` | name, type | 新建上下文变量 |
| `cases` | case | 分情况（case 为命题或结构） |
| `type_cases` | case | 归纳数据类型上的分情况 |
| `cut` | cut_goal | 插入中间命题；它**同时**是新目标和可引用事实 |
| `rewrite` | theorem, sym | 重写目标或事实；无 theorem 时用等式事实（`source=prev`） |
| `inst` | s | 有 facts 时实例化 forall 事实；否则给 exists 目标提供见证 |
| `assumption` | - | 目标命题就是自身假设之一时关门 |
| `refl` / `eq_intro` / `trans` | (-) / (-) / s | 自反 / 双向证等式 / 中间项 |
| `unfold` | theorem, sym | 展开（`sym=true` 折叠）定义 |
| `norm` | - | 用该类型注册的归一化器归一化等式目标 |
| `nat_norm` | - | nat 等式归一化（`level=10` 领域计算，**确定性**，非 oracle） |
| `nat_const_ineq` | - | nat 常量不等式判定（`limit=bit1_neq_one`） |
| `simp` | - | 用本理论 `hint_rewrite` 迭代重写（基础库禁用） |
| `auto` | - | 通用自动化（基础库禁用） |
| `z3` | - | level-0 oracle，需 trust（基础库禁用） |

### 5.2 tactic 与 method 的关系

- **method**（`method/methods/core.py`）是 `.pyhol` 步骤调用的一层，也是受检通道。
- **tactic**（`tactic/steps.py`、`tactic/goal.py`）是更底层的 L2 逆向翻译层：
  每个 Tactic 把 goal 形状翻译成「宏名 + 参数（+ 子目标）」，本身不含推导逻辑。
  写库证明**不需要**直接碰 tactic；它不出现在 `.pyhol` 里。
- 再往下是 kernel 的 15 原语与宏（level 0/1/10）。方法 → 宏/原语 → `ProofTerm`。

### 5.3 证明管线（从文件到 VALID）

1. **解析**：`syntax/pyhol` 把 `.pyhol` 解析成条目的 `steps`（方法名 + `goal`/`facts`/参数），
   存入 `basic.theory_cache[name]['content']`（条目有 name/prop/vars/attributes/steps）。
2. **装配理论**：`basic.load_theory` / `context.set_context` 把该理论（含 import 闭包）的
   定理装进 kernel 的 `theory.thy`；`theorems`/`thm` 查的就是它。
3. **回放**：`core/verify.validate_theory` 对每条定理建 `StableProofState`
   （`method/stable_state.py`），逐条 `apply_method_dict(step)`。
   回放经 `apply_method`（受检通道）：查注册表（`core/method.has_method`，受 `limit` 约束）
   → `Method.apply` → kernel 原语/宏 → `ProofTerm`。
   回放**默认吞异常**返回 `False`（`strict=True` 才抛出真实异常，REPL 用后者）。
4. **稳定 id**：`StableProofState` 按**命题值去重**分配 sid；`goal=`/`facts=` 用 sid；
   `#[N]` 注解回放时成为 `new_ids`，可强推 sid（见 §3.2/§3.3）。
5. **信任**：level-0 oracle 宏需名字在 `trust` 集；`verify(trust=...)` 默认空集，
   由 shell/验证器显式传入（内核不按需加载）。库验证用 `validate_library.py` 的
   `LIBRARY_ORACLES`。
6. **四态**：VALID / STEP_FAILED / DEP_FAILED / UNPROVED；依赖检查只看
   `step['theorem']`。

---

## 6. 失败诊断

步骤失败会打印：真实异常、出错行、实时 sid 列表、当前目标。示例：

```
STEP FAILED: AssertionError: rewrite: unable to apply theorem.
  failing line: ← rewrite nat_plus_def_2 sym=false goal=1
  live stable ids: [0, 1, 2]
  #[1] 0 + Suc y = Suc (0 + y)
```

想还原一个被吞掉的异常，用 `apply_method_dict(step, strict=True)`（回放默认
`strict=False`，只返回 False，是给库回放用的）。

---

## 7. 已修复的痛点（历史，供参考）

1. `apply_method_dict` 吞异常 → 新增 `strict=True` 可选参数（默认行为不变）。
2. 无目标态视图 → `goals` / `all`，每步后列出新增 `#[N]`。
3. `var` 类型含空格被拆错 → 只按首个空白切分。
4. `var a 'a goal=3`（方法步骤）被误当成 REPL `var` 命令 → 步骤行优先识别。
5. `str(term)` 类型推断会抛异常、matcher 的 lazy trace 亦然 → `_prop_str`/`_exc_str` 防崩。
6. 单请求内部异常会打挂常驻 server → `handle_request` 兜底，进程不退。

**发现新痛点就改 `repl/`，并补测试。** 不要绕过 REPL 去用前后端 API。
7. 旧 `var` 声明跨 goal 残留，与见证名撞车（`elim: duplicate name p`）
   → 新增 `reset` 命令（清变量与当前 goal）。
8. 写证明靠猜定理名/方法 → 新增 `methods` / `theorems [-v]` / `thm NAME`
   三个查询命令（查的是当前理论闭包与受检注册表，见 §5.0）。

---

## 8. 使用中发现的限制（给后续 AI）

1. **`facts=[a, b]` 不能有空格**（`[a, b]` 会被按空白切成 `[a,` 与 `b]`，
   报 `fact sid '[' not found`）。写成 `facts=[a,b]`。
2. **跨分支的“同命题事实”不能互相引用（stable-ID 别名）**：
   `apply_method` 用 `ItemID.can_depend_on`（`kernel/proof.py:71`）检查
   `facts=` 必须与目标在**同一分支**且位置在前；而 `StableProofState` 按
   **命题值**去重分配 sid，于是两个兄弟分支里出现的同一命题（典型：两个分支
   都引入 `0 = 1` 这类假设）会共用 sid，第二个分支引用它时报
   `apply_method: illegal dependence`。这是 stable-ID 回放层的别名问题，
   不是 HOL 语义（LCF 里每个分支各有自己的 hyps/context）。
   **绕过办法**：把多个分支都要用的事实提到分支点**之上**
   （如 `→ forward one_nonzero goal=F` 再 `type_cases …`），让它成为所有
   分支的共同祖先；并让各分支导出的矛盾命题保持**字面不同**（一支推 `1=0`，
   另一支推 `0=1`）。
3. **声明顺序是硬约束**：`validate_theory` 按文件顺序装配理论，证明不能引用
   声明在其后的定理（报 `Theorem X not found`）。REPL 里整理论已加载，
   **不会**报这个错——所以 REPL 通过后仍要
   `python .cache/validate_one.py <theory>` 复验。必要时把被依赖定理整体前移
   （如 `less_lesseqI` 移到 `less_lesseq` 之前）。
4. **`rule` 不能把 iff 当逆向规则**（`rule less_exist` 对 `k<n` 报
   MatchException）。由 `∃d. n=k+Suc d` 反推 `k<n`：先 `cut` 出该 exists 命题
   并证明，再 `→ rewrite target=fact less_exist sym=true`，`→` 会直接落在
   目标位置并关门。
5. **`type_cases`/`induct` 需要自由变量**：绑定在 `∀` 里的不行
   （`induction: cannot find variable`）；用 `var` 声明或 `elim` 出见证。
   `type_cases m` 会连 goal 里的假设一起代入，因此**不要提前 `intro`**。
6. **依赖 `limit` 的方法**：`methods` 显示 `[needs X]`（如 `nat_const_ineq`
   需 `bit1_neq_one`、`nat_norm` 需 `nat_nat_power_def_1`）。
7. **`rewrite` 可自动关门**：goal 被重写成与某个已有事实相同/自反时，
   这一步本身就关闭 goal（导出里不会多出 `apply_prev`），回放可复现。

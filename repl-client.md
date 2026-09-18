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
- **改了 `repl/` 或 `.pyhol` 之后必须换一个端口重起**（理论/代码都只在启动时读）。
  端口被占用时服务端会打印 `cannot bind ... another server on this port?` 并
  退出 2——这是有意的：Windows 的 `SO_REUSEADDR` 允许第二个 server 抢占端口、
  客户端继续连到旧进程，看上去"重启成功"其实还在跑旧代码（§7 第 11 条）。
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
| `validate [THEORY]` | 增量重验（命中缓存即跳过；只重放受影响的文件与文件内后缀） |
| `<步骤行>` | 直接粘贴 `.pyhol` 步骤，如 `← rule iffI goal=0` |
| `undo` | 撤销最后一步（从头重放重建，坏步骤不留痕） |
| `export` | 输出 `.pyhol` proof 块（**自动重新生成 `#[N]` 注解**） |
| `item NAME` | 输出完整 `.pyhol` 条目：`theorem NAME` + `fixes` + `prop` + `proof..qed`（见 §4.1） |
| `let NAME REF` | 给稳定 ID 起别名，步骤行里用名字引用（见 §4.1） |
| `check` | 打印 `VALID` 或剩余目标数 |
| `trust NAME,...` / `trust +N` / `trust -N` | 设置/追加/移除会话信任集 |
| `help`、`quit`/`exit`/`q` | |

步骤行与 `.pyhol` 完全同构，可直接从库里复制粘贴。
**`goal=` / `facts=` 除了字面 ID，还接受语义引用**（`@`、`"命题"`、别名）；
命令行上写语义引用、`export`/`item` 输出字面 ID——见 §4.1，这是写证明时的默认用法。

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
- **z3 后端在 REPL 启动时已绑定**（`repl/repl.py` 里 import `solvers.z3wrapper`，
  与 `validate_library.py`/`.cache/validate_one.py` 一致；没有 z3 的检出仍可用）。
  否则 `← z3` 会报 `Z3 method: not installed`，real/int/hoare 这些 oracle 条目在
  REPL 里根本证不了。注意 **z3 的可用改写规则取决于"此刻理论里有什么"**
  （`z3wrapper.norm_term` 走 `has_theorem` 判断），所以在 REPL 里证过的 z3 步骤
  不一定在库回放时也成立——必须用 `.cache/validate_one.py <理论> --force` 复核
  （实例见 `library/real.pyhol` 的 `real_inv_0` NOTE）。

### 3.2 `#[N]` 注解只是显示，但会强制 sid

注解在回放时变成 `new_ids`，**若与引擎自动编号不一致会强制覆盖 sid**，从而
挪动后续 `goal=` 的指向。不确定时**省略注解**最安全；`export` 会生成正确注解。

### 3.3 稳定 id 的坑

sid 按 **命题值（prop + hyps）去重**：不同分支里相同的命题会共用同一个 sid，
`next_sid` 不递增。所以手写 `goal=N` 时不要凭直觉递增，每步后看 `all` 输出。
引用只能在同一分支内（这是正常的证明作用域），跨分支引用会报
`illegal dependence`——见 §8.2。

### 3.4 `loc` 是项树路径

`rewrite ... loc="1"` 等：`"0"` 函数部分、`"1"` 参数部分、`"0.1"` 函数的参数。
对 `A ⟷ B`（内部是 `=`）而言，左操作数在 `"0.1"`、右操作数在 `"1"`。
**`loc` 无法进入 `λ` / 量词体**（抽象不是 `Comb`）。

### 3.5 `rewrite` 会抓最外层匹配

`(P⟷¬P)⟷false` 上直接 `rewrite iff_conv_conj_disj` 会把整个目标当 `A⟷B`。
需要 `loc` 指定子位置。

---

## 4. 常见技巧（手工证明）

### 4.1 语义引用：不要手算 `#[N]`

`#[N]` 按**命题去重**分配（§3.3），所以步号与 ID 不成正比；一条 `rule`/`cases`
开出几个子目标、一次重写顺手关掉一个目标，都会让"我猜下一个是 N+1"出错。
步骤行的 `goal=` / `facts=` 因此可以直接写语义引用，REPL 在应用前把它们
解析成字面 ID 并回显 `resolved: ...`（`export` / `item` 输出的永远是字面 ID）：

```
goal=@             上一步新开的第一个仍开的子目标；否则上一步的目标（若仍开）；
                   否则跳到当前最新仍开的目标（会打印 note 说明）
goal=@N            同上，N 步之前（@0 = 上一步）
goal="<命题>"      仍开目标里命题匹配的那个
facts=[@]          上一步派生出来的那个事实
facts=[@N]         同上，N 步之前
facts=["<命题>"]   事实里命题匹配的那个
facts=[NAME]       用 `let NAME <引用>` 起的别名
let NAME 3         起别名；引用形式：<字面ID> | @ | @N | "命题" | goal=<引用>
let                不带参数时列出当前所有别名
```

- **匹配按打印出来的命题**（空白不敏感）：完全相等优先；否则取"包含该文本"的
  项，命中多个时用**最大的 ID** 并打印 note。命题文本就用 `all` / 步骤回显里
  打印出来的那份（变量名以当前打印为准，`intro` 会改名，别用旧文本）。
- **带引号的文本是"用时解析"的**：绑定时不锁定 ID，真正用到那一步才按
  *那个目标的依赖范围* 解析，所以不会因为后面又开了新目标而指错。
- **事实引用会按引擎自己的依赖规则检查**（`ItemID.can_depend_on`：同一子证明里
  更靠前的行）。引到父目标、兄弟分支、或用旧变量名匹配到祖先命题时，报的是
  `CANNOT RESOLVE REFERENCE: ... cannot depend on`，而不是等到回放才
  `apply_method: illegal dependence`。这一步失败不留痕（gap 不变）。

### 4.2 写回理论文件：用 `item`，不要手抄命题

```
item strict_sorted_appendI
```

输出 `theorem NAME` + `fixes`（会话里 `var` 声明的变量，**保留 `'a::C` 注解**）
+ `prop`（给 `goal` 的原文，不是脱糖后的）+ `proof..qed`。整段直接粘进
`.pyhol` 即可；手抄命题/注解是 sugar 与类型都容易抄错的地方。

### 4.3 其它技巧

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
9. `facts=[1, 2]`（逗号后有空格）被分词器切成两半，报 `fact sid '[' not found`
   → `facts=` / `new_ids=` 的方括号列表在分词**之前**从整行里取出
   （`syntax/pyhol.py:_extract_bracket_ids`），空格随便写；不是纯 ID 列表的
   方括号仍然走老路径，诊断不变。
10. 手算 `#[N]` 易错（§3.3/§8.2）→ 新增 §4.1 的语义引用与 `let` 别名，
    并把引擎的依赖规则（`can_depend_on`）搬进解析器，提前报
    `cannot depend on` 而不是事后 `illegal dependence`。
11. 重启常驻 server 时，Windows 上 `SO_REUSEADDR` 会让**第二个** server
    悄悄抢占同端口，客户端仍然连到跑着旧代码的那个进程（"重启了但没生效"）
    → `--serve` 不再设 `SO_REUSEADDR`（POSIX 仍设，TIME_WAIT 需要），
    端口被占时直接报 `cannot bind ... another server on this port?` 并退出 2。

---

## 8. 使用中发现的限制（给后续 AI）

1. ~~**`facts=[a, b]` 不能有空格**~~ 已修（§7 第 9 条），现在 `facts=[a, b]`
   与 `facts=[a,b]` 等价。
2. **跨分支不能互相引用是正常语义，不是缺陷；假设可以用**：
   - HOL/LCF 的证明是「每个分支各自线性」的：`apply_method` 用
     `ItemID.can_depend_on`（`kernel/proof.py:71`）强制 `facts=` 必须是目标的
     **同分支、且位置在前**的项。**这是正确的，不要去改引擎。**
   - 会踩到的情形：`StableProofState` 按 **Thm**（`Thm.__eq__`：假设集合 + 命题，
     `kernel/thm.py:105`）去重分配 sid——比"同一命题"严；两个兄弟分支里
     出现的**同假设集合、同命题**的条目（典型：两支都引入 `0 = 1` 这类假设）
     共用同一 sid，回放时会
     解析到另一个分支的位置，于是报 `apply_method: illegal dependence`。
     这是**那条证明的结构问题**（同一命题不该同时当两个分支的假设），不是引擎
     缺陷。
   - 正确写法：把多个分支都要用的事实提到分支点**之上**
     （如先 `→ forward one_nonzero goal=F` 再 `type_cases …`），让它成为所有分支
     的共同祖先；并让各分支导出的矛盾命题保持**字面不同**（一支推 `1=0`，
     另一支推 `0=1`）。
   - 另外：`intro` 引入的假设**可以当事实用**（`facts=[h]`），`assumption` 在命题
     等于某个 hyp 时可关门——这是 HOL 的正常做法（kernel 的 `Thm` 自带 `hyps`）。
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


---

## 9. 增量验证（缓存机制）

`validate_theory` / `validate_incremental`（`core/incremental.py`）现在是**带依赖链的增量验证**，
全库跑也走缓存，**不需要 `--force`**：

- **文件粒度**：每个 `.pyhol` 在 `.cache/<name>.json` 的 `meta` 里存 `source_hash`（整文件内容 sha1）、
  `item_hashes`（每个 item 的**源码块** sha1）、`imports_epoch`（其 imports 的传递指纹）。三者都匹配才整体复用。
- **文件内后缀**：文件被编辑（own hash 变）但 imports 未变时，用 `first_diff_index` 找到**第一个变化的 item**，
  只重放它及其之后；之前的 item 状态原样复用（后面 item 可能依赖它，所以不能更细）。
- **跨文件级联**：任何上游文件变化都会改变下游的 `imports_epoch`，于是下游缓存自动失效并重验；
  `validate_incremental` 还会把「判定变化」的文件的下游推入队列，保证邻居不残留旧状态。
- **删除定理**：被删定理的判定**立刻**从内存表（`basic.drop_status`）与 json 中消失；
  `load_status` 也会跳过当前源码里不存在的名字，防止陈旧 json 在重放过程中把它复活。
- 数据结构就是「按 item 顺序的哈希列表 + 反向 imports 邻接表」，都是 O(n) 的轻量结构；
  定理级细粒度依赖图不需要，反而更慢且容易漏失效。
- 客户端里用 `validate [THEORY]` 触发；常驻进程因此不用重启就能复用已解析的理论。

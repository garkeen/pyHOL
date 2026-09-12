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

## 5. 失败诊断

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

## 6. 已修复的痛点（历史，供参考）

1. `apply_method_dict` 吞异常 → 新增 `strict=True` 可选参数（默认行为不变）。
2. 无目标态视图 → `goals` / `all`，每步后列出新增 `#[N]`。
3. `var` 类型含空格被拆错 → 只按首个空白切分。
4. `var a 'a goal=3`（方法步骤）被误当成 REPL `var` 命令 → 步骤行优先识别。
5. `str(term)` 类型推断会抛异常、matcher 的 lazy trace 亦然 → `_prop_str`/`_exc_str` 防崩。
6. 单请求内部异常会打挂常驻 server → `handle_request` 兜底，进程不退。

**发现新痛点就改 `repl/`，并补测试。** 不要绕过 REPL 去用前后端 API。

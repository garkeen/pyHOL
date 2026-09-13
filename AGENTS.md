# holpy 工作区指令

holpy 是用 Python 实现的 HOL 定理证明器（LCF 风格）。三层架构，单向依赖：

```
kernel/      逻辑内核：Type/Term/Thm/15 原语/ProofTerm/Theory，只此可造定理
  ↓
core/        逻辑层：Conv/Tactic/Macro/Matcher/Auto/Search/Items/Defcheck/Verify，
             组合原语与宏；theories/ 为领域内容，solvers/ 为纯算法核
  ↓
method/+backend/ 应用层：Method/ProofState/Flask API，点击式证明，不写证明语言
```

信任模型：15 条原语是唯一凭空构造定理的入口；宏按 level 展开或求值
（None 永远展开 / 0 oracle 不可展开 / 1 标准宏 / 10 领域计算）；
任何 ProofTerm 可 export 为线性 Proof，由 check_proof 独立校验。

## 1. 报错要清晰

报错必须定位到具体原因，而不是直接抛异常：

- 解析类：区分变量不在上下文、lexer 根本没定义该符号、括号没闭合三类。
- 证明类：关不掉就诚实失败（`TacticException('Cannot solve ...')`），不留半截证明，
  不改 gap 计数。`auto`/`solve`/`simp` 的失败语义是契约，改动不得放宽。
- 宏断言（assert）用于拒绝非法输入，信息里写清期望与实际（如 goal 形状不对、
  前提数量不对），方便调用方定位。

## 2. 测试要清晰

两种测试，分工不同，都要写：

- 主动 test（`test_*`）：防回归。每个新功能至少一个“之前失败、现在能过”的用例；
  旧用例原样保留。宏用 `test_macro`（同时验 eval、get_proof_term、check_proof），
  方法用 `test_method` 或 StableProofState（验关门、gap 数、行记录）。
- 被动 assert：标非法输入。每个新入口至少一个“必须失败”的用例
  （抛指定异常、gap 不变、无副作用）。

测试布局：测试跟模块走（`kernel/tests/`、`core/tests/`…），跨模块的才放顶层。
全量 library 验证（`validate_library.py`）很贵，平时只跑相关回归；
验证结果走顶层 `.cache/` 缓存，命中即跳过重放，`--force` 才全量重验。

## 3. 架构要分离，中间层可序列化

- 模块单向依赖：`core` 不依赖 `method`，`kernel` 不依赖任何人。
  新增引用先查 import 方向，循环依赖宁可把代码下沉，不许上浮。
- 证明表示可序列化：ProofTerm ⟷ 线性 Proof ⟷ `.pyhol` 文本 ⟷ JSON，
  链条上每一段都可独立重验。证明行一旦生成不可改写（无 thin/sym 这类行改写）。
- Method 是 Tactic/Macro 的用户接口：操作 ProofState（goals + facts），
  经 `apply_tactic` / `apply_macro` 受检通道，不直调内核。
  前向（forward/rewrite-fact/inst）与后向（rule/cases/rewrite-goal/induct）分开；
  匹配分两步：模式网模糊取候选（`search.candidates_for`），精确匹配确认。
- 求解器以 `(goal, pts) -> ProofTerm` 形状注册进 `global_autos` / `global_autos_neg`
 （默认随理论加载，注册数量用测试断住防回归），`auto` 只做分发不写判定。

## 4. 工作方式

- **写证明一律用常驻 REPL + `repl/client`，不要写每次重载理论的临时脚本。**
  理论加载一次，之后所有步进都走同一条连接：

  ```bash
  python -m repl.repl --serve --port 8854 --theory <理论> &   # 后台起一次
  python -m repl.client --port 8854 --stdin < 步骤文件         # 或 “cmd1” “cmd2” ...
  ```

  客户端指令：`theory NAME`、`var NAME TYPE`（**不写 `::`**，写法是 `var A 'a set`）、
  `goal <prop>`（只给命题，上下文变量靠 `var` 预先声明）、步进行、
  `all`（列出全部条目与稳定 ID）、`undo`、`check`、`export`、`thm NAME`。
  退出码 0/1/2；出现 `STEP FAILED` 会打印失败行与当前所有稳定 ID。
  做完工作**记得关掉后台服务**。

  **两个坑**：`check` 只做 `compute_only`，说 VALID 不等于独立重放通过，
  最终必须用 `.cache/validate_one.py <理论>` 复核；临时脚本（每次新进程、
  重载整条 import 链）的稳定 ID 分配顺序可能与 REPL 不同，两边混用会让
  先前记下的字面 sid 失效——要就用 REPL，别在两个工具之间来回抄 sid。
- 小步：一次只动一两个文件；机制先用不落盘原型验证，再落盘；先测后写测后跑回归。
- 代码里不写思维链，不假装完成：没跑过的测试不写“通过”，没验证的结论不写“已确认”。
- 改共用件（如 `simp_sweep`、`solve`、`basic.load_theory_cache`）必须跑全相关回归；
  改动若改变失败语义或行记录格式，先报备再动手。
- 提交信息写清改了什么、测试结果是什么（主动几例、回归几例）。

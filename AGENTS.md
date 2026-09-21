# pyHOL 工作区指令

pyHOL 是用 Python 实现的 HOL 定理证明器（LCF 风格）。三层架构，单向依赖：

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

## 0. 禁止简化实现，禁止特判实现

**本条排在最前，与后面任何条款冲突时以本条为准。**

**不许把"没写完"做成实现的一部分。** 一条机制要么按一般情形写出来，要么明确
标成未实现；中间那条路——写一个只认当前样例形状的分支，再对外说"支持了"——是禁止的。

- **禁止特判分支**：不许在代码里写死形状。已出现过、以后一律不许再出现的：
  「互递归只支持两个函数」「只支持每个函数一个参数」「一条子句只许一个递归调用」
  「只认某个类型名/常量名/构造子名」。规模（函数个数 N、参数个数、每条子句的调用数、
  和树的形状）必须**从输入算出来**——和类型按 N 造嵌套树、注入/剥层沿路径走、
  前提里每个调用给一条 IH、分量逐个取，都是可写的。
- **判据**：一段代码的成立若依赖"我们的样例恰好是这个形状"，它就是特判。
  动手前先问一句：换成 N 个函数、多个参数、一条子句多个调用，这份代码还成立吗？
  不成立就现在把一般情形写出来，不许先落一个窄版本再说。
- **成本不是理由**。"难写""要多几百行""要新模板"都不是跳过的借口。真正做不了的
  只有需要新内核原语/新语义这类根本性障碍——那种要在动手前讲清楚并给出替代路线，
  而不是先交半截。
- **诚实失败不是挡箭牌**。`FunGenError` 的诚实失败是给"用户输入超出语言能力"
  （依赖不在作用域、完全不支持的类型）用的，不是给"我还没实现"用的：后者必须在
  代码注释、文档、提交信息里都写成**未实现**，并且不许计入验收条目。
- **验收不许打折**。宣称"验收达成/做完"时，列出的每一项都必须是真的一般实现；
  文档或提交信息里出现"目前只支持 …""只处理了 … 的情况"，就等于任务未完成。
- **发现即登记**：已经存在的特判每发现一处，就在移植文档里登记一处（写清在哪、
  影响什么、一般情形怎么实现），清掉才算了结；不许因为"样例能过"就留着。

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

测试布局：测试跟模块走（`kernel/tests/`、`core/tests/`…），顶层不放测试文件；
跨层的集成测试按被测模块归位，测试里的装配 import（如 `method.stable_state`）
归 import lint 的 tests 豁免覆盖。
全量 library 验证（`validate_library.py`）很贵，平时只跑相关回归；
验证结果走顶层 `.cache/` 缓存，命中即跳过重放，`--force` 才全量重验。

**只要跑就要有时间上限：单条命令、单个测试、单次验证都不许超过 2 分钟，超时算错。**
日常验收只重放指定条目（`.cache/check_item.py <理论> <条目…>`），
整文件 `validate_one --force` 不是常规手段。

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
  `all`（列出全部条目与稳定 ID）、`undo`、`check`、`export`、
  `item NAME`（输出整段可粘贴的 `.pyhol` 条目：theorem/fixes/prop/proof/qed）、
  `let NAME REF`（给稳定 ID 起别名）、`thm NAME`。
  退出码 0/1/2；出现 `STEP FAILED` 会打印失败行与当前所有稳定 ID。
  改了 `repl/` 或 `.pyhol` 之后**换端口重起**（端口被占会明确报错并退出 2）；
  做完工作**记得关掉后台服务**。

  **步进行里不要手算稳定 ID**：`goal=` / `facts=` 接受语义引用——`goal=@`
  （上一步开的仍开子目标／上一步的目标／最新仍开目标）、`goal="<命题>"`、
  `facts=[@]`（上一步派生的事实）、`facts=["<命题>"]`、`facts=[别名]`。
  REPL 会回显 `resolved: ...` 的字面形态，`export` / `item` 输出的也是字面 ID。
  事实引用按引擎的依赖规则（`ItemID.can_depend_on`）预检：指到父目标或兄弟
  分支会直接报 `cannot depend on`，而不是回放时才 `illegal dependence`。
  细节见 `repl/repl-client.md` §4.1。

  **两个坑**：`check` 只做 `compute_only`，说 VALID 不等于独立重放通过，
  最终必须用 `.cache/validate_one.py <理论>` 复核；临时脚本（每次新进程、
  重载整条 import 链）的稳定 ID 分配顺序可能与 REPL 不同，两边混用会让
  先前记下的字面 sid 失效——要就用 REPL，别在两个工具之间来回抄 sid。
- 小步：一次只动一两个文件；机制先用不落盘原型验证，再落盘；先测后写测后跑回归。
- 代码里不写思维链，不假装完成：没跑过的测试不写“通过”，没验证的结论不写“已确认”。
- 改共用件（如 `simp_sweep`、`solve`、`basic.load_theory_cache`）必须跑全相关回归；
  改动若改变失败语义或行记录格式，先报备再动手。
- 提交信息写清改了什么、测试结果是什么（主动几例、回归几例）。

## 5. 禁止探针

- **生成器（以及任何代码）不得向 method 层回问运行状态。** 不许新建
  `StableProofState`、逐步 `apply_method_dict`、再读回开放目标或新建条目的数量；
  也不许为此在 `core` 与 `method` 之间新增注入点（`set_probe_fn` / `probe_open` /
  `probe_step` 这类一律禁止）。
  理由：这是"拿运行结果反推生成"的旁路，把本来能在生成器里静态算出来的东西
  推给了一次试跑；实测代价也离谱——每发一步重放整段前缀是 O(n²)，
  nat 载入从 3.6 秒涨到 30.7 秒。
- **发出的条目里不许出现 `#[N]` 这类用来钉稳定 ID 的标注。** ID 必须静态算出：
  每一步建几个条目由模板决定；会提前关闭目标的步骤（结论即目标的 `rule`、
  `if_P` / `if_not_P`、递减义务化为恒等式时最后那一条重写）在代码里用 `if` 判定，
  判不出来就诚实失败（`FunGenError`，保持原有公理路径），不许偷偷跑去试。


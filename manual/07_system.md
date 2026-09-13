# 系统组织总览

> 本章粗略描述实现层的组织，这些部分较易改动。代码事实以当前目录结构为准。

## 1. 三层架构

```
kernel/          逻辑内核（Type/Term/Thm/原语/ProofTerm/Theory）
  │   15 条原语是唯一凭空构造定理的入口
  ▼
core/       逻辑层（Conv/Tactic/Macro/Matcher/Context/Auto/Search）
  │   组合原语与宏，提供自动化基础设施
  ▼
method/ + backend/ 应用层（Method/ProofState/Flask API）
                  面向用户的 API 与 web IDE
```

## 2. 理论组织

### 2.1 .pyhol 文件格式

理论以 `.pyhol` 文件存储（人类可读文本格式，替代旧 JSON）。每个文件含：

- 头部：`theory <name>`、`imports <list>`、`domains <list>`（可选）、`description "<text>"`。
- 内容：若干条目（item），类型有 `header`、`const`、`datatype`、`type`、`typeabbrev`、`quotient`、`def`、`fun`、`inductive`、`axiom`、`theorem`。

`theorem` 条目可含 `proof` 块（`proof` ... `qed`），内含编号的证明步骤。

### 2.2 Item 类型

| 类型 | 说明 |
|---|---|
| `header` | 章节标题 |
| `const`（`def.ax`） | 常量声明 |
| `type`（`type.ax`） | 公理类型（新增类型常量，`TConst` + 断言） |
| `typeabbrev`（`type.abbrev`） | 类型同义词：只给已有类型起名，不新增类型、不产生公理 |
| `quotient`（`type.quot`） | 商类型：由表示类型与等价关系构造，产出 `abs`/`rep` 常量与商公理 |
| `datatype`（`type.ind`） | 归纳类型 |
| `def` | 定义 |
| `fun`（`def.ind`） | 递归定义函数 |
| `inductive`（`def.pred`） | 归纳谓词 |
| `axiom`（`thm.ax`） | 公理 |
| `theorem`（`thm`） | 定理（可含证明） |

`typeabbrev` 的语法是 `typeabbrev <name> [<args>] = <type>`（如 `typeabbrev set 'a = 'a => bool`）；
`quotient` 的语法是 `quotient <name> (<abs>, <rep>) <relation>`。二者都不进入内核类型表：
`typeabbrev` 在解析期被 `parse_type` 直接展开，`quotient` 经 `core/items.py::Quotient` 产出
`TConst` 与常量扩展。详见 [`../FOUNDATION_DEBT.md`](../FOUNDATION_DEBT.md) §1–2。

### 2.3 理论加载流程

1. `basic.load_metadata()`：扫描 `library/` 所有 `.pyhol`，构建依赖图，拓扑排序。
2. `get_import_order(filenames)`：按拓扑序返回加载顺序。
3. `load_theory(filename)`：按序加载所有依赖，逐条 `unchecked_extend`。
4. 每条 item 解析后调 `get_extension()` 产生 `Extension` 列表，加入理论。

### 2.4 Extension

五种 `Extension`（见 [`02_kernel.md`](02_kernel.md) §8）：`TConst`、`Constant`、`Theorem`、`Attribute`、`Overload`。

`unchecked_extend` 遍历 exts，按类型分发。**不校验证明**（显式公理直接信任；`fun`/`datatype` 在解析时另有语法合法性检查，见 §2.6）。

### 2.5 自动生成的定理

- `Datatype`：自动生成 distinct（`_neq`）、inject（`_inject`）、归纳定理（`_induct` + `var_induct` 属性）。
- `Fun`：每条 rule 一条 `_def_N` 定理 + `hint_rewrite` 属性。
- `Inductive`：每条 intro rule + `hint_backward` 属性 + `_cases` 消除定理。
- `Definition`：生成 `<cname>_def` 定理。

### 2.6 定义合法性检查

两项语法检查（`core/defcheck.py` 的 `check_fun_recursion` / `check_datatype_positivity`）在解析时执行，失败则报错拒收：

- `Fun`（`def.ind`）：**结构递归**。恰有一个参数在每条等式中匹配构造器模式（其余参数是普通变量）；每个递归调用必须作用于该参数模式的构造器子项（如 `Suc m` 的子项 `m`），其他参数可经 `hd`/`tl` 等全函数变换；同一构造器不得有重复等式。通过即存在实现，等式作为公理一致。
- `Datatype`（`type.ind`）：**严格正性**。构造器参数中类型自身只能正出现：直接作为参数，或位于函数类型值域；出现于函数定义域（负出现，如 `(bad ⇒ bad) ⇒ bad`）或嵌套于其他归纳类型（如 `bad list`）则拒绝。否则注入性公理与 Cantor 定理矛盾。

## 3. 领域扩展机制

> **注**：当前的 `theories/` 包机制是权益之计，后续可能调整。

当前机制：
- `.pyhol` 头部 `domains <name>` 声明要加载的领域包。
- `core/basic.py` 在加载理论时 `importlib.import_module('theories.<name>')`。
- 领域包的 `__init__.py` 导入 `conv.py`、`macro.py`、`method.py`，通过 `@register_macro`/`@register_method` 装饰器注册（幂等）。

领域包目录：`theories/{logic,nat,real,integer,function,expr}/`。各包的组成按需裁剪，不是固定四件套：
- `logic/`：`conv.py` + `macro.py` + `logic.py`（无 `method.py`）；
- `nat/`：`conv.py` + `macro.py` + `method.py`（另有 `interval.py`/`util_nat.py`）；
- `integer/`：`conv.py` + `macro.py` + `method.py` + `omega.py`（omega 的证明装配）；
- `real/`：`conv.py` + `macro.py` + `method.py` + `simplex.py`/`simplex_strict.py`（后两者**不**被 `__init__.py` 引入，刻意懒装载）；
- `function/`、`expr/`：`macro.py`（+ `method.py`），无 `conv.py`。

`theories/` 顶层还有跨域非域模块 `poly.py`、`z3rec.py`（内容层的先例，见 `ARCHITECTURE_AUDIT.md` §7.4）。

`method/methods/__init__.py` 预加载 `nat`/`real`/`function`/`expr` 四个领域包（以及 `method.methods.z3`、`imperative.imp`，后者注册 `vcg` 方法），
确保方法在任何理论加载前就可用（IDE 方法列表需要）；`logic` 与 `integer` 由 `.pyhol` 的 `domains` 声明在加载期激活（`theories/integer/__init__.py` 负责 omega 的 auto 注册）。
装饰器幂等，重复导入是 no-op。

## 4. 自动化

### 4.1 auto（core/auto.py）

`solve(goal, pts, depth=0)`：自动证明 goal。策略：
1. 若 goal 匹配某条件，直接返回。
2. 若某条件是合取/析取，分解后递归。
3. 连接词分解（合取/析取/蕴涵/全称，硬编码）。
4. 先 `norm` 归一化 goal 再尝试。
5. 按 goal 的 head 查 `global_autos`/`global_autos_neg` 注册表。
6. `solve_hints`：`hint_backward` 模式网回链（结论精确匹配、前提递归），
   再试假设中蕴涵的 MP。深度上限 6，失败抛 `TacticException`（诚实失败）。

`norm(t, pts)`：自动归一化。按 head 查 `global_autos_norm` 注册表，应用注册的 conv/函数。

`auto_macro`（level 1，可展开）：`norm` 规范形比较 + `solve` 交错到不动点
（上限 10 轮，`simp_sweep` 推进，`chain.symmetric().equal_elim` 接回原目标）。
成功零 gap，失败抛错；记录仍为单行。

求解器注册（`basic.load_theory_cache` 随理论默认加载，`core/tests/auto_test.py` 断住数量）：
sympy（实数/自然数比较，oracle level 0）8 + 2，omega（整数比较，反证关门）4 + 4。

### 4.2 Z3（solvers/z3wrapper.py）

- `convert(t, ...)`：HOL 项 -> Z3 表达式。
- `norm_term(t)`：用一组重写定理归一化后调 `fologic.simplify`。
- `solve(t)`：调 Z3 检查 `¬t` 是否 unsat（unsat 即证明）。
- `z3` 宏（level 0，oracle，`core/macro/z3.py`）：不可展开，依赖 Z3 正确性；`z3` 方法（`method/methods/z3.py`）以 oracle 行落证明。

### 4.3 其他求解器

| 模块 | 职责 |
|---|---|
| `solvers/omega.py` | 整数线性算术（Omega Test）纯算法核（factoid/求解矩阵） |
| `theories/integer/omega.py` | omega 的证明装配与 auto 注册（内容层） |
| `theories/real/simplex.py` / `simplex_strict.py` | Simplex 算法与证明装配（实数/整数） |
| `solvers/tseitin.py` | Tseitin 编码（命题公式 -> CNF） |
| `solvers/sat.py` | DPLL SAT 求解（单文件） |
| `solvers/congc.py` | 同余闭包（congruence closure）算法 |
| `solvers/sympywrapper.py` | 用 sympy solveset 判定区间上的实数不等式 |
| `theories/z3rec.py` | Z3 proof reconstruction（实验链，跨域） |
| `solvers/fologic.py` | 一阶逻辑简化 |

> 自动证明的 best-first 搜索在 `core/auto.py`（见 §4.1）。

### 4.4 方法层自动化

- `simp`：只化简，不关门。全体 `hint_rewrite` 无前提定理定点迭代重写 + β 归一，
  must-change（无效果报错）。不看 facts，不调判定过程。
- `auto`：关门。`auto_macro` 经受检通道单行记录，成功零 gap，失败抛错。
  化简是它的内置子程序（`simp_sweep`），不是调用 `simp` method。
- `norm`：只证等式。按目标类型经 `norm_registry` 分发到 `nat_norm`/`real_norm`/`int_norm`
  等领域宏方法（受检宏调用，无 MacroTactic 逃生门）。

## 5. 语法层（syntax/）

| 模块 | 职责 |
|---|---|
| `parser.py` | 基于 lark 的类型/项/定理解析器，含 Hindley-Milner 类型推断（`infertype.py`） |
| `printer.py` | 漂亮打印 |
| `pprint.py` | 高亮打印的 AST 表示 |
| `operator.py` | 运算符优先级与结合性表 |
| `settings.py` | 全局设置（unicode、highlight、line_length） |
| `pyhol.py` | `.pyhol` 格式的解析与导出（新 `#[N]` 稳定 ID 格式） |
| `numeral.py` / `logicops.py` | 数字与逻辑常量的语法糖（普通函数，靠显式 import 装载） |
| `function_tools.py` / `list_tools.py` / `set_tools.py` / `string_tools.py` | 语法糖与记号定义 |

## 6. 应用层

### 6.1 Flask 后端（backend/）

- `backend/app.py`：Flask 应用工厂 `create_app()`（CORS + 自定义 JSON provider），模块级单例 `app = create_app()`。
- `backend/__init__.py`：导入 `backend.app` 的单例后依次导入 `ide`、`ide_v2`、`imperative`、`manual`，
  各模块的 `@app.route` 装饰器在此刻注册到**单例**上。
- `backend/ide.py`：理论编辑与文件管理接口（`/api/find-files`、`/api/load-json-file`、`/api/save-file`、
  `/api/check-modify`、`/api/validate-theory`、`/api/theorem-search`、`/api/theory-status` 等）。
- `backend/ide_v2.py`：新管线证明接口（`/api/v2/init-saved-proof`、`/api/v2/apply-method`、`/api/v2/backward-search`、`/api/v2/forward-search`、`/api/v2/trust-report`），
  以稳定 `#[N]` ID 对接 `method/stable_state.py::StableProofState`。请求体可带 `trust`（计算 oracle 放行集），
  省略即用 `core/verify.COMPUTATION_ORACLES`；`trust-report` 跑完整 verify 返回 `rpt.oracles`/`rpt.axioms`。
- `backend/imperative.py`：Hoare 逻辑程序验证接口（`/api/imp-list`、`/api/imp-load`、`/api/imp-compile`）。
- `backend/manual.py`：手册阅读接口（`/api/manual-list`、`/api/manual-load`）。

> **注意**：路由挂在模块级单例上，`create_app()` 每次调用返回的是**没有路由**的新 app。
> 测试/嵌入要拿 `from backend import app`（即单例），再 `.test_client()`；重复调 `create_app()` 不会重新注册路由。

### 6.2 前端（frontend/）

Vue 3 + Vite 单页应用，路由（`src/router.js`）：
- `/` → `Index.vue`（首页）
- `/ide` → `Editor.vue`（HOL 证明 IDE）
- `/program` → `ProgramIDE.vue`（程序验证 IDE）
- `/manual` → `Manual.vue`（手册阅读）

开发服务器端口 8080，`vite.config.js` 把 `/api` 代理到 Flask（`http://127.0.0.1:5000`）。前端 `src/api/index.js` 用 axios（`baseURL: '/api'`）与后端通信。

`Editor.vue` 对每种 item 类型分发到对应的 `components/items/*Edit.vue`，涵盖内核 `item_table` 的全部条目，
包括 `type.abbrev`（`TypeAbbrevEdit.vue`）与 `type.quot`（`QuotientEdit.vue`）。证明面板
`components/proof/ProofArea.vue` 的方法下拉框按后端 proof state 的 `method_direction` 分组，不再硬编码词表。



### 6.3 校验监控（core/verify.py + core/basic.py）

`core/verify.py::validate_theory(filename)`：重放文件内所有定理的证明，返回本文件的
`(statuses, errors)`——状态为 `VALID`/`STEP_FAILED`/`DEP_FAILED`/`AXIOM`/`UNPROVED`，失败定理带错误原因。
结果按源文件哈希 + 依赖理论哈希缓存到顶层 `.cache/*.json`（增量：源改动只从首个改动条目起重放，
依赖改动则整文件重验；`force=True` 全量）。四态判定与信任报告在 `verify`，重放原语在 `kernel/replay.py`。

跨理论累积的状态表（供 `/api/theory-status` 读取）住在 `core/basic.py`（`statuses`/`errors` +
`get_all_statuses`/`set_status`/`set_error`——2026-09 从 kernel 迁出，见 `ARCHITECTURE_AUDIT.md` §7.4）。
`method/` 只提供注入的 replay 函数（`method/stable_state.py::_verify_replay`），不参与状态判定。

## 7. 目录索引

| 目录 | 职责 |
|---|---|
| `kernel/` | 逻辑内核（Type/Term/Thm/原语/Proof/ProofTerm/Theory/Macro/Extension/Report） |
| `core/` | 逻辑层基础设施（Conv/Macro/Matcher/Auto/Search/Items/Defcheck/Verify） |
| `tactic/` | 逆向翻译层（`goal.py` 的 Goal 定义 + `steps.py` 的 rule/cases/induct/...） |
| `method/` | 方法层与证明状态（`methods/`、`stable_state.py`、`init.py`） |
| `theories/` | 领域扩展包（logic/nat/real/integer/function/expr） |
| `syntax/` | 解析、打印、设置、`.pyhol` 格式 |
| `solvers/` | 外部求解器与自动证明（Z3/Omega/Simplex/Tseitin/SAT/Congc/Sympy） |
| `backend/` | Flask 后端 API |
| `frontend/` | Vue 3 前端 |
| `library/` | 理论库（`.pyhol` 文件） |
| `imperative/` | Hoare 逻辑程序验证（独立子模块，`.imp` 格式） |
| `repl/` | 自洽 REPL（交互/脚本/常驻三模式，不依赖前后端；见 `repl-client.md`） |
| `util/` | 纯工具函数（name/typecheck/unionfind 等） |
| `manual/` | 本手册 |

## 8. 数据流

### 8.1 理论加载

```
.pyhol 文件
  ↓ pyhol.parse_pyhol
dict
  ↓ items.parse_item
Item 对象 (.get_extension())
  ↓ theory.unchecked_extend
theory.thy.data 更新（type_sig/term_sig/theorems/attributes/...）
```

### 8.2 证明校验

```
theorem.steps (in .pyhol, 稳定 #[N] ID 字典)
  ↓ method/stable_state.py::StableProofState.apply_method_dict
      （sid -> 位置 id 翻译）
  ↓ method/methods/core.py::apply_method
Method.apply -> Tactic / Macro -> ProofTerm
  ↓ ProofTerm.export()
线性 Proof
  ↓ core/verify.py::verify（宏按 level 展开/求值，构信任报告，四态判定）
  ↓ kernel/replay.py::replay（只跑 15 原语 + 3 假设规则）
最终 Thm + 信任报告（axioms / oracles / gaps）
```

- `verify(compute_only=True)` 是方法层的增量校验：每行都重推，但跳过最后的独立原语重放；
  完整 `verify()` 才跑 `kernel/replay` 的独立重放。
- `repl`/`backend` 都只调 `method` 通道，不直连内核（见目录索引与 `ARCHITECTURE_AUDIT.md` §4）。


---

**返回**：[`README.md`](README.md)

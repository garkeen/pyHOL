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
- 内容：若干条目（item），类型有 `header`、`const`、`datatype`、`type`、`def`、`fun`、`inductive`、`axiom`、`theorem`。

`theorem` 条目可含 `proof` 块（`proof` ... `qed`），内含编号的证明步骤。

### 2.2 Item 类型

| 类型 | 说明 |
|---|---|
| `header` | 章节标题 |
| `const`（`def.ax`） | 常量声明 |
| `type`（`type.ax`） | 公理类型 |
| `datatype`（`type.ind`） | 归纳类型 |
| `def` | 定义 |
| `fun`（`def.ind`） | 递归定义函数 |
| `inductive`（`def.pred`） | 归纳谓词 |
| `axiom`（`thm.ax`） | 公理 |
| `theorem`（`thm`） | 定理（可含证明） |

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

两项语法检查（`method/struct_recursion.py`）在解析时执行，失败则报错拒收：

- `Fun`（`def.ind`）：**结构递归**。恰有一个参数在每条等式中匹配构造器模式（其余参数是普通变量）；每个递归调用必须作用于该参数模式的构造器子项（如 `Suc m` 的子项 `m`），其他参数可经 `hd`/`tl` 等全函数变换；同一构造器不得有重复等式。通过即存在实现，等式作为公理一致。
- `Datatype`（`type.ind`）：**严格正性**。构造器参数中类型自身只能正出现：直接作为参数，或位于函数类型值域；出现于函数定义域（负出现，如 `(bad ⇒ bad) ⇒ bad`）或嵌套于其他归纳类型（如 `bad list`）则拒绝。否则注入性公理与 Cantor 定理矛盾。

## 3. 领域扩展机制

> **注**：当前的 `theories/` 包机制是权益之计，后续可能调整。

当前机制：
- `.pyhol` 头部 `domains <name>` 声明要加载的领域包。
- `core/basic.py` 在加载理论时 `importlib.import_module('theories.<name>')`。
- 领域包的 `__init__.py` 导入 `conv.py`、`macro.py`、`method.py`，通过 `@register_macro`/`@register_method` 装饰器注册（幂等）。

领域包目录：`theories/{nat,real,integer,function,expr}/`，每个含 `__init__.py` + `conv.py` + `macro.py` + `method.py`（部分）。

`method/methods/__init__.py` 也会预加载所有领域包，确保方法在理论加载前就注册。

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

求解器注册（`basic.load_theory_cache` 随理论默认加载，`auto_test.py` 断住数量）：
sympy（实数/自然数比较，oracle level 0）8 + 2，omega（整数比较，反证关门）4 + 4。

### 4.2 Z3（solvers/z3wrapper.py）

- `convert(t, ...)`：HOL 项 -> Z3 表达式。
- `norm_term(t)`：用一组重写定理归一化后调 `fologic.simplify`。
- `solve(t)`：调 Z3 检查 `¬t` 是否 unsat（unsat 即证明）。
- `z3` 宏（level 0，oracle，`core/macros/z3.py`）：不可展开，依赖 Z3 正确性；`z3` 方法（`method/methods/z3.py`）以 oracle 行落证明。

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

> `sat/` 与 `smt/`（veriT 集成）已移除；自动证明的 best-first 搜索在 `core/auto.py`（见 §4.1）。

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
| `json_output.py` | JSON 输出 |

## 6. 应用层

### 6.1 Flask 后端（backend/）

- `backend/app.py`：Flask 应用工厂（`create_app()`，CORS + 自定义 JSON provider）。
- `backend/ide.py`：理论编辑与文件管理接口（`/api/find-files`、`/api/save-file`、`/api/validate-theory` 等）。
- `backend/ide_v2.py`：新管线证明接口（`/api/v2/init-saved-proof`、`/api/v2/apply-method`、`/api/v2/backward-search`、`/api/v2/forward-search`）。
- `app/imperative.py`：Hoare 逻辑程序验证接口（独立子模块，`.imp` 文件）。
- `app/manual.py`：手册阅读接口（`/api/manual-list`、`/api/manual-load`）。

`app/__init__.py` 导入上述路由模块（`ide`、`ide_v2`、`imperative`、`manual`），使所有 `/api/*` 路由在 `create_app()` 时注册。

### 6.2 前端（frontend/）

Vue 3 + Vite 单页应用，路由（`src/router.js`）：
- `/` → `Index.vue`（首页）
- `/ide` → `Editor.vue`（HOL 证明 IDE）
- `/program` → `ProgramIDE.vue`（程序验证 IDE）
- `/manual` → `Manual.vue`（手册阅读）

开发服务器端口 8080，`vite.config.js` 把 `/api` 代理到 Flask（`http://127.0.0.1:5000`）。前端 `src/api/index.js` 用 axios（`baseURL: '/api'`）与后端通信。



### 6.3 校验监控（method/monitor.py）

`validate_theory(filename)`：重放所有定理的证明，记录状态（`VALID`/`STEP_FAILED`/`DEP_FAILED`/`AXIOM`/`UNPROVED`），并记录每个失败定理的错误原因，缓存到 `.json`。

## 7. 目录索引

| 目录 | 职责 |
|---|---|
| `kernel/` | 逻辑内核（Type/Term/Thm/原语/Proof/ProofTerm/Theory/Macro/Extension/Report） |
| `theories/` | 领域扩展包（logic/nat/real/integer/function/expr） |
| `core/` | 逻辑层基础设施（Tactic/Conv/Macro/Matcher/Auto/Search） |
| `method/` | 方法层与证明状态（ProofState/Method/Items/Monitor） |
| `syntax/` | 解析、打印、设置、`.pyhol` 格式 |
| `solvers/` | 外部求解器与自动证明（Z3/Omega/Simplex/Tseitin/SAT/Congc/Sympy） |
| `app/` | Flask 后端 API |
| `frontend/` | Vue 3 前端 |
| `library/` | 理论库（`.pyhol` 文件） |
| `imperative/` | Hoare 逻辑程序验证（独立子模块，`.imp` 格式） |
| `util/` | 工具函数（name/typecheck/unionfind/nat/set/list/string 等） |
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
theorem.steps (in .pyhol)
  ↓ state.parse_steps -> apply_method
Method.apply -> Tactic/Macro -> ProofTerm
  ↓ .export()
线性 Proof
  ↓ theory.check_proof（原语真校验 + 宏按 level 展开/求值）
校验报告 + 最终 Thm
```


---

**返回**：[`README.md`](README.md)

# 系统组织总览

> 本章粗略描述实现层的组织，这些部分较易改动。代码事实以当前目录结构为准。

## 1. 三层架构

```
kernel/          逻辑内核（Type/Term/Thm/原语/ProofTerm/Theory）
  │   15 条原语是唯一凭空构造定理的入口
  ▼
logic/           逻辑层（Conv/Tactic/Macro/Matcher/Context）
  │   组合原语与宏，提供自动化基础设施
  ▼
server/ + app/   应用层（Method/ProofState/Flask API）
                  面向用户的 API 与 web IDE
```

## 2. 理论组织

### 2.1 .pyhol 文件格式

理论以 `.pyhol` 文件存储（人类可读文本格式，替代旧 JSON）。每个文件含：

- 头部：`theory <name>`、`imports <list>`、`domains <list>`（可选）、`description "<text>"`。
- 内容：若干条目（item），类型有 `header`、`const`、`datatype`、`type`、`def`、`fun`、`inductive`、`axiom`、`theorem`。

`theorem` 条目可含 `proof` 块（`proof` ... `qed`），内含编号的证明步骤。

### 2.2 八种 Item 类型

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

`unchecked_extend` 遍历 exts，按类型分发。**不校验证明**（定义/公理直接信任）。

### 2.5 自动生成的定理

- `Datatype`：自动生成 distinct（`_neq`）、inject（`_inject`）、归纳定理（`_induct` + `var_induct` 属性）。
- `Fun`：每条 rule 一条 `_def_N` 定理 + `hint_rewrite` 属性。
- `Inductive`：每条 intro rule + `hint_backward` 属性 + `_cases` 消除定理。
- `Definition`：生成 `<cname>_def` 定理。

## 3. 领域扩展机制

> **注**：当前的 `domains/` 包机制是权益之计，后续可能调整。

当前机制：
- `.pyhol` 头部 `domains <name>` 声明要加载的领域包。
- `logic/basic.py` 在加载理论时 `importlib.import_module('domains.<name>')`。
- 领域包的 `__init__.py` 导入 `conv.py`、`macro.py`、`method.py`，通过 `@register_macro`/`@register_method` 装饰器注册（幂等）。

领域包目录：`domains/{nat,real,integer,function,expr}/`，每个含 `__init__.py` + `conv.py` + `macro.py` + `method.py`（部分）。

`server/methods/__init__.py` 也会预加载所有领域包，确保方法在理论加载前就注册。

## 4. 自动化

### 4.1 auto（logic/auto.py）

`solve(goal, pts)`：自动证明 goal。策略：
1. 若 goal 匹配某条件，直接返回。
2. 若某条件是合取/析取，分解后递归。
3. 按 goal 的 head 查 `global_autos`/`global_autos_neg` 注册表。
4. 先 `norm` 归一化 goal 再尝试。

`norm(t, pts)`：自动归一化。按 head 查 `global_autos_norm` 注册表，应用注册的 conv/函数。

`auto_macro`（level 1）：把 `solve`/`norm` 包成宏。

### 4.2 Z3（prover/z3wrapper.py）

- `convert(t, ...)`：HOL 项 -> Z3 表达式。
- `norm_term(t)`：用一组重写定理归一化后调 `fologic.simplify`。
- `solve(t)`：调 Z3 检查 `¬t` 是否 unsat（unsat 即证明）。
- `Z3Macro`（level 0，oracle）：不可展开，依赖 Z3 正确性。

### 4.3 其他 prover

| 模块 | 职责 |
|---|---|
| `prover/auto/auto.py` | best-first search 自动证明 |
| `prover/omega.py` | 自然数线性算术 |
| `prover/simplex.py` / `simplex_strict.py` | Simplex 算法（实数/整数） |
| `prover/tseitin.py` | Tseitin 编码（命题公式 -> CNF） |
| `prover/sat/zchaff.py` | DPLL SAT 求解 |
| `prover/proofrec.py` | Z3 proof reconstruction |
| `prover/fologic.py` | 一阶逻辑简化 |
| `smt/veriT/` | veriT SMT 集成 |

### 4.4 方法层自动化

- `simp`：遍历所有 `hint_rewrite` 定理，构造 `top_conv(rewr_conv(...))` 链。
- `norm`/`eval`/`linarith`：按目标类型分发到 `nat_norm`/`real_norm`/`int_norm` 等 `MacroTactic`。

## 5. 语法层（syntax/）

| 模块 | 职责 |
|---|---|
| `parser.py` | 基于 lark 的类型/项/定理解析器，含 Hindley-Milner 类型推断（`infertype.py`） |
| `printer.py` | 漂亮打印 |
| `pprint.py` | 高亮打印的 AST 表示 |
| `operator.py` | 运算符优先级与结合性表 |
| `settings.py` | 全局设置（unicode、highlight、line_length） |
| `pyhol.py` | `.pyhol` 格式的解析与导出 |
| `json_output.py` | JSON 输出 |

## 6. 应用层

### 6.1 Flask 后端（app/）

- `app/app.py`：Flask 应用工厂（`create_app()`，CORS + 自定义 JSON provider）。
- `app/ide.py`：理论编辑与证明接口（`/api/init-saved-proof`、`/api/forward-search`、`/api/backward-search`、`/api/apply-method`、`/api/load-json-file`、`/api/save-file`、`/api/validate-theory` 等）。
- `app/imperative.py`：Hoare 逻辑程序验证接口（独立子模块，`.imp` 文件）。
- `app/saint.py`：SAINT 符号积分 CAS 接口（独立子模块，`.calc` 文件）。
- `app/saint_library.py`：SAINT 基础库（`base.calc`）编辑接口。

`app/__init__.py` 导入上述路由模块，使所有 `/api/*` 路由在 `create_app()` 时注册。

### 6.2 前端（frontend/）

Vue 3 + Vite 单页应用，路由（`src/router.js`）：
- `/` → `Index.vue`（首页）
- `/ide` → `Editor.vue`（HOL 证明 IDE）
- `/saint` → `SaintIDE.vue`（SAINT 积分 IDE）
- `/program` → `ProgramIDE.vue`（程序验证 IDE）

开发服务器端口 8080，`vite.config.js` 把 `/api` 代理到 Flask（`http://127.0.0.1:5000`）。前端 `src/api/index.js` 用 axios（`baseURL: '/api'`）与后端通信。

### 6.3 SAINT 符号积分子系统

SAINT（`SAINT/`）是与 HOL 内核**互相独立**的符号计算 CAS，专精积分，模仿 Slagle 1961 的 SAINT 论文。数学事实以**数据**（`.calc` 文件）而非硬编码行为存放。

**式 AST**（`SAINT/expr.py`）：`Var/Const/Op/Fun/Deriv/Integral/EvalAt/Summation/Limit/SkolemFunc/Symbol`，用 `ty` 字段做标记联合；`Location` 处理子项定位（点号寻址如 `"1.0"`）。

**解析**（`SAINT/parser.py`）：Lark LALR 文法，优先级链 `atom < uminus < pow < times < plus < compare`。支持定积分 `INT x:[a,b]. body`、不定积分 `INT x. body`、导数 `D x. expr`、极限 `LIM {x -> a}. expr`、求和 `SUM(n,0,oo,body)`、绝对值 `|expr|`。

**归一化 / 相等判定**（`SAINT/poly.py`）：`normalize(e, conds)` 把表达式转成多项式（`to_poly`）再转回（`from_poly`），两项相等 ⟺ 归一化后相同。条件（`SAINT/conditions.py`）记录 `n != -1`、`x > 0` 等假设，用于 `check_wellformed`。

**规则引擎**（`SAINT/rules.py`）：每个 `Rule` 子类实现 `eval(e, ctx) -> Expr`。规则包括 `FullSimplify`（固定点循环）、`Linearity`、`CommonIntegral`/`DefiniteIntegralIdentity`/`IndefiniteIntegralIdentity`、`Substitution`/`SubstitutionInverse`、`IntegrationByParts`、`RewriteTrigonometric`（数据驱动 Fu 规则）、`SeriesExpansionIdentity`/`SeriesEvaluationIdentity`/`MergeSummation`/`SummationSimplify`、`ElimAbs`/`SplitRegion`/`ElimInfInterval`/`LHopital`/`ReduceLimit` 等。`make_rule(name, params)`（`app/saint.py`）是 API 层到规则类的分发器。

**自动证明**（`SAINT/slagle.py`）：把积分搜索建成 OR/AND 目标树，BFS 探索（按式深排序，默认 20s 超时）。算法规则 + 启发式规则（返回多个候选下一步）。

**`.calc` 数据格式**（`SAINT/calcfmt.py`）：`parse_calc_text`/`load_calc_file`/`export_calc`。一个文件混合：

- `theory` / `imports` 头部
- `header "标题" level = N` 章节
- `theorem "等式" conds = [...] category = ...` / `definition`：作为恒等式载入上下文
- `table sin ... endtable`：函数取值表
- `calculation "名"` + `goal`（目标积分）+ `target`（期望闭式）+ `calc <步骤> qed`：计算任务

关键设计：**`.calc` 只存过程（规则序列 + 参数），不存中间结果**——结果通过重放每条规则（`check_item`/`apply_step` in `rules.py`）重新推导；若给了 `target`，最终式必须 `normalize` 到它。

**SAINT API**（`app/saint.py`）：

| 端点 | 作用 |
|---|---|
| `/api/saint/files` | 列出所有 `.calc` 文件 |
| `/api/saint/load` | 加载 `.calc`，返回条目；目标为等式 `A = B` 时拆成 `goal=A`/`target=B`，渲染 LaTeX |
| `/api/saint/parse` | 解析表达式字符串，返回 `{text, latex}` |
| `/api/saint/apply` | 重放已有步骤后应用新规则，返回完整 `Calculation`（含各步 old/new 式） |
| `/api/saint/verify` | `normalize(expr1) == normalize(expr2)` 判相等 |
| `/api/saint/save` | `export_calc` 写回 `.calc` 文件 |
| `/api/saint/suggest` | 建议适用规则（无参规则 + 代换候选 + 分部积分 + 级数展开） |
| `/api/saint/library` | 返回 `base.calc` 库条目，按章节分组 |
| `/api/saint/library/save` | 保存库条目回 `base.calc` |

### 6.4 参数化系统验证

参数化系统验证**不是独立组件**，而是直接用 `.pyhol` 理论表达（由主 IDE 管理）。`library/gcl.pyhol` 提供 GCL 基础（`varType`/`scalarValue` 数据类型、`scalar_is_nat` 等）；具体系统作为导入 `gcl` 的理论，用 `inductive` 定义转换关系、`def` 定义不变量、`theorem` 声明不变量保持命题。

- `library/mutual_ex.pyhol`：互斥协议（4 条规则、5 条不变量，最小示例）。
- `library/german.pyhol`：German 缓存一致性协议（13 条规则、49 条不变量，大型案例）。

**GCL 编码**：状态是函数 `s :: varType ⇒ scalarValue`。标量变量 `CurCmd` 编码为 `s (Ident idx)`，参数化函数 `Cache_State k` 编码为 `s (Para (Ident idx) k)`；nat 值包成 `NatV`、bool 值包成 `BoolV`。转换规则 `trans` 是 `inductive`，其自动生成的 `trans_cases` 处理参数化情形分析（如 `k = i` 分支），配合 `function.pyhol` 的 `fun_upd_same`/`fun_upd_other` 重写引理可证不变量保持。不变量保持命题 `inv_preserved`（`∀s1 s2. inv s1 ⟶ trans s1 s2 ⟶ inv s2`）作为 `theorem` 声明，可留作待证目标（`UNPROVED`）。

### 6.5 校验监控（server/monitor.py）

`validate_theory(filename)`：重放所有定理的证明，记录状态（`VALID`/`STEP_FAILED`/`DEP_FAILED`/`AXIOM`/`UNPROVED`），并记录每个失败定理的错误原因，缓存到 `.json`。

## 7. 目录索引

| 目录 | 职责 |
|---|---|
| `kernel/` | 逻辑内核（Type/Term/Thm/原语/Proof/ProofTerm/Theory/Macro/Extension/Report） |
| `logic/` | 逻辑层（Conv/Tactic/Matcher/Context/Macros/Auto/Basic） |
| `domains/` | 领域扩展包（nat/real/integer/function/expr） |
| `server/` | 方法层与证明状态（ProofState/Method/Items/Monitor） |
| `syntax/` | 解析、打印、设置、`.pyhol` 格式 |
| `prover/` | 外部求解器与自动证明（Z3/Omega/Simplex/Tseitin/SAT/Auto） |
| `smt/` | SMT 集成（veriT） |
| `sat/` | SAT 求解器 |
| `app/` | Flask 后端 API |
| `frontend/` | Vue 3 前端 |
| `library/` | 理论库（`.pyhol` 文件） |
| `imperative/` | Hoare 逻辑程序验证（独立子模块，`.imp` 格式） |
| `SAINT/` | 符号积分 CAS（独立子模块，`.calc` 格式） |
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

### 8.3 SAINT 计算流程

```
.calc 书 ──calcfmt.py──▶ dict {theory, imports, content[...]}
  │
  ├─ context.load_book ─▶ Context（恒等式/函数表/条件）
  │
calculation "goal" ──parser.py──▶ Expr AST ──compstate.Calculation──▶ perform_rule
  │
  ▼
rules.py Rule.eval ──poly.normalize──▶ 规范多项式形式（相等判定）
  │
  ├─ apply_step（重放 + 校验）
  ├─ check_item（target 检查）
  └─ slagle.py（自动 OR/AND 搜索）
  │
  ▼
app/saint.py REST ──(axios /api, vite 代理)──▶ SaintIDE.vue
```

## 9. 与 HOL Light 的对比

| 概念 | HOL Light | holpy |
|---|---|---|
| 内核原语 | 8 个（`fusion.ml`） | 15 个（`kernel/thm.py`） |
| 转换 | `term -> thm` | `Conv` 类 |
| 策略 | `TAC`（目标->子目标） | `Tactic` 类 |
| 简化器 | 完整 simpset + term net | 基础 `simp` 方法 |
| **宏** | 无 | `Macro` + `level`/`eval`（自创） |
| **证明序列化** | 无（运行时调用序列） | `ProofTerm` + `check_proof`（自创） |
| **方法层** | 无（直接 OCaml REPL） | `Method` + 搜索/显示（自创） |
| **.pyhol 格式** | 无 | 自创 |
| 定义 | 强制 WF 证明 | `unchecked_extend` 信任 |
| 归纳类型 | `define_type` 产 `_RECURSION` | 只产 `_induct`，无 `_RECURSION` |

holpy 的"严肃性"来自"证明可独立重验"，而非"定义被强制保证一致"。

---

**返回**：[`README.md`](README.md)

# pyHOL Frontend API & Feature Documentation

> 本文件与 `backend/ide.py`、`backend/ide_v2.py`、`backend/imperative.py`、`backend/manual.py`
> 的实际路由保持一致。路由表以 Flask `app.url_map` 为准（`from backend import app`）。
>
> 权威来源：后端实现 + `manual/06_method.md`（方法层）+ `manual/07_system.md`（系统组织）。
> 前端调用点用 `grep -rn "api\.\(post\|put\|get\)\|fetch('/api" frontend/src` 复核。

## API 汇总表

### 理论编辑与证明（backend/ide.py）

| API 路由 | 方法 | 功能 | 前端调用位置 |
|----------|------|------|-------------|
| `/api/find-files` | POST | 理论文件列表（依赖拓扑序） | `Editor.load_files()` |
| `/api/load-json-file` | POST | 加载理论内容（`export_web` 条目） | `Editor.open_file()/reload_file()`、`ProgramIDE.prove_vc()/save_proof()` |
| `/api/save-file` | POST | 导出 `.pyhol` 并写盘 | `Editor.persist()`、`ProgramIDE.save_proof()` |
| `/api/rename-file` | POST | 重命名理论/程序文件 | `Editor.rename_file()`、`ProgramIDE.rename_file()` |
| `/api/remove-file` | PUT | 删除文件 | `Editor.delete_file()`、`ProgramIDE.delete_file()` |
| `/api/check-modify` | POST | 校验单个条目 | `Editor.check_item()/save_item()` |
| `/api/validate-theory` | POST | 验证文件内全部定理 | `Editor.validate_all()`、`ProgramIDE.save_proof()` |
| `/api/theorem-search` | POST | 按名称子串搜索定理（≤30 条） | `ProofArea.search_theorems()` |
| `/api/theory-status` | GET | 全部定理状态缓存 | `Editor.compute_thm_status()` |

### 证明（新管线，backend/ide_v2.py）

以稳定 `#[N]` ID 对接 `method/stable_state.py::StableProofState`；每次交互前重放历史步骤，后端无状态。

| API 路由 | 方法 | 功能 | 前端调用位置 |
|----------|------|------|-------------|
| `/api/v2/init-saved-proof` | POST | 重放 `steps[:index]`，返回证明状态 | `ProofArea.gotoStep()` |
| `/api/v2/apply-method` | POST | 应用一个方法步骤 | `ProofArea.apply_method_ajax()` |
| `/api/v2/backward-search` | POST | 反向搜索（有 goal） | `ProofArea.match_thm()` |
| `/api/v2/forward-search` | POST | 正向搜索（无 goal，有 facts） | `ProofArea.match_thm()` |
| `/api/v2/trust-report` | POST | 完整 verify，返回信任报告 | `ProofArea.check_trust()` |

### 程序验证（backend/imperative.py）

| API 路由 | 方法 | 功能 |
|----------|------|------|
| `/api/imp-list` | POST | 列出 `imperative/programs/*.imp` |
| `/api/imp-load` | POST | 解析 `.imp` 为结构化 `programs` |
| `/api/imp-compile` | POST | 保存并编译，生成 ``<name>.pyhol`` 与 VC 列表 |

> `.imp` 程序与自动生成的 `.pyhol` 都住在 `imperative/programs/`，**不**进 `library/`、不进主 IDE 文件列表。

### 手册（backend/manual.py）

| API 路由 | 方法 | 功能 |
|----------|------|------|
| `/api/manual-list` | POST | 列出 `manual/*.md`（README 置顶） |
| `/api/manual-load` | POST | 读取某个 markdown 文件 |

---

## API 详细规范

### 1. `/api/find-files` (POST)

**输入**：`{}`

**返回**：`{ "theories": ["logic_base", "logic", "set", "nat", ...] }`

`basic.load_metadata()` 扫描 `library/` 全部 `.pyhol` 后按 `order` 排序；只含手写理论库。

---

### 2. `/api/load-json-file` (POST)

**输入**：`{ filename, line_length?, profile? }`

**返回**：
```json
{
    "name": "set",
    "imports": ["logic"],
    "domains": [],
    "description": "...",
    "content": [
        {
            "ty": "type.abbrev", "name": "set", "args": ["a"], "def": "'a => bool",
            "display": {...}, "edit": {...}, "ext": ""
        },
        {
            "ty": "thm", "name": "conj_comm",
            "vars": { "A": "bool", "B": "bool" },
            "prop": "A ∧ B ⟷ B ∧ A",
            "attributes": ["hint_rewrite"],
            "steps": [ { "method_name": "rule", "goal": 0, "theorem": "iffI" } ],
            "display": {...}, "edit": {...}, "ext": "..."
        }
    ]
}
```

- 每个条目的 `export_web()` 形状（`core/items.py::Item.export_web`）= `export_json()` + `display` + `edit` + `ext`
  （`ext` 为 `printer.print_extensions(get_extension())`）。
- 条目 JSON 形状由条目类决定，前端必须按 `ty` 分发（见下方「条目类型」）。
- `display`/`edit` 里的 `prop`/`def` 等字段在超出行宽时是**字符串列表**（`[pprint.N(...)]`），
  不是可回灌的证明输入。后端 `ide_v2._load_theory` 会优先从理论缓存取解析后的 `prop`，避免把显示文本当输入。
- `steps` 为稳定 `#[N]` ID 字典（见 §6）。

---

### 3. `/api/save-file` (POST)

**输入**：`{ filename, content: { name, imports, domains, description, content } }`

`pyhol.export_pyhol(content)` 后写入 `basic.save_user_file(filename)`（`library/`，或已在
`imperative/programs/` 的文件），并使该文件的 `theory_cache` 时间戳失效。删除条目前端字段
`display`/`edit`/`ext`/`error`/`_error`/`_from_disk`，只留核心字段。

**返回**：`{}`

---

### 4. `/api/rename-file` (POST)

**输入**：`{ old, new, overwrite? }`。名字可带 `.pyhol`/`.json`/`.imp` 或裸名。
**返回**：`{ "ok": true }` 或 `{ "ok": false, "error": "..." }`。

---

### 5. `/api/remove-file` (PUT)

**输入**：`{ filename }`（裸名会先试 `library/`，再试 `imperative/programs/`）。
**返回**：`{}`。

---

### 6. `/api/check-modify` (POST)

**输入**：`{ filename, line_length?, limit_ty?, limit_name?, item }`。
已有条目传 `limit_ty`/`limit_name` 以在正确上下文里检查；新条目省略。

**返回**：`{ "item": { ... } }`；`item.error` 存在即失败：
```json
{ "error": { "err_type": "ItemException", "err_str": "...", "trace": "..." } }
```

`core/items.py::parse_edit(item)` 按 `item.ty` 建条目并 `parse`；前端新增条目必须先给出该 `ty` 需要的字段。

---

### 7. `/api/theorem-search` (POST)

**输入**：`{ theory_name, thm_name, pattern }`

**返回**：`{ "results": [ { "name": "conj_comm", "prop": "...", "attrs": ["hint_rewrite"] } ] }`（最多 30 条，大小写不敏感子串）。

---

### 8. `/api/theory-status` (GET)

**返回**：`{ "conj_comm": "VALID", "conjD1": "AXIOM", ... }`

读取 `core/basic.py` 的累积状态表（2026-09 从 kernel 迁出）。空对象表示尚未跑过验证。

---

### 9. `/api/validate-theory` (POST)

**输入**：`{ filename, force? }`

**返回**：
```json
{
    "statuses": { "conj_comm": "VALID", "bad_thm": "STEP_FAILED" },
    "errors": { "bad_thm": "proof has 1 open goal(s): ..." },
    "valid": 10, "axiom": 3, "unproved": 2, "failed": 1, "total": 16
}
```

四态：`VALID` / `AXIOM` / `UNPROVED` / `STEP_FAILED` / `DEP_FAILED`（后两者计入 `failed`）。
缓存按源哈希 + 依赖哈希，`force=true` 忽略缓存。

---

### 10. `/api/v2/init-saved-proof` (POST)

**输入**：`{ theory_name, thm_name, vars, prop, steps, index? }`

**返回**：
```json
{
    "state": {
        "vars": { "A": "bool" },
        "proof": [
            { "id": "0", "sid": 0, "rule": "sorry", "args": null, "prevs": [],
              "th": "A ⟶ A", "is_goal": true, "goal_pos": true,
              "origin": null, "case": null, "indent": 1 }
        ],
        "num_gaps": 1,
        "method_sig": { "rule": ["theorem"], "cut": ["cut_goal"] },
        "method_list_params": { "intro": ["names"], "elim": ["names"] },
        "method_direction": { "rule": "backward", "forward": "forward", "cut": "direct" },
        "open_goals": [ { "sid": 0, "prop": "A ⟶ A" } ]
    },
    "history": [ { "method_name": "rule", "goal": 0, "facts": [], "display": "rule conjI" } ],
    "num_gaps": 1,
    "load_time": 0.01
}
```

证明行显示语义（动词即身份）：

| 字段 | 含义 |
|---|---|
| `sid` | 稳定 ID（int）。`0` 是要证的定理（隐含） |
| `id` | 位置 ID（字符串，调试/缩进用） |
| `is_goal` | `rule == 'sorry'`：该行是缺口 |
| `goal_pos` | `true` → 显示为 `show ... by ...`；`false` → `have ... by ...` |
| `origin: "cut"` | cut 引入的中间目标（未证显示裸 `cut <prop>`，已证动词用 `cut`） |
| `case` | cases/disjE/induct 分支，前缀 `case <expr>:` |
| `rule: "obtain"` | elim 的显示行，渲染 `obtain <args> from #<prevs>` |
| `rule: "apply_prev"` / `"auto_close"` | 手动 / 自动闭合的可见行 |
| `indent` | 缩进层级（= 位置 ID 深度） |

`open_goals` 是后端给出的完整缺口表（含命题），前端**应直接使用**，不要自己从 `proof` 过滤重建。

---

### 11. `/api/v2/apply-method` (POST)

**输入**：`{ theory_name, thm_name, vars, prop, steps, index, step }`，
`step = { method_name, goal?, facts?, ...方法参数 }`；`goal`/`facts` 是稳定 ID。
无 goal 的正向步骤由后端 `_find_insertion_point` 自动定位。

**返回（成功）**：`{ state, new_items: [{sid, prop}], num_gaps, apply_time }`。
前端把 `new_items` 的 sid 写回 `step.new_ids` 以便重放。

**返回（需要参数）**：`{ "query": ["param_x"], "query_hints": {...} }`。
前端弹查询框，填入后以 `param_` 前缀重发（`rule`/`forward`/`apply_prev` 走 Inst；`names` 走列表）。

**返回（错误）**：`{ "error": { "err_type": "...", "err_str": "...", "trace": "..." } }`。

---

### 12. `/api/v2/backward-search` (POST)

**输入**：`{ theory_name, thm_name, vars, prop, steps, index, goal, facts }`

**返回**：
```json
{
    "results": [
        { "method_name": "rule", "theorem": "conjI", "goal": 5, "facts": [1],
          "_goal": ["A", "B"], "_thm": "A ⟹ B ⟹ A ∧ B", "fuzzy": false },
        { "method_name": "accept", "theorem": "conj_comm", "_goal": [], "_exact": true, "fuzzy": false }
    ],
    "fuzzy": [ { "method_name": "rule", "theorem": "conjI", "facts": [3], "fuzzy": true } ],
    "ctxt": {}
}
```

- `_goal` 为空 = 闭合目标；`_needs_params` = 需参数；`_fact` = 推导出的新事实。
- `results` 用原始事实顺序，`fuzzy` 是其余排列/子集（从大到小）。
- 精确闭合通道（C1）：整条命题匹配 goal 的定理以 `accept` 建议出现，不看 `hint_*` 属性。

---

### 13. `/api/v2/forward-search` (POST)

**输入**：`{ theory_name, thm_name, vars, prop, steps, index, facts }`

**返回**：`{ "results": [...], "fuzzy": [...], "ctxt": {} }`，结果形状同上，但只含正向方法
（`forward`、`rewrite`/`inst` 的 `target == 'fact'` 模式）。

---

### 14. `/api/imp-list` (POST)

**返回**：`{ "files": [ { "name": "gcd", "text": "..." } ] }`

---

### 15. `/api/imp-load` (POST)

**输入**：`{ name }`

**返回**：`{ ok, theory, imports, programs: [ { name, vars: [[nm, ty]], pre, post, body } ] }`；
失败 `{ "ok": false, "error": "..." }`。

---

### 16. `/api/imp-compile` (POST)

**输入**：`{ name, theory?, imports?, programs: [...] }`（结构化）或 `{ name, text }`（原文）。

**返回**：`{ ok, name, num_vcs, vcs: [ { program, index, name, prop, smt, proved } ] }`；
失败 `{ "ok": false, "error": "..." }`。

生成 ``<name>.pyhol`` 到 `imperative/programs/`；`proved = smt or 已有手工证明`。

---

### 17. `/api/manual-list` (POST) / `/api/manual-load` (POST)

`manual-list` → `{ "files": [ { "name": "README", "title": "README" }, ... ] }`。
`manual-load` 输入 `{ name }` → `{ ok, name, text }`。

---

## Trust（computation oracles）

计算 oracle 是"没有推导、直接信任结果"的 level-0 宏（`z3`、`nat_eval`、`real_eval`…）。
`/v2/*` 是**无状态**的（每次请求从头重放），所以 trust 集合必须**随每个请求发送**。

- **请求字段** `trust: string[]`：本次会话放行的 oracle 名。
  省略 → 后端默认 `core.verify.COMPUTATION_ORACLES`（11 个，与 `validate_library.py` 同一集合）；
  `[]` → 严格模式。
- **状态字段** `state.trust`（本次生效集合）、`state.known_oracles`（可选清单）。
- **`/api/validate-theory`** 同样接受 `trust`，省略即用同一默认值 —— 这样 IDE 的 Validate
  与命令行 `validate_library.py` 结论一致（此前 IDE 不传 trust，`auto`/`norm` 会莫名失败）。
- **`/api/v2/trust-report`**：交互态的 `verify(compute_only=True)` 会跳过最后那次独立原语重放，
  所以 `state` 里拿不到"这条证明到底用了哪些 oracle"。该端点按需跑**完整 verify**，返回
  `{ oracles, axioms, num_gaps, trust }`。前端 "Full verify" 按钮调它。
- **自我授权（重要）**：显式应用 level-0 方法（Auto tab 的 `z3`、`nat_norm` 等）时，
  `ProofState.apply_macro` 会把宏名写进会话 trust —— 这类步骤**不受 trust 列表限制**，
  即把 `z3` 取消勾选也不会拦住 `z3` 按钮。trust 列表真正约束的是**宏展开内部**发出的 oracle
  节点（`norm`/`auto` 做常数折叠时经 `*_eval_conv` 的 `auto_solve`）。这不是缺陷，是
  `core/verify.py` 的设计（显式受检调用即授权，见 `method/methods/core.py:396`）。

前端实现：会话状态在 `src/api/trust.js`（`null` = 用后端默认；显式数组 = 会话覆盖），
`ProofArea.vue` 头部 "Oracles n/m" 打开面板，改动经 `withTrust()` 附到 `init-saved-proof`
/`apply-method`/`backward-search`/`forward-search`/`trust-report` 的请求体上。

---

## 组件功能清单

### views/Editor.vue（主视图，三栏布局）

| 功能 | 方法 |
|------|------|
| 加载文件列表 / 打开 / 重载 | `load_files()` / `open_file(name)` / `reload_file()` |
| 新建 / 重命名 / 删除 | `create_file()` / `rename_file(old)` / `delete_file(name)` |
| 保存到磁盘 / 保存元数据 | `persist()` / `save_metadata()` |
| 验证全部 | `validate_all(force)` |
| 查询状态缓存 | `compute_thm_status()` |
| 条目增删移 | `add_item(ty)` / `remove_item(index)` / `move_item(index, dir)` |
| 编辑（检查/保存） | `check_item(index)` / `save_item(index)` |
| 证明切换 / 保存证明 | `toggle_prove(index)` / `save_proof(index, steps)` |
| 历史跳转 | `proof_goto_step(idx)` → `proof_area_ref.gotoStep` |

- 条目渲染按 `item.ty` 分发内容预览，编辑表单分发到 `components/items/*Edit.vue`。
- 证明模式下布局：Theory 30% / Proof 50% / History 20%。

### components/proof/ProofArea.vue（证明面板）

| 功能 | 方法 |
|------|------|
| 初始化 | `init_proof()`（有 `old_steps` 则重放，否则空证明） |
| 跳转步骤 | `gotoStep(new_index, set_selected, update_history)` → `/api/v2/init-saved-proof` |
| 后退/前进 | `step_backward()` / `step_forward()` |
| 搜索 | `match_thm()`（无 goal 有 facts → forward-search；有 goal → backward-search） |
| 应用建议 | `apply_suggestion(res)` |
| 应用方法（含参数查询） | `apply_method(method_name, args)` → `apply_method_ajax(input)` |
| 手动 / 自动 | `apply_manual_method()` / `apply_auto(method_name)` |
| 定理补全 | `search_theorems(pattern)`（≥2 字符） |
| 目标定位 | `compute_new_goal(start)` / `get_line_no_from_sid(sid)` |
| 保存 | `emit_save()` |
| 暴露 | `defineExpose({ apply_method, gotoStep, step_backward, step_forward, proof, num_gaps, steps, init_proof })` |

**选择模型**：`goal`（选中的缺口行下标，-1 表示无）+ `facts`（事实行下标数组）。
- 双击 sorry 行 → 选为目标；双击普通行命题 → 选为事实。
- 无目标 + 有事实 → 正向搜索；有目标 → 反向搜索。
- **方法列表不再硬编码**：Manual 下拉与 Auto 按钮按 `state.method_direction` 分组，
  候选来自 `state.method_sig`（后端已按 `limit` 过滤掉当前理论不可用的方法）。

### components/proof/ProofLine.vue（证明行）

- 双击命题 → 选事实；双击 sorry → 选目标。
- 动词渲染：`assume` / `fix` / `have` / `show` / `cut` / `obtain` / `apply_prev` / `auto_close` / 方法名。
- `rule: "intros"` 的机械框架行不渲染。

### components/proof/ProofQuery.vue（参数查询弹窗）

- `query = { title, desc?, fields, list_fields?, hints? }`；`list_fields` 渲染 +/- 动态输入框，提交时逗号 join。

### items/*Edit.vue（条目编辑表单）

| `item.ty` | 组件 | `getData()` 字段 |
|---|---|---|
| `header` | `HeaderEdit.vue` | `depth`, `name` |
| `type.ax` | `AxTypeEdit.vue` | `name`, `args` |
| `type.abbrev` | `TypeAbbrevEdit.vue` | `name`, `args`, `def` |
| `type.quot` | `QuotientEdit.vue` | `name`, `abs`, `rep`, `rel` |
| `type.ind` | `DatatypeEdit.vue` | `name`, `args`, `constrs` |
| `def.ax` | `ConstantEdit.vue` | `name`, `type` |
| `def` | `DefinitionEdit.vue` | `name`, `type`, `prop` |
| `def.ind` / `def.pred` | `InductiveEdit.vue` | `name`, `type`, `rules` |
| `thm` / `thm.ax` | `TheoremEdit.vue` | `name`, `vars`, `prop`, `attributes` |

---

## 项目类型 (item.ty)

以 `core/items.py::item_table` 为准（11 种）：

| ty | `.pyhol` 关键字 | 说明 |
|----|--------|------|
| `header` | — | 章节标题 |
| `type.ax` | `type` | 公理类型 |
| `type.abbrev` | `typeabbrev` | 类型同义词（如 `typeabbrev set 'a = 'a => bool`） |
| `type.quot` | `quotient` | 商类型（如 `quotient real (mk_real, dest_real) treal_eq`） |
| `type.ind` | `datatype` | 归纳数据类型 |
| `def.ax` | `constant` | 常量声明 |
| `def` | `definition` | 定义 |
| `def.ind` | `fun` | 归纳定义（递归函数） |
| `def.pred` | `inductive` | 归纳谓词 |
| `thm` | `theorem` | 定理 |
| `thm.ax` | `axiom` | 公理 |

---

## 定理状态图标

| 状态 | 图标 | 颜色 | 说明 |
|------|------|------|------|
| `VALID` | ✓ | 绿色 | 证明有效 |
| `STEP_FAILED` | ✗ | 红色 | 证明重放失败 |
| `DEP_FAILED` | ⚠ | 橙色 | 依赖的定理失败 |
| `UNPROVED` | ○ | 灰色 | 未证明 |
| `AXIOM` | □ | 青色 | 公理 |

---

## 布局结构（证明模式）

```
┌──────────────────────────────────────────────────────────────────┐
│ pyHOL  [file ▼] [New] [Items ▼]                    logic | Saving..│
├───────────────────────┬────────────────────────────┬───────────────┤
│  Theory Panel (30%)   │  Proof Panel (50%)         │ History (20%) │
│  文件操作 / 元数据      │  标题行（thm/gaps）          │ Open goals    │
│  item 列表 + 状态图标   │  选择栏（goal/facts）        │ （含命题）     │
│                       │  Suggest/Manual/Auto tabs   │ History       │
│                       │  证明行（双击选 goal/fact）   │ ← / n/m / →   │
└───────────────────────┴────────────────────────────┴───────────────┘
```

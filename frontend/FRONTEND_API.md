# HOLPy Frontend API & Feature Documentation

> 本文件与 `app/ide.py`、`app/integral.py`、`app/imperative.py` 的路由保持一致。
> 最近提交（`ff638694` 三栏证明布局、`7db402d7` 前后向搜索分离）改变了证明搜索流程，
> 新增了 `/api/forward-search`、`/api/backward-search`、`/api/theorem-search`、`/api/validate-theory`、`/api/theory-status`、`/api/remove-file`、`/api/find-link`。

## API 汇总表

### 理论编辑与证明（app/ide.py）

| API 路由 | HTTP 方法 | 功能 | 前端调用位置 |
|----------|----------|------|-------------|
| `/api/find-files` | POST | 获取理论文件列表 | Editor.load_files() |
| `/api/load-json-file` | POST | 加载理论文件内容 | Editor.open_file() / reload_file() |
| `/api/save-file` | POST | 保存理论文件（导出为 .pyhol） | Editor.persist() |
| `/api/remove-file` | PUT | 删除理论文件 | Editor.delete_file() |
| `/api/check-modify` | POST | 检查修改的 item | Editor.check_item() / save_item() |
| `/api/find-link` | POST | 定位 item 所在文件与位置 | ExpressionNode |
| `/api/v2/init-saved-proof` | POST | 加载/跳转到证明步骤（稳定 `#[N]` ID） | ProofArea.gotoStep() |
| `/api/v2/forward-search` | POST | 正向搜索（仅事实，无目标，稳定 ID） | ProofArea.match_thm() |
| `/api/v2/backward-search` | POST | 反向搜索（有目标，可选事实，稳定 ID） | ProofArea.match_thm() |
| `/api/v2/apply-method` | POST | 应用证明方法（稳定 ID） | ProofArea.apply_method_ajax() |
| `/api/theorem-search` | POST | 按名称模式搜索定理（手动 tab 补全） | ProofArea.search_theorems() |
| `/api/check-proof` | POST | 检查证明完整性（后端保留） | — |
| `/api/validate-theory` | POST | 验证理论全部定理 | Editor.validate_all() |
| `/api/theory-status` | GET | 查询全部定理证明状态缓存 | Editor.compute_thm_status() |

### 积分验证（app/integral.py）

| API 路由 | HTTP 方法 | 功能 |
|----------|----------|------|
| `/api/integral-load-book-list` | POST | 加载积分书列表 |
| `/api/integral-load-book-content` | POST | 加载积分书内容 |
| `/api/integral-open-file` | POST | 打开积分文件 |
| `/api/integral-save-file` | POST | 保存积分文件 |
| `/api/clear-item` | POST | 清空 item |
| `/api/query-integral` | POST | 计算积分 |
| `/api/query-latex-expr` | POST | 查询 LaTeX 表达式 |
| `/api/query-identities` | POST | 查询恒等式 |
| `/api/add-function-definition` | POST | 添加函数定义 |
| `/api/add-goal` | POST | 添加目标 |
| `/api/proof-by-calculation` | POST | 计算法证明 |
| `/api/proof-by-induction` | POST | 归纳法证明 |
| `/api/proof-by-rewrite-goal` | POST | 重写目标证明 |
| `/api/expand-definition` | POST | 展开定义 |
| `/api/fold-definition` | POST | 折叠定义 |
| `/api/solve-equation` | POST | 解方程 |
| `/api/perform-step` | POST | 执行证明步骤 |
| `/api/query-theorems` | POST | 查询可用定理 |
| `/api/query-vars` | POST | 查询变量 |
| `/api/query-expr` | POST | 解析表达式 |
| `/api/query-last-expr` | POST | 查询最近表达式 |

### 程序验证（app/imperative.py）

| API 路由 | HTTP 方法 | 功能 |
|----------|----------|------|
| `/api/get-program-file` | POST | 加载程序文件 |
| `/api/program-verify` | POST | 验证程序 |
| `/api/save-program-proof` | POST | 保存程序证明 |

---

## API 详细规范

### 1. `/api/find-files` (POST)

**功能**：返回所有理论文件的列表（按依赖拓扑顺序排序）。

**输入参数**：无

**返回格式**：
```json
{ "theories": ["logic_base", "logic", "set", "nat", ...] }
```

---

### 2. `/api/load-json-file` (POST)

**功能**：加载指定理论文件的完整内容。在 `fresh_theory()` 中解析并导出每个 item 的 display/edit/ext 数据。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 理论文件名（不含 .pyhol 后缀） |
| `line_length` | int | (可选) 打印行最大长度 |
| `profile` | boolean | (可选) 是否启用性能分析 |

**返回格式**：
```json
{
    "name": "logic",
    "imports": ["logic_base"],
    "domains": [],
    "description": "Basic results in logic",
    "content": [
        {
            "ty": "thm",
            "name": "conj_comm",
            "display": { "ty": "thm", "name": "...", "vars": [...], "prop": [...], "attributes": [...] },
            "edit": { "ty": "thm", "name": "...", "vars": "...", "prop": "...", "attributes": [...] },
            "ext": "...",
            "vars": { "A": "bool", "B": "bool" },
            "prop": "A ∧ B ⟷ B ∧ A",
            "attributes": ["hint_rewrite"],
            "steps": [
                { "method_name": "apply_backward_step", "goal_id": "0", "theorem": "iffI" }
            ]
        }
    ]
}
```

---

### 3. `/api/save-file` (POST)

**功能**：将内容保存为 `.pyhol` 文本（`pyhol.export_pyhol`），写入 `library/<filename>.pyhol`，并使该文件的理论缓存失效（删除 timestamp）。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 理论文件名 |
| `content` | object | `{ name, imports, domains, description, content }` |

**返回格式**：`{}`

---

### 4. `/api/remove-file` (PUT)

**功能**：删除 `library/<filename>.pyhol`，并从 `theory_cache` 移除。

**输入参数**：`{ "filename": "my_theory" }`

**返回格式**：`{}`

---

### 5. `/api/check-modify` (POST)

**功能**：在 `fresh_theory()` 中加载理论（可选 limit），解析编辑数据并导出检查结果。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 理论文件名 |
| `item` | object | 编辑后的 item 数据（getData()） |
| `limit_ty` | string | (可选) 限制类型（已有 item 传 `old_item.ty`） |
| `limit_name` | string | (可选) 限制名称（已有 item 传 `old_item.name`） |
| `line_length` | int | (可选) |

**返回格式**：
```json
{
    "item": {
        "ty": "thm", "name": "conj_comm",
        "display": {...}, "edit": {...}, "ext": "...",
        "vars": {...}, "prop": "...", "attributes": [...],
        "error": { "err_type": "...", "err_str": "...", "trace": "..." }
    }
}
```
`item.error` 存在表示检查失败。

---

### 6. `/api/v2/init-saved-proof` (POST)

**功能**（新稳定 ID 管道）：加载理论到指定定理为止，重放 `steps` 到 `index`，返回证明状态。每次交互（搜索/应用/跳转）前都会调用，后端是无状态的。步骤使用稳定 ID：`step = { method_name, goal (int sid), facts ([int sid]), new_ids ([int],可选) }`。`#0` 是要证明的定理（隐含）。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称（新定理可能不在文件中，此时加载整个理论） |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表（全部历史步骤） |
| `index` | int | (可选) 重放到该步骤索引 |

**返回格式**：
```json
{
    "state": {
        "vars": { "A": "bool", "B": "bool" },
        "proof": [
            { "id": "0", "th": "A ⟹ B ⟹ A ∧ B ⟹ ...", "rule": "assume", "args": "", "prevs": [] },
            { "id": "1", "th": "...", "rule": "sorry", "args": "", "prevs": [] },
            { "id": "2", "th": "...", "rule": "intros", "args": "", "prevs": ["0","1"] }
        ],
        "num_gaps": 1,
        "method_sig": { "cut": ["goal"], "apply_backward_step": ["theorem"], ... },
        "method_list_params": { "introduction": ["names"], "exists_elim": ["names"] }
    },
    "history": [
        { "step_output": [...], "goal_id": "0", "fact_ids": ["1"] }
    ],
    "num_gaps": 1
}
```

---

### 7. `/api/v2/forward-search` (POST)

**功能**（新稳定 ID 管道）：正向搜索 —— 无需目标，根据选中事实推导新事实。返回结果的 `facts`/`goal` 为稳定 ID。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称 |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表 |
| `index` | int | 当前步骤索引 |
| `step` | object | `{ "fact_ids": ["1", "3"] }`（必须有事实） |

**返回格式**：
```json
{
    "results": [
        {
            "method_name": "apply_forward_step",
            "theorem": "subset_trans",
            "fact_ids": ["1", "3"],
            "_fact": ["B ⊆ C"],
            "_thm": "A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C"
        },
        {
            "method_name": "apply_forward_step",
            "theorem": "image_union",
            "_needs_params": ["param_x"]
        }
    ],
    "ctxt": {}
}
```
- `_fact`：推导出的新事实
- `_thm`：定理陈述
- `_needs_params`：参数未定，点击后走参数查询

---

### 8. `/api/v2/backward-search` (POST)

**功能**（新稳定 ID 管道）：反向搜索 —— 必须有目标，可选事实。若存在闭合目标的解，只保留闭合解。返回结果的 `facts`/`goal` 为稳定 ID。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称 |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表 |
| `index` | int | 当前步骤索引 |
| `step` | object | `{ "goal_id": "5", "fact_ids": ["1", "3"] }` |

**返回格式**：
```json
{
    "results": [
        {
            "method_name": "apply_backward_step",
            "theorem": "conjI",
            "goal_id": "5",
            "fact_ids": ["1"],
            "_goal": ["A", "B"],
            "_thm": "A ⟹ B ⟹ A ∧ B"
        },
        { "method_name": "reflexive", "goal_id": "5", "_goal": [] }
    ],
    "ctxt": { "A": "bool", "B": "bool" }
}
```

---

### 9. `/api/theorem-search` (POST)

**功能**：在当前理论上下文中按名称子串（不区分大小写）搜索定理，最多返回 30 条，用于手动 tab 的定理自动补全。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 正在证明的定理（用于 limit 上下文） |
| `pattern` | string | 匹配模式 |

**返回格式**：
```json
{
    "results": [
        { "name": "conj_comm", "prop": "A ∧ B ⟷ B ∧ A", "attrs": ["hint_rewrite"] }
    ]
}
```

---

### 10. `/api/v2/apply-method` (POST)

**功能**（新稳定 ID 管道）：应用证明方法。`step` 使用稳定 ID（`goal`/`facts`），无 goal 的正向方法由后端自动定位插入点。成功时返回 `state` + `new_items`（`[{sid, prop}]`），前端把 `new_items` 的 sid 写回步骤的 `new_ids` 以便重放。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称 |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表 |
| `index` | int | 当前步骤索引 |
| `step` | object | `{ "method_name": "...", "goal_id": "5", "fact_ids": [...], "theorem": "...", ... }`（方法参数，param_* 前缀为实例化参数） |

**返回格式（成功）**：
```json
{
    "state": { "vars": {...}, "proof": [...], "num_gaps": 0, "method_sig": {...}, "method_list_params": {...} },
    "history": [ { "step_output": [...], "goal_id": "5", "fact_ids": [...] } ],
    "step": { "method_name": "...", "goal_id": "5", ... }
}
```
前端用返回的 `step`（后端解析后的 goal_id）覆盖本地 step 再入史。

**返回格式（需要参数）**：
```json
{ "query": ["param_x", "param_y"] }
```
前端弹出查询，填入后以 `param_` 前缀重发。

**返回格式（错误）**：
```json
{ "error": { "err_type": "...", "err_str": "...", "trace": "..." } }
```

---

### 11. `/api/check-proof` (POST)

**功能**：重放全部步骤并检查证明，返回 gap 数（后端保留，前端未直接调用）。

**输入参数**：同 `init-saved-proof`（含 `steps`，不含 `index`）

**返回格式**：`{ "num_gaps": 0 }`

---

### 12. `/api/validate-theory` (POST)

**功能**：验证理论中所有定理。使用 `.json` 状态缓存：`.pyhol` 未变化时直接返回缓存结果；否则重放每个定理的证明并写回缓存。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 理论文件名 |
| `force` | boolean | (可选) 为 true 时忽略缓存强制重验 |

**返回格式**：
```json
{
    "statuses": { "conj_comm": "VALID", "conjD1": "AXIOM", "big_thm": "UNPROVED", "bad_thm": "STEP_FAILED" },
    "errors": { "bad_thm": "proof has 1 open goal(s): ..." },
    "valid": 10, "axiom": 3, "unproved": 2, "failed": 1, "total": 16
}
```

`errors` 为每个失败定理的错误原因（`STEP_FAILED`/`DEP_FAILED` 才有），`VALID`/`AXIOM`/`UNPROVED` 无对应条目。

---

### 13. `/api/theory-status` (GET)

**功能**：返回当前全局理论中所有定理的状态映射（内存中 `theory.thy.thm_status`）。

**返回格式**：
```json
{ "conj_comm": "VALID", "conjD1": "AXIOM", "big_thm": "UNPROVED", "bad_thm": "STEP_FAILED" }
```

---

### 14. `/api/find-link` (POST)

**功能**：查询 item 的定义位置（用于表达式跳转）。

**输入参数**：`{ "filename": "nat", "ext_ty": "thm", "name": "plus_comm" }`

**返回格式**：`{ "filename": "nat", "index": 12 }` 或 `{}`（未找到）

---

## 组件功能清单

### views/Editor.vue（主视图，三栏布局）

| 功能 | 方法 | 说明 |
|------|------|------|
| 加载文件列表 | `load_files()` | 调用 `/api/find-files` |
| 打开文件 | `open_file(name)` | 调用 `/api/load-json-file`，标记 `_from_disk` |
| 重新加载 | `reload_file()` | 重新加载当前文件 |
| 新建文件 | `create_file()` | prompt 名称后调用 `/api/save-file` |
| 删除文件 | `delete_file()` | 调用 `/api/remove-file` (PUT) |
| 保存到磁盘 | `persist()` | 清理内部字段（`_error/_from_disk/display/edit/ext/error`）后调用 `/api/save-file` |
| 保存元数据 | `save_metadata()` | 编辑 imports/domains/description 后保存并重载 |
| 验证全部 | `validate_all(force)` | 调用 `/api/validate-theory`，toast 显示统计 |
| 查询状态缓存 | `compute_thm_status()` | fetch `/api/theory-status`，缺失 item 填默认值 |
| 添加项目 | `add_item(ty)` | 按 ty 初始化空 item 并进入编辑 |
| 删除项目 | `remove_item(index)` | 确认后删除并持久化 |
| 移动项目 | `move_item(index, dir)` | 上移/下移并持久化 |
| 检查编辑 | `check_item(index)` | 调 `/api/check-modify`（已有 item 传 limit_ty/limit_name） |
| 保存编辑 | `save_item(index)` | check-modify → 更新内存 item（保留 steps）→ persist → reload |
| 证明切换 | `toggle_prove(index)` | 打开/关闭 ProofArea |
| 保存证明 | `save_proof(index, steps)` | 写回 steps 并持久化 |
| 历史跳转 | `proof_goto_step(idx)` | 委托 `proof_area_ref.gotoStep` |
| 上下文更新 | `handle_set_context(data)` | 接收 history/history_idx/open_goals |

### components/proof/ProofArea.vue（证明面板）

| 功能 | 方法 | 说明 |
|------|------|------|
| 初始化 | `init_proof()` | 有 old_steps 则恢复，否则空证明 |
| 跳转步骤 | `gotoStep(new_index, set_selected, update_history)` | 调 `/api/init-saved-proof`，更新 proof/num_gaps/method_sig，emit open_goals |
| 后退/前进 | `step_backward()` / `step_forward()` | index ±1 后 gotoStep |
| 搜索方法 | `match_thm()` | 按选择分派：无目标有事实 → `/forward-search`；有目标 → `/backward-search` |
| 应用建议 | `apply_suggestion(res)` | 只取 method-specific 参数，用当前选择（current_state） |
| 应用方法 | `apply_method(method_name, args)` | 按 method_sig 检查缺参 → 查询弹窗或直接 `apply_method_ajax` |
| 手动应用 | `apply_manual_method()` | 手动 tab：所选方法 + manual_params |
| 自动方法 | `apply_auto(method_name)` | 无参自动方法（simp/norm/eval 等） |
| 执行方法 | `apply_method_ajax(input)` | 调 `/api/apply-method`；query → 查询弹窗重发；error → toast；成功 → 用返回 step、截断史后 push、gotoStep |
| 定理补全 | `search_theorems(pattern)` | 调 `/api/theorem-search`（pattern ≥ 2 字符） |
| 新目标 | `compute_new_goal(start)` | 找第一个 sorry 行 |
| 目标/事实定位 | `get_line_no_from_id(id)` | proof 数组索引 ↔ item id |
| 保存步骤 | `emit_save()` | emit `save-steps`（深拷贝） |
| 暴露接口 | `defineExpose` | `apply_method / gotoStep / step_backward / step_forward / proof / num_gaps / steps / init_proof` |

**选择模型**：`goal`（选中的 sorry 行号，为 -1 表示无目标）+ `facts`（事实行号数组）。
- 双击 sorry 行 → 选为目标（`mark_goal`，清除事实）
- 双击普通行命题 → 选为事实（`mark_fact`；无目标模式下允许同层及外层上下文事实）
- 无目标 + 有事实 → 正向搜索；有目标 → 反向搜索

### components/proof/ProofLine.vue（证明行）

- 双击命题 → 选中为事实；双击 sorry 行 → 选中为目标
- 方向标记：`→` 正向推导（apply_forward_step/apply_fact 等）、`←` 反向应用（apply_backward_step 等）
- `can_select` 控制可点击性（无目标模式允许同层 + 外层事实）

### components/proof/ProofContext.vue（上下文面板）

| 功能 | 说明 |
|------|------|
| 显示变量 | `ctxt` 对象，格式 `name :: type` |
| 显示历史 | `steps` 数组，每个元素有 `step_output` |
| 步骤选择 | 单击选择，Shift+点击扩展选区 |
| 步骤跳转 | 点击步骤调用 `ref_proof.gotoStep(index)` |
| 删除步骤 | `deleteStep()` 删除选中步骤 |

### components/proof/ProofStatus.vue（状态面板）

| 功能 | 说明 |
|------|------|
| 显示状态 | `status` 文本 |
| 显示堆栈 | `trace` 文本（可展开/折叠） |
| 显示指令 | `instr` 高亮文本 + `instr_no` 编号 |
| 步骤跳转 | `<` `>` 按钮调用 step_backward/step_forward |
| 显示搜索结果 | `search_res` 列表（Suggest tab 按方向分组：derive/rewrite/backward 互斥） |
| 应用方法 | 点击搜索结果调用 `ref_proof.apply_thm_tactic(i)`（现为 apply_suggestion） |

### components/proof/ProofQuery.vue（参数查询弹窗）

| 功能 | 说明 |
|------|------|
| 显示标题 | `query.title` |
| 显示字段 | `query.fields` 数组 |
| 参数输入 | ExpressionEdit 输入框 |
| 确认 | emit `query-ok` 携带 `vals` |
| 取消 | emit `query-cancel` |

---

## 项目类型 (item.ty)

| ty | 关键字 | 显示组件 | 编辑组件 | 说明 |
|----|--------|----------|----------|------|
| `header` | — | 直接渲染 | HeaderEdit | 标题段落 |
| `type.ax` | `type` | AxTypeEdit | AxTypeEdit | 类型声明 |
| `def.ax` | `constant` | Constant | ConstantEdit | 常量声明 |
| `type.ind` | `datatype` | Datatype | DatatypeEdit | 归纳数据类型 |
| `def` | `definition` | Definition | DefinitionEdit | 定义 |
| `def.ind` | `fun` | Inductive | InductiveEdit | 归纳定义 |
| `def.pred` | `inductive` | Inductive | InductiveEdit | 归纳谓词 |
| `thm` | `theorem` | Theorem | TheoremEdit | 定理 |
| `thm.ax` | `axiom` | Axiom | TheoremEdit | 公理 |

---

## 定理状态图标

| 状态 | 图标 | 颜色 | 说明 |
|------|------|------|------|
| `VALID` | ✓ | 绿色 | 证明有效 |
| `STEP_FAILED` | ✗ | 红色 | 证明重放失败 |
| `DEP_FAILED` | ⚠ | 橙色 | 依赖的定理失败 |
| `UNPROVED` | ○ | 灰色 | 未证明 |
| `AXIOM` | □ | 青色 | 公理 |
| `PENDING` | ⏳ | 灰色 | 待验证 |
| `DIRTY` | • | 黄色 | 文件已修改 |

---

## 布局结构（证明模式）

```
┌──────────────────────────────────────────────────────────────────┐
│ HOLPy  [file ▼] [New] [Items ▼]                    logic | Saving..│
├───────────────────────┬────────────────────────────┬───────────────┤
│  Theory Panel (30%)   │  Proof Panel (50%)         │ History (20%) │
│  ┌─────────────────┐  │  ┌──────────────────────┐  │ Open goals     │
│  │ Delete|Validate |  │  │ thm prop ... [gaps]  │  │ ────────────── │
│  │ Force Validate  │  │  │ [Selection bar]      │  │ History        │
│  │ metadata        │  │  │ [Suggest/Manual/Auto]│  │ 0 Initial      │
│  ├─────────────────┤  │  ├──────────────────────┤  │ 1 intros       │
│  │ items list      │  │  │ proof lines          │  │ 2 apply_prev   │
│  │ (thm/def/...)   │  │  │ (双击选 goal/facts)  │  │ ...            │
│  └─────────────────┘  │  └──────────────────────┘  │                │
│                       │  [← 后退 | n/m | 前进 →]    │                │
└───────────────────────┴────────────────────────────┴───────────────┘
```

- **顶部菜单栏**：文件下拉（`find-files`）、New、Items 添加菜单、当前文件名、Saving/Validating 状态
- **左侧 Theory Panel（30%）**：文件操作按钮、元数据编辑、item 列表（含状态图标、编辑/证明按钮）
- **中间 Proof Panel（50%）**：ProofArea —— 标题行（定理名/命题/gaps）、选择栏（goal/facts）、三个 tab（Suggest 建议 / Manual 手动 / Auto 自动）、证明行列表
- **右侧 History Panel（20%）**：Open goals 列表 + 证明历史（可点击跳转、←→ 导航）
- Toast 提示在顶部居中显示

# HOLPy Frontend API & Feature Documentation

## API 汇总表

| API 路由 | HTTP 方法 | 功能 | 前端调用位置 |
|----------|----------|------|-------------|
| `/api/find-files` | POST | 获取理论文件列表 | Editor.load_filelist() |
| `/api/load-json-file` | POST | 加载理论文件内容 | Editor.load_file() |
| `/api/save-file` | POST | 保存理论文件 | Theory.save_json_file() |
| `/api/check-modify` | POST | 检查修改的 item | Theory.parse_item() |
| `/api/init-saved-proof` | POST | 加载/跳转到证明步骤 | ProofArea.gotoStep() |
| `/api/search-method` | POST | 搜索可用方法 | ProofArea.match_thm() |
| `/api/apply-method` | POST | 应用证明方法 | ProofArea.apply_method_ajax() |
| `/api/check-proof` | POST | 检查证明完整性 | (未在前端直接调用) |
| `/api/check-theory` | POST | 检查理论完整性 | (未在前端直接调用) |

---

## API 详细规范

### 1. `/api/find-files` (POST)

**功能**：返回所有理论文件的列表。

**输入参数**：无特殊参数

**返回格式**：
```json
{
    "theories": ["thy1", "thy2", ...]
}
```

---

### 2. `/api/load-json-file` (POST)

**功能**：加载指定理论文件的完整内容。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 文件名 |
| `line_length` | int | 打印行最大长度 |
| `profile` | boolean | 是否启用性能分析 |

**返回格式**：
```json
{
    "name": "theory_name",
    "imports": ["dep1", "dep2"],
    "description": "...",
    "content": [
        {
            "ty": "thm",
            "name": "theorem_name",
            "display": { ... },
            "edit": { ... },
            "proof": [...],
            "num_gaps": 0,
            "vars": { "x": "nat" },
            "prop": "x + y = y + x",
            "steps": [...]
        }
    ]
}
```

---

### 3. `/api/save-file` (POST)

**功能**：将数据保存到 JSON 文件。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 文件名 |
| `content` | object | 要保存的完整内容 |

**返回格式**：`{}`

---

### 4. `/api/check-modify` (POST)

**功能**：检查修改后的 item 是否有效。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `filename` | string | 文件名 |
| `line_length` | int | 打印行最大长度 |
| `item` | object | 要检查的编辑数据 |
| `limit_ty` | string | (可选) 限制类型 |
| `limit_name` | string | (可选) 限制名称 |

**返回格式**：
```json
{
    "ty": "thm",
    "name": "...",
    "display": { ... },
    "edit": { ... },
    "ext": "...",
    "error": { "err_type": "...", "err_str": "...", "trace": "..." }
}
```

---

### 5. `/api/init-saved-proof` (POST)

**功能**：加载已保存的证明，返回到指定步骤的证明状态。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称 |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表 |
| `index` | int | 要跳转到的步骤索引 |

**返回格式**：
```json
{
    "proof": {
        "vars": { "x": "nat" },
        "proof": [
            { "id": "0", "th": "...", "rule": "sorry", "args": "", "prevs": [] }
        ],
        "num_gaps": 1,
        "method_sig": { "cut": ["goal"], "induction": ["var"] }
    },
    "steps": [
        { "step_output": [...], "goal_id": "0", "fact_ids": [] }
    ],
    "num_gaps": 1
}
```

---

### 6. `/api/search-method` (POST)

**功能**：搜索适用于当前证明状态的方法/定理。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称 |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表 |
| `index` | int | 当前步骤索引 |
| `step` | object | `{ "goal_id": "0", "fact_ids": ["1"] }` |

**返回格式**：
```json
{
    "search_res": [
        {
            "method_name": "apply_backward_step",
            "display": [...],
            "goal_id": "0",
            "fact_ids": [],
            "theorem": "add_comm"
        }
    ],
    "ctxt": { "x": "nat", "y": "nat" }
}
```

---

### 7. `/api/apply-method` (POST)

**功能**：应用一个证明方法。

**输入参数**：
| 参数 | 类型 | 说明 |
|------|------|------|
| `theory_name` | string | 理论名称 |
| `thm_name` | string | 定理名称 |
| `vars` | dict | 变量字典 |
| `prop` | string | 命题 |
| `steps` | list | 步骤列表 |
| `index` | int | 当前步骤索引 |
| `step` | object | 方法参数 |

**返回格式（成功）**：
```json
{
    "proof": { "vars": {...}, "proof": [...], "num_gaps": 0, "method_sig": {...} },
    "steps": [{ "step_output": [...] }],
    "num_gaps": 0
}
```

**返回格式（需要参数）**：
```json
{
    "query": ["param_name1", "param_name2"]
}
```

**返回格式（错误）**：
```json
{
    "error": { "err_type": "...", "err_str": "...", "trace": "..." }
}
```

---

## 组件功能清单

### Editor.vue 功能

| 功能 | 方法 | 说明 |
|------|------|------|
| 加载文件列表 | `load_filelist()` | 调用 `/api/find-files` |
| 新建文件 | `new_file()` | 弹窗输入名称 |
| 打开文件 | `open_file()` | 弹窗输入文件名并加载 |
| 刷新文件 | `load_file()` | 调用 `/api/load-json-file` |
| 保存文件 | `save_file()` | 调用 `/api/save-file` |
| 设置证明引用 | `handle_set_proof(ref)` | 保存 ProofArea 引用 |
| 处理查询 | `handle_query(query)` | 显示 ProofQuery |
| 查询确认 | `handle_query_ok(vals)` | 返回参数值 |
| 查询取消 | `handle_query_cancel()` | 取消查询 |
| 链接跳转 | `handleGoToLink(filename, index)` | 跳转到导入的理论 |
| 删除步骤 | `delete_step()` | 委托 ProofContext |
| 插入目标 | `apply_cut()` | `ref_proof.apply_method('cut')` |
| 情况分析 | `apply_cases()` | `ref_proof.apply_method('cases')` |
| 归纳法 | `apply_induction()` | `ref_proof.apply_method('induction')` |
| 引入 | `introduction()` | `ref_proof.apply_method('introduction')` |
| 恢复引入 | `revert_intro()` | `ref_proof.apply_method('revert_intro')` |
| 新变量 | `new_var()` | `ref_proof.apply_method('new_var')` |
| 后向应用 | `apply_backward_step()` | `ref_proof.apply_method('apply_backward_step')` |
| 前向应用 | `apply_forward_step()` | `ref_proof.apply_method('apply_forward_step')` |
| 重写目标 | `rewrite_goal()` | `ref_proof.apply_method('rewrite_goal')` |
| 重写事实 | `rewrite_fact()` | `ref_proof.apply_method('rewrite_fact')` |
| 移除选中 | `remove_selected()` | 委托 Theory |
| 上移项目 | `item_move_up()` | 委托 Theory |
| 下移项目 | `item_move_down()` | 委托 Theory |
| 添加项目 | `add_item()` | 委托 Theory |

---

### Theory.vue 功能

| 功能 | 方法 | 说明 |
|------|------|------|
| 选择项目 | `handle_select(index)` | 选中指定项目 |
| 编辑项目 | `edit_item(index)` | 进入编辑模式 |
| 检查编辑 | `check_edit()` | 调用 `/api/check-modify` |
| 保存编辑 | `save_edit()` | 保存编辑结果 |
| 取消编辑 | `cancel_edit()` | 取消编辑 |
| 添加项目 | `add_item(ty, pos)` | 在指定位置添加新项目 |
| 移除选中 | `remove_selected()` | 移除选中的项目 |
| 上移项目 | `item_move_up()` | 上移选中的项目 |
| 下移项目 | `item_move_down()` | 下移选中的项目 |
| 保存文件 | `save_json_file()` | 调用 `/api/save-file` |
| 初始化证明 | `init_proof(index)` | 显示 ProofArea |
| 保存证明 | `save_proof()` | 保存证明到 theory |
| 重置证明 | `reset_proof()` | 清空证明重新开始 |
| 取消证明 | `cancel_proof()` | 隐藏 ProofArea |

---

### ProofArea.vue 功能

| 功能 | 方法 | 说明 |
|------|------|------|
| 初始化证明 | `init_proof()` | 根据 old_proof 决定新证明或恢复 |
| 空证明初始化 | `init_empty_proof()` | 清空 steps，gotoStep(0) |
| 恢复证明 | `init_saved_proof()` | 恢复 old_steps，gotoStep(len) |
| 跳转步骤 | `gotoStep(index, set_selected)` | 调用 `/api/init-saved-proof` |
| 后退一步 | `step_backward()` | gotoStep(index - 1) |
| 前进一步 | `step_forward()` | gotoStep(index + 1) |
| 删除步骤 | `deleteStep(start, end)` | 删除步骤并跳转 |
| 选择目标/事实 | `mark_text(line_no)` | 选择 sorry 行作为 goal，或选择事实 |
| 搜索方法 | `match_thm()` | 调用 `/api/search-method` |
| 应用搜索结果 | `apply_thm_tactic(res_id)` | 应用搜索结果中的方法 |
| 应用方法 | `apply_method(method_name, args)` | 检查参数，可能触发查询 |
| 执行方法 | `apply_method_ajax(input)` | 调用 `/api/apply-method` |
| 构建状态 | `current_state()` | 构建当前证明状态对象 |

---

### ProofStatus.vue 功能

| 功能 | 说明 |
|------|------|
| 显示状态 | `status` 文本 |
| 显示堆栈 | `trace` 文本（可展开/折叠） |
| 显示指令 | `instr` 高亮文本 + `instr_no` 编号 |
| 步骤跳转 | `<` `>` 按钮调用 step_backward/step_forward |
| 显示搜索结果 | `search_res` 列表 |
| 应用方法 | 点击搜索结果调用 `ref_proof.apply_thm_tactic(i)` |

---

### ProofContext.vue 功能

| 功能 | 说明 |
|------|------|
| 显示变量 | `ctxt` 对象，格式 `name :: type` |
| 显示历史 | `steps` 数组，每个元素有 `step_output` |
| 步骤选择 | 单击选择，Shift+点击扩展选区 |
| 步骤跳转 | 点击步骤调用 `ref_proof.gotoStep(index)` |
| 删除步骤 | `deleteStep()` 删除选中步骤 |

---

### ProofQuery.vue 功能

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
| `header` | — | 直接渲染 | 无 | 标题段落 |
| `type.ax` | `type` | Expression | 无 | 类型声明 |
| `def.ax` | `constant` | Constant | ConstantEdit | 常量声明 |
| `type.ind` | `datatype` | Datatype | DatatypeEdit | 归纳数据类型 |
| `def` | `definition` | Definition | DefinitionEdit | 定义 |
| `def.ind` | `fun` | Inductive | InductiveEdit | 归纳定义 |
| `def.pred` | `inductive` | Inductive | InductiveEdit | 归纳谓词 |
| `thm` | `theorem` | Theorem | TheoremEdit | 定理 |
| `thm.ax` | `axiom` | Axiom | TheoremEdit | 公理 |

---

## 证明状态图标

| 条件 | 图标 | 颜色 |
|------|------|------|
| `proof === undefined` | ✗ | 红色 |
| `num_gaps > 0` | ✗ | 橙色 |
| `num_gaps === 0` | ✓ | 绿色 |

---

## 布局结构

```
┌─────────────────────────────────────────────────────────┐
│  HOLPy  [File ▼] [Proof ▼]  File: nat                   │
├──────────┬────────────────────────────┬─────────────────┤
│          │                            │   Message       │
│  Files   │     Theory Content         ├─────────────────┤
│   or     │                            │  Proof Status   │
│ Context  │                            │                 │
│          │                            │  (搜索结果)     │
│          │                            │                 │
└──────────┴────────────────────────────┴─────────────────┘
```

- **左侧（250px）**：文件列表 / 证明上下文
- **中间（自适应）**：理论内容 / 证明区域
- **右侧（300px）**：消息 / 证明状态

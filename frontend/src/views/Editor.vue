<template>
  <div class="editor-container">
    <!-- 顶部菜单 -->
    <nav class="navbar navbar-expand navbar-dark bg-dark">
      <div class="container-fluid">
        <span class="navbar-brand">HOLPy</span>
        <div class="navbar-nav">
          <!-- File菜单 -->
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">File</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="new_file">New</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="open_file">Open</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="load_filelist">Refresh</a></li>
              <li><hr class="dropdown-divider"></li>
              <li><a class="dropdown-item" href="#" @click.prevent="save_file">Save</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="remove_file">Delete</a></li>
            </ul>
          </div>
          
          <!-- Items菜单（有文件时显示） -->
          <div class="nav-item dropdown" v-if="theory">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Items</a>
            <ul class="dropdown-menu">
              <li><h6 class="dropdown-header">Add</h6></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('thm')">Theorem</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def')">Definition</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.ax')">Constant</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('type.ind')">Datatype</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.ind')">Fun</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.pred')">Inductive</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('thm.ax')">Axiom</a></li>
              <li><hr class="dropdown-divider"></li>
              <li><h6 class="dropdown-header">Manage</h6></li>
              <li><a class="dropdown-item" href="#" @click.prevent="remove_selected"
                     :class="{disabled: selected_index < 0}">Remove selected</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="item_move_up"
                     :class="{disabled: selected_index <= 0}">Move up</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="item_move_down"
                     :class="{disabled: selected_index < 0 || selected_index >= theory.content.length - 1}">Move down</a></li>
            </ul>
          </div>
        </div>
        <span class="text-light ms-3" v-if="filename">File: {{ filename }}</span>
        <span class="text-light ms-3" v-if="loading">Loading...</span>
      </div>
    </nav>

    <!-- 主内容区 -->
    <div class="main-content">
      <!-- 左侧面板：始终显示文件列表 -->
      <div class="left-panel">
        <div class="panel-section">
          <h6 class="panel-title">Files</h6>
          <div class="file-list">
            <div v-for="file in filelist" :key="file" 
                 class="file-item" 
                 :class="{active: filename === file}"
                 @click="select_file(file)">
              {{ file }}
            </div>
          </div>
        </div>
      </div>

      <!-- 中间面板：理论内容 -->
      <div class="center-panel">
        <!-- Loading状态 -->
        <div v-if="loading" class="loading-state">
          <div class="spinner"></div>
          <p>Loading...</p>
        </div>
        
        <!-- 未选择文件 -->
        <div v-else-if="!filename" class="empty-state">
          <h4>Select a file to begin</h4>
          <p>Choose a theory file from the left panel</p>
        </div>
        
        <!-- 理论内容 -->
        <Theory v-else-if="theory" 
                :theory="theory"
                :active_index="active_index"
                :ui_state="ui_state"
                :selected_index="selected_index"
                :theorem_status="theorem_status"
                @set-message="onSetMessage"
                @set-proof="handle_set_proof"
                @set-status="handle_set_status"
                @set-context="handle_set_context"
                @query="handle_query"
                @goto-link="handleGoToLink"
                @save-file="save_file"
                @toggle-edit="toggle_edit"
                @toggle-prove="toggle_prove"
                @edit-submit="on_edit_submit"
                @select-item="select_item"
                ref="theory_ref"/>
      </div>

      <!-- 右侧面板：仅PROVE状态显示Context -->
      <div class="right-panel">
        <div v-if="message" class="panel-section message-section">
          <div class="alert" :class="{'alert-danger': message.type === 'error', 'alert-info': message.type !== 'error'}">
            {{ message.data }}
          </div>
        </div>
        <div v-if="ui_state === 'PROVE'" class="panel-section">
          <h6 class="panel-title">Context</h6>
          <ProofContext ref="ref_context" :ref_proof="ref_proof"/>
        </div>
        <div v-if="ui_state === 'PROVE'" class="panel-section">
          <h6 class="panel-title">Proof Status</h6>
          <ProofStatus ref="ref_status" :ref_proof="ref_proof"/>
        </div>
      </div>
    </div>

    <!-- 查询对话框 -->
    <div v-if="query" class="modal-overlay" @click.self="handle_query_cancel">
      <div class="modal-content">
        <div class="modal-header">
          <h5 class="modal-title">{{ query.title }}</h5>
          <button type="button" class="btn-close" @click="handle_query_cancel"></button>
        </div>
        <div class="modal-body">
          <ProofQuery :query="query"
                      @query-ok="handle_query_ok"
                      @query-cancel="handle_query_cancel"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref, nextTick } from 'vue'
import api from '../api'
import Theory from '../components/Theory.vue'
import ProofContext from '../components/proof/ProofContext.vue'
import ProofStatus from '../components/proof/ProofStatus.vue'
import ProofQuery from '../components/proof/ProofQuery.vue'

// ==================== 状态机 ====================
const ui_state = ref('BROWSE')  // 'BROWSE' | 'EDIT' | 'PROVE'
const active_index = ref(-1)
const selected_index = ref(-1)
const loading = ref(false)

// ==================== 数据 ====================
const filelist = ref([])
const filename = ref(null)
const theory = ref(null)
const message = ref(null)
const query = ref(undefined)

// 依赖图
const deps = ref({})
const reverse_deps = ref({})
const theorem_status = ref({})

// 组件引用
const theory_ref = ref(null)
const ref_context = ref(null)
const ref_status = ref(null)
const ref_proof = ref(null)

// ==================== API调用 ====================
const api_load_filelist = async () => {
  try {
    const response = await api.post('/find-files')
    filelist.value = response.data.theories
  } catch (err) {
    message.value = {type: 'error', data: 'Failed to load file list'}
  }
}

const api_load_file = async (name) => {
  try {
    const response = await api.post('/load-json-file', {
      filename: name,
      profile: false,
      line_length: 80
    })
    return response.data
  } catch (err) {
    message.value = {type: 'error', data: 'Failed to load file'}
    return null
  }
}

const api_save_file = async (data) => {
  try {
    await api.post('/save-file', {
      filename: filename.value,
      content: data
    })
    return true
  } catch (err) {
    message.value = {type: 'error', data: 'Failed to save file'}
    return false
  }
}

const api_check_modify = async (item) => {
  try {
    const response = await api.post('/check-modify', {
      filename: filename.value,
      limit_ty: item.ty,
      limit_name: item.name,
      line_length: 80,
      item: item
    })
    return response.data.item
  } catch (err) {
    return { error: { err_type: 'ServerError', err_str: 'Server error' } }
  }
}

// ==================== 状态转换 ====================
const toggle_edit = (index) => {
  if (ui_state.value === 'EDIT' && active_index.value === index) {
    ui_state.value = 'BROWSE'
    active_index.value = -1
  } else {
    ui_state.value = 'EDIT'
    active_index.value = index
  }
}

const toggle_prove = (index) => {
  if (ui_state.value === 'PROVE' && active_index.value === index) {
    ui_state.value = 'BROWSE'
    active_index.value = -1
    clear_context()
  } else {
    ui_state.value = 'PROVE'
    active_index.value = index
    clear_context()
  }
}

const select_item = (index) => {
  selected_index.value = index
}

const select_file = async (name) => {
  if (loading.value) return
  
  // 清除所有状态
  ui_state.value = 'BROWSE'
  active_index.value = -1
  selected_index.value = -1
  clear_context()
  
  // 显示loading
  loading.value = true
  filename.value = name
  theory.value = null
  
  try {
    const data = await api_load_file(name)
    if (data) {
      theory.value = data
      compute_deps_and_status()
    }
  } finally {
    loading.value = false
  }
}

// ==================== 依赖图和状态 ====================
const compute_deps_and_status = () => {
  if (!theory.value) return
  
  deps.value = {}
  reverse_deps.value = {}
  
  for (const item of theory.value.content) {
    if (!item.name) continue
    deps.value[item.name] = new Set()
    
    if (item.steps) {
      for (const step of item.steps) {
        if (step.theorem) {
          deps.value[item.name].add(step.theorem)
        }
      }
    }
  }
  
  for (const [name, dep_set] of Object.entries(deps.value)) {
    if (!reverse_deps.value[name]) reverse_deps.value[name] = new Set()
    for (const dep of dep_set) {
      if (!reverse_deps.value[dep]) reverse_deps.value[dep] = new Set()
      reverse_deps.value[dep].add(name)
    }
  }
  
  theorem_status.value = {}
  for (const item of theory.value.content) {
    if (item.name) {
      theorem_status.value[item.name] = compute_status(item)
    }
  }
}

const compute_status = (item) => {
  if (item.ty === 'thm.ax') return 'AXIOM'
  if (item.ty === 'thm') {
    if (!item.proof) return 'UNPROVED'
    if (item.num_gaps > 0) return 'INVALID'
    return 'VALID'
  }
  return 'VALID'
}

const mark_dirty = (name) => {
  const queue = [name]
  const visited = new Set()
  
  while (queue.length > 0) {
    const current = queue.shift()
    if (visited.has(current)) continue
    visited.add(current)
    
    if (current in theorem_status.value) {
      theorem_status.value[current] = 'DIRTY'
    }
    
    if (reverse_deps.value[current]) {
      for (const dep of reverse_deps.value[current]) {
        queue.push(dep)
      }
    }
  }
}

// ==================== 编辑操作 ====================
const on_edit_submit = (index, new_item) => {
  const old_item = theory.value.content[index]
  const old_prop = old_item.prop
  
  Object.assign(old_item, new_item)
  
  if (new_item.prop && new_item.prop !== old_prop) {
    old_item.proof = null
    old_item.steps = null
    old_item.num_gaps = null
  }
  
  mark_dirty(old_item.name)
  
  ui_state.value = 'BROWSE'
  active_index.value = -1
}

// ==================== 保存 ====================
const save_file = async () => {
  if (!theory.value) return
  
  const dirty_items = theory.value.content.filter(
    i => i.name && theorem_status.value[i.name] === 'DIRTY'
  )
  
  const sorted = topological_sort(dirty_items)
  
  for (const item of sorted) {
    const result = await api_check_modify(item)
    if (result.error) {
      theorem_status.value[item.name] = 'INVALID'
      message.value = { 
        type: 'error', 
        data: `Theorem ${item.name} check failed: ${result.error.err_str}` 
      }
      return
    }
    if (item.ty === 'thm') {
      result.proof = item.proof
      result.num_gaps = item.num_gaps
      result.steps = item.steps
    }
    Object.assign(item, result)
    theorem_status.value[item.name] = 'VALID'
  }
  
  const content = theory.value.content
    .filter(i => 'name' in i)
    .map(i => {
      const copy = JSON.parse(JSON.stringify(i))
      delete copy.error
      delete copy.display
      delete copy.edit
      delete copy.ext
      return copy
    })
  
  const success = await api_save_file({
    name: theory.value.name,
    imports: theory.value.imports,
    description: theory.value.description,
    content: content
  })
  
  if (success) {
    // 重新加载
    loading.value = true
    try {
      const data = await api_load_file(filename.value)
      if (data) {
        theory.value = data
        compute_deps_and_status()
      }
    } finally {
      loading.value = false
    }
    
    active_index.value = -1
    selected_index.value = -1
    ui_state.value = 'BROWSE'
    message.value = {type: 'OK', data: 'File saved'}
  }
}

const topological_sort = (items) => {
  const names = new Set(items.map(i => i.name))
  const visited = new Set()
  const result = []
  
  const visit = (name) => {
    if (visited.has(name)) return
    visited.add(name)
    
    if (deps.value[name]) {
      for (const dep of deps.value[name]) {
        if (names.has(dep)) {
          visit(dep)
        }
      }
    }
    
    result.push(name)
  }
  
  for (const name of names) {
    visit(name)
  }
  
  return result.map(name => items.find(i => i.name === name))
}

// ==================== 文件操作 ====================
const new_file = async () => {
  const name = prompt("Name of the theory")
  if (!name) return
  
  // 创建新文件数据
  const new_theory = {
    name: name,
    imports: [],
    description: '',
    content: []
  }
  
  // 保存到后端
  const success = await api_save_file(new_theory)
  if (!success) return
  
  // 刷新文件列表
  await api_load_filelist()
  
  // 选择新文件
  await select_file(name)
  message.value = {type: 'OK', data: `Created ${name}`}
}

const open_file = () => {
  const name = prompt("Open file")
  if (name) {
    select_file(name)
  }
}

const remove_file = async () => {
  if (!filename.value) return
  if (!confirm(`Are you sure you want to delete ${filename.value}?`)) return
  
  try {
    await api.put('/remove-file', { filename: filename.value })
    filelist.value = filelist.value.filter(f => f !== filename.value)
    filename.value = undefined
    theory.value = undefined
    ui_state.value = 'BROWSE'
    active_index.value = -1
    selected_index.value = -1
    message.value = {type: 'OK', data: 'File deleted'}
  } catch (err) {
    message.value = {type: 'error', data: 'Failed to delete file'}
  }
}

// ==================== 项管理 ====================
const add_item = (ty) => {
  if (!theory.value) return
  
  const new_item = {
    ty: ty,
    name: '',
    edit: { ty: ty, name: '' }
  }
  
  // 根据类型添加默认字段
  if (ty === 'thm' || ty === 'thm.ax') {
    new_item.vars = {}
    new_item.prop = ''
    new_item.attributes = []
  } else if (ty === 'def') {
    new_item.type = ''
    new_item.prop = ''
    new_item.attributes = []
  } else if (ty === 'def.ax') {
    new_item.type = ''
  } else if (ty === 'type.ind') {
    new_item.args = []
    new_item.constrs = []
  } else if (ty === 'def.ind' || ty === 'def.pred') {
    new_item.type = ''
    new_item.rules = []
  }
  
  // 添加到末尾
  theory.value.content.push(new_item)
  
  // 进入编辑模式
  const index = theory.value.content.length - 1
  ui_state.value = 'EDIT'
  active_index.value = index
  selected_index.value = index
  
  message.value = {type: 'OK', data: `Added new ${ty}`}
}

const remove_selected = () => {
  if (!theory.value || selected_index.value < 0) return
  
  const item = theory.value.content[selected_index.value]
  if (!confirm(`Remove ${item.name || item.ty}?`)) return
  
  theory.value.content.splice(selected_index.value, 1)
  
  // 调整选中索引
  if (selected_index.value >= theory.value.content.length) {
    selected_index.value = theory.value.content.length - 1
  }
  
  // 如果正在编辑/证明这个项，关闭
  if (active_index.value === selected_index.value) {
    ui_state.value = 'BROWSE'
    active_index.value = -1
  }
  
  message.value = {type: 'OK', data: 'Item removed'}
}

const item_move_up = () => {
  if (!theory.value || selected_index.value <= 0) return
  
  const content = theory.value.content
  const idx = selected_index.value
  
  // 交换
  const temp = content[idx]
  content[idx] = content[idx - 1]
  content[idx - 1] = temp
  
  selected_index.value = idx - 1
  
  // 调整active_index
  if (active_index.value === idx) {
    active_index.value = idx - 1
  } else if (active_index.value === idx - 1) {
    active_index.value = idx
  }
}

const item_move_down = () => {
  if (!theory.value || selected_index.value < 0) return
  if (selected_index.value >= theory.value.content.length - 1) return
  
  const content = theory.value.content
  const idx = selected_index.value
  
  // 交换
  const temp = content[idx]
  content[idx] = content[idx + 1]
  content[idx + 1] = temp
  
  selected_index.value = idx + 1
  
  // 调整active_index
  if (active_index.value === idx) {
    active_index.value = idx + 1
  } else if (active_index.value === idx + 1) {
    active_index.value = idx
  }
}

// ==================== 其他操作 ====================
const clear_context = () => {
  ref_proof.value = null
  if (ref_context.value) {
    ref_context.value.setContext({ ctxt: {}, steps: [] })
  }
  if (ref_status.value) {
    ref_status.value.setStatus({ status: '', search_res: [], instr: [], instr_no: '' })
  }
}

const handleGoToLink = (link_filename, index) => {
  if (link_filename !== filename.value) {
    select_file(link_filename).then(() => {
      if (index !== undefined && theory_ref.value) {
        nextTick(() => {
          selected_index.value = index
        })
      }
    })
  }
}

const onSetMessage = (msg) => {
  message.value = msg
}

const handle_set_proof = (proof_ref) => {
  ref_proof.value = proof_ref
}

const handle_set_status = (data) => {
  if (ref_status.value) {
    ref_status.value.setStatus(data)
  }
}

const handle_set_context = (data) => {
  if (ref_context.value) {
    ref_context.value.setContext(data)
  }
}

const handle_query = (q) => {
  query.value = q
}

const handle_query_ok = (vals) => {
  if (query.value && query.value.resolve) {
    query.value.resolve(vals)
  }
  query.value = undefined
}

const handle_query_cancel = () => {
  if (query.value && query.value.resolve) {
    query.value.resolve(undefined)
  }
  query.value = undefined
}

// ==================== 初始化 ====================
api_load_filelist()
</script>

<style scoped>
.editor-container {
  height: 100vh;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

.main-content {
  flex: 1;
  display: flex;
  overflow: hidden;
}

.left-panel {
  width: 250px;
  min-width: 250px;
  border-right: 1px solid #dee2e6;
  overflow-y: auto;
  background: #f8f9fa;
}

.center-panel {
  flex: 1;
  overflow-y: auto;
  padding: 15px;
}

.right-panel {
  width: 300px;
  min-width: 300px;
  border-left: 1px solid #dee2e6;
  overflow-y: auto;
  background: #f8f9fa;
}

.panel-section {
  padding: 10px;
  border-bottom: 1px solid #dee2e6;
}

.panel-title {
  font-weight: bold;
  color: #495057;
  margin-bottom: 10px;
  padding-bottom: 5px;
  border-bottom: 2px solid #007bff;
}

.file-list {
  max-height: calc(100vh - 120px);
  overflow-y: auto;
}

.file-item {
  padding: 8px 12px;
  cursor: pointer;
  border-radius: 4px;
  margin-bottom: 2px;
}

.file-item:hover {
  background: #e9ecef;
}

.file-item.active {
  background: #007bff;
  color: white;
}

.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  color: #6c757d;
}

.loading-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  color: #6c757d;
}

.spinner {
  width: 40px;
  height: 40px;
  border: 4px solid #f3f3f3;
  border-top: 4px solid #007bff;
  border-radius: 50%;
  animation: spin 1s linear infinite;
  margin-bottom: 10px;
}

@keyframes spin {
  0% { transform: rotate(0deg); }
  100% { transform: rotate(360deg); }
}

.message-section {
  padding: 10px;
}

.message-section .alert {
  margin: 0;
  font-size: 14px;
}

.modal-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0,0,0,0.5);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1050;
}

.modal-content {
  background: white;
  border-radius: 8px;
  width: 500px;
  max-width: 90%;
  box-shadow: 0 4px 20px rgba(0,0,0,0.15);
}

.modal-header {
  padding: 15px 20px;
  border-bottom: 1px solid #dee2e6;
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.modal-body {
  padding: 20px;
}
</style>

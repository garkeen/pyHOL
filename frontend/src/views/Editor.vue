<template>
  <div class="editor-container">
    <!-- Top menu bar -->
    <nav class="navbar navbar-expand navbar-dark bg-dark">
      <div class="container-fluid">
        <span class="navbar-brand">HOLPy</span>
        <div class="navbar-nav">
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">File</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="create_file">New</a></li>
              <li><hr class="dropdown-divider"></li>
              <li><a class="dropdown-item" href="#" @click.prevent="load_files">Refresh file list</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown" v-if="theory">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Items</a>
            <ul class="dropdown-menu">
              <li><h6 class="dropdown-header">Add</h6></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('thm')">Theorem</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('thm.ax')">Axiom</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def')">Definition</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.ax')">Constant</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('type.ind')">Datatype</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.ind')">Fun</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.pred')">Inductive</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="add_item('header')">Header</a></li>
            </ul>
          </div>
        </div>
        <div class="ms-auto d-flex align-items-center gap-3">
          <span class="text-light" v-if="filename">{{ filename }}</span>
          <span class="text-light" v-if="saving">Saving...</span>
          <span class="text-light" v-if="validating">Validating...</span>
        </div>
      </div>
    </nav>

    <!-- Main content -->
    <div class="main-content">
      <!-- Left: file list -->
      <div class="left-panel">
        <h6 class="panel-title">Files</h6>
        <div class="file-list">
          <div v-for="f in filelist" :key="f"
               class="file-item" :class="{active: filename === f}"
               @click="open_file(f)">
            {{ f }}
          </div>
        </div>
      </div>

      <!-- Center: theory content -->
      <div class="center-panel">
        <div v-if="loading" class="loading-state"><div class="spinner"></div><p>Loading...</p></div>
        <div v-else-if="!filename" class="empty-state"><h4>Select a file</h4></div>
        <div v-else-if="theory">
          <!-- File header -->
          <div class="file-header">
            <div class="file-header-row">
              <button class="btn btn-sm btn-danger" @click="delete_file">Delete File</button>
              <button class="btn btn-sm btn-primary" @click="validate_all(false)">Validate All</button>
              <button class="btn btn-sm btn-warning" @click="validate_all(true)" title="Ignore cache, re-validate everything">Force Validate</button>
            </div>
            <!-- Metadata -->
            <div class="metadata-section">
              <div class="meta-row">
                <label class="meta-label">theory</label>
                <span class="meta-value">{{ theory.name }}</span>
              </div>
              <div class="meta-row">
                <label class="meta-label">imports</label>
                <input class="meta-input" v-model="meta_imports" placeholder="one per line"/>
              </div>
              <div class="meta-row">
                <label class="meta-label">domains</label>
                <input class="meta-input" v-model="meta_domains" placeholder="comma-separated (e.g. nat, real)"/>
              </div>
              <div class="meta-row">
                <label class="meta-label">description</label>
                <input class="meta-input" v-model="meta_description"/>
              </div>
              <button class="btn btn-sm btn-outline-primary mt-1" @click="save_metadata">Save Metadata</button>
            </div>
          </div>

          <!-- Items -->
          <div v-for="(item, index) in theory.content" :key="index" class="item-wrapper">
            <!-- Item header -->
            <div class="item-row" :class="{'item-selected': selected === index, 'item-error': item._error}"
                 @click="selected = index">
              <span class="item-idx">{{ index }}</span>
              <span class="item-type">{{ typeLabel(item.ty) }}</span>
              <span class="item-name">{{ item.name || '' }}</span>
              <span v-if="thm_status[item.name]" class="item-status" :class="'status-' + thm_status[item.name].toLowerCase()">
                {{ statusIcon(thm_status[item.name]) }}
              </span>
              <div class="item-actions">
                <button class="btn btn-sm btn-outline-secondary" @click.stop="toggle_edit(index)" title="Edit">
                  {{ editing === index ? 'Close' : 'Edit' }}
                </button>
                <button v-if="item.ty === 'thm'" class="btn btn-sm btn-outline-success" @click.stop="toggle_prove(index)" title="Prove">
                  {{ proving === index ? 'Close' : 'Prove' }}
                </button>
                <button class="btn btn-sm btn-outline-warning" @click.stop="move_item(index, -1)" :disabled="index === 0" title="Move up">↑</button>
                <button class="btn btn-sm btn-outline-warning" @click.stop="move_item(index, 1)" :disabled="index === theory.content.length - 1" title="Move down">↓</button>
                <button class="btn btn-sm btn-outline-danger" @click.stop="remove_item(index)" title="Delete">✕</button>
              </div>
            </div>

            <!-- Edit form -->
            <div v-if="editing === index" class="edit-section">
              <HeaderEdit v-if="item.ty === 'header'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <ConstantEdit v-else-if="item.ty === 'def.ax'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <DefinitionEdit v-else-if="item.ty === 'def'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <DatatypeEdit v-else-if="item.ty === 'type.ind'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <InductiveEdit v-else-if="item.ty === 'def.ind' || item.ty === 'def.pred'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <TheoremEdit v-else-if="item.ty === 'thm' || item.ty === 'thm.ax'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <AxTypeEdit v-else-if="item.ty === 'type.ax'" :item="item" :ref="el => { if (el) edit_ref = el }"/>
              <div class="edit-actions">
                <button class="btn btn-sm btn-primary" @click="check_item(index)">Check</button>
                <button class="btn btn-sm btn-success" @click="save_item(index)">Save</button>
                <button class="btn btn-sm btn-secondary" @click="editing = -1">Cancel</button>
              </div>
            </div>

            <!-- Proof area -->
            <div v-if="proving === index && item.ty === 'thm'" class="proof-section">
              <ProofArea
                :key="'proof-' + theory.name + '-' + item.name + '-' + index"
                :theory_name="theory.name"
                :thm_name="item.name"
                :vars="item.vars"
                :prop="item.prop"
                :old_steps="item.steps"
                :ref="el => { if (el) proof_area_ref = el }"
                @save-steps="(steps) => save_proof(index, steps)"
                @set-message="msg => toast(msg)"
                @set-context="data => { proof_ctxt = data.ctxt || {}; proof_history = data.history || []; proof_history_idx = data.history_idx || -1 }"/>
            </div>
          </div>
        </div>
      </div>

      <!-- Right panel: proof context (shown when proving) -->
      <div v-if="proving >= 0" class="right-panel">
        <div class="panel-section">
          <h6 class="panel-title">Variables</h6>
          <div v-if="proof_ctxt && Object.keys(proof_ctxt).length > 0">
            <div v-for="(T, nm) in proof_ctxt" :key="nm" class="ctxt-var">
              <span class="ctxt-name">{{ nm }}</span> :: <span class="ctxt-type">{{ formatType(T) }}</span>
            </div>
          </div>
          <div v-else class="ctxt-empty">No context</div>
        </div>
        <div class="panel-section">
          <h6 class="panel-title">Proof History</h6>
          <div v-if="proof_history.length > 0">
            <div class="history-item" :class="{'history-selected': proof_history_idx === 0}"
                 @click="proof_goto_step(0)">
              <span class="history-idx">0</span>
              <span class="history-text">Initial</span>
            </div>
            <div v-for="(h, i) in proof_history" :key="i" class="history-item"
                 :class="{'history-selected': proof_history_idx === i + 1}"
                 @click="proof_goto_step(i + 1)">
              <span class="history-idx">{{ i + 1 }}</span>
              <span v-if="h.step_output" class="history-text">{{ formatHistory(h.step_output) }}</span>
            </div>
          </div>
          <div v-else class="ctxt-empty">No steps yet</div>
        </div>
      </div>
    </div>

    <!-- Toast -->
    <Transition name="toast">
      <div v-if="message" class="toast" :class="message.type === 'error' ? 'toast-error' : 'toast-ok'">
        <span>{{ message.type === 'error' ? '✗' : '✓' }}</span>
        <span class="toast-text">{{ message.data }}</span>
        <button class="toast-close" @click="message = null">&times;</button>
      </div>
    </Transition>
  </div>
</template>

<script setup>
import { ref, onMounted } from 'vue'
import api from '../api'
import TheoremEdit from '../components/items/TheoremEdit.vue'
import ConstantEdit from '../components/items/ConstantEdit.vue'
import DefinitionEdit from '../components/items/DefinitionEdit.vue'
import DatatypeEdit from '../components/items/DatatypeEdit.vue'
import InductiveEdit from '../components/items/InductiveEdit.vue'
import HeaderEdit from '../components/items/HeaderEdit.vue'
import AxTypeEdit from '../components/items/AxTypeEdit.vue'
import ProofArea from '../components/proof/ProofArea.vue'

// ==================== State ====================
const filelist = ref([])
const filename = ref(null)
const theory = ref(null)
const loading = ref(false)
const saving = ref(false)
const message = ref(null)
const selected = ref(-1)
const editing = ref(-1)
const proving = ref(-1)
const thm_status = ref({})
const validating = ref(false)

// Metadata editing
const meta_imports = ref('')
const meta_domains = ref('')
const meta_description = ref('')

// Proof context (right panel)
const proof_ctxt = ref({})
const proof_history = ref([])
const proof_history_idx = ref(-1)

let edit_ref = null  // set by function ref in template
let toastTimer = null

const toast = (msg) => {
  message.value = msg
  if (toastTimer) clearTimeout(toastTimer)
  if (msg && msg.type !== 'error') {
    toastTimer = setTimeout(() => { message.value = null }, 3000)
  }
}

// ==================== File operations ====================
const load_files = async () => {
  try {
    const res = await api.post('/find-files')
    filelist.value = res.data.theories
  } catch (e) {
    toast({ type: 'error', data: 'Failed to load file list' })
  }
}

const open_file = async (name) => {
  if (loading.value) return
  loading.value = true
  filename.value = name
  theory.value = null
  editing.value = -1
  proving.value = -1
  selected.value = -1
  try {
    const res = await api.post('/load-json-file', { filename: name, line_length: 80 })
    res.data.content.forEach(item => { item._from_disk = true })
    theory.value = res.data
    meta_imports.value = (res.data.imports || []).join('\n')
    meta_domains.value = (res.data.domains || []).join(', ')
    meta_description.value = res.data.description || ''
    compute_thm_status()
  } catch (e) {
    toast({ type: 'error', data: 'Failed to load ' + name })
  } finally {
    loading.value = false
  }
}

const reload_file = async () => {
  if (!filename.value) return
  const name = filename.value
  loading.value = true
  try {
    const res = await api.post('/load-json-file', { filename: name, line_length: 80 })
    res.data.content.forEach(item => { item._from_disk = true })
    theory.value = res.data
    meta_imports.value = (res.data.imports || []).join('\n')
    meta_domains.value = (res.data.domains || []).join(', ')
    meta_description.value = res.data.description || ''
    compute_thm_status()
  } catch (e) {
    toast({ type: 'error', data: 'Failed to reload' })
  } finally {
    loading.value = false
  }
}

const create_file = async () => {
  const name = prompt('New theory name:')
  if (!name) return
  saving.value = true
  try {
    await api.post('/save-file', {
      filename: name,
      content: { name, imports: [], domains: [], description: '', content: [] }
    })
    await load_files()
    await open_file(name)
    toast({ type: 'OK', data: `Created ${name}` })
  } catch (e) {
    toast({ type: 'error', data: 'Failed to create file' })
  } finally {
    saving.value = false
  }
}

const delete_file = async () => {
  if (!filename.value) return
  if (!confirm(`Delete file "${filename.value}"? This cannot be undone.`)) return
  try {
    await api.put('/remove-file', { filename: filename.value })
    filename.value = null
    theory.value = null
    await load_files()
    toast({ type: 'OK', data: 'File deleted' })
  } catch (e) {
    toast({ type: 'error', data: 'Failed to delete file' })
  }
}

// ==================== Persist to disk ====================
const persist = async () => {
  if (!theory.value) return false
  saving.value = true
  try {
    // Clean items: remove internal fields
    const content = theory.value.content.map(item => {
      const copy = { ...item }
      delete copy._error
      delete copy._from_disk
      delete copy.display
      delete copy.edit
      delete copy.ext
      delete copy.error
      return copy
    })
    await api.post('/save-file', {
      filename: filename.value,
      content: {
        name: theory.value.name,
        imports: theory.value.imports || [],
        domains: theory.value.domains || [],
        description: theory.value.description || '',
        content
      }
    })
    return true
  } catch (e) {
    toast({ type: 'error', data: 'Failed to save to disk' })
    return false
  } finally {
    saving.value = false
  }
}

// ==================== Metadata ====================
const save_metadata = async () => {
  if (!theory.value) return
  theory.value.imports = meta_imports.value.split('\n').map(s => s.trim()).filter(Boolean)
  theory.value.domains = meta_domains.value.split(',').map(s => s.trim()).filter(Boolean)
  theory.value.description = meta_description.value
  const ok = await persist()
  if (ok) {
    await reload_file()
    toast({ type: 'OK', data: 'Metadata saved' })
  }
}

// ==================== Item operations ====================
const add_item = (ty) => {
  if (!theory.value) return
  const item = { ty, name: '' }
  if (ty === 'thm' || ty === 'thm.ax') { item.vars = ''; item.prop = ''; item.attributes = [] }
  else if (ty === 'def') { item.type = ''; item.prop = ''; item.attributes = [] }
  else if (ty === 'def.ax') { item.type = '' }
  else if (ty === 'type.ax') { item.args = [] }
  else if (ty === 'type.ind') { item.type = ''; item.args = []; item.constrs = '' }
  else if (ty === 'def.ind' || ty === 'def.pred') { item.type = ''; item.rules = '' }
  else if (ty === 'header') { item.depth = 0 }

  theory.value.content.push(item)
  const idx = theory.value.content.length - 1
  editing.value = idx
  selected.value = idx
  toast({ type: 'OK', data: `Added ${typeLabel(ty)}` })
}

const remove_item = async (index) => {
  const item = theory.value.content[index]
  if (!confirm(`Delete "${item.name || typeLabel(item.ty)}"?`)) return
  theory.value.content.splice(index, 1)
  editing.value = -1
  proving.value = -1
  const ok = await persist()
  if (ok) {
    await reload_file()
    toast({ type: 'OK', data: 'Deleted' })
  }
}

const move_item = async (index, dir) => {
  const content = theory.value.content
  const target = index + dir
  if (target < 0 || target >= content.length) return
  const tmp = content[index]
  content[index] = content[target]
  content[target] = tmp
  selected.value = target
  if (editing.value === index) editing.value = target
  else if (editing.value === target) editing.value = index
  const ok = await persist()
  if (ok) await reload_file()
}

// ==================== Edit operations ====================
const toggle_edit = (index) => {
  if (editing.value === index) {
    editing.value = -1
  } else {
    editing.value = index
    proving.value = -1
    selected.value = index
  }
}

const check_item = async (index) => {
  if (!edit_ref) return
  const data = edit_ref.getData()
  const old_item = theory.value.content[index]
  const is_existing = old_item._from_disk
  try {
    const req = { filename: filename.value, line_length: 80, item: data }
    if (is_existing) {
      req.limit_ty = old_item.ty
      req.limit_name = old_item.name
    }
    const res = await api.post('/check-modify', req)
    const result = res.data.item
    if (result.error) {
      toast({ type: 'error', data: `${result.error.err_type}: ${result.error.err_str}` })
    } else {
      toast({ type: 'OK', data: 'Check passed' })
    }
  } catch (e) {
    toast({ type: 'error', data: 'Check failed: ' + (e.message || 'server error') })
  }
}

const save_item = async (index) => {
  if (!edit_ref) return
  const data = edit_ref.getData()

  if (!data.name) {
    toast({ type: 'error', data: 'Name is required' })
    return
  }

  const old_item = theory.value.content[index]
  const is_existing = old_item._from_disk

  saving.value = true
  try {
    // 1. Validate via check-modify
    const req = { filename: filename.value, line_length: 80, item: data }
    if (is_existing) {
      req.limit_ty = old_item.ty
      req.limit_name = old_item.name
    }
    const res = await api.post('/check-modify', req)
    const result = res.data.item
    if (result.error) {
      toast({ type: 'error', data: `${result.error.err_type}: ${result.error.err_str}` })
      return
    }

    // 2. Update item in memory (keep steps for theorems)
    const steps = old_item.steps
    // Only take core fields from check-modify result
    const updated = { ty: result.ty, name: result.name }
    if (result.vars !== undefined) updated.vars = result.vars
    if (result.prop !== undefined) updated.prop = result.prop
    if (result.type !== undefined) updated.type = result.type
    if (result.attributes !== undefined) updated.attributes = result.attributes
    if (result.args !== undefined) updated.args = result.args
    if (result.constrs !== undefined) updated.constrs = result.constrs
    if (result.rules !== undefined) updated.rules = result.rules
    if (result.depth !== undefined) updated.depth = result.depth
    if (result.overloaded !== undefined) updated.overloaded = result.overloaded
    if (steps) updated.steps = steps
    updated._from_disk = true
    theory.value.content[index] = updated

    // 3. Persist to disk
    const ok = await persist()
    if (ok) {
      // 4. Reload from disk to confirm
      await reload_file()
      editing.value = -1
      toast({ type: 'OK', data: `Saved "${updated.name}"` })
    }
  } catch (e) {
    toast({ type: 'error', data: 'Save failed: ' + (e.message || 'server error') })
  } finally {
    saving.value = false
  }
}

// ==================== Proof ====================
const toggle_prove = (index) => {
  if (proving.value === index) {
    proving.value = -1
  } else {
    proving.value = index
    editing.value = -1
    selected.value = index
  }
}

const save_proof = async (index, steps) => {
  theory.value.content[index].steps = steps
  const ok = await persist()
  if (ok) {
    await reload_file()
    toast({ type: 'OK', data: 'Proof saved' })
  }
}

// ==================== Validate All ====================
const validate_all = async (force = false) => {
  if (!filename.value) return
  validating.value = true
  try {
    const resp = await api.post('/validate-theory', { filename: filename.value, force })
    thm_status.value = resp.data.statuses
    const d = resp.data
    toast({ type: 'OK', data: `Valid: ${d.valid} | Axiom: ${d.axiom} | Unproved: ${d.unproved} | Failed: ${d.failed} | Total: ${d.total}` })
  } catch (e) {
    toast({ type: 'error', data: 'Validation failed' })
  } finally {
    validating.value = false
  }
}

// ==================== Helpers ====================
const compute_thm_status = async () => {
  // Try to load cached status from backend
  try {
    const resp = await fetch('/api/theory-status')
    if (resp.ok) {
      const cached = await resp.json()
      if (Object.keys(cached).length > 0) {
        thm_status.value = cached
        // Fill in missing items
        for (const item of theory.value.content) {
          if (!(item.name in thm_status.value)) {
            thm_status.value[item.name] = item.ty === 'thm.ax' ? 'AXIOM' : 'UNPROVED'
          }
        }
        return
      }
    }
  } catch (e) {}

  // No cache, show defaults
  thm_status.value = {}
  if (!theory.value) return
  for (const item of theory.value.content) {
    thm_status.value[item.name] = item.ty === 'thm.ax' ? 'AXIOM' : 'UNPROVED'
  }
}

const typeLabel = (ty) => ({
  'header': 'header', 'type.ax': 'type', 'type.ind': 'datatype',
  'def.ax': 'constant', 'def': 'definition', 'def.ind': 'fun',
  'def.pred': 'inductive', 'thm.ax': 'axiom', 'thm': 'theorem'
}[ty] || ty)

const statusIcon = (s) => ({
  'VALID': '✓', 'STEP_FAILED': '✗', 'DEP_FAILED': '⚠',
  'PENDING': '⏳', 'UNPROVED': '○', 'AXIOM': '□', 'DIRTY': '•'
}[s] || '')

const formatHistory = (step_output) => {
  if (Array.isArray(step_output)) {
    return step_output.map(item => item.text || String(item)).join('')
  }
  return String(step_output)
}

const formatType = (T) => {
  if (typeof T === 'string') return T
  if (Array.isArray(T)) return T.map(item => item.text || String(item)).join('')
  return String(T)
}

// Reference to ProofArea for navigating history
let proof_area_ref = null

const proof_goto_step = (step_idx) => {
  if (proof_area_ref && typeof proof_area_ref.gotoStep === 'function') {
    proof_area_ref.gotoStep(step_idx)
  }
}

// ==================== Init ====================
onMounted(() => { load_files() })
</script>

<style scoped>
.editor-container { height: 100vh; display: flex; flex-direction: column; overflow: hidden; }
.main-content { flex: 1; display: flex; overflow: hidden; }
.left-panel { width: 220px; min-width: 220px; border-right: 1px solid #dee2e6; overflow-y: auto; background: #f8f9fa; padding: 10px; }
.center-panel { flex: 1; overflow-y: auto; padding: 15px; }
.panel-title { font-weight: bold; color: #495057; margin-bottom: 10px; padding-bottom: 5px; border-bottom: 2px solid #007bff; }
.file-list { overflow-y: auto; }
.file-item { padding: 6px 10px; cursor: pointer; border-radius: 4px; margin-bottom: 2px; font-size: 14px; }
.file-item:hover { background: #e9ecef; }
.file-item.active { background: #007bff; color: white; }
.empty-state, .loading-state { display: flex; flex-direction: column; align-items: center; justify-content: center; height: 100%; color: #6c757d; }
.spinner { width: 36px; height: 36px; border: 4px solid #f3f3f3; border-top: 4px solid #007bff; border-radius: 50%; animation: spin 1s linear infinite; margin-bottom: 10px; }
@keyframes spin { 0% { transform: rotate(0deg); } 100% { transform: rotate(360deg); } }

/* File header */
.file-header { background: #f8f9fa; border: 1px solid #dee2e6; border-radius: 6px; padding: 12px; margin-bottom: 15px; }
.file-header-row { display: flex; gap: 8px; margin-bottom: 10px; }
.metadata-section { border-top: 1px solid #dee2e6; padding-top: 10px; }
.meta-row { display: flex; align-items: center; margin-bottom: 6px; }
.meta-label { font-weight: bold; color: #006000; width: 80px; flex-shrink: 0; }
.meta-input { flex: 1; padding: 4px 8px; border: 1px solid #ced4da; border-radius: 4px; font-size: 14px; }
.meta-value { font-family: Consolas, monospace; }

/* Items */
.item-wrapper { border-bottom: 1px solid #eee; }
.item-row { display: flex; align-items: center; padding: 4px 8px; cursor: pointer; gap: 8px; }
.item-row:hover { background: #f5f5f5; }
.item-selected { background: #e8f0fe !important; }
.item-error { background: #ffe0e0 !important; }
.item-idx { color: #999; font-size: 12px; width: 24px; text-align: right; }
.item-type { font-weight: bold; color: #006000; min-width: 70px; font-size: 13px; }
.item-name { font-family: Consolas, monospace; font-size: 14px; flex: 1; }
.item-status { font-size: 16px; }
.item-actions { display: flex; gap: 4px; }
.item-actions .btn { padding: 1px 6px; font-size: 12px; }

.status-valid { color: #28a745; }
.status-step_failed { color: #dc3545; }
.status-dep_failed { color: #fd7e14; }
.status-pending { color: #6c757d; }
.status-unproved { color: #6c757d; }
.status-axiom { color: #17a2b8; }
.status-dirty { color: #ffc107; }

/* Edit section */
.edit-section { margin: 8px 0; padding: 12px; background: #f9f9f9; border: 1px solid #ddd; border-radius: 4px; }
.edit-actions { margin-top: 8px; display: flex; gap: 6px; }

/* Proof section */
.proof-section { margin: 8px 0; padding: 12px; background: #fff; border: 1px solid #28a745; border-radius: 4px; }

/* Toast */
.toast { position: fixed; top: 20px; left: 50%; transform: translateX(-50%); z-index: 2000; display: flex; align-items: center; gap: 10px; padding: 12px 20px; border-radius: 8px; box-shadow: 0 4px 20px rgba(0,0,0,0.2); font-size: 14px; max-width: 600px; min-width: 280px; }
.toast-ok { background: #d4edda; color: #155724; border: 1px solid #c3e6cb; }
.toast-error { background: #f8d7da; color: #721c24; border: 1px solid #f5c6cb; }
.toast-text { flex: 1; word-break: break-word; }
.toast-close { background: none; border: none; font-size: 20px; cursor: pointer; color: inherit; opacity: 0.5; }
.toast-close:hover { opacity: 1; }
.toast-enter-active { animation: toast-in 0.3s ease; }
.toast-leave-active { animation: toast-out 0.3s ease; }
@keyframes toast-in { from { opacity: 0; transform: translateX(-50%) translateY(-20px); } to { opacity: 1; transform: translateX(-50%) translateY(0); } }
@keyframes toast-out { from { opacity: 1; } to { opacity: 0; transform: translateX(-50%) translateY(-20px); } }

/* Right panel */
.right-panel { width: 280px; min-width: 280px; border-left: 1px solid #dee2e6; overflow-y: auto; background: #f8f9fa; padding: 10px; }
.panel-section { margin-bottom: 15px; }
.ctxt-var { padding: 2px 0; font-size: 13px; }
.ctxt-name { font-family: Consolas, monospace; font-weight: bold; }
.ctxt-type { font-family: Consolas, monospace; color: #555; }
.ctxt-empty { color: #999; font-size: 13px; font-style: italic; }
.history-item { padding: 3px 6px; font-size: 12px; cursor: pointer; border-radius: 3px; display: flex; gap: 6px; }
.history-item:hover { background: #e9ecef; }
.history-selected { background: #cce5ff !important; }
.history-idx { color: #999; min-width: 20px; text-align: right; }
.history-text { font-family: Consolas, monospace; }
</style>

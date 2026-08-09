<template>
  <div class="editor-container">
    <!-- Top menu bar -->
    <nav class="navbar navbar-expand navbar-dark bg-dark">
      <div class="container-fluid">
        <span class="navbar-brand" style="padding-left: 44px">HOLPy</span>
        <div class="ms-auto d-flex align-items-center gap-3">
          <span class="text-light" v-if="filename">{{ filename }}</span>
          <span class="text-light" v-if="saving">Saving...</span>
          <span class="text-light" v-if="validating">Validating...</span>
        </div>
      </div>
    </nav>

    <!-- Main content -->
    <div class="main-content" :class="{'proving-mode': proving >= 0}">
      <!-- Collapsible sidebar: file selection and management -->
      <FileSidebar
        title="Theory Files"
        :files="filelist"
        :active="filename"
        :show-create="true"
        @open="open_file"
        @create="create_file"
        @rename="rename_file"
        @delete="delete_file"/>

      <!-- Theory list (full width when not proving, 30% when proving) -->
      <div class="theory-panel">
        <div v-if="loading" class="loading-state"><div class="spinner"></div><p>Loading...</p></div>
        <div v-else-if="!filename" class="empty-state"><h4>Select a file</h4></div>
        <div v-else-if="theory">
          <!-- File header -->
          <div class="file-header">
            <div class="file-header-row">
              <button class="btn btn-sm btn-primary" @click="validate_all(false)">Validate All</button>
              <button class="btn btn-sm btn-warning" @click="validate_all(true)" title="Ignore cache, re-validate everything">Force Validate</button>
              <div class="dropdown ms-auto">
                <button class="btn btn-sm btn-success dropdown-toggle" data-bs-toggle="dropdown"
                        title="Add a new item to this theory">+ Add Item</button>
                <ul class="dropdown-menu dropdown-menu-end">
                  <li><h6 class="dropdown-header">New item</h6></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('thm')">Theorem</a></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('thm.ax')">Axiom</a></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('def')">Definition</a></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.ax')">Constant</a></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('type.ind')">Datatype</a></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.ind')">Fun</a></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('def.pred')">Inductive</a></li>
                  <li><hr class="dropdown-divider"/></li>
                  <li><a class="dropdown-item" href="#" @click.prevent="add_item('header')">Section Header</a></li>
                </ul>
              </div>
            </div>
            <div class="metadata-section">
              <div class="meta-row"><label class="meta-label">theory</label><span class="meta-value">{{ theory.name }}</span></div>
              <div class="meta-row"><label class="meta-label">imports</label><input class="meta-input" v-model="meta_imports" placeholder="one per line"/></div>
              <div class="meta-row"><label class="meta-label">domains</label><input class="meta-input" v-model="meta_domains" placeholder="comma-separated"/></div>
              <div class="meta-row"><label class="meta-label">description</label><input class="meta-input" v-model="meta_description"/></div>
              <button class="btn btn-sm btn-outline-primary mt-1" @click="save_metadata">Save Metadata</button>
            </div>
          </div>

          <!-- Items list -->
          <div class="items-list">
            <div v-for="(item, index) in theory.content" :key="index" class="item-wrapper">
              <!-- Header: special section title styling -->
              <div v-if="item.ty === 'header'" class="item-row item-header-row"
                   :class="{'item-selected': selected === index}"
                   @click="selected = index">
                <span class="item-header-text">{{ item.name || '(header)' }}</span>
                <div class="item-actions">
                  <button class="btn btn-sm btn-outline-secondary" @click.stop="toggle_edit(index)">Edit</button>
                  <button class="btn btn-sm btn-outline-warning" @click.stop="move_item(index, -1)" :disabled="index === 0">↑</button>
                  <button class="btn btn-sm btn-outline-warning" @click.stop="move_item(index, 1)" :disabled="index === theory.content.length - 1">↓</button>
                  <button class="btn btn-sm btn-outline-danger" @click.stop="remove_item(index)">✕</button>
                </div>
              </div>
              <!-- Regular item: name on line 1, content on line 2 -->
              <div v-else class="item-block" :class="{'item-selected': selected === index, 'item-error': item._error}"
                   @click="selected = index">
                <div class="item-row">
                  <span class="item-idx">{{ index }}</span>
                  <span class="item-type">{{ typeLabel(item.ty) }}</span>
                  <span class="item-name">{{ item.name || '' }}</span>
                  <span v-if="thm_status[item.name]" class="item-status" :class="'status-' + thm_status[item.name].toLowerCase()"
                        :title="thm_errors[item.name] || ''">
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
                <!-- Content preview: fixes on one line, prop on next -->
                <div v-if="item.display" class="item-content">
                  <template v-if="item.ty === 'thm' || item.ty === 'thm.ax'">
                    <div v-if="formatDisplay(item.display.vars)" class="item-fixes">fixes {{ formatDisplay(item.display.vars) }}</div>
                    <div class="item-prop-text">{{ formatDisplay(item.display.prop) }}</div>
                  </template>
                  <template v-else-if="item.ty === 'def.ax'">
                    <div class="item-type-sig">:: {{ formatDisplay(item.display.type) }}</div>
                  </template>
                  <template v-else-if="item.ty === 'def'">
                    <div class="item-type-sig">:: {{ formatDisplay(item.display.type) }}</div>
                    <div class="item-prop-text">= {{ formatDisplay(item.display.prop) }}</div>
                  </template>
                  <template v-else-if="item.ty === 'def.ind' || item.ty === 'def.pred'">
                    <div class="item-type-sig">:: {{ formatDisplay(item.display.type) }}</div>
                  </template>
                </div>
              </div>
              <!-- Edit form (inline) -->
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
            </div>
          </div>
        </div>
      </div>

      <!-- Proof panel (50% when proving) -->
      <div v-if="proving >= 0 && proving_item" class="proof-panel">
        <ProofArea
          :key="'proof-' + theory.name + '-' + proving_item.name + '-' + proving"
          :theory_name="theory.name"
          :thm_name="proving_item.name"
          :vars="proving_item.vars"
          :prop="proving_item.prop"
          :old_steps="proving_item.steps"
          :ref="el => { if (el) proof_area_ref = el }"
          @save-steps="(steps) => save_proof(proving, steps)"
          @set-message="msg => toast(msg)"
          @set-context="handle_set_context"
          @query="handle_query"
          @close-prove="toggle_prove(proving)"/>
      </div>

      <!-- History panel (20% when proving) -->
      <div v-if="proving >= 0" class="history-panel">
        <div class="history-panel-header">
          <span class="panel-title-sm">History</span>
          <div class="history-nav">
            <button class="btn btn-sm btn-outline-secondary" @click="proof_goto_step(proof_history_idx - 1)" :disabled="proof_history_idx <= 0">←</button>
            <span class="history-idx-display">{{ proof_history_idx }}/{{ proof_history.length }}</span>
            <button class="btn btn-sm btn-outline-secondary" @click="proof_goto_step(proof_history_idx + 1)" :disabled="proof_history_idx >= proof_history.length">→</button>
          </div>
        </div>
        <div v-if="open_goals.length > 0" class="open-goals-section">
          <div class="open-goals-title">Open goals</div>
          <div v-for="gid in open_goals" :key="gid" class="open-goal-item">{{ gid }}</div>
        </div>
        <div class="history-list">
          <div class="history-item" :class="{'history-selected': proof_history_idx === 0}"
               @click="proof_goto_step(0)">
            <span class="history-idx">0</span>
            <span class="history-text">Initial</span>
          </div>
          <div v-for="(h, i) in proof_history" :key="i" class="history-item"
               :class="{'history-selected': proof_history_idx === i + 1}"
               @click="proof_goto_step(i + 1)">
            <span class="history-idx">{{ i + 1 }}</span>
            <span v-if="formatHistory(h)" class="history-text">{{ formatHistory(h) }}</span>
          </div>
        </div>
      </div>
    </div>

    <!-- Query dialog -->
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
import ProofQuery from '../components/proof/ProofQuery.vue'
import FileSidebar from '../components/FileSidebar.vue'

// ==================== State ====================
const filelist = ref([])
const filename = ref(null)
const theory = ref(null)
const loading = ref(false)
const saving = ref(false)
const message = ref(null)
const query = ref(undefined)
const selected = ref(-1)
const editing = ref(-1)
const proving = ref(-1)
const proving_item = ref(null)
const open_goals = ref([])

const handle_set_context = (data) => {
  proof_history.value = data.history || []
  proof_history_idx.value = (data.history_idx !== undefined && data.history_idx !== null) ? data.history_idx : -1
  open_goals.value = data.open_goals || []
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
const thm_status = ref({})
const thm_errors = ref({})
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

const rename_file = async (oldName) => {
  if (!oldName) return
  const newName = prompt(`Rename file "${oldName}" to:`, oldName)
  if (!newName || newName === oldName) return
  try {
    const res = await api.post('/rename-file', { old: oldName, new: newName })
    if (!res.data.ok) {
      toast({ type: 'error', data: res.data.error || 'Rename failed' })
      return
    }
    await load_files()
    if (filename.value === oldName) {
      await open_file(newName)
    }
    toast({ type: 'OK', data: `Renamed to ${newName}` })
  } catch (e) {
    toast({ type: 'error', data: 'Rename failed' })
  }
}

const delete_file = async (name = null) => {
  const target = name || filename.value
  if (!target) return
  if (!confirm(`Delete file "${target}"? This cannot be undone.`)) return
  try {
    await api.put('/remove-file', { filename: target })
    if (target === filename.value) {
      filename.value = null
      theory.value = null
    }
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
    proving_item.value = null
    proof_area_ref = null
    open_goals.value = []
  } else {
    proving.value = index
    proving_item.value = theory.value.content[index]
    editing.value = -1
    selected.value = index
  }
}

const save_proof = async (index, steps) => {
  theory.value.content[index].steps = steps
  console.log('[SAVE] save_proof called, index =', index, 'steps.length =', steps.length, 'content exists =', !!theory.value.content[index])
  const ok = await persist()
  console.log('[SAVE] persist returned', ok)
  if (ok) {
    await reload_file()
    // Re-validate so the theorem list status refreshes immediately
    try {
      const resp = await api.post('/validate-theory', { filename: filename.value, force: false })
      thm_status.value = resp.data.statuses
      thm_errors.value = resp.data.errors || {}
    } catch (e) {
      console.log('[SAVE] re-validate failed', e)
    }
    toast({ type: 'OK', data: 'Proof saved' })
  }
}
const validate_all = async (force = false) => {
  if (!filename.value) return
  validating.value = true
  try {
    const resp = await api.post('/validate-theory', { filename: filename.value, force })
    thm_status.value = resp.data.statuses
    thm_errors.value = resp.data.errors || {}
    const d = resp.data
    let msg = `Valid: ${d.valid} | Axiom: ${d.axiom} | Unproved: ${d.unproved} | Failed: ${d.failed} | Total: ${d.total}`
    toast({ type: d.failed ? 'error' : 'OK', data: msg })
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

const formatHistory = (h) => {
  if (h === undefined || h === null) return ''
  if (h.step_output) {
    if (Array.isArray(h.step_output)) {
      return h.step_output.map(item => item.text || String(item)).join('')
    }
    return String(h.step_output)
  }
  // New stable-ID pipeline: history entries carry method_name/goal/facts.
  let s = h.method_name || ''
  if (h.goal !== undefined && h.goal !== null) s += ' goal=' + h.goal
  if (h.facts && h.facts.length) s += ' facts=[' + h.facts.join(',') + ']'
  return s
}

const formatType = (T) => {
  if (typeof T === 'string') return T
  if (Array.isArray(T)) return T.map(item => item.text || String(item)).join('')
  return String(T)
}

const formatDisplay = (d) => {
  if (!d) return ''
  if (typeof d === 'string') return d
  if (Array.isArray(d)) return d.map(formatDisplay).join('')
  if (d.text) return d.text
  return ''
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
.theory-panel { flex: 1; overflow-y: auto; padding: 12px; min-width: 0; }
.proving-mode .theory-panel { flex: 0 0 30%; border-right: 1px solid #dee2e6; }
.proof-panel { flex: 0 0 50%; display: flex; flex-direction: column; overflow: hidden; min-width: 0; }
.history-panel { flex: 0 0 20%; border-left: 1px solid #dee2e6; display: flex; flex-direction: column; overflow: hidden; background: #f8f9fa; min-width: 180px; }
.history-panel-header { display: flex; align-items: center; justify-content: space-between; padding: 8px 10px; border-bottom: 1px solid #dee2e6; }
.panel-title-sm { font-weight: 700; font-size: 13px; color: #495057; }
.history-nav { display: flex; align-items: center; gap: 4px; }
.history-idx-display { font-size: 12px; color: #666; min-width: 30px; text-align: center; }
.history-list { flex: 1; overflow-y: auto; padding: 4px; }
.open-goals-section { padding: 6px 8px; border-bottom: 1px solid #e0e0e0; }
.open-goals-title { font-size: 11px; font-weight: 700; color: #c0392b; text-transform: uppercase; margin-bottom: 3px; }
.open-goal-item { font-family: Consolas, monospace; font-size: 12px; color: #333; padding: 1px 0; }
.file-select { width: auto; min-width: 120px; cursor: pointer; }
.center-panel { flex: 1; overflow-y: auto; padding: 12px; }-list { overflow-y: auto; }
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
.item-wrapper { border-bottom: 1px solid #e8e8e8; }
.item-block { padding: 0; }
.item-row { display: flex; align-items: center; padding: 5px 10px; gap: 8px; cursor: pointer; }
.item-row:hover { background: #f8f9fa; }
.item-selected { background: #e8f0fe !important; }
.item-error { background: #fff0f0 !important; }
.item-idx { color: #aaa; font-size: 11px; width: 20px; text-align: right; flex-shrink: 0; }
.item-type { font-size: 11px; color: #006000; min-width: 65px; flex-shrink: 0; text-transform: uppercase; letter-spacing: 0.3px; }
.item-name { font-family: Consolas, monospace; font-size: 13px; font-weight: 600; color: #1a1a1a; flex-shrink: 0; }
.item-status { font-size: 14px; flex-shrink: 0; }
.item-actions { display: flex; gap: 3px; margin-left: auto; flex-shrink: 0; }
.item-actions .btn { padding: 1px 7px; font-size: 11px; }
.item-content { margin-left: 36px; padding: 0 10px 6px 0; font-family: Consolas, monospace; font-size: 13px; line-height: 1.5; }
.item-content .item-fixes { color: #888; font-size: 12px; }
.item-content .item-prop-text { color: #333; }
.item-content .item-type-sig { color: #555; }
.item-header-row { background: #f5f0ff; border-left: 3px solid #6610f2; padding: 8px 10px !important; }
.item-header-text { font-weight: 700; font-size: 14px; color: #333; flex: 1; }

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
.modal-overlay { position: fixed; inset: 0; background: rgba(0,0,0,0.5); display: flex; align-items: center; justify-content: center; z-index: 1000; }
.modal-content { background: #fff; border-radius: 8px; padding: 16px; min-width: 360px; max-width: 560px; box-shadow: 0 4px 16px rgba(0,0,0,0.3); }
.modal-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 12px; }
.modal-title { margin: 0; font-size: 15px; }
.modal-body { font-size: 14px; }
.btn-close { background: none; border: none; font-size: 16px; cursor: pointer; }
</style>

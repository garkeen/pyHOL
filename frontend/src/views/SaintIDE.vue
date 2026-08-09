<template>
  <div class="saint-container">
    <nav class="navbar navbar-dark bg-dark">
      <span class="navbar-brand" style="padding-left: 44px">SAINT</span>
      <span class="text-light small">{{ currentFile || 'Interactive Integral CAS' }}</span>
      <span v-if="dirty" class="text-warning small ms-2">Unsaved changes</span>
    </nav>
    <div class="saint-body">
      <!-- Collapsible sidebar: file selection -->
      <FileSidebar
        title="SAINT Files"
        :files="files"
        :active="currentFile"
        @open="openFile"
        @rename="renameFile"
        @delete="deleteFile"/>

      <!-- Left: items list (always visible) -->
      <div class="saint-main">
        <div v-if="currentFile" class="file-header">
          <div class="file-header-row">
            <button class="btn btn-sm btn-primary" @click="saveFile" :disabled="!dirty">Save</button>
            <span class="text-muted small" v-if="!dirty">All changes saved</span>
            <div class="dropdown ms-auto">
              <button class="btn btn-sm btn-success dropdown-toggle" data-bs-toggle="dropdown"
                      title="Add an item to this file">+ Add Item</button>
              <ul class="dropdown-menu dropdown-menu-end">
                <li><h6 class="dropdown-header">New item</h6></li>
                <li><a class="dropdown-item" href="#" @click.prevent="addNew('theorem')">Theorem</a></li>
                <li><a class="dropdown-item" href="#" @click.prevent="addNew('definition')">Definition</a></li>
                <li><hr class="dropdown-divider"/></li>
                <li><a class="dropdown-item" href="#" @click.prevent="addNew('calculation')">Calculation Problem</a></li>
              </ul>
            </div>
          </div>
          <div class="metadata-section">
            <div class="meta-row"><label class="meta-label">theory</label><span class="meta-value">{{ theoryName }}</span></div>
            <div class="meta-row"><label class="meta-label">imports</label><input class="meta-input" v-model="importsText" placeholder="comma-separated"/></div>
            <div class="meta-row"><label class="meta-label">description</label><input class="meta-input" v-model="description"/></div>
          </div>
        </div>
        <div v-if="parseError" class="alert alert-danger py-1 small">{{ parseError }}</div>

        <div v-for="(item, i) in fileItems" :key="i" class="item-row">
          <!-- Header -->
          <template v-if="item.type === 'header'">
            <div class="item-header" :style="{marginLeft: (item.level-1)*16+'px'}">{{ item.name }}</div>
          </template>
          <!-- Table -->
          <template v-else-if="item.type === 'table'">
            <div class="item-table">{{ item.name }} table ({{ Object.keys(item.table || {}).length }} values)</div>
          </template>
          <!-- Calculation with goal (computation task) -->
          <template v-else-if="item.type === 'calculation' && item.goal">
            <div class="item-calc" @mouseenter="hoverIdx = i" @mouseleave="hoverIdx = -1">
              <span class="type-badge type-calculation">calc</span>
              <span class="item-name">{{ item.name }}</span>
              <MathEquation :data="'\\(' + item.goal_latex + '\\)'" />
              <span v-if="hoverIdx === i" class="item-actions">
                <button class="btn btn-link btn-sm py-0 px-1" @click.stop="startEdit(i)">✎</button>
                <button class="btn btn-link btn-sm py-0 px-1" @click.stop="startCompute(item)">▶</button>
                <button class="btn btn-link btn-sm py-0 px-1 text-danger" @click.stop="deleteItem(i)">✕</button>
              </span>
            </div>
          </template>
          <!-- Editable items (theorem, definition, single-line calculation) -->
          <template v-else>
            <div class="item-lib" @mouseenter="hoverIdx = i" @mouseleave="hoverIdx = -1">
              <span class="type-badge" :class="'type-' + item.type">{{ item.type }}</span>
              <MathEquation v-if="item.latex" :data="'\\(' + item.latex + '\\)'" />
              <span v-else class="text-muted small">{{ item.expr }}</span>
              <span v-if="hoverIdx === i" class="item-actions">
                <button class="btn btn-link btn-sm py-0 px-1" @click.stop="startEdit(i)">✎</button>
                <button class="btn btn-link btn-sm py-0 px-1 text-danger" @click.stop="deleteItem(i)">✕</button>
              </span>
            </div>
          </template>
        </div>
      </div>

      <!-- Right panel: edit or calculation workspace (only when active) -->
      <div v-if="computing || editIdx >= 0" class="saint-side">
        <!-- Calculation workspace -->
        <div v-if="computing" class="calc-workspace">
          <div class="calc-header">
            <span>{{ computingName }}</span>
            <button class="btn btn-sm btn-outline-secondary ms-auto" @click="closeWorkspace">✕</button>
          </div>

          <div v-if="targetLatex" class="target-bar">
            <span class="target-label">Expected:</span>
            <MathEquation :data="'\\(' + targetLatex + '\\)'" />
            <button v-if="steps.length" class="btn btn-outline-primary btn-sm ms-2" @click="verifyResult">Verify</button>
            <span v-if="verifyStatus" :class="{'text-success': verifyStatus.includes('Match'), 'text-danger': verifyStatus.includes('No')}">{{ verifyStatus }}</span>
          </div>
          <div class="calc-display" v-if="startLatex">
            <div class="calc-line calc-start"><MathEquation :data="'\\(' + startLatex + '\\)'" /></div>
            <div v-for="(step, i) in displaySteps" :key="i" class="calc-line">
              <span class="eq-sign">=</span>
              <MathEquation :data="'\\(' + step.latex_res + '\\)'" />
              <span class="rule-tag">{{ step.rule.str }}</span>
            </div>
          </div>
          <div class="rule-palette" v-if="startLatex">
            <div v-if="suggestions.length" class="suggestions">
              <div class="suggestions-title">Suggestions</div>
              <div class="suggestion-list">
                <button v-for="(s, i) in suggestions" :key="i" class="btn btn-sm btn-outline-success suggestion-btn"
                  @click="applySuggestion(s)">
                  {{ s.label }}
                </button>
              </div>
            </div>
            <div v-if="suggestLoading" class="small text-muted py-1">Finding suggestions...</div>

            <div class="rule-buttons mt-2">
              <button v-for="r in RULES" :key="r.name" class="btn btn-sm"
                :class="selectedRule === r.name ? 'btn-dark' : 'btn-outline-secondary'"
                @click="selectRule(r)">{{ r.label }}</button>
              <button class="btn btn-sm btn-outline-info" @click="loadSuggestions" :disabled="suggestLoading">💡 Suggest</button>
            </div>

            <div v-if="selectedRule && currentRuleParams.length" class="rule-params">
              <div v-for="p in currentRuleParams" :key="p.key" class="param-row">
                <label class="param-label">{{ p.label }}</label>
                <input v-model="paramValues[p.key]" class="form-control form-control-sm param-input" :placeholder="p.placeholder" />
              </div>
            </div>

            <div class="mt-2">
              <button v-if="selectedRule" class="btn btn-success btn-sm" @click="applyRule" :disabled="applying">{{ applying ? '...' : 'Apply' }}</button>
              <button class="btn btn-outline-danger btn-sm ms-2" @click="undoStep" :disabled="!steps.length">Undo</button>
              <button class="btn btn-outline-secondary btn-sm ms-2" @click="resetCalculation" :disabled="!steps.length">Reset</button>
              <button class="btn btn-warning btn-sm ms-2" @click="saveSteps" :disabled="!steps.length || computingItemIdx < 0">Save Steps</button>
            </div>
          </div>
          <div v-if="applyError" class="alert alert-danger mt-2 py-1 small">{{ applyError }}</div>
        </div>

        <!-- Edit workspace -->
        <div v-else class="edit-workspace">
          <div class="calc-header">
            <span>Edit item</span>
            <button class="btn btn-sm btn-outline-secondary ms-auto" @click="closeWorkspace">✕</button>
          </div>
          <div v-if="editItem && editItem.type === 'calculation' && editItem.goal">
            <div class="edit-form">
              <label class="edit-label">Name</label>
              <input v-model="editItem.name" class="form-control form-control-sm edit-input" placeholder="Name" />
              <label class="edit-label mt-2">Goal</label>
              <input v-model="editItem.goal" class="form-control form-control-sm edit-input" placeholder="INT x. ..." @keyup.enter="finishEditCalc()" @keyup.esc="closeWorkspace" />
              <div class="edit-actions mt-2">
                <button class="btn btn-success btn-sm" @click="finishEditCalc()">OK</button>
                <button class="btn btn-outline-secondary btn-sm" @click="cancelEdit()">Cancel</button>
              </div>
            </div>
          </div>
          <div v-else-if="editItem">
            <div class="edit-form">
              <label class="edit-label">Type</label>
              <select v-model="editItem.type" class="form-select form-select-sm form-ctrl">
                <option value="theorem">theorem</option>
                <option value="definition">definition</option>
                <option value="calculation">calculation</option>
              </select>
              <label class="edit-label mt-2">Expression</label>
              <input v-model="editItem.expr" class="form-control form-control-sm edit-input mono" @keyup.enter="finishEdit()" @keyup.esc="cancelEdit()" />
              <div class="edit-actions mt-2">
                <button class="btn btn-success btn-sm" @click="finishEdit()">OK</button>
                <button class="btn btn-outline-secondary btn-sm" @click="cancelEdit()">Cancel</button>
              </div>
            </div>
          </div>
        </div>

        </div>
    </div>
  </div>
</template>

<script setup>
import { ref, computed, onMounted } from 'vue'
import api from '../api'
import MathEquation from '../components/util/MathEquation.vue'
import FileSidebar from '../components/FileSidebar.vue'

const RULES = [
  { name: 'simplify', label: 'Simplify', params: [] },
  { name: 'substitute', label: 'Substitute', params: [
    { key: 'var_name', label: 'u =', placeholder: 'u' },
    { key: 'g', label: 'g(x) =', placeholder: 'x^2' },
  ]},
  { name: 'substitute_inverse', label: 'Subst Inv', params: [
    { key: 'var_name', label: 'var =', placeholder: 'x' },
    { key: 'g', label: 'g(u) =', placeholder: 'u/2' },
  ]},
  { name: 'integrate_by_parts', label: 'By Parts', params: [
    { key: 'parts_u', label: 'u =', placeholder: 'x' },
    { key: 'parts_v', label: "v' =", placeholder: 'exp(x)' },
  ]},
  { name: 'definite_integral_identity', label: 'Def ID', params: [] },
  { name: 'indefinite_integral_identity', label: 'Indef ID', params: [] },
  { name: 'integrate_by_equation', label: 'Solve Eq', params: [
    { key: 'lhs', label: 'Original:', placeholder: '(auto)' },
  ]},
  { name: 'rewrite_trig', label: 'Trig', params: [
    { key: 'rule', label: 'Rule:', placeholder: 'TR0' },
  ]},
  { name: 'series_expansion', label: 'Series', params: [
    { key: 'index_var', label: 'Index:', placeholder: 'n' },
  ]},
  { name: 'series_evaluation', label: 'Series Eval', params: [] },
  { name: 'int_sum_exchange', label: 'Exch ∫Σ', params: [] },
  { name: 'expand_polynomial', label: 'Expand', params: [] },
  { name: 'unfold_power', label: 'Unfold', params: [] },
  { name: 'elim_abs', label: 'Elim Abs', params: [] },
  { name: 'elim_inf_interval', label: 'Elim Inf', params: [] },
  { name: 'split_region', label: 'Split', params: [
    { key: 'c', label: 'c =', placeholder: '1' },
  ]},
]

const files = ref([])
const currentFile = ref('')
const theoryName = ref('')
const importsText = ref('')
const description = ref('')
const fileItems = ref([])
const dirty = ref(false)
const hoverIdx = ref(-1)
const editIdx = ref(-1)
const savedExpr = ref('')

const computing = ref(false)
const computingName = ref('')
const computingItemIdx = ref(-1)
const exprInput = ref('')
const parseError = ref('')
const startLatex = ref('')
const startExpr = ref('')
const targetLatex = ref('')
const targetExpr = ref('')
const steps = ref([])
const displaySteps = ref([])
const selectedRule = ref('')
const paramValues = ref({})
const suggestions = ref([])
const suggestLoading = ref(false)
const applying = ref(false)
const applyError = ref('')
const verifyStatus = ref('')

const editItem = computed(() => {
  if (editIdx.value < 0 || editIdx.value >= fileItems.value.length) return null
  return fileItems.value[editIdx.value]
})

const currentRuleParams = computed(() => {
  const r = RULES.find(r => r.name === selectedRule.value)
  return r ? r.params : []
})

onMounted(async () => {
  const res = await api.post('/saint/files')
  files.value = res.data.files
})

async function openFile(name) {
  currentFile.value = name
  closeWorkspace()
  const res = await api.post('/saint/load', { filename: name })
  fileItems.value = res.data.items
  theoryName.value = res.data.theory || name
  importsText.value = (res.data.imports || []).join(', ')
  description.value = res.data.description || ''
  parseError.value = ''
}

async function refreshFileList() {
  const res = await api.post('/saint/files')
  files.value = res.data.files
  if (!currentFile.value) return
  if (!files.value.includes(currentFile.value)) {
    currentFile.value = ''
    fileItems.value = []
    closeWorkspace()
  }
}

async function renameFile(oldName) {
  const newName = prompt(`Rename file "${oldName}" to:`, oldName)
  if (!newName || newName === oldName) return
  try {
    const res = await api.post('/rename-file', { old: oldName, new: newName })
    if (!res.data.ok) {
      console.error('Rename failed:', res.data.error)
      return
    }
    await refreshFileList()
    if (currentFile.value === oldName) {
      await openFile(newName)
    }
  } catch (e) { console.error('Rename:', e) }
}

async function deleteFile(name) {
  if (!confirm(`Delete file "${name}"? This cannot be undone.`)) return
  try {
    await api.put('/remove-file', { filename: name })
    await refreshFileList()
    if (currentFile.value === name) {
      currentFile.value = ''
      fileItems.value = []
      closeWorkspace()
    }
  } catch (e) { console.error('Delete:', e) }
}

// Workspace management: edit and computation both live in the right panel
function closeWorkspace() {
  computing.value = false
  computingItemIdx.value = -1
  editIdx.value = -1
  parseError.value = ''
  suggestions.value = []
}

function startEdit(i) {
  editIdx.value = i
  computing.value = false
  savedExpr.value = fileItems.value[i].expr || ''
}

// Item editing
async function finishEditCalc() {
  if (editIdx.value < 0) return
  const idx = editIdx.value
  editIdx.value = -1
  dirty.value = true
  try {
    const res = await api.post('/saint/parse', { expr: fileItems.value[idx].goal })
    if (res.data.status === 'ok') fileItems.value[idx].goal_latex = res.data.latex
  } catch {}
}
function finishEdit() {
  if (editIdx.value < 0) return
  dirty.value = true
  refreshItemLatex(editIdx.value)
  editIdx.value = -1
}
function cancelEdit() {
  if (editIdx.value >= 0 && savedExpr.value) {
    fileItems.value[editIdx.value].expr = savedExpr.value
  }
  editIdx.value = -1
}
function deleteItem(i) {
  fileItems.value.splice(i, 1)
  dirty.value = true
  if (editIdx.value === i) editIdx.value = -1
  else if (editIdx.value > i) editIdx.value -= 1
}
function addNew(type) {
  if (type === 'calculation') {
    fileItems.value.push({
      type: 'calculation', name: 'New Problem', goal: 'INT x. x', target: null, conds: [], calc: [],
    })
    startEdit(fileItems.value.length - 1)
  } else {
    fileItems.value.push({
      type: type, expr: 'f(x) = x', latex: '', category: '', conds: [],
    })
    startEdit(fileItems.value.length - 1)
  }
  dirty.value = true
}
async function refreshItemLatex(i) {
  if (i < 0 || i >= fileItems.value.length) return
  const item = fileItems.value[i]
  if (!item.expr) return
  try {
    const res = await api.post('/saint/parse', { expr: item.expr })
    if (res.data.status === 'ok') item.latex = res.data.latex
  } catch {}
}
async function saveFile() {
  try {
    await api.post('/saint/save', {
      filename: currentFile.value,
      name: theoryName.value || currentFile.value,
      imports: importsText.value.split(',').map(s => s.trim()).filter(s => s),
      description: description.value,
      items: fileItems.value,
    })
    dirty.value = false
  } catch (e) { console.error('Save:', e) }
}

// Computation
async function startCompute(item) {
  computing.value = true
  computingName.value = item.name
  computingItemIdx.value = fileItems.value.indexOf(item)
  editIdx.value = -1
  exprInput.value = item.goal
  targetExpr.value = item.target || ''
  targetLatex.value = ''
  verifyStatus.value = ''
  parseError.value = ''
  try {
    const res = await api.post('/saint/parse', { expr: item.goal })
    if (res.data.status === 'ok') {
      startLatex.value = res.data.latex
      startExpr.value = res.data.text
      steps.value = []
      displaySteps.value = []
      selectedRule.value = ''
    } else { parseError.value = res.data.msg }
  } catch (e) { parseError.value = e.message }
  if (item.target) {
    api.post('/saint/parse', { expr: item.target }).then(res => {
      if (res.data.status === 'ok') targetLatex.value = res.data.latex
    })
  }
}
async function loadSuggestions() {
  if (!startExpr.value) return
  suggestions.value = []
  suggestLoading.value = true
  try {
    const cur = displaySteps.value.length ? displaySteps.value[displaySteps.value.length - 1].res : startExpr.value
    const res = await api.post('/saint/suggest', { expr: cur })
    if (res.data.status === 'ok') {
      suggestions.value = res.data.suggestions
    }
  } catch (e) { console.error('Suggest:', e) } finally { suggestLoading.value = false }
}
async function applySuggestion(s) {
  selectedRule.value = ''
  applyError.value = ''
  verifyStatus.value = ''
  applying.value = true
  try {
    const res = await api.post('/saint/apply', {
      start: startExpr.value, steps: steps.value,
      rule: s.rule, params: s.params,
    })
    if (res.data.status === 'ok') {
      displaySteps.value = res.data.calculation.steps
      steps.value.push({ rule: s.rule, params: s.params })
      suggestions.value = []
    } else { applyError.value = res.data.msg }
  } catch (e) { applyError.value = e.message } finally { applying.value = false }
}

function selectRule(r) {
  selectedRule.value = r.name
  paramValues.value = {}
  if (r.name === 'integrate_by_equation' && startExpr.value) paramValues.value.lhs = startExpr.value
  applyError.value = ''
}
async function applyRule() {
  applyError.value = ''
  if (!selectedRule.value || !startExpr.value) return
  const params = {}
  for (const p of currentRuleParams.value) { if (paramValues.value[p.key]) params[p.key] = paramValues.value[p.key] }
  applying.value = true
  verifyStatus.value = ''
  try {
    const res = await api.post('/saint/apply', { start: startExpr.value, steps: steps.value, rule: selectedRule.value, params })
    if (res.data.status === 'ok') {
      displaySteps.value = res.data.calculation.steps
      steps.value.push({ rule: selectedRule.value, params })
    } else { applyError.value = res.data.msg }
  } catch (e) { applyError.value = e.message } finally { applying.value = false }
}
async function verifyResult() {
  if (!steps.value.length || !targetExpr.value) return
  const cur = displaySteps.value[displaySteps.value.length - 1].res
  try {
    const res = await api.post('/saint/verify', { expr1: cur, expr2: targetExpr.value })
    if (res.data.status === 'ok') verifyStatus.value = res.data.match ? '✓ Match' : '✗ No match'
  } catch (e) { verifyStatus.value = 'Error' }
}
function saveSteps() {
  if (computingItemIdx.value < 0 || !steps.value.length) return
  const item = fileItems.value[computingItemIdx.value]
  if (!item) return
  item.calc = steps.value.map(s => {
    const reasonMap = {
      simplify: "Simplification", substitute: "Substitution",
      substitute_inverse: "Substitution inverse", integrate_by_parts: "Integrate by parts",
      rewrite: "Rewrite", rewrite_trig: "Rewrite trigonometric",
      unfold_power: "Unfold power", split_region: "Split region",
      elim_abs: "Elim abs", elim_inf_interval: "Eliminate infinity",
      solve_equation: "Solve equation", series_expansion: "Series expansion",
      series_evaluation: "Series evaluation", int_sum_exchange: "Exchange integral and sum",
      expand_polynomial: "Expand polynomial", definite_integral_identity: "Definite integral identity",
      indefinite_integral_identity: "Indefinite integral identity",
      integrate_by_equation: "Solve equation", linearity: "Linearity",
    }
    return { reason: reasonMap[s.rule] || s.rule, params: s.params || {} }
  })
  dirty.value = true
}

function undoStep() {
  if (!steps.value.length) return
  steps.value.pop()
  displaySteps.value.pop()
  applyError.value = ''
  verifyStatus.value = ''
}
function resetCalculation() {
  steps.value = []
  displaySteps.value = []
  selectedRule.value = ''
  applyError.value = ''
  verifyStatus.value = ''
}
</script>

<style scoped>
.saint-container { display: flex; flex-direction: column; height: 100vh; }
.saint-body { display: flex; flex: 1; overflow: hidden; }

.saint-main { flex: 1; overflow-y: auto; padding: 16px; min-width: 0; }
.saint-side { flex: 0 0 46%; min-width: 420px; border-left: 1px solid #dee2e6; overflow-y: auto; padding: 12px; background: #fafbfc; }

.file-header { margin-bottom: 14px; }
.file-header-row { display: flex; align-items: center; gap: 8px; margin-bottom: 10px; }
.metadata-section { background: #f5f7fa; border: 1px solid #e1e5eb; border-radius: 4px; padding: 8px; }
.meta-row { display: flex; align-items: center; gap: 8px; margin-bottom: 6px; }
.meta-row:last-child { margin-bottom: 0; }
.meta-label { font-weight: 600; font-size: 12px; min-width: 70px; color: #555; }
.meta-value { font-size: 13px; color: #212529; }
.meta-input { flex: 1; padding: 3px 6px; font-size: 13px; border: 1px solid #ccc; border-radius: 3px; }

.input-bar { display: flex; gap: 8px; margin-bottom: 12px; }
.expr-input { flex: 1; font-family: monospace; }
.item-row { padding: 2px 0; }
.item-header { font-size: 0.9rem; font-weight: 600; color: #343a40; padding: 8px 0 4px; border-bottom: 1px solid #eee; margin-bottom: 4px; }
.item-lib { display: flex; align-items: baseline; gap: 6px; padding: 3px 8px; border-radius: 4px; }
.item-lib:hover { background: #f0f7ff; }
.item-name { font-size: 0.85rem; font-weight: 600; color: #4a148c; min-width: 80px; }
.item-calc { display: flex; align-items: baseline; gap: 6px; padding: 4px 8px; background: #f8f0fc; border-radius: 4px; margin: 2px 0; }
.item-table { font-size: 0.85rem; color: #6c757d; padding: 3px 0; }
.item-actions { margin-left: auto; white-space: nowrap; }
.type-badge { font-size: 0.65rem; padding: 0 4px; border-radius: 2px; text-transform: uppercase; white-space: nowrap; min-width: 28px; text-align: center; }
.type-theorem { background: #d4edda; color: #155724; }
.type-definition { background: #cce5ff; color: #004085; }
.type-calculation { background: #f3e5f5; color: #4a148c; }

/* Right panel */
.calc-header { display: flex; align-items: center; margin-bottom: 10px; }
.side-placeholder { color: #999; text-align: center; padding: 40px 0; font-size: 13px; }

/* Edit workspace */
.edit-workspace { }
.edit-form { max-width: 560px; }
.edit-label { font-size: 0.8rem; color: #495057; font-weight: 600; display: block; }
.edit-input { font-size: 0.85rem; }
.edit-actions { display: flex; gap: 6px; }
.mono { font-family: monospace; }
.form-ctrl { max-width: 200px; }

.target-bar { display: flex; align-items: baseline; gap: 6px; padding: 8px 12px; background: #fffde7; border: 1px solid #fff9c4; border-radius: 6px; margin-bottom: 8px; font-size: 0.9rem; }
.target-label { font-size: 0.8rem; color: #827717; font-weight: 600; }
.calc-display { background: white; border: 1px solid #dee2e6; border-radius: 8px; padding: 14px; margin-bottom: 12px; }
.calc-line { display: flex; align-items: baseline; gap: 8px; padding: 3px 0; }
.calc-start { font-size: 1.1em; border-bottom: 1px solid #f0f0f0; padding-bottom: 6px; margin-bottom: 4px; }
.eq-sign { color: #6c757d; font-weight: bold; min-width: 16px; }
.rule-tag { font-size: 0.75rem; color: #0d6efd; background: #e7f1ff; padding: 1px 6px; border-radius: 3px; margin-left: 8px; }
.rule-palette { background: #f8f9fa; border: 1px solid #dee2e6; border-radius: 8px; padding: 10px; }
.suggestions { margin-bottom: 8px; }
.suggestions-title { font-size: 0.8rem; color: #198754; font-weight: 600; margin-bottom: 4px; }
.suggestion-list { display: flex; flex-wrap: wrap; gap: 4px; }
.suggestion-btn { font-size: 0.8rem; }
.rule-buttons { display: flex; flex-wrap: wrap; gap: 5px; margin-bottom: 8px; }
.rule-params { display: flex; flex-wrap: wrap; gap: 10px; margin-bottom: 6px; }
.param-row { display: flex; align-items: center; gap: 4px; }
.param-label { font-size: 0.85rem; color: #495057; white-space: nowrap; }
.param-input { width: 100px; font-family: monospace; }

.ms-auto { margin-left: auto; }
.ms-2 { margin-left: 8px; }
.mt-2 { margin-top: 8px; }
</style>
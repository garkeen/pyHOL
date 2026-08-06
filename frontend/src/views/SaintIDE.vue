<template>
  <div class="saint-container">
    <nav class="navbar navbar-dark bg-dark">
      <span class="navbar-brand">SAINT</span>
      <span class="text-light small">{{ currentFile || 'Interactive Integral CAS' }}</span>
      <button v-if="dirty" class="btn btn-warning btn-sm ms-auto" @click="saveFile">Save File</button>
    </nav>
    <div class="saint-body">
      <!-- Left: file list -->
      <div class="saint-files">
        <h6>Files</h6>
        <ul class="file-list">
          <li v-for="f in files" :key="f" @click="openFile(f)" :class="{active: currentFile === f}">{{ f }}</li>
        </ul>
      </div>

      <!-- Right: items or calculation -->
      <div class="saint-main">
        <!-- Calculation workspace -->
        <div v-if="computing" class="calc-workspace">
          <div class="calc-header">
            <button class="btn btn-sm btn-outline-secondary" @click="computing = false">← Back</button>
            <span class="ms-2">{{ computingName }}</span>
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
                      <div class="rule-palette" v-if="startLatex">
            <!-- Suggestions -->
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
              <button v-for="r in RULES" :key="r.name" class="btn btn-sm" :class="selectedRule === r.name ? 'btn-dark' : 'btn-outline-secondary'" @click="selectRule(r)">{{ r.label }}</button>
              <button class="btn btn-sm btn-outline-info" @click="loadSuggestions" :disabled="suggestLoading">💡 Suggest</button>
              <button class="btn btn-sm btn-outline-info" @click="loadSuggestions" :disabled="suggestLoading">💡 Suggest</button>
            </div>
              <button v-for="r in RULES" :key="r.name" class="btn btn-sm" :class="selectedRule === r.name ? 'btn-dark' : 'btn-outline-secondary'" @click="selectRule(r)">{{ r.label }}</button>
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
            </div>
          </div>
          <div v-if="applyError" class="alert alert-danger mt-2 py-1 small">{{ applyError }}</div>
        </div>

        <!-- Items list -->
        <div v-else class="items-list">
          <div class="input-bar">
            <input v-model="exprInput" class="form-control expr-input" placeholder="INT x. x^2" @keyup.enter="startManualCalc" />
            <button class="btn btn-primary btn-sm" @click="startManualCalc">Compute</button>
            <button v-if="currentFile" class="btn btn-outline-success btn-sm" @click="addItem">+ Item</button>
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
              <div class="item-calc">
                <span class="type-badge type-calculation">calc</span>
                <span class="item-name">{{ item.name }}</span>
                <MathEquation :data="'\\(' + item.goal + '\\)'" />
                <button class="btn btn-outline-primary btn-sm ms-auto" @click="startCompute(item)">Compute</button>
              </div>
            </template>
            <!-- Editable items (theorem, definition, single-line calculation) -->
            <template v-else>
              <div class="item-lib" @mouseenter="hoverIdx = i" @mouseleave="hoverIdx = -1">
                <!-- Edit mode -->
                <template v-if="editIdx === i">
                  <select v-model="item.type" class="form-select form-select-sm type-select">
                    <option value="theorem">theorem</option>
                    <option value="definition">definition</option>
                    <option value="calculation">calculation</option>
                  </select>
                  <input v-model="item.expr" class="form-control form-control-sm lib-edit-input" @keyup.enter="finishEdit" @keyup.esc="cancelEdit" />
                  <button class="btn btn-success btn-sm" @click="finishEdit">OK</button>
                  <button class="btn btn-outline-secondary btn-sm" @click="cancelEdit">Cancel</button>
                </template>
                <!-- Display mode -->
                <template v-else>
                  <span class="type-badge" :class="'type-' + item.type">{{ item.type }}</span>
                  <MathEquation v-if="item.latex" :data="'\\(' + item.latex + '\\)'" />
                  <span v-else class="text-muted small">{{ item.expr }}</span>
                  <span v-if="hoverIdx === i" class="item-actions">
                    <button class="btn btn-link btn-sm py-0 px-1" @click.stop="startEdit(i)">✎</button>
                    <button class="btn btn-link btn-sm py-0 px-1 text-danger" @click.stop="deleteItem(i)">✕</button>
                  </span>
                </template>
              </div>
            </template>
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
const fileItems = ref([])
const dirty = ref(false)
const hoverIdx = ref(-1)
const editIdx = ref(-1)
const savedExpr = ref('')

const computing = ref(false)
const computingName = ref('')
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
  computing.value = false
  dirty.value = false
  editIdx.value = -1
  const res = await api.post('/saint/load', { filename: name })
  fileItems.value = res.data.items
}

// Item editing
function startEdit(i) {
  editIdx.value = i
  savedExpr.value = fileItems.value[i].expr || ''
}
function finishEdit() {
  editIdx.value = -1
  dirty.value = true
  refreshItemLatex(editIdx.value)
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
}
function addItem() {
  fileItems.value.push({
    type: 'theorem', expr: 'f(x) = x', latex: '', category: '', conds: [],
  })
  dirty.value = true
  startEdit(fileItems.value.length - 1)
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
      name: currentFile.value,
      imports: [],
      items: fileItems.value,
    })
    dirty.value = false
  } catch (e) { console.error('Save:', e) }
}

// Computation
async function startCompute(item) {
  computing.value = true
  computingName.value = item.name
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
async function startManualCalc() {
  parseError.value = ''
  if (!exprInput.value.trim()) return
  try {
    const res = await api.post('/saint/parse', { expr: exprInput.value })
    if (res.data.status === 'ok') {
      computing.value = true
      computingName.value = 'Manual'
      startLatex.value = res.data.latex
      startExpr.value = res.data.text
      targetLatex.value = ''
      targetExpr.value = ''
      steps.value = []
      displaySteps.value = []
      selectedRule.value = ''
      verifyStatus.value = ''
    } else { parseError.value = res.data.msg }
  } catch (e) { parseError.value = e.message }
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
.saint-files { width: 180px; border-right: 1px solid #dee2e6; padding: 10px; background: #f8f9fa; overflow-y: auto; }
.saint-files h6 { font-size: 0.8rem; text-transform: uppercase; color: #6c757d; }
.file-list { list-style: none; padding: 0; margin: 0; }
.file-list li { padding: 4px 8px; cursor: pointer; border-radius: 4px; font-size: 0.85rem; }
.file-list li:hover { background: #e9ecef; }
.file-list li.active { background: #0d6efd; color: white; }
.saint-main { flex: 1; overflow-y: auto; padding: 16px; }
.input-bar { display: flex; gap: 8px; margin-bottom: 12px; }
.expr-input { flex: 1; font-family: monospace; }
.items-list { max-width: 800px; }
.item-row { padding: 2px 0; }
.item-header { font-size: 0.9rem; font-weight: 600; color: #343a40; padding: 8px 0 4px; border-bottom: 1px solid #eee; margin-bottom: 4px; }
.item-lib { display: flex; align-items: baseline; gap: 6px; padding: 3px 8px; border-radius: 4px; }
.item-lib:hover { background: #f0f7ff; }
.item-calc { display: flex; align-items: baseline; gap: 6px; padding: 4px 8px; background: #f8f0fc; border-radius: 4px; margin: 2px 0; }
.item-name { font-size: 0.85rem; font-weight: 600; color: #4a148c; min-width: 80px; }
.item-table { font-size: 0.85rem; color: #6c757d; padding: 3px 0; }
.item-actions { margin-left: auto; white-space: nowrap; }
.type-badge { font-size: 0.65rem; padding: 0 4px; border-radius: 2px; text-transform: uppercase; white-space: nowrap; min-width: 28px; text-align: center; }
.type-theorem { background: #d4edda; color: #155724; }
.type-definition { background: #cce5ff; color: #004085; }
.type-calculation { background: #f3e5f5; color: #4a148c; }
.type-select { width: auto; font-size: 0.75rem; }
.lib-edit-input { flex: 1; font-family: monospace; font-size: 0.8rem; }
.ms-auto { margin-left: auto; }
.ms-2 { margin-left: 8px; }
.calc-workspace { max-width: 800px; }
.calc-header { display: flex; align-items: center; margin-bottom: 12px; }
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
</style>

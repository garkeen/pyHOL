<template>
  <div class="saint-container">
    <nav class="navbar navbar-dark bg-dark">
      <span class="navbar-brand">SAINT</span>
      <span class="text-light small">Interactive Integral CAS</span>
      <button v-if="libraryDirty" class="btn btn-warning btn-sm ms-auto" @click="saveLibrary">Save Library</button>
    </nav>

    <div class="saint-body">
      <!-- Left: Library -->
      <div class="saint-library">
        <div class="library-header">
          <h6>Library</h6>
          <input v-model="libSearch" class="form-control form-control-sm lib-search" placeholder="Search..." />
        </div>
        <div class="library-content">
          <div v-for="(section, si) in filteredSections" :key="si" class="lib-section">
            <div class="lib-section-title" :style="{paddingLeft: (section.level-1)*12+'px'}" @click="toggleSection(si)">
              <span class="toggle">{{ expanded[si] ? '▼' : '▶' }}</span>
              {{ section.name }}
              <span class="lib-count">{{ section.items.length }}</span>
            </div>
            <div v-if="expanded[si]" class="lib-items">
              <div v-for="(item, ii) in section.items" :key="ii" class="lib-item"
                @mouseenter="hoverItem = si+'-'+ii" @mouseleave="hoverItem = ''">
                <span class="type-badge" :class="'type-' + item.type">{{ item.type }}</span>
                <template v-if="editingItem === si+'-'+ii">
                  <input v-model="item.expr" class="form-control form-control-sm lib-edit-input"
                    @keyup.enter="finishEdit" @keyup.esc="cancelEdit" />
                </template>
                <template v-else>
                  <MathEquation v-if="item.latex" :data="'\\(' + item.latex + '\\)'" />
                  <span v-else class="text-muted small">{{ item.expr || item.name }}</span>
                </template>
                <span v-if="hoverItem === si+'-'+ii && editingItem !== si+'-'+ii" class="item-actions">
                  <button class="btn btn-link btn-sm py-0 px-1" @click.stop="startEdit(si, ii)">✎</button>
                  <button class="btn btn-link btn-sm py-0 px-1 text-danger" @click.stop="deleteItem(si, ii)">✕</button>
                </span>
              </div>
              <button class="btn btn-outline-secondary btn-sm w-100 mt-1 lib-add-btn" @click="addItem(si)">+ Add</button>
            </div>
          </div>
        </div>
      </div>

      <!-- Right: Calculation workspace -->
      <div class="saint-main">
        <div class="input-bar">
          <select v-model="selectedFile" class="form-select form-select-sm problem-select" @change="loadFile">
            <option value="">-- Problem set --</option>
            <option v-for="f in problemFiles" :key="f" :value="f">{{ f }}</option>
          </select>
          <input v-model="exprInput" class="form-control expr-input" placeholder="INT x. x^2" @keyup.enter="parseExpr" />
          <button class="btn btn-primary btn-sm" @click="parseExpr">Parse</button>
        </div>

        <div v-if="problems.length" class="problem-list-bar">
          <span v-for="(p, i) in problems" :key="i" class="problem-chip" @click="loadProblem(p)">{{ p.name }}</span>
        </div>
        <div v-if="parseError" class="alert alert-danger py-1 small">{{ parseError }}</div>

        <!-- Target display -->
        <div v-if="targetLatex" class="target-bar">
          <span class="target-label">Expected:</span>
          <MathEquation :data="'\\(' + targetLatex + '\\)'" />
          <button v-if="steps.length" class="btn btn-outline-primary btn-sm ms-2" @click="verifyResult">Verify</button>
          <span v-if="verifyStatus" class="verify-result" :class="verifyStatus">{{ verifyStatus }}</span>
        </div>

        <!-- Calculation display -->
        <div class="calc-display" v-if="startLatex">
          <div class="calc-line calc-start">
            <MathEquation :data="'\\(' + startLatex + '\\)'" />
          </div>
          <div v-for="(step, i) in displaySteps" :key="i" class="calc-line">
            <span class="eq-sign">=</span>
            <MathEquation :data="'\\(' + step.latex_res + '\\)'" />
            <span class="rule-tag">{{ step.rule.str }}</span>
          </div>
        </div>

        <!-- Rule palette -->
        <div class="rule-palette" v-if="startLatex">
          <div class="rule-buttons">
            <button v-for="r in RULES" :key="r.name" class="btn btn-sm"
              :class="selectedRule === r.name ? 'btn-dark' : 'btn-outline-secondary'" @click="selectRule(r)">{{ r.label }}</button>
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
    </div>
  </div>
</template>

<script setup>
import { ref, computed, onMounted, reactive } from 'vue'
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

// Library state
const librarySections = ref([])
const libSearch = ref('')
const expanded = reactive({})
const hoverItem = ref('')
const editingItem = ref(null)
const libraryDirty = ref(false)

// Problem state
const problemFiles = ref([])
const selectedFile = ref('')
const problems = ref([])

// Calculation state
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
const applying = ref(false)
const applyError = ref('')
const verifyStatus = ref('')

const currentRuleParams = computed(() => {
  const r = RULES.find(r => r.name === selectedRule.value)
  return r ? r.params : []
})

const filteredSections = computed(() => {
  if (!libSearch.value.trim()) return librarySections.value
  const q = libSearch.value.toLowerCase()
  return librarySections.value.map(s => ({
    ...s, items: s.items.filter(item =>
      (item.expr || '').toLowerCase().includes(q) || (item.latex || '').toLowerCase().includes(q)
    )
  })).filter(s => s.items.length > 0)
})

onMounted(async () => {
  try {
    const [libRes, fileRes] = await Promise.all([
      api.post('/saint/library'), api.post('/saint/files')
    ])
    librarySections.value = libRes.data.sections
    librarySections.value.forEach((_, i) => { expanded[i] = false })
    problemFiles.value = fileRes.data.files.filter(f => f !== 'base')
  } catch (e) { console.error('Init failed:', e) }
})

// Library editing
function toggleSection(i) { expanded[i] = !expanded[i] }
function startEdit(si, ii) { editingItem.value = si + '-' + ii }
function finishEdit() { editingItem.value = null; libraryDirty.value = true; refreshLatex() }
function cancelEdit() { editingItem.value = null }
function deleteItem(si, ii) {
  librarySections.value[si].items.splice(ii, 1)
  libraryDirty.value = true
}
function addItem(si) {
  librarySections.value[si].items.push({
    type: 'axiom', expr: 'f(x) = x', latex: '', category: '', conds: [], attributes: [], rule: '', const_vars: []
  })
  libraryDirty.value = true
}
async function saveLibrary() {
  try {
    await api.post('/saint/library/save', { sections: librarySections.value })
    libraryDirty.value = false
    await refreshLatex()
  } catch (e) { console.error('Save failed:', e) }
}
async function refreshLatex() {
  for (const s of librarySections.value) {
    for (const item of s.items) {
      if (item.expr) {
        try {
          const res = await api.post('/saint/parse', { expr: item.expr })
          if (res.data.status === 'ok') item.latex = res.data.latex
        } catch {}
      }
    }
  }
}

// Problems
async function loadFile() {
  problems.value = []
  if (!selectedFile.value) return
  try {
    const res = await api.post('/saint/load', { filename: selectedFile.value })
    problems.value = res.data.problems
  } catch (e) { console.error('Load:', e) }
}

function loadProblem(p) {
  exprInput.value = p.goal
  targetExpr.value = p.target || ''
  targetLatex.value = ''
  verifyStatus.value = ''
  parseExpr()
  if (p.target) {
    api.post('/saint/parse', { expr: p.target }).then(res => {
      if (res.data.status === 'ok') targetLatex.value = res.data.latex
    })
  }
}

// Calculation
async function parseExpr() {
  parseError.value = ''
  if (!exprInput.value.trim()) return
  try {
    const res = await api.post('/saint/parse', { expr: exprInput.value })
    if (res.data.status === 'ok') {
      startLatex.value = res.data.latex
      startExpr.value = res.data.text
      steps.value = []
      displaySteps.value = []
      selectedRule.value = ''
      verifyStatus.value = ''
    } else { parseError.value = res.data.msg }
  } catch (e) { parseError.value = e.message }
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
    const res = await api.post('/saint/apply', {
      start: startExpr.value, steps: steps.value, rule: selectedRule.value, params
    })
    if (res.data.status === 'ok') {
      displaySteps.value = res.data.calculation.steps
      steps.value.push({ rule: selectedRule.value, params })
    } else { applyError.value = res.data.msg }
  } catch (e) { applyError.value = e.message } finally { applying.value = false }
}

async function verifyResult() {
  if (!steps.value.length || !targetExpr.value) return
  const currentExpr = displaySteps.value[displaySteps.value.length - 1].res
  try {
    const res = await api.post('/saint/verify', { expr1: currentExpr, expr2: targetExpr.value })
    if (res.data.status === 'ok') {
      verifyStatus.value = res.data.match ? '✓ Match' : '✗ No match'
    }
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
.saint-library { width: 320px; border-right: 1px solid #dee2e6; display: flex; flex-direction: column; background: #f8f9fa; }
.library-header { padding: 8px 10px; border-bottom: 1px solid #dee2e6; }
.library-header h6 { font-size: 0.85rem; text-transform: uppercase; color: #6c757d; margin: 0 0 5px; }
.lib-search { font-size: 0.85rem; }
.library-content { flex: 1; overflow-y: auto; padding: 4px 0; }
.lib-section { margin-bottom: 2px; }
.lib-section-title { padding: 4px 10px; cursor: pointer; font-size: 0.85rem; font-weight: 600; color: #343a40; display: flex; align-items: center; gap: 4px; }
.lib-section-title:hover { background: #e9ecef; }
.toggle { font-size: 0.7rem; width: 10px; }
.lib-count { margin-left: auto; font-size: 0.75rem; color: #999; }
.lib-items { padding: 2px 0; }
.lib-item { padding: 3px 10px 3px 28px; font-size: 0.85rem; display: flex; align-items: baseline; gap: 6px; border-bottom: 1px solid #f0f0f0; position: relative; }
.lib-item:hover { background: #f0f7ff; }
.lib-edit-input { flex: 1; font-family: monospace; font-size: 0.8rem; }
.item-actions { margin-left: auto; white-space: nowrap; }
.type-badge { font-size: 0.65rem; padding: 0 4px; border-radius: 2px; text-transform: uppercase; white-space: nowrap; min-width: 28px; text-align: center; }
.type-axiom { background: #fff3cd; color: #856404; }
.type-theorem { background: #d4edda; color: #155724; }
.type-definition { background: #cce5ff; color: #004085; }
.type-table { background: #e2e3e5; color: #383d41; }
.lib-add-btn { font-size: 0.75rem; }
.saint-main { flex: 1; overflow-y: auto; padding: 16px; }
.input-bar { display: flex; gap: 8px; margin-bottom: 8px; }
.problem-select { width: auto; font-size: 0.85rem; }
.expr-input { flex: 1; font-family: monospace; }
.problem-list-bar { display: flex; flex-wrap: wrap; gap: 4px; margin-bottom: 8px; }
.problem-chip { font-size: 0.8rem; padding: 2px 8px; background: #e9ecef; border-radius: 10px; cursor: pointer; }
.problem-chip:hover { background: #dee2e6; }
.target-bar { display: flex; align-items: baseline; gap: 6px; padding: 8px 12px; background: #fffde7; border: 1px solid #fff9c4; border-radius: 6px; margin-bottom: 8px; font-size: 0.9rem; }
.target-label { font-size: 0.8rem; color: #827717; font-weight: 600; }
.verify-result { font-size: 0.85rem; font-weight: 600; }
.verify-result.✓\ Match { color: #2e7d32; }
.verify-result.✗\ No\ match { color: #c62828; }
.calc-display { background: white; border: 1px solid #dee2e6; border-radius: 8px; padding: 14px; margin-bottom: 12px; min-height: 50px; }
.calc-line { display: flex; align-items: baseline; gap: 8px; padding: 3px 0; }
.calc-start { font-size: 1.1em; border-bottom: 1px solid #f0f0f0; padding-bottom: 6px; margin-bottom: 4px; }
.eq-sign { color: #6c757d; font-weight: bold; min-width: 16px; }
.rule-tag { font-size: 0.75rem; color: #0d6efd; background: #e7f1ff; padding: 1px 6px; border-radius: 3px; margin-left: 8px; }
.rule-palette { background: #f8f9fa; border: 1px solid #dee2e6; border-radius: 8px; padding: 10px; }
.rule-buttons { display: flex; flex-wrap: wrap; gap: 5px; margin-bottom: 8px; }
.rule-params { display: flex; flex-wrap: wrap; gap: 10px; margin-bottom: 6px; }
.param-row { display: flex; align-items: center; gap: 4px; }
.param-label { font-size: 0.85rem; color: #495057; white-space: nowrap; }
.param-input { width: 100px; font-family: monospace; }
.ms-auto { margin-left: auto; }
</style>

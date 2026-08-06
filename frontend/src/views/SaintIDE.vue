<template>
  <div class="saint-container">
    <nav class="navbar navbar-dark bg-dark">
      <span class="navbar-brand">SAINT</span>
      <span class="text-light small">Interactive Integral CAS</span>
    </nav>

    <div class="saint-body">
      <!-- Left: file browser -->
      <div class="saint-sidebar">
        <div class="sidebar-section">
          <h6>Files</h6>
          <ul class="file-list">
            <li v-for="f in files" :key="f" @click="loadFile(f)" :class="{active: currentFile === f}">
              {{ f }}
            </li>
          </ul>
        </div>
        <div v-if="problems.length" class="sidebar-section">
          <h6>Problems</h6>
          <ul class="file-list">
            <li v-for="(p, i) in problems" :key="i" @click="loadProblem(p)">
              {{ p.name }}
            </li>
          </ul>
        </div>
      </div>

      <!-- Center: calculation -->
      <div class="saint-main">
        <!-- Expression input -->
        <div class="input-bar">
          <input v-model="exprInput" class="form-control expr-input"
            placeholder="INT x. x^2" @keyup.enter="parseExpr" />
          <button class="btn btn-primary btn-sm" @click="parseExpr">Parse</button>
          <button class="btn btn-success btn-sm" @click="startCalculation">Start</button>
        </div>
        <div v-if="parseError" class="alert alert-danger py-1 small">{{ parseError }}</div>

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
            <button v-for="r in RULES" :key="r.name"
              class="btn btn-sm"
              :class="selectedRule === r.name ? 'btn-dark' : 'btn-outline-secondary'"
              @click="selectRule(r)">
              {{ r.label }}
            </button>
          </div>

          <div v-if="selectedRule && currentRuleParams.length" class="rule-params">
            <div v-for="p in currentRuleParams" :key="p.key" class="param-row">
              <label class="param-label">{{ p.label }}</label>
              <input v-model="paramValues[p.key]" class="form-control form-control-sm param-input"
                :placeholder="p.placeholder" />
            </div>
          </div>

          <div class="mt-2">
            <button v-if="selectedRule" class="btn btn-success btn-sm" @click="applyRule" :disabled="applying">
              {{ applying ? '...' : 'Apply' }}
            </button>
            <button class="btn btn-outline-danger btn-sm ms-2" @click="undoStep" :disabled="!steps.length">
              Undo
            </button>
            <button class="btn btn-outline-secondary btn-sm ms-2" @click="resetCalculation" :disabled="!steps.length">
              Reset
            </button>
          </div>
        </div>

        <div v-if="applyError" class="alert alert-danger mt-2 py-1 small">{{ applyError }}</div>
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
  { name: 'definite_integral_identity', label: 'Def Integral ID', params: [] },
  { name: 'indefinite_integral_identity', label: 'Indef Integral ID', params: [] },
  { name: 'integrate_by_equation', label: 'Solve Eq', params: [
    { key: 'lhs', label: 'Original:', placeholder: '(auto)' },
  ]},
  { name: 'rewrite_trig', label: 'Rewrite Trig', params: [
    { key: 'rule', label: 'Rule:', placeholder: 'TR0' },
  ]},
  { name: 'expand_polynomial', label: 'Expand', params: [] },
  { name: 'unfold_power', label: 'Unfold Power', params: [] },
  { name: 'elim_abs', label: 'Elim Abs', params: [] },
  { name: 'elim_inf_interval', label: 'Elim Inf', params: [] },
  { name: 'split_region', label: 'Split Region', params: [
    { key: 'c', label: 'c =', placeholder: '1' },
  ]},
]

const files = ref([])
const problems = ref([])
const currentFile = ref('')

const exprInput = ref('')
const parseError = ref('')
const startLatex = ref('')
const startExpr = ref('')

// steps: [{rule: 'simplify', params: {}}]  -- for replay
const steps = ref([])
// displaySteps: from backend export, with latex
const displaySteps = ref([])

const selectedRule = ref('')
const paramValues = ref({})
const applying = ref(false)
const applyError = ref('')

const currentRuleParams = computed(() => {
  const r = RULES.find(r => r.name === selectedRule.value)
  return r ? r.params : []
})

onMounted(async () => {
  try {
    const res = await api.post('/saint/files')
    files.value = res.data.files
  } catch (e) {
    console.error('Failed to load files:', e)
  }
})

async function loadFile(name) {
  currentFile.value = name
  problems.value = []
  try {
    const res = await api.post('/saint/load', { filename: name })
    problems.value = res.data.problems
  } catch (e) {
    console.error('Failed to load file:', e)
  }
}

function loadProblem(p) {
  exprInput.value = p.goal
  parseExpr()
}

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
    } else {
      parseError.value = res.data.msg
    }
  } catch (e) {
    parseError.value = e.message
  }
}

function startCalculation() {
  parseExpr()
}

function selectRule(r) {
  selectedRule.value = r.name
  paramValues.value = {}
  if (r.name === 'integrate_by_equation' && startExpr.value) {
    paramValues.value.lhs = startExpr.value
  }
  applyError.value = ''
}

async function applyRule() {
  applyError.value = ''
  if (!selectedRule.value || !startExpr.value) return

  const params = {}
  for (const p of currentRuleParams.value) {
    if (paramValues.value[p.key]) {
      params[p.key] = paramValues.value[p.key]
    }
  }

  applying.value = true
  try {
    const res = await api.post('/saint/apply', {
      start: startExpr.value,
      steps: steps.value,
      rule: selectedRule.value,
      params: params,
    })
    if (res.data.status === 'ok') {
      const calc = res.data.calculation
      displaySteps.value = calc.steps
      // Record the step for replay
      steps.value.push({ rule: selectedRule.value, params: params })
    } else {
      applyError.value = res.data.msg
    }
  } catch (e) {
    applyError.value = e.message
  } finally {
    applying.value = false
  }
}

function undoStep() {
  if (steps.value.length === 0) return
  steps.value.pop()
  displaySteps.value.pop()
  applyError.value = ''
}

function resetCalculation() {
  steps.value = []
  displaySteps.value = []
  selectedRule.value = ''
  applyError.value = ''
}
</script>

<style scoped>
.saint-container {
  display: flex;
  flex-direction: column;
  height: 100vh;
}
.saint-body {
  display: flex;
  flex: 1;
  overflow: hidden;
}
.saint-sidebar {
  width: 240px;
  border-right: 1px solid #dee2e6;
  overflow-y: auto;
  padding: 10px;
  background: #f8f9fa;
}
.sidebar-section { margin-bottom: 15px; }
.sidebar-section h6 {
  font-size: 0.85rem;
  color: #6c757d;
  text-transform: uppercase;
  margin-bottom: 5px;
}
.file-list { list-style: none; padding: 0; margin: 0; }
.file-list li {
  padding: 4px 8px;
  cursor: pointer;
  border-radius: 4px;
  font-size: 0.9rem;
}
.file-list li:hover { background: #e9ecef; }
.file-list li.active { background: #0d6efd; color: white; }
.saint-main {
  flex: 1;
  overflow-y: auto;
  padding: 20px;
}
.input-bar {
  display: flex;
  gap: 8px;
  margin-bottom: 10px;
}
.expr-input { flex: 1; font-family: monospace; }
.calc-display {
  background: white;
  border: 1px solid #dee2e6;
  border-radius: 8px;
  padding: 16px;
  margin-bottom: 15px;
  min-height: 60px;
}
.calc-line {
  display: flex;
  align-items: baseline;
  gap: 8px;
  padding: 4px 0;
}
.calc-start {
  font-size: 1.1em;
  border-bottom: 1px solid #f0f0f0;
  padding-bottom: 8px;
  margin-bottom: 4px;
}
.eq-sign {
  color: #6c757d;
  font-weight: bold;
  min-width: 20px;
}
.rule-tag {
  font-size: 0.8rem;
  color: #0d6efd;
  background: #e7f1ff;
  padding: 1px 6px;
  border-radius: 3px;
  margin-left: 8px;
}
.rule-palette {
  background: #f8f9fa;
  border: 1px solid #dee2e6;
  border-radius: 8px;
  padding: 12px;
}
.rule-buttons {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  margin-bottom: 10px;
}
.rule-params {
  display: flex;
  flex-wrap: wrap;
  gap: 12px;
  margin-bottom: 8px;
}
.param-row { display: flex; align-items: center; gap: 4px; }
.param-label { font-size: 0.85rem; color: #495057; white-space: nowrap; }
.param-input { width: 120px; font-family: monospace; }
</style>

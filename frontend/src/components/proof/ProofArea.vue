<template>
  <div class="proof-area">
    <!-- Header: theorem name + prop + close -->
    <div class="proof-header">
      <span class="proof-thm-name">{{ thm_name }}</span>
      <span class="proof-thm-prop">{{ formatProp }}</span>
      <span class="proof-gaps">{{ num_gaps }} gaps</span>
      <button class="btn btn-sm btn-outline-secondary" @click="show_trust = !show_trust"
              title="Computation oracles admitted this session">Oracles {{ trust_summary }}</button>
      <button class="btn btn-sm btn-outline-secondary" @click="emit('close-prove')" title="Close">✕</button>
    </div>

    <!-- Trust panel: admit/reject computation oracles (audit §7.1) -->
    <div v-if="show_trust" class="trust-panel">
      <div class="trust-row">
        <span class="trust-title">Admitted computation oracles</span>
        <span class="trust-hint">{{ trust_is_default ? 'backend default' : 'session override' }}</span>
        <button class="btn btn-sm btn-outline-secondary trust-reset" @click="resetTrust"
                :disabled="trust_is_default">Default</button>
        <button class="btn btn-sm btn-outline-primary trust-check" @click="check_trust">Full verify</button>
      </div>
      <div class="trust-items">
        <label v-for="name in known_oracles" :key="name" class="trust-item"
               :class="{admitted: isAdmitted(name)}">
          <input type="checkbox" :checked="isAdmitted(name)" @change="toggleOracle(name)"/>
          <span class="trust-name">{{ name }}</span>
        </label>
      </div>
      <div v-if="trust_report" class="trust-report">
        oracles used: {{ trust_report.oracles.length ? trust_report.oracles.join(', ') : 'none' }}
        &nbsp;|&nbsp; axioms: {{ trust_report.axioms.length ? trust_report.axioms.length : 'none' }}
        &nbsp;|&nbsp; gaps: {{ trust_report.num_gaps }}
      </div>
      <div v-if="trust_error" class="trust-error">{{ trust_error }}</div>
    </div>

    <!-- Proof lines (scrollable) -->
    <div class="proof-lines-scroll">
      <div v-if="proof !== undefined" class="proof-lines">
        <div v-for="(line, idx) in proof" :key="line.sid || idx"
             class="proof-line-row" :class="{'line-goal': goal === idx, 'line-fact': facts.includes(idx)}">
          <ProofLine :line="line" :is_goal="goal === idx"
                     :is_fact="facts.includes(idx)" :can_select="can_select(idx)"
                     @select-fact="mark_fact(idx)"
                     @select-goal="mark_goal(idx)"/>
        </div>
      </div>
      <div v-else class="proof-loading">Loading proof...</div>
    </div>

    <!-- Selection bar -->
    <div class="selection-bar">
      <template v-if="goal !== -1 && proof && proof[goal]">
        <span class="sel-goal">Goal: {{ proof[goal].sid }} ({{ formatProofLine(proof[goal]) }})</span>
        <button class="btn btn-sm btn-outline-secondary sel-clear" @click="goal = -1; match_thm()">✕</button>
      </template>
      <span v-else class="sel-goal">Goal: (none)</span>
      <template v-if="facts.length > 0 && proof">
        <span class="sel-facts">Facts: <span v-for="fi in facts" :key="fi" class="sel-fact" @click="mark_fact(fi)">{{ proof[fi]?.sid }}✕ </span></span>
      </template>
    </div>

    <!-- Tabs -->
    <div class="tab-bar">
      <button class="tab-btn" :class="{active: active_tab === 'suggest'}" @click="active_tab = 'suggest'">Suggest</button>
      <button class="tab-btn" :class="{active: active_tab === 'manual'}" @click="active_tab = 'manual'">Manual</button>
      <button class="tab-btn" :class="{active: active_tab === 'auto'}" @click="active_tab = 'auto'">Auto</button>
    </div>

    <!-- Tab content -->
    <div class="tab-content">
      <!-- Suggest tab -->
      <div v-if="active_tab === 'suggest'" class="suggest-tab">
        <div v-if="derive_suggestions.length > 0" class="suggest-group">
          <div class="suggest-group-title">→ Derive</div>
          <div v-for="(res, i) in derive_suggestions" :key="'d'+i" class="suggest-item" @click="apply_suggestion(res)">
            <span class="suggest-dir">→</span>
            <span class="suggest-method">{{ res.theorem || res.method_name }}</span>
            <span v-if="res._thm" class="suggest-thm">{{ res._thm }}</span>
            <span v-if="res._fact" class="suggest-result">⇒ {{ res._fact.join(' ') }}</span>
            <span v-if="!res._fact && res._needs_params" class="suggest-needs">needs: {{ res._needs_params.map(p => p.replace('param_', '')).join(', ') }}</span>
            <span v-if="!res._fact && !res._needs_params && !res._goal" class="suggest-nopreview">(no preview)</span>
          </div>
        </div>
        <div v-if="rewrite_suggestions.length > 0" class="suggest-group">
          <div class="suggest-group-title">→ Rewrite</div>
          <div v-for="(res, i) in rewrite_suggestions" :key="'r'+i" class="suggest-item" @click="apply_suggestion(res)">
            <span class="suggest-dir">~</span>
            <span class="suggest-method">{{ res.theorem || res.method_name }}</span>
            <span v-if="res._thm" class="suggest-thm">{{ res._thm }}</span>
            <span v-if="res._fact" class="suggest-result">⇒ {{ res._fact.join(' ') }}</span>
          </div>
        </div>
        <div v-if="backward_suggestions.length > 0" class="suggest-group">
          <div class="suggest-group-title">← Backward</div>
          <div v-for="(res, i) in backward_suggestions" :key="'b'+i" class="suggest-item" @click="apply_suggestion(res)">
            <span class="suggest-dir">←</span>
            <span class="suggest-method">{{ res.theorem || res.method_name }}</span>
            <span v-if="res._thm" class="suggest-thm">{{ res._thm }}</span>
            <span v-if="res._goal" class="suggest-result">⇒ {{ res._goal.length === 0 ? 'closes' : res._goal.length + ' subgoals' }}</span>
            <span v-if="!res._fact && !res._goal" class="suggest-nopreview">(no preview)</span>
          </div>
        </div>
        <div v-if="fuzzy_suggestions.length > 0" class="suggest-group">
          <details>
            <summary class="suggest-group-title">? Fuzzy ({{ fuzzy_suggestions.length }})</summary>
            <div v-for="(grp, gi) in fuzzy_suggestions" :key="'f'+gi" class="fuzzy-item">
              <div class="fuzzy-head">
                <span class="suggest-dir">?</span>
                <span class="suggest-method">{{ grp.theorem }}</span>
                <span v-if="grp._thm" class="suggest-thm">{{ grp._thm }}</span>
              </div>
              <div v-for="(m, mi) in grp.matches" :key="'m'+mi" class="fuzzy-match" @click="apply_suggestion(m)">
                <span class="fuzzy-facts">[{{ (m._facts || []).join(', ') }}]</span>
                <span v-if="m._goal" class="suggest-result">⇒ {{ m._goal.length === 0 ? 'closes' : m._goal.length + ' subgoals' }}</span>
                <span v-else-if="m._fact" class="suggest-result">⇒ {{ m._fact.join(' ') }}</span>
              </div>
            </div>
          </details>
        </div>
        <div v-if="derive_suggestions.length === 0 && rewrite_suggestions.length === 0 && backward_suggestions.length === 0 && fuzzy_suggestions.length === 0" class="suggest-empty">
          Select a goal or fact to see suggestions
        </div>
      </div>

      <!-- Manual tab -->
      <div v-if="active_tab === 'manual'" class="manual-tab">
        <div class="manual-row">
          <label>Method:</label>
          <select v-model="manual_method" class="method-select">
            <option value="">-- select --</option>
            <optgroup v-if="manual_groups.forward.length" label="⟶ Forward (needs facts, no goal)">
              <option v-for="n in manual_groups.forward" :key="'mf'+n" :value="n">{{ n }}</option>
            </optgroup>
            <optgroup v-if="manual_groups.backward.length" label="← Backward (needs goal)">
              <option v-for="n in manual_groups.backward" :key="'mb'+n" :value="n">{{ n }}</option>
            </optgroup>
            <optgroup v-if="manual_groups.direct.length" label="Structural">
              <option v-for="n in manual_groups.direct" :key="'md'+n" :value="n">{{ n }}</option>
            </optgroup>
          </select>
        </div>
        <div v-if="manual_method && method_params.length > 0" class="manual-params">
          <div v-for="p in method_params" :key="p" class="param-row">
            <label class="param-label">{{ p }}:</label>
            <input v-model="manual_params[p]" class="param-input" :placeholder="param_hint(p)"
                   @input="p === 'theorem' ? search_theorems(manual_params[p]) : null"/>
            <div v-if="p === 'theorem' && theorem_results.length > 0" class="theorem-dropdown">
              <div v-for="tr in theorem_results" :key="tr.name" class="theorem-item"
                   @click="manual_params[p] = tr.name; theorem_results = []">
                <span class="th-name">{{ tr.name }}</span>
                <span class="th-prop">{{ tr.prop }}</span>
              </div>
            </div>
          </div>
        </div>
        <button v-if="manual_method" class="btn btn-sm btn-primary" @click="apply_manual_method"
                :disabled="goal === -1 && !FORWARD_METHODS.has(manual_method) && manual_method !== 'var'">
          Apply
        </button>
      </div>

      <!-- Auto tab -->
      <div v-if="active_tab === 'auto'" class="auto-tab">
        <template v-for="[name, desc] in auto_methods" :key="'auto'+name">
          <button class="btn btn-sm btn-outline-primary auto-btn" @click="apply_auto(name)"
                  :disabled="goal === -1">{{ name }}</button>
          <span class="auto-desc">{{ desc }}</span>
        </template>
        <div v-if="auto_methods.length === 0" class="auto-empty">No automatic methods available.</div>
      </div>
    </div>

    <!-- Footer -->
    <div class="proof-footer">
      <span class="proof-status">{{ status_text }}</span>
      <button class="btn btn-sm btn-success" @click="emit_save">Save Proof</button>
    </div>
  </div>
</template>

<script setup>
import { ref, computed, onMounted } from 'vue'
import api from '../../api'
import ProofLine from './ProofLine.vue'
import {
  trustOverride, knownOracles, effectiveTrust,
  setKnownOracles, setEffectiveTrust,
  currentTrust, isAdmitted, toggleOracle, resetTrust, withTrust,
} from '../../api/trust'

const props = defineProps({
  theory_name: String,
  thm_name: String,
  vars: { type: Object, default: () => ({}) },
  prop: { type: [Array, Object, String], default: '' },
  old_steps: { type: Array, default: () => [] },
  editor: Object
})

const emit = defineEmits(['set-message', 'query', 'set-context', 'set-status', 'set-proof', 'save-steps', 'close-prove'])

const method_sig = ref({})
const method_list_params = ref({})
const method_direction = ref({})
const index = ref(0)
const history = ref([])
const steps = ref([])
const goal = ref(-1)
const facts = ref([])
const proof = ref(undefined)
const open_goals = ref([])
const num_gaps = ref(0)
const search_res = ref([])
const fuzzy_res = ref([])
const active_tab = ref('suggest')
const manual_method = ref('')
const manual_params = ref({})
const theorem_results = ref([])

// Trust panel (audit §7.1).  `known_oracles`/`effectiveTrust` come from
// the backend proof state; the session override lives in api/trust.js so
// it survives switching theorems within the session.
const show_trust = ref(false)
const trust_report = ref(null)
const trust_error = ref('')

const trust_names = computed(() => currentTrust() ?? knownOracles.value)
const trust_is_default = computed(() => trustOverride.value === null)
const trust_summary = computed(
  () => trust_names.value.length + '/' + knownOracles.value.length)

const check_trust = async () => {
  trust_error.value = ''
  trust_report.value = null
  try {
    const res = await api.post('/v2/trust-report', withTrust({
      theory_name: props.theory_name, thm_name: props.thm_name,
      vars: props.vars, prop: props.prop,
      steps: steps.value, index: index.value,
    }))
    if (res.data.error) {
      trust_error.value = res.data.error.err_str || String(res.data.error)
    } else {
      trust_report.value = res.data
      setEffectiveTrust(res.data.trust)
    }
  } catch (e) {
    trust_error.value = 'trust report failed'
  }
}

// Fields that are comma-separated lists (rendered as +/- dynamic inputs)
const listFieldsFor = (mn) => new Set(method_list_params.value[mn] || [])

// Methods usable without a selected goal (fact mode). rewrite/inst are
// dual-mode: with no goal selected they run in fact mode (target='fact'
// is injected at apply time).
const FORWARD_METHODS = new Set(['forward', 'rewrite', 'inst'])
// Methods whose params are instantiations (sent with param_ prefix for Inst).
// All other methods expect plain keys (cut/cases/induct/var/...).
const INST_PARAM_METHODS = new Set(['rule', 'forward', 'apply_prev'])

// Dual-mode rewrite results carry a target marker from the backend
// (fact mode: target='fact'); goal mode has no marker.
const isFactRewrite = (r) => r.method_name === 'rewrite' && r.target === 'fact'
const isGoalRewrite = (r) => r.method_name === 'rewrite' && r.target !== 'fact'

const method_sig_map = {
  'rule': ['theorem'], 'resolve': ['theorem'], 'accept': ['theorem'],
  'apply_prev': [], 'forward': ['theorem'],
  'rewrite': ['theorem', 'sym'], 'unfold': ['theorem', 'sym'],
  'intro': [], 'elim': ['names'], 'inst': ['s'], 'trans': ['s'],
  'induct': ['theorem', 'var'], 'cases': ['case'], 'type_cases': ['case'], 'cut': ['cut_goal'],
  'var': ['name', 'type'], 'refl': [], 'eq_intro': [], 'assumption': [],
  'simp': [], 'norm': [],
}

const method_params = computed(() => {
  // Prefer the backend-provided signature (stable-ID pipeline); fall back
  // to the static map below for manual tab.
  const sig = method_sig.value[manual_method.value]
  if (sig) return sig
  return method_sig_map[manual_method.value] || []
})

// Fallback direction map, used only before the first proof state arrives
// (method_direction is empty).  Mirrors method/stable_state._method_directions.
const static_direction = (name) => {
  if (['cut', 'var', 'elim'].includes(name)) return ['direct']
  if (name === 'forward') return ['forward']
  if (['rewrite', 'inst'].includes(name)) return ['backward', 'forward']
  return ['backward']
}

// Manual method picker driven by the backend list: method_sig is already
// limit-filtered to what the current theory offers, so the picker can
// never present an unavailable method (it grows with domain loading --
// nat_norm/int_norm/real_norm/vcg appear only when their limit theorem
// is loaded).  Dual-mode methods show up in both forward and backward.
const manual_groups = computed(() => {
  const dirs = method_direction.value
  const have_backend = Object.keys(method_sig.value).length > 0
  const names = have_backend
    ? Object.keys(method_sig.value).sort()
    : Object.keys(method_sig_map).sort()
  const groups = { forward: [], backward: [], direct: [] }
  for (const n of names) {
    const d = have_backend ? (dirs[n] || ['direct']) : static_direction(n)
    if (d.includes('forward')) groups.forward.push(n)
    if (d.includes('backward')) groups.backward.push(n)
    if (d.includes('direct')) groups.direct.push(n)
  }
  return groups
})

// Auto tab: curated set, filtered to what the backend actually offers
// (vcg only exists once hoare/while_rule is loaded).
const AUTO_METHODS = [
  ['simp', 'hint_rewrite auto-rewrite (does not close)'],
  ['norm', 'domain / numeric normalization'],
  ['auto', 'close the goal (may use computation oracles)'],
  ['z3', 'SMT solver (oracle)'],
  ['vcg', 'Hoare logic VC generation'],
]
const auto_methods = computed(
  () => AUTO_METHODS.filter(([n]) => n in method_sig.value || n in method_sig_map))

const param_hint = (p) => ({
  'theorem': 'theorem name', 'sym': 'true/false', 'loc': 'position', 'case': 'expression',
  'var': 'variable', 's': 'term', 'names': 'names', 'name': 'name', 'type': 'HOL type',
  'goal': 'proposition', 'cut_goal': 'proposition', 'index': 'assumption index',
}[p] || p)

const derive_suggestions = computed(() => {
  if (goal.value !== -1) return []  // backward mode: no derive
  return search_res.value.filter(r => !r.fuzzy && !isFactRewrite(r))
})

const rewrite_suggestions = computed(() => {
  if (goal.value !== -1) {
    // Backward mode: only goal-rewrites go here
    return search_res.value.filter(r => !r.fuzzy && isGoalRewrite(r))
  }
  return search_res.value.filter(r => !r.fuzzy && isFactRewrite(r))
})

const backward_suggestions = computed(() => {
  if (goal.value === -1) return []  // forward mode: no backward
  return search_res.value.filter(r => !r.fuzzy && !isGoalRewrite(r))
})

// Fuzzy suggestions: group by (method, theorem), each group lists all
// successful (fact subset, permutation) matches with their results.
const fuzzy_suggestions = computed(() => {
  const groups = new Map()
  for (const r of fuzzy_res.value) {
    if (!r.fuzzy) continue
    const key = r.method_name + '::' + (r.theorem || '')
    if (!groups.has(key)) {
      groups.set(key, { method_name: r.method_name, theorem: r.theorem || r.method_name, _thm: r._thm, matches: [] })
    }
    groups.get(key).matches.push(r)
  }
  return Array.from(groups.values())
})

const formatProp = computed(() => {
  if (!props.prop) return ''
  if (typeof props.prop === 'string') return props.prop
  if (Array.isArray(props.prop)) return props.prop.map(item => {
    if (typeof item === 'string') return item
    if (item && item.text) return item.text
    return ''
  }).join('')
  return String(props.prop)
})

const formatDisplay = (d) => {
  if (!d) return ''
  if (typeof d === 'string') return d
  if (Array.isArray(d)) return d.map(formatDisplay).join('')
  if (d.text) return d.text
  return ''
}

const formatProofLine = (line) => {
  if (!line) return ''
  if (line.th_hl) return formatDisplay(line.th_hl)
  if (line.th) {
    if (typeof line.th === 'string') return line.th
    if (Array.isArray(line.th)) return line.th.map(item => {
      if (typeof item === 'string') return item
      if (item && item.text) return item.text
      return ''
    }).join('')
    return String(line.th)
  }
  return ''
}

const can_depend_on = (aIdStr, bIdStr) => {
  // True if line a can depend on line b in the proof tree (ItemID
  // semantics: same prefix, b strictly earlier at the last level).
  const A = (aIdStr || '').split('.').map(Number)
  const B = (bIdStr || '').split('.').map(Number)
  if (!A.length || !B.length) return true  // no id available: allow
  if (B.length > A.length) return false
  if (A.slice(0, B.length - 1).join('.') !== B.slice(0, B.length - 1).join('.')) return false
  return B[B.length - 1] < A[A.length - 1]
}

const can_select = (idx) => {
  if (!proof.value || idx < 0 || idx >= proof.value.length) return false
  const line = proof.value[idx]
  if (!line) return false
  // Same line cannot be both goal and fact
  if (goal.value === idx) return false
  if (goal.value !== -1) {
    // Goal mode: anchor is the goal; fact must be usable by it.
    return can_depend_on(proof.value[goal.value].id, line.id)
  }
  if (facts.value.length > 0) {
    // Forward mode: anchor is the first selected fact
    const anchor = proof.value[facts.value[0]]
    return can_depend_on(line.id, anchor.id)
  }
  return true
}

const mark_fact = (line_no) => {
  if (!proof.value) return
  const line = proof.value[line_no]
  if (!line) return
  
  let i = facts.value.indexOf(line_no)
  if (i !== -1) {
    // Deselect: always allowed
    facts.value.splice(i, 1)
  } else {
    // Select: if this line is the goal, switch to fact
    if (goal.value === line_no) {
      goal.value = -1
      facts.value = [line_no]  // becomes first fact, determines context
      match_thm()
      return
    }
    if (!can_select(line_no)) return
    facts.value.push(line_no)
  }
  match_thm()
}

const mark_goal = (line_no) => {
  if (!proof.value) return
  const line = proof.value[line_no]
  // Backend marks the open goals; use it rather than re-deriving from rule.
  if (!line || !line.is_goal) return
  
  if (goal.value === line_no) {
    // Deselect goal
    goal.value = -1
    facts.value = []
  } else {
    // Switch goal: clear facts (context changed)
    // Also remove this line from facts if it was a fact
    let fi = facts.value.indexOf(line_no)
    if (fi !== -1) facts.value.splice(fi, 1)
    goal.value = line_no
    facts.value = []
  }
  match_thm()
}

const current_state = () => {
  if (goal.value === -1 && facts.value.length === 0) return undefined
  const fact_arr = facts.value.map(i => proof.value[i].sid)
  const goal_val = goal.value !== -1 ? proof.value[goal.value].sid : null
  return withTrust({
    theory_name: props.theory_name,
    thm_name: props.thm_name,
    vars: props.vars,
    prop: props.prop,
    steps: steps.value,
    index: index.value,
    step: { goal: goal_val, facts: fact_arr },
  })
}

const match_thm = async () => {
  const input = current_state()
  if (input === undefined) {
    search_res.value = []
    fuzzy_res.value = []
    emit('set-context', { ctxt: {}, history: history.value, history_idx: -1, open_goals: open_goals.value })
    return
  }
  try {
    let endpoint, resultsKey
    if (goal.value === -1 && facts.value.length > 0) {
      // Forward search: no goal, has facts
      endpoint = '/v2/forward-search'
      resultsKey = 'results'
    } else if (goal.value !== -1) {
      // Backward search: has goal
      endpoint = '/v2/backward-search'
      resultsKey = 'results'
    } else {
      search_res.value = []
      fuzzy_res.value = []
      return
    }
    const response = await api.post(endpoint, {
      ...input,
      goal: input.step.goal,
      facts: input.step.facts,
    })
    search_res.value = response.data[resultsKey] || []
    fuzzy_res.value = response.data.fuzzy || []
    emit('set-context', {
      ctxt: response.data.ctxt || {},
      history: history.value,
      history_idx: index.value,
      open_goals: open_goals.value
    })
  } catch (err) {
    search_res.value = []
    fuzzy_res.value = []
  }
}

const apply_suggestion = (res) => {
  // Pass method-specific args; fact_ids (the successful permutation order
  // found during search) is used instead of the live click order, so that
  // applying a suggestion always matches.
  const args = {}
  if (res.theorem) args.theorem = res.theorem
  if (res.sym) args.sym = res.sym
  if (res.var) args.var = res.var
  if (res.facts) args.facts = res.facts
  // Dual-mode markers: required for unambiguous replay of rewrite/inst
  // (a fact rewrite at a gap position is otherwise inferred as goal mode).
  if (res.target) args.target = res.target
  if (res.source && res.method_name === 'rewrite') args.source = res.source
  // Context shown in the parameter query dialog
  const desc = { thm: res._thm || '', result: '' }
  if (res._goal) desc.result = '⇒ ' + (res._goal.length === 0 ? 'closes' : res._goal.length + ' subgoals')
  else if (res._fact) desc.result = '⇒ ' + (Array.isArray(res._fact) ? res._fact.join(' ') : res._fact)
  if (res._needs_params) desc.needs = res._needs_params.map(p => p.replace('param_', ''))
  if (desc.thm || desc.result || desc.needs) args._desc = desc
  apply_method(res.method_name, args)
}

const apply_method = async (method_name, args) => {
  const sigs = method_sig.value[method_name] || []
  const input = current_state()
  if (!input) {
    emit('set-message', { type: 'error', data: 'No goal or fact selected: click a line first' })
    return
  }
  input.step.method_name = method_name
  if (args !== undefined) {
    // Only use search result's goal_id if user explicitly selected a goal
    // Otherwise keep null so backend inserts after last fact
    if (goal.value !== -1) {
      input.step.goal = args.goal || input.step.goal
    }
    if (args.facts !== undefined) input.step.facts = args.facts
  } else { args = {} }
  const sigList = []
  for (let i = 0; i < sigs.length; i++) {
    const sig = sigs[i]
    if (sig in args) { input.step[sig] = args[sig] }
    else { sigList.push(sig) }
  }
  if (sigList.length > 0) {
    const query_result = await new Promise((resolve, reject) => {
      emit('query', { title: 'Parameters for ' + method_name, fields: sigList, list_fields: [...listFieldsFor(method_name)], resolve, reject })
    })
    if (query_result !== undefined) {
      for (const k in query_result) {
        if (k === 'names') { input.step[k] = query_result[k] }
        else if (INST_PARAM_METHODS.has(method_name)) { input.step['param_' + k] = query_result[k] }
        else { input.step[k] = query_result[k] }
      }
      await apply_method_ajax(input, args._desc)
    }
  } else { await apply_method_ajax(input, args._desc) }
}

const apply_manual_method = async () => {
  if (!manual_method.value) return
  const method_name = manual_method.value
  const params = { ...manual_params.value }
  const args = { ...params }
  // Dual-mode methods without a selected goal run in fact mode.
  if ((method_name === 'rewrite' || method_name === 'inst') && goal.value === -1) {
    args.target = 'fact'
  }
  await apply_method(method_name, args)
  manual_params.value = {}
  theorem_results.value = []
}

const apply_auto = (method_name) => {
  apply_method(method_name, {})
}

const apply_method_ajax = async (input, desc = null) => {
  emit('set-status', { status: 'Running' })
  try {
    const result = await api.post('/v2/apply-method', input)
    if ('query' in result.data) {
      let qTitle = 'Parameters for ' + input.step.method_name
      if (input.step.theorem) qTitle += ': ' + input.step.theorem
      const query_result = await new Promise((resolve, reject) => {
        emit('query', { title: qTitle, desc: desc, fields: result.data.query.map(s => s === 'names' ? s : s.slice(6)), list_fields: [...listFieldsFor(input.step.method_name)], hints: result.data.query_hints || {}, resolve, reject })
      })
      if (query_result !== undefined) {
        for (const k in query_result) {
          if (k === 'names') { input.step[k] = query_result[k] }
          else if (INST_PARAM_METHODS.has(input.step.method_name)) { input.step['param_' + k] = query_result[k] }
          else { input.step[k] = query_result[k] }
        }
        await apply_method_ajax(input, desc)
      }
    } else if ('error' in result.data) {
      emit('set-message', { type: 'error', data: result.data.error.err_type + ': ' + result.data.error.err_str })
    } else {
      // Record new_ids and annotated props from backend response
      if (result.data.new_items) {
        const nis = result.data.new_items
        input.step.new_ids = nis.map(ni => ni.sid)
        input.step.new_items = nis  // [{sid, prop}] kept for #[N] annotation export
      }
      if (input.step.facts && input.step.facts.length === 0) { delete input.step.facts }
      // Truncate + push (branch and discard)
      steps.value = steps.value.slice(0, index.value)
      steps.value.push(input.step)
      await gotoStep(index.value + 1, false, true)
    }
  } catch (err) {
    emit('set-message', { type: 'error', data: 'Error applying method' })
  }
}

const search_theorems = async (pattern) => {
  if (!pattern || pattern.length < 2) { theorem_results.value = []; return }
  try {
    const res = await api.post('/theorem-search', {
      theory_name: props.theory_name, thm_name: props.thm_name, pattern: pattern
    })
    theorem_results.value = res.data.results || []
  } catch (e) { theorem_results.value = [] }
}

const gotoStep = async (new_index, set_selected, update_history = false) => {
  index.value = new_index
  const data = withTrust({
    theory_name: props.theory_name, thm_name: props.thm_name,
    vars: props.vars, prop: props.prop, steps: steps.value, index: index.value
  })
  try {
    const response = await api.post('/v2/init-saved-proof', data)
    if (response.data.error) {
      emit('set-message', { type: 'error', data: response.data.error })
      return
    }
    const state = response.data.state
    const new_history = response.data.history || []
    if (update_history) { history.value = new_history }
    num_gaps.value = state.num_gaps
    method_sig.value = state.method_sig || {}
    method_list_params.value = state.method_list_params || {}
    method_direction.value = state.method_direction || {}
    setKnownOracles(state.known_oracles)
    setEffectiveTrust(state.trust)
    proof.value = state.proof
    // Open goals come from the backend ({sid, prop}); do not rebuild them
    // from the proof lines -- the backend's list is the authoritative one.
    open_goals.value = state.open_goals || []
    emit('set-context', {
      ctxt: {},
      history: history.value,
      history_idx: index.value,
      open_goals: open_goals.value
    })
    facts.value = []
    if (index.value >= history.value.length) {
      goal.value = compute_new_goal(0)
    } else {
      goal.value = get_line_no_from_sid(history.value[index.value].goal)
      const hist_facts = history.value[index.value].facts
      if (hist_facts !== undefined) {
        for (let i = 0; i < hist_facts.length; i++) {
          const fact_no = get_line_no_from_sid(hist_facts[i])
          if (can_select(fact_no)) { facts.value.push(fact_no) }
        }
      }
    }
    match_thm()
  } catch (err) { emit('set-message', { type: 'error', data: 'Error loading proof state' }) }
}

const compute_new_goal = (start) => {
  if (!proof.value) return -1
  for (let i = start; i < proof.value.length; i++) {
    if (proof.value[i].is_goal) return i
  }
  return -1
}

const get_line_no_from_sid = (id) => {
  if (!proof.value) return -1
  for (let i = 0; i < proof.value.length; i++) {
    if (proof.value[i].sid === id) return i
  }
  return -1
}

const step_backward = () => { if (index.value > 0) gotoStep(index.value - 1) }
const step_forward = () => { if (index.value < history.value.length) gotoStep(index.value + 1) }

const status_text = ref('')

const emit_save = () => {
  emit('save-steps', JSON.parse(JSON.stringify(steps.value)))
}

const init_proof = async () => {
  if (!props.old_steps || props.old_steps.length === 0) {
    steps.value = []; history.value = []; await gotoStep(0, false, true)
  } else {
    steps.value = JSON.parse(JSON.stringify(props.old_steps))
    await gotoStep(steps.value.length, false, true)
  }
}

onMounted(() => { if (props.prop) init_proof() })

defineExpose({ apply_method, gotoStep, step_backward, step_forward, proof, num_gaps, steps, init_proof })
</script>

<style scoped>
.proof-area { display: flex; flex-direction: column; height: 100%; overflow: hidden; }
.proof-header { display: flex; align-items: center; gap: 8px; padding: 6px 10px; background: #f0f4ff; border-bottom: 1px solid #d0d7de; flex-shrink: 0; }
.proof-thm-name { font-weight: 700; font-size: 13px; color: #333; flex-shrink: 0; }
.proof-thm-prop { font-family: Consolas, monospace; font-size: 12px; color: #555; flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.proof-gaps { font-size: 11px; color: #c0392b; flex-shrink: 0; }
.trust-panel { flex-shrink: 0; border-bottom: 1px solid #d0d7de; background: #fffdf5; padding: 6px 10px; font-size: 12px; }
.trust-row { display: flex; align-items: center; gap: 8px; }
.trust-title { font-weight: 700; color: #8a6d1a; }
.trust-hint { color: #999; font-size: 11px; }
.trust-reset, .trust-check { margin-left: auto; padding: 1px 8px; font-size: 11px; }
.trust-check { margin-left: 4px; }
.trust-items { display: flex; flex-wrap: wrap; gap: 2px 12px; margin: 6px 0 2px; }
.trust-item { display: flex; align-items: center; gap: 4px; font-family: Consolas, monospace; color: #999; }
.trust-item.admitted { color: #1a1a1a; }
.trust-name { font-size: 11px; }
.trust-report { color: #2e7d32; font-size: 11px; margin-top: 4px; }
.trust-error { color: #c0392b; font-size: 11px; margin-top: 4px; }
.proof-lines-scroll { flex: 1; overflow-y: auto; padding: 4px 8px; min-height: 0; }
.proof-lines { font-family: Consolas, monospace; }
.proof-line-row { cursor: pointer; padding: 1px 4px; border-radius: 3px; }
.proof-line-row:hover { background: #f0f0f0; }
.line-goal { }
.line-fact { }
.selection-bar { display: flex; align-items: center; gap: 8px; padding: 4px 10px; border-top: 1px solid #e0e0e0; border-bottom: 1px solid #e0e0e0; font-size: 12px; flex-shrink: 0; flex-wrap: wrap; }
.sel-goal { color: #c0392b; }
.sel-facts { color: #856404; }
.sel-fact { cursor: pointer; }
.sel-clear { padding: 0 4px; font-size: 10px; }
.tab-bar { display: flex; border-bottom: 1px solid #dee2e6; flex-shrink: 0; }
.tab-btn { padding: 4px 12px; border: none; background: none; cursor: pointer; font-size: 13px; color: #666; border-bottom: 2px solid transparent; }
.tab-btn.active { color: #007bff; border-bottom-color: #007bff; font-weight: 600; }
.tab-content { flex-shrink: 0; max-height: 40%; overflow-y: auto; padding: 6px 10px; }
.suggest-group { margin-bottom: 8px; }
.suggest-group-title { font-size: 11px; font-weight: 700; color: #888; text-transform: uppercase; margin-bottom: 3px; }
.suggest-item { display: flex; align-items: baseline; gap: 6px; padding: 3px 6px; cursor: pointer; border-radius: 3px; font-size: 12px; }
.suggest-item:hover { background: #e8f0fe; }
.suggest-dir { font-weight: 700; min-width: 20px; }
.suggest-method { font-family: Consolas, monospace; color: #1a73e8; }
.suggest-thm { font-family: Consolas, monospace; color: #666; font-size: 11px; }
.suggest-result { font-family: Consolas, monospace; color: #333; }
.suggest-needs { color: #e67e22; font-size: 11px; }
.suggest-nopreview { color: #aaa; font-style: italic; }
.suggest-empty { color: #999; font-size: 12px; padding: 8px; }
.suggest-group summary { cursor: pointer; }
.fuzzy-item { margin: 4px 0 6px 6px; border-left: 2px solid #e0e0e0; padding-left: 6px; }
.fuzzy-head { display: flex; align-items: baseline; gap: 6px; font-size: 12px; }
.fuzzy-match { display: flex; align-items: baseline; gap: 6px; padding: 2px 6px; cursor: pointer; border-radius: 3px; font-size: 11px; }
.fuzzy-match:hover { background: #fdf3e0; }
.fuzzy-facts { font-family: Consolas, monospace; color: #856404; }
.manual-row { display: flex; align-items: center; gap: 6px; margin-bottom: 6px; }
.manual-row label { font-size: 12px; color: #666; min-width: 50px; }
.method-select { font-size: 12px; padding: 2px 4px; flex: 1; }
.manual-params { margin-bottom: 6px; }
.param-row { position: relative; margin-bottom: 4px; }
.param-label { font-size: 11px; color: #666; display: inline-block; min-width: 60px; }
.param-input { font-size: 12px; padding: 2px 6px; border: 1px solid #ccc; border-radius: 3px; width: 200px; }
.theorem-dropdown { position: absolute; z-index: 100; background: white; border: 1px solid #ccc; border-radius: 3px; max-height: 200px; overflow-y: auto; width: 100%; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }
.theorem-item { padding: 3px 8px; cursor: pointer; font-size: 11px; display: flex; gap: 8px; }
.theorem-item:hover { background: #e8f0fe; }
.th-name { font-family: Consolas, monospace; color: #1a73e8; flex-shrink: 0; }
.th-prop { font-family: Consolas, monospace; color: #666; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.auto-tab { display: flex; flex-direction: column; gap: 4px; }
.auto-btn { width: fit-content; }
.auto-desc { font-size: 11px; color: #888; margin-left: 8px; }
.auto-empty { color: #999; font-size: 12px; font-style: italic; }
.proof-footer { display: flex; align-items: center; justify-content: space-between; padding: 4px 10px; border-top: 1px solid #dee2e6; background: #f8f9fa; flex-shrink: 0; }
.proof-status { font-size: 11px; color: #666; }
.proof-loading { padding: 20px; color: #999; }
</style>

<template>
  <div class="proof-area">
    <!-- Header: theorem name + prop -->
    <div class="proof-header">
      <div class="proof-thm-name">{{ thm_name }}</div>
      <div class="proof-thm-prop">{{ formatProp }}</div>
      <button class="btn btn-sm btn-outline-secondary proof-close-btn" @click="emit('close-prove')" title="Close proof">✕</button>
    </div>

    <!-- Proof lines (scrollable, main area) -->
    <div class="proof-lines-scroll">
      <div v-if="proof !== undefined" class="proof-lines">
        <div v-for="(line, idx) in proof" :key="line.id || idx"
             class="proof-line-row" :class="{'line-goal': goal === idx, 'line-fact': facts.includes(idx)}"
             @click="mark_text(idx)">
          <ProofLine :line="line" :is_last_id="is_last_id(idx)" :is_goal="goal === idx"
                     :is_fact="facts.includes(idx)" :can_select="can_select(goal, idx)"/>
        </div>
      </div>
      <div v-else class="proof-loading">Loading proof...</div>
    </div>

    <!-- Goal box: show full proposition -->
    <div v-if="goal !== -1 && proof && proof[goal]" class="goal-box">
      <span class="goal-tag">Goal</span>
      <span class="goal-id-text">{{ proof[goal].id }}:</span>
      <span class="goal-prop">{{ formatProofLine(proof[goal]) }}</span>
    </div>

    <!-- Facts box: show selected facts content -->
    <div v-if="facts.length > 0 && proof" class="facts-box">
      <div v-for="fi in facts" :key="fi" class="fact-item" @click="mark_text(fi)">
        <span class="fact-id">{{ proof[fi]?.id }}:</span>
        <span class="fact-prop">{{ formatProofLine(proof[fi]) }}</span>
      </div>
    </div>

    <!-- Method search results with subgoal count -->
    <div v-if="search_res.length > 0" class="search-results">
      <div class="search-title">Suggested methods:</div>
      <div v-for="(res, i) in search_res" :key="i" class="search-item" @click="apply_thm_tactic(i)">
        <span class="search-name">{{ res.theorem || res.method_name }}</span>
        <span v-if="res._goal !== undefined" class="search-subgoals">
          {{ res._goal.length === 0 ? '✓ closes' : res._goal.length + ' subgoals' }}
        </span>
      </div>
    </div>

    <!-- Manual method selector -->
    <div class="method-selector">
      <div class="search-title">Manual method:</div>
      <div class="method-form">
        <select v-model="manual_method" class="method-select">
          <option value="">-- select method --</option>
          <optgroup label="Logic">
            <option value="introduction">introduction</option>
            <option value="apply_backward_step">apply_backward_step</option>
            <option value="apply_forward_step">apply_forward_step</option>
            <option value="apply_prev">apply_prev</option>
            <option value="cut">cut</option>
            <option value="cases">cases</option>
            <option value="induction">induction</option>
            <option value="forall_elim">forall_elim</option>
            <option value="exists_elim">exists_elim</option>
            <option value="inst_exists_goal">inst_exists_goal</option>
            <option value="new_var">new_var</option>
          </optgroup>
          <optgroup label="Equality">
            <option value="sym">sym (a=b -> b=a)</option>
            <option value="subst">subst (replace in goal)</option>
          </optgroup>
          <optgroup label="Rewriting">
            <option value="rewrite_goal">rewrite_goal</option>
            <option value="rewrite_fact">rewrite_fact</option>
            <option value="unfold">unfold (expand definition)</option>
            <option value="fold">fold (contract definition)</option>
            <option value="simp">simp (auto rewrite)</option>
          </optgroup>
          <optgroup label="Assumptions">
            <option value="insert">insert (add theorem as assumption)</option>
            <option value="thin">thin (remove assumption)</option>
            <option value="drule">drule (forward, consume fact)</option>
            <option value="frule">frule (forward, keep fact)</option>
          </optgroup>
          <optgroup label="Automation">
            <option value="norm">norm (polynomial normalization)</option>
            <option value="eval">eval (constant evaluation)</option>
            <option value="linarith">linarith (linear arithmetic)</option>
            <option value="z3">z3 (SMT solver)</option>
          </optgroup>
          <optgroup label="Manual (escape hatch)">
            <option value="call_tactic">call_tactic</option>
            <option value="call_macro">call_macro</option>
          </optgroup>
        </select>
        <div v-if="manual_method && method_params.length > 0" class="method-params">
          <div v-for="p in method_params" :key="p" class="param-row">
            <label class="param-label">{{ p }}:</label>
            <input v-model="manual_params[p]" class="param-input" :placeholder="param_hint(p)"/>
          </div>
        </div>
        <button v-if="manual_method" class="btn btn-sm btn-primary mt-1" @click="apply_manual_method"
                :disabled="goal === -1 && manual_method !== 'new_var'">
          Apply
        </button>
      </div>
    </div>

    <!-- Footer: status + undo + save -->
    <div class="proof-footer">
      <span class="proof-status">{{ status_text }}</span>
      <div class="proof-actions">
        <button class="btn btn-sm btn-outline-warning" @click="undo" :disabled="index <= 0" title="Undo last step">Undo</button>
        <button class="btn btn-sm btn-success" @click="emit_save">Save Proof</button>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref, computed, onMounted } from 'vue'
import api from '../../api'
import ProofLine from './ProofLine.vue'

const props = defineProps({
  theory_name: String,
  thm_name: String,
  vars: {
    type: Object,
    default: () => ({})
  },
  prop: {
    type: [Array, Object, String],
    default: ''
  },
  old_steps: {
    type: Array,
    default: () => []
  },
  editor: Object
})

const emit = defineEmits(['set-message', 'query', 'set-context', 'set-status', 'set-proof', 'save-steps', 'close-prove'])

const method_sig = ref({})
const index = ref(0)
const history = ref([])
const steps = ref([])
const goal = ref(-1)
const facts = ref([])
const proof = ref(undefined)
const num_gaps = ref(0)

const search_res = ref([])

// Manual method selector
const manual_method = ref('')
const manual_params = ref({})

// Method parameter definitions
const method_sig_map = {
  'introduction': [],
  'apply_backward_step': ['theorem'],
  'apply_forward_step': ['theorem'],
  'apply_prev': [],
  'cut': ['goal'],
  'cases': ['case'],
  'induction': ['theorem', 'var'],
  'forall_elim': ['s'],
  'exists_elim': ['names'],
  'inst_exists_goal': ['s'],
  'new_var': ['name', 'type'],
  'sym': [],
  'subst': ['theorem'],
  'rewrite_goal': ['theorem', 'sym', 'loc'],
  'rewrite_fact': ['theorem', 'sym', 'loc'],
  'unfold': ['theorem'],
  'fold': ['theorem'],
  'simp': [],
  'insert': ['theorem'],
  'thin': ['index'],
  'drule': ['theorem'],
  'frule': ['theorem'],
  'norm': [],
  'eval': [],
  'linarith': [],
  'z3': [],
  'nat_norm': [],
  'real_norm': [],
  'call_tactic': ['tactic_name'],
  'call_macro': ['macro_name'],
}

// Additional params for call_tactic based on selected tactic
const call_tactic_extra_params = {
  'rule': ['theorem'],
  'rewrite_goal': ['theorem', 'sym', 'loc'],
  'resolve': ['theorem'],
  'cases': ['case'],
  'apply_prev': [],
  'intros': [],
  'assumption': [],
}

const method_params = computed(() => {
  const base = method_sig_map[manual_method.value] || []
  if (manual_method.value === 'call_tactic') {
    const tactic_name = manual_params.value.tactic_name || ''
    const extra = call_tactic_extra_params[tactic_name] || []
    return [...base, ...extra]
  }
  return base
})

// Additional params for call_tactic based on tactic_name
const call_tactic_params = {
  'rule': ['theorem'],
  'rewrite_goal': ['theorem', 'sym'],
  'apply_prev': [],
  'intros': [],
  'assumption': [],
  'resolve': ['theorem'],
  'cases': ['case'],
}

const param_hint = (p) => {
  const hints = {
    'theorem': 'theorem name',
    'sym': 'true/false',
    'loc': 'position, e.g. 0.1',
    'case': 'boolean expression',
    'var': 'variable name',
    's': 'term',
    'names': 'comma-separated names',
    'name': 'variable name',
    'type': 'HOL type',
    'goal': 'proposition',
    'tactic_name': 'rule/rewrite_goal/apply_prev/intros/...',
    'macro_name': 'macro name',
  }
  return hints[p] || p
}

const is_last_id = (idx) => {
  if (!proof.value) return false
  if (idx === proof.value.length - 1) return true
  return proof.value[idx + 1] && proof.value[idx + 1].rule === 'intros'
}

const can_select = (current_goal, idx) => {
  if (current_goal === -1) return false
  if (!proof.value) return false
  
  const goal_id = proof.value[current_goal].id.split('.')
  const fact_id = proof.value[idx].id.split('.')
  const len = fact_id.length
  
  if (len > goal_id.length) return false
  for (let i = 0; i < len - 1; i++) {
    if (fact_id[i] !== goal_id[i]) return false
  }
  return Number(fact_id[len - 1]) < Number(goal_id[len - 1])
}

const mark_text = (line_no) => {
  console.log('[ProofArea] mark_text line_no:', line_no, 'proof:', proof.value ? proof.value.length : 'null')
  if (!proof.value) return
  
  const line = proof.value[line_no]
  console.log('[ProofArea] line:', line ? line.rule : 'undefined', 'current goal:', goal.value)
  
  if (line.rule === 'sorry') {
    goal.value = line_no
    facts.value = []
    console.log('[ProofArea] set goal to', line_no)
  } else if (goal.value !== -1) {
    if (!can_select(goal.value, line_no)) return
    
    let i = facts.value.indexOf(line_no)
    if (i === -1) {
      facts.value.push(line_no)
    } else {
      facts.value.splice(i, 1)
    }
    console.log('[ProofArea] toggled fact', line_no, 'facts:', facts.value)
  }
  match_thm()
}

const compute_new_goal = (start) => {
  if (!proof.value) return -1
  for (let i = start; i < proof.value.length; i++) {
    if (proof.value[i].rule === 'sorry') {
      return i
    }
  }
  return -1
}

const display_num_gaps = () => {
  const gaps = proof.value ? proof.value.filter(p => p.rule === 'sorry').length : 0
  num_gaps.value = gaps
  if (gaps > 0) {
    status_text.value = gaps + ' gap(s) remaining'
  } else {
    status_text.value = 'Proof complete!'
  }
}

const display_instructions = () => {
  if (history.value.length > 0) {
    if (index.value === 0) {
      emit('set-status', { 
        status: '', 
        instr: [{color: 0, text: 'Initial'}], 
        instr_no: '0/' + history.value.length 
      })
    } else {
      const step = history.value[index.value - 1]
      if (step && step.step_output) {
        emit('set-status', { 
          status: '', 
          instr: step.step_output, 
          instr_no: index.value + '/' + history.value.length 
        })
      }
    }
  }
}

const get_line_no_from_id = (id) => {
  if (!proof.value) return -1
  let found = -1
  for (let i = 0; i < proof.value.length; i++) {
    if (proof.value[i].id === id) found = i
  }
  return found
}

const current_state = () => {
  if (goal.value === -1) return undefined
  
  const fact_ids = facts.value.map(i => proof.value[i].id)
  const goal_id = proof.value[goal.value].id
  
  return {
    theory_name: props.theory_name,
    thm_name: props.thm_name,
    vars: props.vars,
    prop: props.prop,
    steps: steps.value,
    index: index.value,
    step: {
      goal_id: goal_id,
      fact_ids: fact_ids,
    }
  }
}

const match_thm = async () => {
  const input = current_state()
  console.log('[ProofArea] match_thm, input:', input ? 'ok' : 'undefined')
  if (input === undefined) {
    search_res.value = []
    emit('set-context', { ctxt: {}, history: history.value, history_idx: -1 })
    return
  }
  
  console.log('[ProofArea] searching with goal_id:', input.step.goal_id, 'fact_ids:', input.step.fact_ids)
  try {
    const response = await api.post('/search-method', input)
    search_res.value = response.data.search_res || []
    console.log('[ProofArea] search results:', search_res.value.length)
    emit('set-context', {
      ctxt: response.data.ctxt || {},
      history: history.value,
      history_idx: index.value
    })
  } catch (err) {
    search_res.value = []
    console.error('[ProofArea] search error:', err)
  }
}

const apply_thm_tactic = (res_id) => {
  console.log('[ProofArea] apply_thm_tactic res_id:', res_id, 'search_res:', search_res.value.length)
  if (res_id >= 0 && res_id < search_res.value.length) {
    const res = search_res.value[res_id]
    console.log('[ProofArea] applying:', res.method_name, res.theorem || '')
    apply_method(res.method_name, res)
  }
}

const apply_manual_method = async () => {
  if (!manual_method.value) return
  if (goal.value === -1 && manual_method.value !== 'new_var') {
    emit('set-message', { type: 'error', data: 'Select a goal (click sorry) first' })
    return
  }
  
  const method_name = manual_method.value
  const params = { ...manual_params.value }
  
  // For call_tactic, merge tactic-specific params
  if (method_name === 'call_tactic' && params.tactic_name) {
    // params already includes tactic_name and any extra fields
  }
  
  // Build args object
  const args = { ...params }
  
  console.log('[ProofArea] manual apply:', method_name, args)
  await apply_method(method_name, args)
  
  // Clear params for next use
  manual_params.value = {}
}

const apply_method = async (method_name, args) => {
  const sigs = method_sig.value[method_name] || []
  const input = current_state()
  if (!input) return
  
  input.step.method_name = method_name
  
  if (args !== undefined) {
    input.step.goal_id = args.goal_id || input.step.goal_id
    if (args.fact_ids !== undefined) {
      input.step.fact_ids = args.fact_ids
    }
  } else {
    args = {}
  }
  
  const sigList = []
  for (let i = 0; i < sigs.length; i++) {
    const sig = sigs[i]
    if (sig in args) {
      input.step[sig] = args[sig]
    } else {
      sigList.push(sig)
    }
  }
  
  if (sigList.length > 0) {
    const query_result = await new Promise((resolve, reject) => {
      emit('query', {
        title: 'Method ' + method_name,
        fields: sigList,
        resolve: resolve,
        reject: reject
      })
    })
    
    if (query_result !== undefined) {
      Object.assign(input.step, query_result)
      await apply_method_ajax(input)
    }
  } else {
    await apply_method_ajax(input)
  }
}

const apply_method_ajax = async (input) => {
  emit('set-status', { status: 'Running' })
  
  try {
    const result = await api.post('/apply-method', input)
    
    if ('query' in result.data) {
      const query_result = await new Promise((resolve, reject) => {
        emit('query', {
          title: 'Query for parameters',
          fields: result.data.query.map(s => s === 'names' ? s : s.slice(6)),
          resolve: resolve,
          reject: reject
        })
      })
      
      if (query_result !== undefined) {
        for (const k in query_result) {
          if (k === 'names') {
            input.step[k] = query_result[k]
          } else {
            input.step['param_' + k] = query_result[k]
          }
        }
        await apply_method_ajax(input)
      }
    } else if ('error' in result.data) {
      emit('set-message', { 
        type: 'error', 
        data: result.data.error.err_type + ': ' + result.data.error.err_str 
      })
    } else {
      if (input.step.fact_ids && input.step.fact_ids.length === 0) {
        delete input.step.fact_ids
      }
      steps.value = steps.value.slice(0, index.value)
      steps.value.push(input.step)
      console.log('[SAVE] truncated to', steps.value.length, 'steps after apply')
      // and returns the correct state - no need to set state here
      await gotoStep(index.value + 1)
    }
  } catch (err) {
    emit('set-message', { type: 'error', data: 'Error applying method' })
  }
}

const gotoStep = async (new_index, set_selected) => {
  index.value = new_index
  
  const data = {
    theory_name: props.theory_name,
    thm_name: props.thm_name,
    vars: props.vars,
    prop: props.prop,
    steps: steps.value,
    index: index.value
  }
  
  try {
    const response = await api.post('/init-saved-proof', data)
    
    if (response.data.error) {
      emit('set-message', { type: 'error', data: response.data.error })
      return
    }
    
    const state = response.data.state
    const new_history = response.data.history || []
    // Only update history if new one is longer (preserve full history for display)
    if (new_history.length >= history.value.length) {
      history.value = new_history
    }
    num_gaps.value = state.num_gaps
    method_sig.value = state.method_sig || {}
    proof.value = state.proof
    
    facts.value = []
    if (index.value >= history.value.length) {
      goal.value = compute_new_goal(0)
    } else {
      goal.value = get_line_no_from_id(history.value[index.value].goal_id)
      const fact_ids = history.value[index.value].fact_ids
      if (fact_ids !== undefined) {
        for (let i = 0; i < fact_ids.length; i++) {
          const fact_no = get_line_no_from_id(fact_ids[i])
          if (can_select(goal.value, fact_no)) {
            facts.value.push(fact_no)
          }
        }
      }
    }
    
    // Update context - always send full history
    const contextData = { steps: history.value }
    if (set_selected === undefined || set_selected === true) {
      contextData.selected_start = new_index
      contextData.selected_end = new_index
    }
    emit('set-context', contextData)
    
    display_num_gaps()
    display_instructions()
    await match_thm()
  } catch (err) {
    // Don't reset proof state on error - just show the error
    emit('set-message', { type: 'error', data: 'Error loading proof state: ' + (err.message || err) })
  }
}

const deleteStep = (start, end) => {
  steps.value.splice(start, end - start + 1)
  gotoStep(start)
}

const step_backward = () => {
  if (index.value > 0) {
    gotoStep(index.value - 1)
  }
}

const step_forward = () => {
  if (index.value < history.value.length) {
    gotoStep(index.value + 1)
  }
}

const init_proof = async () => {
  console.log('[ProofArea] init_proof, old_steps:', props.old_steps ? props.old_steps.length : 'null', 'prop:', props.prop)
  if (!props.old_steps || props.old_steps.length === 0) {
    steps.value = []
    history.value = []
    await gotoStep(0)
  } else {
    steps.value = JSON.parse(JSON.stringify(props.old_steps))
    await gotoStep(steps.value.length)
  }
}

const status_text = ref('')
const formatDisplay = (disp) => {
  if (Array.isArray(disp)) {
    return disp.map(item => item.text || String(item)).join('')
  }
  return String(disp)
}

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

const undo = () => {
  if (steps.value.length > 0 && index.value > 0) {
    steps.value.splice(index.value - 1, 1)
    gotoStep(index.value - 1)
  }
}

const emit_save = () => {
  console.log('[SAVE] emit_save, steps.length =', steps.value.length, 'index =', index.value)
  emit('save-steps', JSON.parse(JSON.stringify(steps.value)))
}

const exposed = {
  apply_method,
  apply_thm_tactic,
  gotoStep,
  deleteStep,
  step_backward,
  step_forward,
  undo,
  proof,
  num_gaps,
  steps,
  init_proof
}

onMounted(() => {
  if (props.prop) {
    init_proof()
  }
})

defineExpose(exposed)
</script>

<style scoped>
.proof-area { font-size: 14px; }
.proof-lines { margin-bottom: 10px; }
.proof-line-row { cursor: pointer; padding: 1px 4px; border-radius: 3px; }
.proof-line-row:hover { background: #f0f0f0; }
.line-goal { background: #ffe0e0 !important; }
.line-fact { background: #ffffcc !important; }
.proof-loading { color: #999; padding: 10px; }
.goal-info, .facts-info { padding: 4px 8px; font-size: 13px; background: #f8f8f8; border-radius: 4px; margin-bottom: 4px; }
.goal-label { font-weight: bold; color: #333; display: inline; }
.goal-id { font-family: Consolas, monospace; display: inline; margin-left: 6px; }
.search-results { margin-top: 10px; border-top: 1px solid #dee2e6; padding-top: 8px; }
.search-title { font-weight: bold; font-size: 13px; color: #495057; margin-bottom: 6px; }
.search-item { padding: 4px 8px; cursor: pointer; border-radius: 3px; font-size: 13px; margin-bottom: 2px; }
.search-item:hover { background: #ffffcc; }
.search-display { font-family: Consolas, monospace; }
.proof-footer { margin-top: 10px; display: flex; justify-content: space-between; align-items: center; border-top: 1px solid #dee2e6; padding-top: 8px; }
.proof-status { font-size: 13px; color: #666; }
.proof-actions { display: flex; gap: 6px; }
.method-selector { margin-top: 10px; border-top: 1px solid #dee2e6; padding-top: 8px; }
.method-form { display: flex; flex-direction: column; gap: 6px; }
.method-select { padding: 4px 8px; font-size: 13px; border: 1px solid #ced4da; border-radius: 4px; }
.method-params { margin-top: 4px; }
.param-row { display: flex; align-items: center; gap: 6px; margin-bottom: 4px; }
.param-label { font-size: 12px; font-weight: bold; color: #555; min-width: 80px; }
.param-input { flex: 1; padding: 3px 6px; font-size: 13px; border: 1px solid #ced4da; border-radius: 3px; font-family: Consolas, monospace; }

.proof-area { display: flex; flex-direction: column; height: 100%; overflow: hidden; }
.proof-header { display: flex; align-items: center; gap: 8px; padding: 8px 12px; background: #f0f4ff; border-bottom: 1px solid #d0d7de; flex-shrink: 0; }
.proof-thm-name { font-weight: 700; font-size: 14px; color: #333; flex-shrink: 0; }
.proof-thm-prop { font-family: Consolas, monospace; font-size: 13px; color: #555; flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.proof-close-btn { flex-shrink: 0; }
.proof-lines-scroll { flex: 1; overflow-y: auto; padding: 4px 8px; min-height: 0; }
.proof-lines { font-family: Consolas, monospace; }
.proof-line-row { cursor: pointer; padding: 1px 4px; border-radius: 3px; }
.proof-line-row:hover { background: #f0f0f0; }
.line-goal { background: #ffe0e0 !important; }
.line-fact { background: #fff3cd !important; }
.goal-box { display: flex; align-items: baseline; gap: 6px; padding: 6px 12px; background: #fff5f5; border-top: 1px solid #ffcaca; flex-shrink: 0; }
.goal-tag { font-size: 11px; font-weight: 700; color: #c0392b; text-transform: uppercase; }
.goal-id-text { font-family: Consolas, monospace; font-size: 12px; color: #999; }
.goal-prop { font-family: Consolas, monospace; font-size: 13px; color: #333; }
.facts-box { padding: 4px 12px; background: #fffbf0; border-top: 1px solid #ffeaa7; flex-shrink: 0; }
.fact-item { display: flex; align-items: baseline; gap: 6px; padding: 2px 0; cursor: pointer; }
.fact-id { font-family: Consolas, monospace; font-size: 12px; color: #999; }
.fact-prop { font-family: Consolas, monospace; font-size: 13px; color: #555; }
.search-results { padding: 6px 12px; flex-shrink: 0; }
.search-title { font-size: 12px; font-weight: 600; color: #666; margin-bottom: 4px; }
.search-item { display: flex; align-items: center; gap: 8px; padding: 3px 8px; cursor: pointer; border-radius: 3px; }
.search-item:hover { background: #e8f0fe; }
.search-name { font-family: Consolas, monospace; font-size: 13px; color: #1a73e8; }
.search-subgoals { font-size: 11px; color: #888; }
.method-selector { padding: 6px 12px; flex-shrink: 0; }
.method-form { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; }
.method-select { font-size: 13px; padding: 2px 6px; }
.method-params { display: flex; flex-wrap: wrap; gap: 6px; }
.param-row { display: flex; align-items: center; gap: 3px; }
.param-label { font-size: 12px; color: #666; }
.param-input { font-size: 12px; padding: 2px 6px; width: 120px; border: 1px solid #ccc; border-radius: 3px; }
.proof-footer { display: flex; align-items: center; justify-content: space-between; padding: 6px 12px; border-top: 1px solid #dee2e6; background: #f8f9fa; flex-shrink: 0; }
.proof-status { font-size: 12px; color: #666; }
.proof-actions { display: flex; gap: 4px; }
.proof-loading { padding: 20px; color: #999; }
</style>

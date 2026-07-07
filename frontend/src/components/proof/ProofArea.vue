<template>
  <div style="margin-top:8px">
    <div v-if="proof !== undefined">
      <ProofLine v-for="(line, idx) in proof" 
                 :key="line.id || idx" :line="line"
                 :is_last_id="is_last_id(idx)"
                 :is_goal="goal === idx"
                 :is_fact="facts.includes(idx)"
                 :can_select="can_select(goal, idx)"
                 @select="mark_text(idx)"/>
    </div>
  </div>
</template>

<script setup>
import { ref, onMounted } from 'vue'
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
  old_proof: Array,
  editor: Object
})

const emit = defineEmits(['set-message', 'query', 'set-context', 'set-status', 'set-proof'])

const method_sig = ref({})
const index = ref(0)
const history = ref([])
const steps = ref([])
const goal = ref(-1)
const facts = ref([])
const proof = ref(undefined)
const num_gaps = ref(0)

const search_res = ref([])

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
  if (!proof.value) return
  
  if (proof.value[line_no].rule === 'sorry') {
    goal.value = line_no
  } else if (goal.value !== -1) {
    if (!can_select(goal.value, line_no)) return
    
    let i = facts.value.indexOf(line_no)
    if (i === -1) {
      facts.value.push(line_no)
    } else {
      facts.value.splice(i, 1)
    }
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
    emit('set-status', { status: 'OK. ' + gaps + ' gap(s) remaining.', instr: [], instr_no: '' })
  } else {
    emit('set-status', { status: 'OK. Proof complete!', instr: [], instr_no: '' })
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
  if (input === undefined) {
    search_res.value = []
    emit('set-status', { status: '', search_res: [], ctxt: {} })
    emit('set-context', { ctxt: {}, steps: history.value })
    return
  }
  
  try {
    const response = await api.post('/search-method', input)
    search_res.value = response.data.search_res || []
    emit('set-status', { 
      status: '', 
      search_res: response.data.search_res || [] 
    })
    emit('set-context', { 
      ctxt: response.data.ctxt || {}, 
      steps: history.value 
    })
  } catch (err) {
    search_res.value = []
    emit('set-message', { type: 'error', data: 'Error searching methods' })
    emit('set-status', { status: 'Error', search_res: [] })
  }
}

const apply_thm_tactic = (res_id) => {
  if (res_id >= 0 && res_id < search_res.value.length) {
    const res = search_res.value[res_id]
    apply_method(res.method_name, res)
  }
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
      steps.value.splice(index.value, 0, input.step)
      
      // gotoStep will call /init-saved-proof which replays all steps
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
  if (props.old_proof === undefined) {
    steps.value = []
    history.value = []
    await gotoStep(0)
  } else {
    steps.value = JSON.parse(JSON.stringify(props.old_steps || []))
    await gotoStep(steps.value.length)
  }
}

const exposed = {
  apply_method,
  apply_thm_tactic,
  gotoStep,
  deleteStep,
  step_backward,
  step_forward,
  proof,
  num_gaps,
  steps,
  init_proof
}

onMounted(() => {
  if (props.prop) {
    init_proof()
  }
  emit('set-proof', exposed)
})

defineExpose(exposed)
</script>

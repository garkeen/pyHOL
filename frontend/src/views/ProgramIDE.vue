<template>
  <div class="program-ide">
    <!-- Top bar -->
    <div class="topbar">
      <select v-model="current" @change="load_program" class="program-select">
        <option v-for="f in files" :key="f.name" :value="f.name">{{ f.name }}</option>
      </select>
      <button class="btn btn-sm btn-outline-secondary" @click="new_program">New</button>
      <button class="btn btn-sm btn-primary" @click="save_and_compile" :disabled="compiling">
        {{ compiling ? 'Compiling...' : 'Compile' }}
      </button>
      <span v-if="compile_ok" class="status ok">✓ {{ compile_ok }}</span>
      <span v-if="compile_error" class="status err">✗ {{ compile_error }}</span>
    </div>

    <div class="main">
      <!-- File list -->
      <div class="file-list">
        <div v-for="f in files" :key="f.name" class="file-item"
             :class="{selected: f.name === current}" @click="select_file(f.name)">
          {{ f.name }}
        </div>
      </div>

      <!-- Editor + VCs -->
      <div class="editor-pane">
        <textarea v-model="text" class="imp-editor" spellcheck="false"
                  placeholder="Write your .imp program here..."></textarea>
        <div class="vc-panel">
          <div class="vc-title">
            Verification Conditions ({{ vcs.length }})
            <span class="vc-hint">green = proved, red = needs proof</span>
          </div>
          <div v-if="vcs.length === 0" class="vc-empty">No VCs yet — click Compile.</div>
          <div v-for="vc in vcs" :key="vc.index" class="vc-row" :class="vc.proved ? 'vc-ok' : 'vc-bad'">
            <span class="vc-badge">{{ vc.proved ? '✓' : '✗' }}</span>
            <span class="vc-index">#{{ vc.index }}</span>
            <span class="vc-prop">{{ vc.prop }}</span>
            <button v-if="!vc.proved" class="btn btn-sm btn-outline-danger vc-prove"
                    @click="prove_vc(vc)">Prove</button>
          </div>
        </div>
      </div>

      <!-- Proof panel -->
      <div v-if="proving" class="proof-pane">
        <div class="proof-pane-header">
          <span>Prove <b>{{ proving_vc_name }}</b> in <b>{{ current }}</b></span>
          <button class="btn btn-sm btn-outline-secondary" @click="proving = false">✕</button>
        </div>
        <ProofArea
          :key="'imp-proof-' + current + '-' + proving_vc_index"
          :theory_name="current"
          :thm_name="theorem_item ? theorem_item.name : current"
          :vars="theorem_item ? theorem_item.vars : {}"
          :prop="theorem_item ? theorem_item.prop : ''"
          :old_steps="theorem_item ? (theorem_item.steps || []) : []"
          :editor="null"
          @save-steps="save_proof"
          @set-message="toast"
          @query="handle_query"/>
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
import ProofArea from '../components/proof/ProofArea.vue'
import ProofQuery from '../components/proof/ProofQuery.vue'

const files = ref([])
const current = ref('')
const text = ref('')
const compiling = ref(false)
const compile_ok = ref('')
const compile_error = ref('')
const vcs = ref([])
const proving = ref(false)
const proving_vc_index = ref(-1)
const proving_vc_name = ref('')
const theorem_item = ref(null)
const message = ref(null)
const query = ref(undefined)
let toastTimer = null

const toast = (msg) => {
  message.value = msg
  if (toastTimer) clearTimeout(toastTimer)
  if (msg && msg.type !== 'error') {
    toastTimer = setTimeout(() => { message.value = null }, 3000)
  }
}

const load_files = async () => {
  try {
    const res = await api.post('/imp-list')
    files.value = res.data.files
  } catch (e) {
    toast({ type: 'error', data: 'Failed to load program list' })
  }
}

const select_file = async (name) => {
  current.value = name
  await load_program()
}

const load_program = async () => {
  if (!current.value) return
  const f = files.value.find(x => x.name === current.value)
  if (f) text.value = f.text
  vcs.value = []
  compile_ok.value = ''
  compile_error.value = ''
  proving.value = false
}

const new_program = async () => {
  const name = prompt('New program name:')
  if (!name) return
  const tmpl = `theory ${name}
imports hoare

program ${name}
  vars: x: nat
  pre: true
  post: true
  body:
    Skip
`
  try {
    const res = await api.post('/imp-compile', { name, text: tmpl })
    if (!res.data.ok) throw new Error(res.data.error || 'compile failed')
    await load_files()
    current.value = name
    text.value = tmpl
    vcs.value = res.data.vcs || []
    compile_ok.value = `${name} compiled: ${res.data.num_vcs} VCs`
    compile_error.value = ''
  } catch (e) {
    toast({ type: 'error', data: 'Failed to create program: ' + (e.message || e) })
  }
}

const save_and_compile = async () => {
  if (!current.value) return
  compiling.value = true
  compile_ok.value = ''
  compile_error.value = ''
  try {
    const res = await api.post('/imp-compile', { name: current.value, text: text.value })
    if (!res.data.ok) {
      compile_error.value = res.data.error || 'compile failed'
      return
    }
    vcs.value = res.data.vcs || []
    compile_ok.value = `${current.value} compiled: ${res.data.num_vcs} VCs`
    // Refresh the file list (saved text)
    await load_files()
  } catch (e) {
    compile_error.value = e.message || 'compile failed'
  } finally {
    compiling.value = false
  }
}

const prove_vc = async (vc) => {
  if (!current.value) return
  try {
    const res = await api.post('/load-json-file', { filename: current.value, line_length: 80 })
    const content = res.data.content || []
    const vcName = 'vc_' + vc.index
    const item = content.find(it => it.name === vcName)
    if (!item) {
      toast({ type: 'error', data: vcName + ' not found - compile first' })
      return
    }
    theorem_item.value = item
    proving_vc_index.value = vc.index
    proving_vc_name.value = vcName
    proving.value = true
  } catch (e) {
    toast({ type: 'error', data: 'Failed to load compiled theory: ' + (e.message || e) })
  }
}

const save_proof = async (steps) => {
  if (!current.value || !theorem_item.value) return
  const vcName = theorem_item.value.name
  try {
    const res = await api.post('/load-json-file', { filename: current.value, line_length: 80 })
    const content = (res.data.content || []).map(item => {
      const copy = { ...item }
      for (const k of ['_error', '_from_disk', 'display', 'edit', 'ext', 'error']) delete copy[k]
      return copy
    })
    const target = content.find(it => it.name === vcName)
    if (!target) throw new Error(vcName + ' not found')
    target.steps = steps
    await api.post('/save-file', {
      filename: current.value,
      content: {
        name: res.data.name,
        imports: res.data.imports || [],
        domains: res.data.domains || [],
        description: res.data.description || '',
        content
      }
    })
    // Re-validate to update VC status
    const resp = await api.post('/validate-theory', { filename: current.value, force: false })
    const statuses = resp.data.statuses || {}
    const status = statuses[vcName] || 'PENDING'
    // Update the VC in the list
    const vc = vcs.value.find(v => v.index === proving_vc_index.value)
    if (vc) vc.proved = (status === 'VALID')
    toast({ type: status === 'VALID' ? 'OK' : 'error', data: vcName + ': ' + status })
  } catch (e) {
    toast({ type: 'error', data: 'Failed to save proof: ' + (e.message || e) })
  }
}

const handle_query = (q) => {
  query.value = q
}

const handle_query_ok = (vals) => {
  if (query.value && query.value.resolve) query.value.resolve(vals)
  query.value = undefined
}

const handle_query_cancel = () => {
  if (query.value && query.value.resolve) query.value.resolve(undefined)
  query.value = undefined
}

onMounted(async () => {
  await load_files()
  if (files.value.length > 0) {
    current.value = files.value[0].name
    text.value = files.value[0].text
  }
})
</script>

<style scoped>
.program-ide { display: flex; flex-direction: column; height: 100vh; padding: 8px; box-sizing: border-box; }
.topbar { display: flex; align-items: center; gap: 8px; padding: 6px 8px; border-bottom: 1px solid #dee2e6; flex-shrink: 0; }
.program-select { min-width: 200px; padding: 3px 6px; }
.status { font-size: 12px; }
.status.ok { color: #28a745; }
.status.err { color: #dc3545; }
.main { display: flex; flex: 1; min-height: 0; }
.file-list { width: 160px; border-right: 1px solid #dee2e6; overflow-y: auto; padding: 6px 0; flex-shrink: 0; }
.file-item { padding: 5px 12px; cursor: pointer; font-size: 13px; font-family: Consolas, monospace; }
.file-item:hover { background: #f0f0f0; }
.file-item.selected { background: #e8f0fe; font-weight: 600; }
.editor-pane { flex: 1; display: flex; flex-direction: column; min-width: 0; }
.imp-editor { flex: 1; min-height: 0; width: 100%; box-sizing: border-box; font-family: Consolas, monospace; font-size: 13px; padding: 8px; border: none; border-bottom: 1px solid #dee2e6; resize: none; outline: none; }
.vc-panel { flex: 1; min-height: 120px; overflow-y: auto; padding: 8px; }
.vc-title { font-size: 12px; font-weight: 700; color: #555; margin-bottom: 6px; }
.vc-hint { font-weight: 400; color: #999; margin-left: 8px; }
.vc-empty { color: #999; font-size: 12px; padding: 8px; }
.vc-row { display: flex; align-items: baseline; gap: 8px; padding: 4px 8px; border-radius: 3px; margin-bottom: 4px; font-size: 12px; }
.vc-ok { background: #f0faf0; border-left: 3px solid #28a745; }
.vc-bad { background: #fdf0f0; border-left: 3px solid #dc3545; }
.vc-badge { font-weight: 700; }
.vc-ok .vc-badge { color: #28a745; }
.vc-bad .vc-badge { color: #dc3545; }
.vc-index { font-family: Consolas, monospace; color: #666; flex-shrink: 0; }
.vc-prop { font-family: Consolas, monospace; color: #333; flex: 1; overflow-wrap: anywhere; }
.vc-prove { flex-shrink: 0; }
.proof-pane { width: 45%; min-width: 400px; border-left: 1px solid #dee2e6; display: flex; flex-direction: column; flex-shrink: 0; }
.proof-pane-header { display: flex; align-items: center; justify-content: space-between; padding: 6px 10px; border-bottom: 1px solid #dee2e6; font-size: 13px; flex-shrink: 0; }
.proof-pane-header > span { flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.modal-overlay { position: fixed; inset: 0; background: rgba(0,0,0,0.4); display: flex; align-items: center; justify-content: center; z-index: 1000; }
.modal-content { background: white; border-radius: 6px; width: 480px; max-width: 90vw; box-shadow: 0 4px 12px rgba(0,0,0,0.2); }
.modal-header { display: flex; align-items: center; justify-content: space-between; padding: 10px 16px; border-bottom: 1px solid #dee2e6; }
.modal-body { padding: 12px 16px; }
.toast { position: fixed; top: 16px; right: 16px; display: flex; align-items: center; gap: 8px; padding: 10px 14px; border-radius: 4px; font-size: 13px; box-shadow: 0 2px 8px rgba(0,0,0,0.2); z-index: 1100; }
.toast-ok { background: #d4edda; color: #155724; border: 1px solid #c3e6cb; }
.toast-error { background: #f8d7da; color: #721c24; border: 1px solid #f5c6cb; }
.toast-close { background: none; border: none; font-size: 14px; cursor: pointer; }
</style>

<template>
  <div class="program-ide">
    <!-- Top bar -->
    <nav class="navbar navbar-expand navbar-dark bg-dark">
      <div class="container-fluid">
        <span class="navbar-brand">Program IDE</span>
        <select class="form-select form-select-sm file-select" :value="current" @change="load_file($event.target.value)">
          <option value="">-- file --</option>
          <option v-for="f in files" :key="f.name" :value="f.name">{{ f.name }}</option>
        </select>
        <button class="btn btn-sm btn-outline-light ms-1" @click="new_file">New</button>
        <span v-if="status_msg" class="text-light ms-2" :class="status_err ? 'text-danger' : 'text-success'">{{ status_msg }}</span>
      </div>
    </nav>

    <div class="main-content" :class="{'proving-mode': proving}">
      <!-- Program panel -->
      <div class="program-panel">
        <div v-if="!current" class="empty-state"><p>Select or create a file</p></div>
        <div v-else>
          <!-- Metadata -->
          <div class="metadata-section">
            <div class="meta-row">
              <label class="meta-label">theory</label>
              <input class="meta-input" v-model="theory_name" :disabled="!editing_meta" placeholder="theory name"/>
              <label class="meta-label">imports</label>
              <input class="meta-input" v-model="imports_text" :disabled="!editing_meta" placeholder="comma-separated"/>
              <button class="btn btn-sm btn-outline-primary" @click="editing_meta = !editing_meta">{{ editing_meta ? 'Done' : 'Edit' }}</button>
            </div>
          </div>

          <!-- Programs list -->
          <div class="programs-list">
            <div v-for="(prog, idx) in programs" :key="idx" class="program-block" :class="{'program-selected': selected === idx}">
              <!-- Program header -->
              <div class="program-header" @click="selected = idx">
                <span class="prog-name">{{ prog.name }}</span>
                <span class="prog-vars">{{ formatVars(prog.vars) }}</span>
                <div class="prog-actions">
                  <button class="btn btn-sm btn-outline-secondary" @click.stop="toggle_edit(idx)">{{ editing_prog === idx ? 'Close' : 'Edit' }}</button>
                  <button class="btn btn-sm btn-outline-primary" @click.stop="verify_program(idx)" title="Verify this program">Verify</button>
                  <button class="btn btn-sm btn-outline-warning" @click.stop="move_prog(idx, -1)" :disabled="idx === 0">↑</button>
                  <button class="btn btn-sm btn-outline-warning" @click.stop="move_prog(idx, 1)" :disabled="idx === programs.length - 1">↓</button>
                  <button class="btn btn-sm btn-outline-danger" @click.stop="remove_prog(idx)">✕</button>
                </div>
              </div>
              <!-- Summary: pre / post -->
              <div class="prog-summary">
                <span class="prog-pre">pre: {{ prog.pre }}</span>
                <span class="prog-post">post: {{ prog.post }}</span>
              </div>

              <!-- Inline edit form -->
              <div v-if="editing_prog === idx" class="prog-edit">
                <div class="edit-row"><label>name</label><input class="edit-input" v-model="prog.name"/></div>
                <div class="edit-row"><label>vars</label><input class="edit-input" v-model="prog.vars_text" placeholder="x: nat, y: nat"/></div>
                <div class="edit-row"><label>pre</label><input class="edit-input" v-model="prog.pre"/></div>
                <div class="edit-row"><label>post</label><input class="edit-input" v-model="prog.post"/></div>
                <div class="edit-row"><label>body</label><textarea class="edit-body" v-model="prog.body" spellcheck="false" rows="6"></textarea></div>
                <div class="edit-actions">
                  <button class="btn btn-sm btn-primary" @click="save_edit">Save</button>
                  <button class="btn btn-sm btn-secondary" @click="editing_prog = -1">Cancel</button>
                </div>
              </div>

              <!-- VCs for this program -->
              <div v-if="vcs_by_program[prog.name]" class="vc-list">
                <div v-for="vc in vcs_by_program[prog.name]" :key="vc.name"
                     class="vc-row" :class="vc.proved ? 'vc-ok' : 'vc-bad'">
                  <span class="vc-badge">{{ vc.proved ? '✓' : '✗' }}</span>
                  <span class="vc-name">{{ vc.name }}</span>
                  <span class="vc-prop">{{ vc.prop }}</span>
                  <button v-if="!vc.proved" class="btn btn-sm btn-outline-danger vc-prove" @click.stop="prove_vc(vc, prog.name)">Prove</button>
                </div>
              </div>
            </div>
          </div>

          <!-- Add program + Verify buttons -->
          <div class="bottom-actions">
            <button class="btn btn-sm btn-success" @click="add_program">+ Add Program</button>
            <button class="btn btn-sm btn-primary" @click="verify_all" :disabled="verifying">{{ verifying ? 'Verifying...' : 'Verify All' }}</button>
          </div>
        </div>
      </div>

      <!-- Proof panel -->
      <div v-if="proving && theorem_item" class="proof-panel">
        <div class="proof-pane-header">
          <span>Prove <b>{{ proving_vc_name }}</b></span>
          <button class="btn btn-sm btn-outline-secondary" @click="proving = false">✕</button>
        </div>
        <ProofArea
          :key="'imp-proof-' + current + '-' + proving_vc_name"
          :theory_name="current"
          :thm_name="proving_vc_name"
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
          <ProofQuery :query="query" @query-ok="handle_query_ok" @query-cancel="handle_query_cancel"/>
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
import { ref, computed, onMounted } from 'vue'
import api from '../api'
import ProofArea from '../components/proof/ProofArea.vue'
import ProofQuery from '../components/proof/ProofQuery.vue'

const files = ref([])
const current = ref('')
const theory_name = ref('')
const imports_text = ref('')
const programs = ref([])
const editing_meta = ref(false)
const editing_prog = ref(-1)
const selected = ref(-1)
const vcs = ref([])
const verifying = ref(false)
const proving = ref(false)
const proving_vc_name = ref('')
const theorem_item = ref(null)
const message = ref(null)
const query = ref(undefined)
const status_msg = ref('')
const status_err = ref(false)
let toastTimer = null

const toast = (msg) => {
  message.value = msg
  if (toastTimer) clearTimeout(toastTimer)
  if (msg && msg.type !== 'error') toastTimer = setTimeout(() => { message.value = null }, 3000)
}

const formatVars = (vars) => {
  if (!vars || vars.length === 0) return ''
  return vars.map(v => v[0] + ': ' + v[1]).join(', ')
}

const vcs_by_program = computed(() => {
  const map = {}
  for (const vc of vcs.value) {
    if (!map[vc.program]) map[vc.program] = []
    map[vc.program].push(vc)
  }
  return map
})

const load_files = async () => {
  try {
    const res = await api.post('/imp-list')
    files.value = res.data.files
  } catch (e) { toast({ type: 'error', data: 'Failed to load file list' }) }
}

const load_file = async (name) => {
  if (!name) return
  current.value = name
  vcs.value = []
  proving.value = false
  try {
    const res = await api.post('/imp-load', { name })
    if (!res.data.ok) throw new Error(res.data.error)
    theory_name.value = res.data.theory
    imports_text.value = (res.data.imports || []).join(', ')
    programs.value = res.data.programs.map(p => ({
      name: p.name,
      vars: p.vars,
      vars_text: formatVars(p.vars),
      pre: p.pre,
      post: p.post,
      body: p.body,
    }))
    selected.value = programs.value.length > 0 ? 0 : -1
  } catch (e) {
    toast({ type: 'error', data: 'Failed to load: ' + (e.message || e) })
  }
}

const new_file = async () => {
  const name = prompt('New program file name (without .imp):')
  if (!name) return
  theory_name.value = name
  imports_text.value = 'hoare'
  programs.value = [{ name: name, vars: [], vars_text: 'x: nat', pre: 'true', post: 'true', body: 'skip' }]
  current.value = name
  await verify_all()
  await load_files()
}

const toggle_edit = (idx) => {
  editing_prog.value = editing_prog.value === idx ? -1 : idx
}

const save_edit = () => {
  // Parse vars_text back to vars array
  const prog = programs.value[editing_prog.value]
  if (prog) {
    prog.vars = prog.vars_text.split(',').map(s => {
      const [nm, ty] = s.trim().split(':').map(x => x.trim())
      return [nm, ty]
    }).filter(v => v[0] && v[1])
  }
  editing_prog.value = -1
}

const add_program = () => {
  programs.value.push({ name: 'prog' + programs.value.length, vars: [], vars_text: 'x: nat', pre: 'true', post: 'true', body: 'skip' })
  selected.value = programs.value.length - 1
}

const remove_prog = (idx) => {
  programs.value.splice(idx, 1)
  if (selected.value >= programs.value.length) selected.value = programs.value.length - 1
}

const move_prog = (idx, dir) => {
  const ni = idx + dir
  if (ni < 0 || ni >= programs.value.length) return
  const tmp = programs.value[idx]
  programs.value[idx] = programs.value[ni]
  programs.value[ni] = tmp
}

const verify_all = async () => {
  if (!current.value) return
  verifying.value = true
  status_msg.value = ''
  try {
    const res = await api.post('/imp-compile', {
      name: current.value,
      theory: theory_name.value,
      imports: imports_text.value.split(',').map(s => s.trim()).filter(s => s),
      programs: programs.value.map(p => ({
        name: p.name,
        vars: p.vars,
        pre: p.pre,
        post: p.post,
        body: p.body,
      })),
    })
    if (!res.data.ok) {
      status_msg.value = res.data.error || 'compile failed'
      status_err.value = true
      return
    }
    vcs.value = res.data.vcs || []
    const green = vcs.value.filter(v => v.proved).length
    status_msg.value = `${current.value}: ${vcs.value.length} VCs (${green} proved, ${vcs.value.length - green} to prove)`
    status_err.value = false
  } catch (e) {
    status_msg.value = e.message || 'verify failed'
    status_err.value = true
  } finally {
    verifying.value = false
  }
}

const verify_program = async (idx) => {
  // Compile all programs (VCG is fast), then highlight this program's VCs.
  await verify_all()
  selected.value = idx
}

const prove_vc = async (vc, progName) => {
  if (!current.value) return
  try {
    const res = await api.post('/load-json-file', { filename: current.value, line_length: 80 })
    const content = res.data.content || []
    const item = content.find(it => it.name === vc.name)
    if (!item) { toast({ type: 'error', data: vc.name + ' not found' }); return }
    theorem_item.value = item
    proving_vc_name.value = vc.name
    proving.value = true
  } catch (e) {
    toast({ type: 'error', data: 'Failed to load: ' + (e.message || e) })
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
      content: { name: res.data.name, imports: res.data.imports || [], domains: res.data.domains || [], description: res.data.description || '', content }
    })
    const resp = await api.post('/validate-theory', { filename: current.value, force: false })
    const statuses = resp.data.statuses || {}
    const status = statuses[vcName] || 'PENDING'
    const vc = vcs.value.find(v => v.name === vcName)
    if (vc) vc.proved = (status === 'VALID')
    toast({ type: status === 'VALID' ? 'OK' : 'error', data: vcName + ': ' + status })
  } catch (e) {
    toast({ type: 'error', data: 'Failed to save: ' + (e.message || e) })
  }
}

const handle_query = (q) => { query.value = q }
const handle_query_ok = (vals) => { if (query.value && query.value.resolve) query.value.resolve(vals); query.value = undefined }
const handle_query_cancel = () => { if (query.value && query.value.resolve) query.value.resolve(undefined); query.value = undefined }

onMounted(async () => {
  await load_files()
  if (files.value.length > 0) await load_file(files.value[0].name)
})
</script>

<style scoped>
.program-ide { display: flex; flex-direction: column; height: 100vh; box-sizing: border-box; }
.file-select { min-width: 200px; max-width: 300px; }
.main-content { display: flex; flex: 1; min-height: 0; }
.program-panel { flex: 1; overflow-y: auto; padding: 8px; }
.proving-mode .program-panel { flex: 55%; }
.empty-state { text-align: center; padding: 40px; color: #999; }

.metadata-section { background: #f5f7fa; border: 1px solid #e1e5eb; border-radius: 4px; padding: 8px; margin-bottom: 12px; }
.meta-row { display: flex; align-items: center; gap: 8px; }
.meta-label { font-weight: 600; font-size: 12px; min-width: 50px; color: #555; }
.meta-input { flex: 1; padding: 3px 6px; font-size: 13px; border: 1px solid #ccc; border-radius: 3px; }

.programs-list { display: flex; flex-direction: column; gap: 8px; }
.program-block { border: 1px solid #dee2e6; border-radius: 4px; overflow: hidden; }
.program-selected { border-color: #0d6efd; }
.program-header { display: flex; align-items: center; gap: 8px; padding: 6px 10px; background: #f8f9fa; cursor: pointer; }
.prog-name { font-weight: 600; font-size: 13px; min-width: 80px; }
.prog-vars { font-size: 12px; color: #666; font-family: Consolas, monospace; flex: 1; }
.prog-actions { display: flex; gap: 4px; }
.prog-summary { display: flex; gap: 16px; padding: 4px 10px; font-size: 12px; color: #555; font-family: Consolas, monospace; background: #fff; }
.prog-pre, .prog-post { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 50%; }

.prog-edit { padding: 10px; background: #fff; border-top: 1px solid #e1e5eb; }
.edit-row { display: flex; align-items: flex-start; gap: 8px; margin-bottom: 6px; }
.edit-row label { font-weight: 600; font-size: 12px; min-width: 40px; padding-top: 5px; }
.edit-input { flex: 1; padding: 4px 8px; font-size: 13px; border: 1px solid #ccc; border-radius: 3px; font-family: Consolas, monospace; }
.edit-body { flex: 1; padding: 4px 8px; font-size: 13px; border: 1px solid #ccc; border-radius: 3px; font-family: Consolas, monospace; resize: vertical; }
.edit-actions { display: flex; gap: 8px; margin-top: 8px; }

.vc-list { padding: 4px 10px 8px; }
.vc-row { display: flex; align-items: baseline; gap: 8px; padding: 4px 8px; border-radius: 3px; margin-bottom: 4px; font-size: 12px; }
.vc-ok { background: #f0faf0; border-left: 3px solid #28a745; }
.vc-bad { background: #fdf0f0; border-left: 3px solid #dc3545; }
.vc-badge { font-weight: 700; }
.vc-ok .vc-badge { color: #28a745; }
.vc-bad .vc-badge { color: #dc3545; }
.vc-name { font-family: Consolas, monospace; color: #666; flex-shrink: 0; min-width: 120px; }
.vc-prop { font-family: Consolas, monospace; color: #333; flex: 1; overflow-wrap: anywhere; }
.vc-prove { flex-shrink: 0; }

.bottom-actions { display: flex; gap: 8px; padding: 12px 0; }
.proof-panel { width: 45%; min-width: 400px; border-left: 1px solid #dee2e6; display: flex; flex-direction: column; flex-shrink: 0; }
.proof-pane-header { display: flex; align-items: center; justify-content: space-between; padding: 6px 10px; border-bottom: 1px solid #dee2e6; font-size: 13px; flex-shrink: 0; }

.modal-overlay { position: fixed; inset: 0; background: rgba(0,0,0,0.4); display: flex; align-items: center; justify-content: center; z-index: 1000; }
.modal-content { background: white; border-radius: 6px; width: 480px; max-width: 90vw; box-shadow: 0 4px 12px rgba(0,0,0,0.2); }
.modal-header { display: flex; align-items: center; justify-content: space-between; padding: 10px 16px; border-bottom: 1px solid #dee2e6; }
.modal-body { padding: 12px 16px; }
.toast { position: fixed; top: 16px; right: 16px; display: flex; align-items: center; gap: 8px; padding: 10px 14px; border-radius: 4px; font-size: 13px; box-shadow: 0 2px 8px rgba(0,0,0,0.2); z-index: 1100; }
.toast-ok { background: #d4edda; color: #155724; border: 1px solid #c3e6cb; }
.toast-error { background: #f8d7da; color: #721c24; border: 1px solid #f5c6cb; }
.toast-close { background: none; border: none; font-size: 14px; cursor: pointer; }
</style>

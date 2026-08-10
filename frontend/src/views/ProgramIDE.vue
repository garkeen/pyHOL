<template>
  <div class="program-ide">
    <!-- Top bar -->
    <nav class="navbar navbar-expand navbar-dark bg-dark">
      <div class="container-fluid">
        <span class="navbar-brand" style="padding-left: 44px">Program IDE</span>
      </div>
    </nav>

    <div class="main-content">
      <!-- Collapsible sidebar: file selection and management -->
      <FileSidebar
        title="Program Files"
        :files="files.map(f => f.name)"
        :active="current"
        :show-create="true"
        @open="load_file"
        @create="new_file"
        @rename="rename_file"
        @delete="delete_file"/>

      <!-- Program list -->
      <div class="program-panel">
        <div v-if="!current" class="empty-state"><p>Select or create a file</p></div>
        <div v-else>
          <!-- File header: actions + metadata, like the main IDE -->
          <div class="file-header">
            <div class="file-header-row">
              <button class="btn btn-sm btn-primary" @click="verify_all" :disabled="verifying">{{ verifying ? 'Verifying...' : 'Verify All' }}</button>
              <span class="text-muted small" v-if="status_msg" :class="status_err ? 'text-danger' : 'text-success'">{{ status_msg }}</span>
              <button class="btn btn-sm btn-success ms-auto" @click="add_program" title="Add a new program to this file">+ Add Program</button>
            </div>
            <div class="metadata-section">
              <div class="meta-row"><label class="meta-label">theory</label><span class="meta-value">{{ theory_name }}</span></div>
              <div class="meta-row"><label class="meta-label">imports</label><input class="meta-input" v-model="imports_text" placeholder="comma-separated"/></div>
            </div>
          </div>

          <!-- Programs list: name + pre/post only -->
          <div class="programs-list">
            <div v-for="(prog, idx) in programs" :key="idx"
                 class="program-row" :class="{'program-selected': selected === idx, 'prog-ok': prog_status(prog) === 'ok', 'prog-bad': prog_status(prog) === 'bad'}"
                 @click="open_prog(idx)">
              <span class="prog-status" :title="prog_status_title(prog)">{{ prog_status_icon(prog) }}</span>
              <span class="prog-name">{{ prog.name }}</span>
              <span class="prog-sum">{{ prog.pre }}</span>
              <span class="prog-sum prog-post">{{ prog.post }}</span>
              <div class="prog-actions">
                <button class="btn btn-sm btn-outline-secondary" @click.stop="open_prog(idx)" title="Edit">Edit</button>
                <button class="btn btn-sm btn-outline-warning" @click.stop="move_prog(idx, -1)" :disabled="idx === 0" title="Move up">↑</button>
                <button class="btn btn-sm btn-outline-warning" @click.stop="move_prog(idx, 1)" :disabled="idx === programs.length - 1" title="Move down">↓</button>
                <button class="btn btn-sm btn-outline-danger" @click.stop="remove_prog(idx)" title="Delete">✕</button>
              </div>
            </div>
          </div>
        </div>
      </div>

      <!-- Right edit panel: code editing + verification (proof overlays inside) -->
      <div v-if="panel_prog" class="edit-panel">
        <div class="edit-pane-header">
          <span class="edit-pane-title">Program <b class="prog-name-inline">{{ panel_prog.name }}</b></span>
          <div class="edit-pane-btns">
            <button class="btn btn-sm btn-primary" @click="save_verify" :disabled="verifying">{{ verifying ? 'Verifying...' : 'Verify' }}</button>
            <button class="btn btn-sm btn-outline-secondary" @click="panel_idx = -1" title="Close">✕</button>
          </div>
        </div>

        <div class="edit-scroll">
          <div class="prog-edit">
            <div class="section-title">Program</div>
            <div class="edit-grid">
              <div class="edit-field">
                <label>Name</label>
                <input class="edit-input" v-model="panel_prog.name"/>
              </div>
              <div class="edit-field">
                <label>Variables</label>
                <input class="edit-input" v-model="panel_prog.vars_text" placeholder="x: nat, y: nat"/>
              </div>
              <div class="edit-field">
                <label>Precondition</label>
                <input class="edit-input" v-model="panel_prog.pre"/>
              </div>
              <div class="edit-field">
                <label>Postcondition</label>
                <input class="edit-input" v-model="panel_prog.post"/>
              </div>
            </div>

            <div class="section-title mt-3">Body</div>
            <div class="code-editor">
              <pre ref="hlEl" class="code-hl" aria-hidden="true" v-html="bodyHtml"></pre>
              <textarea
                class="code-input" v-model="panel_prog.body" spellcheck="false" rows="12"
                @scroll="syncHl"></textarea>
            </div>

            <div class="edit-actions">
              <button class="btn btn-sm btn-primary" @click="save_edit">Save</button>
              <button class="btn btn-sm btn-outline-secondary" @click="panel_idx = -1">Close</button>
            </div>
          </div>

          <!-- VCs for this program -->
          <div class="panel-vcs">
            <div class="panel-vc-title">Verification conditions</div>
            <div v-if="!vcs_by_program[panel_prog.name] || !vcs_by_program[panel_prog.name].length" class="vc-empty">No VCs yet, click Verify.</div>
            <div v-for="vc in vcs_by_program[panel_prog.name] || []" :key="vc.name"
                 class="vc-card" :class="vc.proved ? 'vc-ok' : 'vc-bad'">
              <div class="vc-line">
                <span class="vc-badge">{{ vc.proved ? '✓' : '✗' }}</span>
                <span class="vc-name">{{ vc.name }}</span>
                <button v-if="!vc.proved" class="btn btn-sm btn-outline-danger vc-prove" @click.stop="prove_vc(vc, panel_prog.name)">Prove</button>
                <span v-else class="vc-proved-tag">proved</span>
              </div>
              <div class="vc-prop">{{ vc.prop }}</div>
            </div>
          </div>
        </div>

        <!-- Proof overlay: covers the edit panel instead of squeezing a new column -->
        <div v-if="proving && theorem_item" class="proof-overlay">
          <div class="proof-overlay-header">
            <button class="btn btn-sm btn-outline-secondary" @click="proving = false" title="Back to edit">←</button>
            <span>Prove <b>{{ proving_vc_name }}</b></span>
            <button class="btn btn-sm btn-outline-secondary ms-auto" @click="proving = false" title="Close">✕</button>
          </div>
          <div class="proof-overlay-body">
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
import FileSidebar from '../components/FileSidebar.vue'

const files = ref([])
const current = ref('')
const theory_name = ref('')
const imports_text = ref('')
const programs = ref([])
const panel_idx = ref(-1)
const selected = ref(-1)
const hlEl = ref(null)
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

const panel_prog = computed(() => {
  if (panel_idx.value < 0 || panel_idx.value >= programs.value.length) return null
  return programs.value[panel_idx.value]
})

const escHtml = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')

const HIGHLIGHT_PATTERNS = [
  { re: /\/\/[^\n]*|#[^\n]*/g, cls: 'tok-com', esc: true },
  { re: /\b\d+\b/g, cls: 'tok-num', esc: false },
  { re: /\b(skip|if|then|else|while|for|break|continue|assert|call|new|true|forall)\b/g, cls: 'tok-kw', esc: false },
  { re: /(:=|==|!=|<=|>=|-->|\+\+|--|\+|-|\*|\/|=|<|>|&|\||~|!)/g, cls: 'tok-op', esc: true },
]

const bodyHtml = computed(() => {
  const src = panel_prog.value ? panel_prog.value.body : ''
  const toks = []
  for (const p of HIGHLIGHT_PATTERNS) {
    p.re.lastIndex = 0
    let m
    while ((m = p.re.exec(src))) toks.push({ s: m.index, e: m.index + m[0].length, text: m[0], p })
  }
  toks.sort((a, b) => a.s - b.s || a.e - b.e)
  let out = ''
  let last = 0
  for (const t of toks) {
    if (t.s < last) continue
    out += escHtml(src.slice(last, t.s))
    out += '<span class="' + t.p.cls + '">' + (t.p.esc ? escHtml(t.text) : t.text) + '</span>'
    last = t.e
  }
  out += escHtml(src.slice(last))
  return out + '\n'
})

const syncHl = (e) => {
  if (hlEl.value) {
    hlEl.value.scrollTop = e.target.scrollTop
    hlEl.value.scrollLeft = e.target.scrollLeft
  }
}

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

const prog_status = (prog) => {
  const prog_vcs = vcs_by_program.value[prog.name]
  if (!prog_vcs || !prog_vcs.length) return 'none'
  return prog_vcs.every(v => v.proved) ? 'ok' : 'bad'
}

const prog_status_icon = (prog) => ({
  'ok': '✓', 'bad': '✗', 'none': '○'
}[prog_status(prog)])

const prog_status_title = (prog) => {
  const prog_vcs = vcs_by_program.value[prog.name]
  if (!prog_vcs || !prog_vcs.length) return 'Not verified'
  const n = prog_vcs.length
  const k = prog_vcs.filter(v => v.proved).length
  return `${k}/${n} VCs proved`
}

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
  panel_idx.value = -1
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
    if (current.value === oldName) {
      await load_file(newName)
    }
    toast({ type: 'OK', data: `Renamed to ${newName}` })
  } catch (e) {
    toast({ type: 'error', data: 'Rename failed' })
  }
}

const delete_file = async (name) => {
  if (!name) return
  if (!confirm(`Delete file "${name}"? This cannot be undone.`)) return
  try {
    await api.put('/remove-file', { filename: name })
    await load_files()
    if (current.value === name) {
      current.value = ''
      programs.value = []
      vcs.value = []
      proving.value = false
      panel_idx.value = -1
    }
    toast({ type: 'OK', data: 'File deleted' })
  } catch (e) {
    toast({ type: 'error', data: 'Failed to delete file' })
  }
}

const open_prog = (idx) => {
  panel_idx.value = idx
  selected.value = idx
}

const save_edit = () => {
  const prog = panel_prog.value
  if (!prog) return
  prog.vars = prog.vars_text.split(',').map(s => {
    const [nm, ty] = s.trim().split(':').map(x => x.trim())
    return [nm, ty]
  }).filter(v => v[0] && v[1])
}

const save_verify = async () => {
  save_edit()
  selected.value = panel_idx.value
  await verify_all()
}

const add_program = () => {
  const prog = { name: 'prog' + programs.value.length, vars: [], vars_text: 'x: nat', pre: 'true', post: 'true', body: 'skip' }
  programs.value.push(prog)
  panel_idx.value = programs.value.length - 1
  selected.value = panel_idx.value
}

const remove_prog = (idx) => {
  programs.value.splice(idx, 1)
  if (panel_idx.value === idx) panel_idx.value = -1
  else if (panel_idx.value > idx) panel_idx.value -= 1
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
.main-content { display: flex; flex: 1; min-height: 0; }

.program-panel { flex: 1; overflow-y: auto; padding: 10px; min-width: 0; }
.empty-state { text-align: center; padding: 40px; color: #999; }

.file-header { margin-bottom: 12px; }
.file-header-row { display: flex; align-items: center; gap: 8px; margin-bottom: 10px; }
.metadata-section { background: #f5f7fa; border: 1px solid #e1e5eb; border-radius: 4px; padding: 8px; margin-bottom: 12px; }
.meta-row { display: flex; align-items: center; gap: 8px; margin-bottom: 6px; }
.meta-row:last-child { margin-bottom: 0; }
.meta-label { font-weight: 600; font-size: 12px; min-width: 70px; color: #555; }
.meta-value { font-size: 13px; color: #212529; }
.meta-input { flex: 1; padding: 3px 6px; font-size: 13px; border: 1px solid #ccc; border-radius: 3px; }

.programs-list { display: flex; flex-direction: column; }
.program-row {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 4px 10px;
  border-bottom: 1px solid #e8e8e8;
  cursor: pointer;
  font-size: 13px;
}
.program-row:hover { background: #f8f9fa; }
.program-selected { background: #e8f0fe !important; }
.prog-status { font-size: 14px; flex-shrink: 0; }
.prog-ok .prog-status { color: #28a745; }
.prog-bad .prog-status { color: #dc3545; }
.prog-name { font-weight: 600; font-family: Consolas, monospace; min-width: 120px; flex-shrink: 0; }
.prog-sum { color: #666; font-family: Consolas, monospace; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 30%; }
.prog-actions { margin-left: auto; display: flex; gap: 3px; flex-shrink: 0; }
.prog-actions .btn { padding: 1px 7px; font-size: 11px; }

/* Right edit panel: 60%, proof overlays inside instead of a new column */
.edit-panel { position: relative; flex: 0 0 60%; min-width: 480px; border-left: 1px solid #dee2e6; display: flex; flex-direction: column; overflow: hidden; background: #fff; }
.edit-pane-header { display: flex; align-items: center; justify-content: space-between; padding: 10px 16px; border-bottom: 1px solid #e9ecef; font-size: 13px; flex-shrink: 0; background: #fafbfc; }
.edit-pane-title { color: #495057; }
.prog-name-inline { color: #1a73e8; }
.edit-pane-btns { display: flex; gap: 6px; }

.edit-scroll { flex: 1; overflow-y: auto; }
.prog-edit { padding: 16px; }

.section-title {
  font-size: 11px; font-weight: 700; text-transform: uppercase; letter-spacing: 0.06em;
  color: #6c757d; margin-bottom: 10px;
  display: flex; align-items: center; gap: 8px;
}
.section-title::before { content: ''; width: 3px; height: 12px; background: #1a73e8; border-radius: 2px; }

.edit-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 12px 16px; }
.edit-field { display: flex; flex-direction: column; }
.edit-field label { font-size: 11px; font-weight: 600; color: #6c757d; margin-bottom: 4px; }

.edit-input {
  width: 100%; padding: 7px 10px; font-size: 13px; font-family: Consolas, 'Courier New', monospace;
  border: 1px solid #ced4da; border-radius: 6px; background: #fff; color: #212529;
  transition: border-color 0.15s, box-shadow 0.15s;
}
.edit-input:focus { border-color: #1a73e8; box-shadow: 0 0 0 3px rgba(26, 115, 232, 0.15); outline: none; }

/* Body editor: white background with keyword highlighting */
.code-editor {
  position: relative;
  background: #fff; border: 1px solid #ced4da; border-radius: 8px;
  transition: border-color 0.15s, box-shadow 0.15s;
}
.code-editor:focus-within { border-color: #1a73e8; box-shadow: 0 0 0 3px rgba(26, 115, 232, 0.15); }
.code-hl, .code-input {
  margin: 0; padding: 12px;
  font-family: Consolas, 'Courier New', monospace; font-size: 13px; line-height: 1.55;
  letter-spacing: normal; word-break: break-word; overflow-wrap: break-word; white-space: pre-wrap;
}
.code-hl {
  position: absolute; inset: 0; overflow: hidden;
  color: #24292f; pointer-events: none; z-index: 0;
}
.code-hl ::selection { background: transparent; }
.code-input {
  position: relative; z-index: 1; display: block; width: 100%; box-sizing: border-box;
  height: 220px; overflow: auto;
  background: transparent; color: transparent; caret-color: #1a73e8;
  border: none; outline: none; resize: none;
}
.code-input::selection { background: rgba(26, 115, 232, 0.25); color: transparent; }
.code-hl :deep(.tok-com) { color: #6a737d; font-style: italic; }
.code-hl :deep(.tok-num) { color: #b35900; }
.code-hl :deep(.tok-kw) { color: #0550ae; font-weight: 600; }
.code-hl :deep(.tok-op) { color: #a626a4; }

.edit-actions { display: flex; gap: 8px; margin-top: 12px; }

/* VCs */
.panel-vcs { border-top: 1px solid #e9ecef; padding: 12px 16px; background: #f6f8fa; }
.panel-vc-title { font-size: 11px; font-weight: 700; text-transform: uppercase; letter-spacing: 0.06em; color: #6c757d; margin-bottom: 8px; display: flex; align-items: center; gap: 8px; }
.panel-vc-title::before { content: ''; width: 3px; height: 12px; background: #6c757d; border-radius: 2px; }
.vc-empty { color: #999; font-size: 12px; font-style: italic; }
.vc-card {
  background: #fff; border: 1px solid #e5e9f0; border-left: 3px solid #adb5bd; border-radius: 6px;
  padding: 8px 12px; margin-bottom: 6px; box-shadow: 0 1px 2px rgba(0,0,0,0.04);
}
.vc-card.vc-ok { border-left-color: #28a745; }
.vc-card.vc-bad { border-left-color: #dc3545; }
.vc-line { display: flex; align-items: center; gap: 8px; }
.vc-badge { font-weight: 700; flex-shrink: 0; }
.vc-ok .vc-badge { color: #28a745; }
.vc-bad .vc-badge { color: #dc3545; }
.vc-name { font-family: Consolas, monospace; color: #495057; flex-shrink: 0; font-weight: 600; }
.vc-prop { font-family: Consolas, monospace; color: #666; margin-top: 4px; font-size: 11px; overflow-wrap: anywhere; }
.vc-prove { margin-left: auto; }
.vc-proved-tag { margin-left: auto; font-size: 11px; color: #28a745; font-weight: 600; }

/* Proof overlay: covers the edit panel, back arrow returns to editing */
.proof-overlay { position: absolute; inset: 0; background: #fff; display: flex; flex-direction: column; z-index: 5; }
.proof-overlay-header { display: flex; align-items: center; gap: 10px; padding: 8px 14px; border-bottom: 1px solid #dee2e6; font-size: 13px; flex-shrink: 0; background: #fafbfc; }
.proof-overlay-body { flex: 1; overflow: hidden; display: flex; flex-direction: column; }

.modal-overlay { position: fixed; inset: 0; background: rgba(0,0,0,0.4); display: flex; align-items: center; justify-content: center; z-index: 1000; }
.modal-content { background: white; border-radius: 6px; width: 480px; max-width: 90vw; box-shadow: 0 4px 12px rgba(0,0,0,0.2); }
.modal-header { display: flex; align-items: center; justify-content: space-between; padding: 10px 16px; border-bottom: 1px solid #dee2e6; }
.modal-body { padding: 12px 16px; }
.toast { position: fixed; top: 16px; right: 16px; display: flex; align-items: center; gap: 8px; padding: 10px 14px; border-radius: 4px; font-size: 13px; box-shadow: 0 2px 8px rgba(0,0,0,0.2); z-index: 1100; }
.toast-ok { background: #d4edda; color: #155724; border: 1px solid #c3e6cb; }
.toast-error { background: #f8d7da; color: #721c24; border: 1px solid #f5c6cb; }
.toast-close { background: none; border: none; font-size: 14px; cursor: pointer; }
</style>
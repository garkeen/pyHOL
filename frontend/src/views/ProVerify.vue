<template>
  <div class="verify-container">
    <!-- Menu -->
    <nav class="navbar navbar-light bg-info">
      <div class="container-fluid">
        <span class="navbar-brand">Program Verification</span>
        <div class="navbar-nav">
          <div class="nav-item dropdown">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">File</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="open_file_prompt">Open file</a></li>
            </ul>
          </div>
          <div class="nav-item dropdown" v-if="ref_proof">
            <a class="nav-link dropdown-toggle" href="#" role="button" data-bs-toggle="dropdown">Proof</a>
            <ul class="dropdown-menu">
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('cut')">Insert goal</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('cases')">Apply cases</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('induction')">Apply induction</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('introduction')">Introduction</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('new_var')">New variable</a></li>
              <li><hr class="dropdown-divider"></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('apply_backward_step')">Backward step</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('apply_forward_step')">Forward step</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('rewrite_goal')">Rewrite goal</a></li>
              <li><a class="dropdown-item" href="#" @click.prevent="apply_method('rewrite_fact')">Rewrite fact</a></li>
            </ul>
          </div>
        </div>
        <span class="text-light ms-3" v-if="file_name">File: {{ file_name }}</span>
      </div>
    </nav>

    <div class="main-content">
      <!-- 左侧文件列表 -->
      <div class="left-panel">
        <div class="panel-section">
          <h6 class="panel-title">Programs</h6>
          <div class="file-list">
            <div v-for="(item, index) in file_data" :key="index">
              <div v-if="item.ty === 'vcg'" class="file-item" 
                   :class="{active: cur_index === index}"
                   @click="init_program(index)">
                <pre class="code-preview">{{ item.com.substring(0, 50) }}...</pre>
              </div>
            </div>
          </div>
        </div>
        
        <!-- 证明上下文 -->
        <div v-show="ref_proof" class="panel-section">
          <h6 class="panel-title">Context</h6>
          <ProofContext ref="ref_context" :ref_proof="ref_proof"/>
        </div>
      </div>

      <!-- 中间面板：程序展示 -->
      <div class="center-panel">
        <div v-if="!file_data || file_data.length === 0" class="empty-state">
          <h4>Click File > Open to load a program file</h4>
        </div>
        <div v-else>
          <Program :lines="lines" :editor="editor"
                   :ref_status="ref_status" :ref_context="ref_context"
                   @set-proof="handle_set_proof"
                   @query="handle_query"
                   @save-proof="handle_save_proof"
                   @set-message="onSetMessage"/>
        </div>
      </div>

      <!-- 右侧面板 -->
      <div class="right-panel">
        <!-- 消息 -->
        <div v-if="message" class="panel-section message-section">
          <div class="alert" :class="{'alert-danger': message.type === 'error', 'alert-info': message.type !== 'error'}">
            {{ message.data }}
          </div>
        </div>
        
        <!-- 证明状态 -->
        <div v-show="ref_proof" class="panel-section">
          <h6 class="panel-title">Proof Status</h6>
          <ProofStatus ref="ref_status" :ref_proof="ref_proof"/>
        </div>
      </div>
    </div>

    <!-- 查询对话框 -->
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
  </div>
</template>

<script setup>
import { ref, onMounted } from 'vue'
import api from '../api'
import Program from '../components/Program.vue'
import ProofStatus from '../components/proof/ProofStatus.vue'
import ProofContext from '../components/proof/ProofContext.vue'
import ProofQuery from '../components/proof/ProofQuery.vue'

const file_name = ref('')
const file_data = ref([])
const cur_index = ref(undefined)
const lines = ref([])
const ref_proof = ref(null)
const ref_status = ref(null)
const ref_context = ref(null)
const query = ref(undefined)
const message = ref(undefined)
const editor = ref({})

const handle_set_proof = (proof_ref) => {
  ref_proof.value = proof_ref
}

const handle_save_proof = async (proof) => {
  try {
    await api.post('/save-program-proof', {
      file_name: file_name.value,
      index: cur_index.value,
      proof: proof
    })
    message.value = { type: 'OK', data: 'Proof saved' }
  } catch (err) {
    message.value = { type: 'error', data: 'Failed to save proof' }
  }
}

const handle_query = (q) => {
  query.value = q
}

const handle_query_ok = (vals) => {
  if (query.value && query.value.resolve) {
    query.value.resolve(vals)
  }
  query.value = undefined
}

const handle_query_cancel = () => {
  if (query.value && query.value.resolve) {
    query.value.resolve(undefined)
  }
  query.value = undefined
}

const onSetMessage = (msg) => {
  message.value = msg
}

const open_file_prompt = () => {
  const name = prompt('Please enter file name', 'test')
  if (name) {
    open_file(name)
  }
}

const open_file = async (name) => {
  file_name.value = name
  try {
    const response = await api.post('/get-program-file', {
      file_name: name
    })
    file_data.value = response.data.file_data
    editor.value = { filename: name }
  } catch (err) {
    message.value = { type: 'error', data: 'Failed to load file' }
  }
}

const init_program = async (index) => {
  const data = file_data.value[index]
  try {
    const response = await api.post('/program-verify', data)
    cur_index.value = index
    lines.value = response.data.lines
  } catch (err) {
    message.value = { type: 'error', data: 'Failed to verify program' }
  }
}

const apply_method = (method_name) => {
  if (ref_proof.value) {
    ref_proof.value.apply_method(method_name)
  }
}

onMounted(() => {
  open_file('test')
})
</script>

<style scoped>
.verify-container {
  height: 100vh;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

.main-content {
  flex: 1;
  display: flex;
  overflow: hidden;
}

.left-panel {
  width: 250px;
  min-width: 250px;
  border-right: 1px solid #dee2e6;
  overflow-y: auto;
  background: #f8f9fa;
}

.center-panel {
  flex: 1;
  overflow-y: auto;
  padding: 15px;
}

.right-panel {
  width: 300px;
  min-width: 300px;
  border-left: 1px solid #dee2e6;
  overflow-y: auto;
  background: #f8f9fa;
}

.panel-section {
  padding: 10px;
  border-bottom: 1px solid #dee2e6;
}

.panel-title {
  font-weight: bold;
  color: #495057;
  margin-bottom: 10px;
  padding-bottom: 5px;
  border-bottom: 2px solid #007bff;
}

.file-list {
  max-height: calc(100vh - 120px);
  overflow-y: auto;
}

.file-item {
  padding: 8px 12px;
  cursor: pointer;
  border-radius: 4px;
  margin-bottom: 2px;
}

.file-item:hover {
  background: #e9ecef;
}

.file-item.active {
  background: #007bff;
  color: white;
}

.code-preview {
  font-size: 11px;
  font-family: Consolas, monospace;
  margin: 0;
  white-space: pre-wrap;
  word-break: break-all;
}

.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  color: #6c757d;
}

.message-section {
  padding: 10px;
}

.message-section .alert {
  margin: 0;
  font-size: 14px;
}

.modal-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0,0,0,0.5);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1050;
}

.modal-content {
  background: white;
  border-radius: 8px;
  width: 500px;
  max-width: 90%;
  box-shadow: 0 4px 20px rgba(0,0,0,0.15);
}

.modal-header {
  padding: 15px 20px;
  border-bottom: 1px solid #dee2e6;
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.modal-body {
  padding: 20px;
}
</style>

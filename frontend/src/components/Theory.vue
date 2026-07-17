<template>
  <div v-if="theory" class="theory-content">
    <!-- 理论头 -->
    <div class="theory-header">
      <div>
        <span class="keyword">theory</span>&nbsp;<span>{{ theory.name }}</span>
        <a href="#" @click.prevent="start_edit_metadata" title="edit metadata" class="edit-icon">
          &#9998;
        </a>
      </div>
      <span class="keyword">imports</span>
      <span v-for="(import_name, index) in theory.imports" :key="index"
            @click="$emit('goto-link', import_name)"
            class="import-link">{{ import_name }}</span>
      <br><br>
      <span class="comment">{{ theory.description }}</span>
      <br><br>
    </div>
    
    <!-- 元数据编辑 -->
    <div v-if="edit_metadata">
      <MetadataEdit :theory="theory" ref="meta_edit_ref"/>
      <div style="margin-top:5px">
        <button class="btn btn-sm btn-primary" @click="save_metadata">Save</button>
        <button class="btn btn-sm btn-secondary" style="margin-left:5px" @click="edit_metadata = false">Cancel</button>
      </div>
    </div>
    
    <!-- 理论项列表 -->
    <div v-for="(item, index) in theory.content" :key="index">
      <!-- Header项 -->
      <div v-if="item.ty === 'header'">
        <span class="header-item">{{ item.name }}</span>
      </div>
      
      <!-- 其他项：显示ItemHeader -->
      <div v-else>
        <ItemHeader :item="item" 
                    :index="index"
                    :status="getStatus(item)"
                    :selected="selected_index === index"
                    :is-editing="isEditing(index)"
                    :is-proving="isProving(index)"
                    @toggle-edit="$emit('toggle-edit', index)"
                    @toggle-prove="$emit('toggle-prove', index)"
                    @click="$emit('select-item', index)"/>
        
        <!-- 编辑表单 -->
        <div v-if="isEditing(index)" class="edit-section">
          <ConstantEdit v-if="item.ty === 'def.ax'" :old_item="item.edit" :ref="(el) => { if (el) edit_ref = el }"/>
          <DefinitionEdit v-else-if="item.ty === 'def'" :old_item="item.edit" :ext="item.ext" :ref="(el) => { if (el) edit_ref = el }"/>
          <DatatypeEdit v-else-if="item.ty === 'type.ind'" :old_item="item.edit" :ext="item.ext" :ref="(el) => { if (el) edit_ref = el }"/>
          <InductiveEdit v-else-if="item.ty === 'def.ind' || item.ty === 'def.pred'" :old_item="item.edit" :ref="(el) => { if (el) edit_ref = el }"/>
          <TheoremEdit v-else-if="item.ty === 'thm' || item.ty === 'thm.ax'" :old_item="item.edit" :ref="(el) => { if (el) edit_ref = el }"/>
          
          <div style="margin-top:5px">
            <button class="btn btn-sm btn-primary" @click="check_edit">Check</button>
            <button class="btn btn-sm btn-success" style="margin-left:5px" @click="save_edit">Save</button>
          </div>
        </div>
        
        <!-- 证明区域 -->
        <div v-if="isProving(index)" class="proof-section">
          <ProofArea :key="'proof-' + theory.name + '-' + item.name + '-' + index"
                     :theory_name="theory.name" :thm_name="item.name"
                     :vars="item.vars" :prop="item.prop"
                     :old_steps="item.steps"
                     :ref="(el) => { if (el) proof = el }"
                     @set-message="$emit('set-message', $event)"
                     @set-status="$emit('set-status', $event)"
                     @set-context="$emit('set-context', $event)"
                     @query="$emit('query', $event)"
                     @set-proof="$emit('set-proof', $event)"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref } from 'vue'
import api from '../api'
import ItemHeader from './items/ItemHeader.vue'
import ConstantEdit from './items/ConstantEdit.vue'
import DefinitionEdit from './items/DefinitionEdit.vue'
import DatatypeEdit from './items/DatatypeEdit.vue'
import InductiveEdit from './items/InductiveEdit.vue'
import TheoremEdit from './items/TheoremEdit.vue'
import MetadataEdit from './items/MetadataEdit.vue'
import ProofArea from './proof/ProofArea.vue'

const props = defineProps({
  theory: {
    type: Object,
    default: undefined
  },
  active_index: {
    type: Number,
    default: -1
  },
  selected_index: {
    type: Number,
    default: -1
  },
  ui_state: {
    type: String,
    default: 'BROWSE'
  },
  theorem_status: {
    type: Object,
    default: () => ({})
  }
})

const emit = defineEmits([
  'set-message', 'set-proof', 'set-status', 'set-context',
  'query', 'goto-link', 'save-file', 'toggle-edit', 'toggle-prove',
  'edit-submit', 'select-item'
])
const edit_metadata = ref(false)
const meta_edit_ref = ref(null)
let edit_ref = null  // set by function ref in template
let proof = null     // set by function ref in template

const isEditing = (index) => {
  return props.ui_state === 'EDIT' && props.active_index === index
}

const isProving = (index) => {
  return props.ui_state === 'PROVE' && props.active_index === index
}

const getStatus = (item) => {
  return props.theorem_status[item.name] || null
}

const start_edit_metadata = () => {
  edit_metadata.value = true
}

const save_metadata = () => {
  if (meta_edit_ref.value) {
    const data = meta_edit_ref.value.getData()
    props.theory.name = data.name
    props.theory.imports = data.imports
    props.theory.description = data.description
  }
  edit_metadata.value = false
  emit('save-file')
}

const check_edit = async () => {
  console.log('[check_edit] called, edit_ref:', edit_ref)
  if (!edit_ref) {
    emit('set-message', { type: 'error', data: 'Error: edit form not ready' })
    return
  }
  
  const current_item = props.theory.content[props.active_index]
  const form_data = edit_ref.getData()
  console.log('[check_edit] form_data:', JSON.stringify(form_data))
  
  const is_new = !current_item.name || !props.theory.content.some(
    (it, i) => i !== props.active_index && it.name === current_item.name
  )
  
  const data = {
    filename: props.theory.name,
    line_length: 80,
    item: form_data
  }
  if (!is_new) {
    data.limit_ty = current_item.ty
    data.limit_name = current_item.name
  }
  
  emit('set-message', { type: 'OK', data: 'Checking...' })
  console.log('[check_edit] sending to /check-modify')
  
  try {
    const response = await api.post('/check-modify', data)
    console.log('[check_edit] response:', JSON.stringify(response.data))
    const item = response.data.item
    
    if ('error' in item) {
      emit('set-message', {
        type: 'error',
        data: item.error.err_type + ': ' + item.error.err_str
      })
    } else {
      emit('set-message', { type: 'OK', data: 'Check passed - no errors' })
    }
  } catch (err) {
    console.error('[check_edit] exception:', err)
    const errDetail = err.response?.data?.error || err.message || 'Unknown error'
    emit('set-message', { type: 'error', data: 'Check failed: ' + errDetail })
  }
}

const save_edit = async () => {
  console.log('[save_edit] called, edit_ref:', edit_ref)
  if (!edit_ref) {
    emit('set-message', { type: 'error', data: 'Error: edit form not ready' })
    return
  }
  
  const current_item = props.theory.content[props.active_index]
  const form_data = edit_ref.getData()
  console.log('[save_edit] form_data:', JSON.stringify(form_data))
  
  if (!form_data.name) {
    emit('set-message', { type: 'error', data: 'Error: theorem name is required' })
    return
  }
  if (!form_data.prop) {
    emit('set-message', { type: 'error', data: 'Error: proposition (shows) is required' })
    return
  }
  
  const is_new = !current_item.name || !props.theory.content.some(
    (it, i) => i !== props.active_index && it.name === current_item.name
  )
  console.log('[save_edit] is_new:', is_new)
  
  const data = {
    filename: props.theory.name,
    line_length: 80,
    item: form_data
  }
  if (!is_new) {
    data.limit_ty = current_item.ty
    data.limit_name = current_item.name
  }
  
  emit('set-message', { type: 'OK', data: 'Saving...' })
  console.log('[save_edit] sending to /check-modify:', JSON.stringify(data))
  
  try {
    const response = await api.post('/check-modify', data)
    console.log('[save_edit] response:', JSON.stringify(response.data))
    const new_item = response.data.item
    
    if ('error' in new_item) {
      console.log('[save_edit] backend error:', new_item.error)
      emit('set-message', {
        type: 'error',
        data: new_item.error.err_type + ': ' + new_item.error.err_str
      })
      return
    }
    
    if (current_item.ty === 'thm') {
      new_item.steps = current_item.steps
    }
    
    console.log('[save_edit] emitting edit-submit')
    emit('edit-submit', props.active_index, new_item)
  } catch (err) {
    console.error('[save_edit] exception:', err)
    const errDetail = err.response?.data?.error || err.message || 'Unknown error'
    emit('set-message', { type: 'error', data: 'Save failed: ' + errDetail })
  }
}

defineExpose({
  getProof: () => proof
})
</script>

<style scoped>
.theory-content {
  min-height: 100%;
}

.theory-header {
  margin-bottom: 10px;
}

.keyword {
  font-weight: bold;
  color: #006000;
}

.comment {
  color: #666;
}

.import-link {
  color: blue;
  cursor: pointer;
  margin-right: 5px;
}

.import-link:hover {
  text-decoration: underline;
}

.header-item {
  font-weight: bold;
  font-size: 1.1em;
}

.edit-icon {
  margin-left: 10px;
  color: #6c757d;
  text-decoration: none;
  font-size: 16px;
  padding: 2px 5px;
  border-radius: 3px;
  transition: all 0.2s ease;
}

.edit-icon:hover {
  color: #007bff;
  background-color: #e9ecef;
  text-decoration: none;
}

.edit-section {
  margin: 10px 0;
  padding: 10px;
  background: #f9f9f9;
  border: 1px solid #ddd;
  border-radius: 4px;
}

.proof-section {
  margin: 10px 0;
  padding: 10px;
  background: #f9f9f9;
  border: 1px solid #ddd;
  border-radius: 4px;
}
</style>

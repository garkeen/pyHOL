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
          <ConstantEdit v-if="item.ty === 'def.ax'" :old_item="item.edit" ref="edit_ref"/>
          <DefinitionEdit v-else-if="item.ty === 'def'" :old_item="item.edit" :ext="item.ext" ref="edit_ref"/>
          <DatatypeEdit v-else-if="item.ty === 'type.ind'" :old_item="item.edit" :ext="item.ext" ref="edit_ref"/>
          <InductiveEdit v-else-if="item.ty === 'def.ind' || item.ty === 'def.pred'" :old_item="item.edit" :ext="item.ext" ref="edit_ref"/>
          <TheoremEdit v-else-if="item.ty === 'thm' || item.ty === 'thm.ax'" :old_item="item.edit" ref="edit_ref"/>
          
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
                     :old_steps="item.steps" :old_proof="item.proof"
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
let edit_ref = ref(null)
let proof = ref(null)

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
  if (!edit_ref.value) return
  
  const data = {
    filename: props.theory.name,
    limit_ty: props.theory.content[props.active_index].ty,
    limit_name: props.theory.content[props.active_index].name,
    line_length: 80,
    item: edit_ref.value.getData()
  }
  
  emit('set-message', { type: 'OK', data: 'Checking...' })
  
  try {
    const response = await api.post('/check-modify', data)
    const item = response.data.item
    
    if ('error' in item) {
      emit('set-message', {
        type: 'error',
        data: item.error.err_type + '\n' + item.error.err_str
      })
    } else {
      emit('set-message', { type: 'OK', data: 'No errors' })
    }
  } catch (err) {
    emit('set-message', { type: 'error', data: 'Server error' })
  }
}

const save_edit = async () => {
  if (!edit_ref.value) return
  
  const data = {
    filename: props.theory.name,
    limit_ty: props.theory.content[props.active_index].ty,
    limit_name: props.theory.content[props.active_index].name,
    line_length: 80,
    item: edit_ref.value.getData()
  }
  
  try {
    const response = await api.post('/check-modify', data)
    const new_item = response.data.item
    
    if ('error' in new_item) {
      emit('set-message', {
        type: 'error',
        data: new_item.error.err_type + '\n' + new_item.error.err_str
      })
      return
    }
    
    // 保留证明数据
    const old_item = props.theory.content[props.active_index]
    if (old_item.ty === 'thm') {
      new_item.proof = old_item.proof
      new_item.num_gaps = old_item.num_gaps
      new_item.steps = old_item.steps
    }
    
    // 更新item
    emit('edit-submit', props.active_index, new_item)
  } catch (err) {
    emit('set-message', { type: 'error', data: 'Server error' })
  }
}

defineExpose({
  getProof: () => proof.value
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

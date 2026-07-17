<template>
  <div class="item-header" :class="{'item-selected': selected, 'item-error': has_error}">
    <!-- 左侧：项类型和名称 -->
    <div class="item-left">
      <span class="item-type">{{ typeLabel }}</span>
      <span class="item-name">{{ item.name }}</span>
      <span v-if="status" class="item-status" :class="'status-' + status.toLowerCase()">
        {{ statusIcon }}
      </span>
    </div>
    
    <!-- 右侧：编辑/证明按钮 -->
    <div class="item-right">
      <button v-if="canEdit" 
              class="btn-icon" 
              :class="{active: isEditing}"
              @click.stop="$emit('toggle-edit')"
              title="Edit">
        &#9998;
      </button>
      <button v-if="canProve"
              class="btn-prove"
              :class="{active: isProving, 'btn-prove-unproved': status === 'UNPROVED'}"
              @click.stop="$emit('toggle-prove')"
              :title="proofTitle">
        <span class="prove-icon">{{ proofIcon }}</span>
        <span v-if="status === 'UNPROVED'" class="prove-label">Prove</span>
      </button>
    </div>
  </div>
</template>

<script setup>
import { computed } from 'vue'

const props = defineProps({
  item: {
    type: Object,
    required: true
  },
  index: {
    type: Number,
    required: true
  },
  status: {
    type: String,
    default: null
  },
  selected: {
    type: Boolean,
    default: false
  },
  isEditing: {
    type: Boolean,
    default: false
  },
  isProving: {
    type: Boolean,
    default: false
  }
})

defineEmits(['toggle-edit', 'toggle-prove'])

const typeLabel = computed(() => {
  switch (props.item.ty) {
    case 'header': return ''
    case 'type.ax': return 'type'
    case 'type.ind': return 'datatype'
    case 'def.ax': return 'constant'
    case 'def': return 'definition'
    case 'def.ind': return 'fun'
    case 'def.pred': return 'inductive'
    case 'thm.ax': return 'axiom'
    case 'thm': return 'theorem'
    default: return props.item.ty
  }
})

const has_error = computed(() => 'error' in props.item)

const canEdit = computed(() => {
  return ['def.ax', 'def', 'def.ind', 'def.pred', 'thm.ax', 'thm', 'type.ind'].includes(props.item.ty)
})

const canProve = computed(() => {
  return props.item.ty === 'thm'
})

const statusIcon = computed(() => {
  switch (props.status) {
    case 'VALID': return '✓'
    case 'STEP_FAILED': return '✗'
    case 'DEP_FAILED': return '⚠'
    case 'PENDING': return '⏳'
    case 'UNPROVED': return '○'
    case 'AXIOM': return '□'
    default: return ''
  }
})

const proofIcon = computed(() => {
  switch (props.status) {
    case 'VALID': return '✓'
    case 'STEP_FAILED': return '✗'
    case 'DEP_FAILED': return '⚠'
    case 'PENDING': return '⏳'
    case 'UNPROVED': return '○'
    default: return '○'
  }
})

const proofTitle = computed(() => {
  switch (props.status) {
    case 'VALID': return 'Proof complete'
    case 'STEP_FAILED': return 'Proof has errors'
    case 'DEP_FAILED': return 'Dependency failed'
    case 'PENDING': return 'Validating...'
    case 'UNPROVED': return 'No proof'
    default: return ''
  }
})
</script>

<style scoped>
.item-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 8px;
  margin: 2px 0;
  border-radius: 4px;
  cursor: pointer;
}

.item-header:hover {
  background-color: #f0f0f0;
}

.item-selected {
  background-color: #e0e0e0;
}

.item-error {
  background-color: #ffe0e0;
}

.item-left {
  display: flex;
  align-items: center;
  gap: 8px;
}

.item-type {
  font-weight: bold;
  color: #006000;
  min-width: 80px;
}

.item-name {
  font-family: Consolas, monospace;
}

.item-status {
  font-size: 14px;
  margin-left: 4px;
}

.status-valid {
  color: #28a745;
}

.status-dirty {
  color: #ffc107;
}

.status-invalid {
  color: #dc3545;
}

.status-unproved {
  color: #6c757d;
}

.status-axiom {
  color: #17a2b8;
}

.status-step_failed {
  color: #dc3545;
}

.status-dep_failed {
  color: #fd7e14;
}

.status-pending {
  color: #6c757d;
}

.item-right {
  display: flex;
  gap: 4px;
}

.btn-icon {
  background: none;
  border: 1px solid transparent;
  padding: 2px 6px;
  cursor: pointer;
  font-size: 14px;
  border-radius: 3px;
  color: #6c757d;
  transition: all 0.2s;
}

.btn-icon:hover {
  background-color: #e9ecef;
  border-color: #ced4da;
  color: #495057;
}

.btn-icon.active {
  background-color: #007bff;
  border-color: #007bff;
  color: white;
}

.btn-prove {
  background: none;
  border: 1px solid transparent;
  padding: 2px 8px;
  cursor: pointer;
  font-size: 14px;
  border-radius: 3px;
  color: #6c757d;
  transition: all 0.2s;
  display: flex;
  align-items: center;
  gap: 4px;
}

.btn-prove:hover {
  background-color: #e9ecef;
  border-color: #ced4da;
  color: #495057;
}

.btn-prove.active {
  background-color: #007bff;
  border-color: #007bff;
  color: white;
}

.btn-prove-unproved {
  border: 1px dashed #007bff;
  color: #007bff;
}

.btn-prove-unproved:hover {
  background-color: #007bff;
  color: white;
}

.prove-label {
  font-size: 12px;
  font-weight: 500;
}
</style>

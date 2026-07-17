<template>
  <form>
    <span>
      <label class="keyword">{{local.ty === 'thm.ax' ? 'axiom' : 'theorem'}}</label>
      <ExpressionEdit v-model="local.name" single-line/>
    </span>
    <div style="margin-top:5px">
      <label class="keyword">fixes</label>
      <ExpressionEdit v-model="local.vars"/>
    </div>
    <div style="margin-top:5px">
      <label class="keyword">shows</label>
      <ExpressionEdit v-model="local.prop"/>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element" title="Used as backward rule: conclusion matches goal">
        <input type="checkbox" :id="'backward-check' + id" value="hint_backward"
               v-model="local.attributes">
        <label :for="'backward-check' + id">Backward</label>
      </span>
      <span class="hint-element" title="Used as backward rule with priority">
        <input type="checkbox" :id="'backward1-check' + id" value="hint_backward1"
               v-model="local.attributes">
        <label :for="'backward1-check' + id">Backward1</label>
      </span>
      <span class="hint-element" title="Used as forward rule: premises match known facts">
        <input type="checkbox" :id="'forward-check' + id" value="hint_forward"
               v-model="local.attributes">
        <label :for="'forward-check' + id">Forward</label>
      </span>
      <span class="hint-element" title="Used as rewrite rule: replaces LHS with RHS">
        <input type="checkbox" :id="'rewrite-check' + id" value="hint_rewrite"
               v-model="local.attributes">
        <label :for="'rewrite-check' + id">Rewrite</label>
      </span>
      <span class="hint-element" title="Used as symmetric rewrite rule: replaces RHS with LHS">
        <input type="checkbox" :id="'rewrite-sym-check' + id" value="hint_rewrite_sym"
               v-model="local.attributes">
        <label :for="'rewrite-sym-check' + id">Rewrite (sym)</label>
      </span>
      <span class="hint-element" title="Used for resolution with goal">
        <input type="checkbox" :id="'resolve-check' + id" value="hint_resolve"
               v-model="local.attributes">
        <label :for="'resolve-check' + id">Resolve</label>
      </span>
    </div>
  </form>
</template>

<script setup>
import { reactive, computed } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  item: { type: Object, required: true },
  old_item: { type: Object, default: null }
})

const source = props.item || props.old_item

// Convert vars dict to string for editing
const varsToString = (v) => {
  if (typeof v === 'string') return v
  if (v && typeof v === 'object') {
    return Object.entries(v).map(([name, type]) => name + ' :: ' + type).join('\n')
  }
  return ''
}

// Convert vars string back to dict for saving
const varsToDict = (s) => {
  if (!s || typeof s !== 'string') return {}
  const result = {}
  for (const line of s.split('\n')) {
    const trimmed = line.trim()
    if (!trimmed) continue
    const parts = trimmed.split('::')
    if (parts.length >= 2) {
      result[parts[0].trim()] = parts.slice(1).join('::').trim()
    }
  }
  return result
}

// Ensure field is string for ExpressionEdit
const toStr = (v) => {
  if (typeof v === 'string') return v
  if (Array.isArray(v)) return v.map(item => item.text || String(item)).join('\n')
  if (v == null) return ''
  return String(v)
}

const local = reactive({
  ty: source.ty || 'thm',
  name: toStr(source.name),
  vars: varsToString(source.vars),
  prop: toStr(source.prop),
  attributes: Array.isArray(source.attributes) ? [...source.attributes] : []
})

const id = computed(() => {
  return (source.ty || 'thm') + '.' + (source.name || '')
})

defineExpose({
  getData: () => {
    const d = JSON.parse(JSON.stringify(local))
    d.vars = varsToDict(d.vars)
    return d
  }
})
</script>

<style scoped>
.keyword {
  font-weight: bold;
  color: #006000;
  margin-right: 5px;
}

.hint-element {
  margin-right: 10px;
}

.hint-element label {
  margin-left: 3px;
}
</style>

<template>
  <form>
    <span>
      <label class="keyword">definition</label>
      <ExpressionEdit v-model="local.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="local.type" min-width="50" single-line/>
      <label class="keyword" style="margin-left:10px">where</label>
    </span>
    <div style="margin-top:3px">
      <ExpressionEdit v-model="local.prop"/>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element">
        <input type="checkbox" :id="'rewrite-check' + id" value="hint_rewrite"
               v-model="local.attributes">
        <label :for="'rewrite-check' + id">Rewrite</label>
      </span>
      <span class="hint-element">
        <input type="checkbox" :id="'rewrite-sym-check' + id" value="hint_rewrite_sym"
               v-model="local.attributes">
        <label :for="'rewrite-sym-check' + id">Rewrite (sym)</label>
      </span>
    </div>
    <pre class="ext-output" v-if="ext">{{ext}}</pre>
  </form>
</template>

<script setup>
import { reactive, computed } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  item: { type: Object, required: true },
  old_item: { type: Object, default: null },
  ext: { type: [String, Array], default: '' }
})

const source = props.item || props.old_item

// Ensure field is string for ExpressionEdit
const toStr = (v) => {
  if (typeof v === 'string') return v
  if (Array.isArray(v)) return v.map(item => item.text || String(item)).join('\n')
  if (v == null) return ''
  return String(v)
}

const local = reactive({
  ty: source.ty || 'def',
  name: toStr(source.name),
  type: toStr(source.type),
  prop: toStr(source.prop),
  attributes: Array.isArray(source.attributes) ? [...source.attributes] : []
})

const id = computed(() => { return (source.ty || 'def') + '.' + (source.name || '') })

defineExpose({
  getData: () => ({ ty: local.ty, name: local.name, type: local.type, prop: local.prop, attributes: local.attributes })
})
</script>

<style scoped>
.keyword {
  font-weight: bold;
  color: #006000;
  margin-right: 5px;
}

.form-element {
  margin: 0 3px;
  font-family: Consolas, monospace;
}

.hint-element {
  margin-right: 10px;
}

.hint-element label {
  margin-left: 3px;
}

.ext-output {
  margin-top: 5px;
  padding: 5px;
  background: #f5f5f5;
  border: 1px solid #ddd;
  font-size: 12px;
  font-family: Consolas, monospace;
}
</style>

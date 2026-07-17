<template>
  <form>
    <span>
      <label class="keyword">datatype</label>
      <ExpressionEdit v-model="local.type" min-width="50" single-line/>
      <span class="form-element">=</span>
    </span>
    <div style="margin-top:5px">
      <ExpressionEdit v-model="local.constrs" min-width="200"/>
    </div>
    <pre class="ext-output" v-if="ext">{{ext}}</pre>
  </form>
</template>

<script setup>
import { reactive } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  item: { type: Object, required: true },
  old_item: { type: Object, default: null },
  ext: { type: [String, Array], default: '' }
})

const source = props.item || props.old_item

// Convert constrs array to string
const constrsToString = (c) => {
  if (typeof c === 'string') return c
  if (Array.isArray(c)) {
    return c.map(con => {
      if (typeof con === 'string') return con
      const args = (con.args || []).join(', ')
      return con.name + (args ? '(' + args + ')' : '') + ' :: ' + (con.type || '')
    }).join('\n')
  }
  return ''
}

const toStr = (v) => {
  if (typeof v === 'string') return v
  if (Array.isArray(v)) return v.map(item => item.text || String(item)).join('\n')
  if (v == null) return ''
  return String(v)
}

const local = reactive({
  name: toStr(source.name),
  type: toStr(source.type),
  args: Array.isArray(source.args) ? [...source.args] : [],
  constrs: constrsToString(source.constrs)
})

defineExpose({
  getData: () => {
    const d = { ty: 'type.ind', name: local.name, args: local.args }
    // Parse constrs string back to array
    d.constrs = local.constrs.split('\n').filter(l => l.trim()).map(line => {
      const parts = line.split('::')
      if (parts.length >= 2) {
        const namePart = parts[0].trim()
        const type = parts.slice(1).join('::').trim()
        const match = namePart.match(/^(\w+)(?:\(([^)]*)\))?$/)
        if (match) {
          return { name: match[1], type, args: match[2] ? match[2].split(',').map(s => s.trim()) : [] }
        }
        return { name: namePart, type, args: [] }
      }
      return { name: line.trim(), type: '', args: [] }
    })
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

.form-element {
  margin: 0 3px;
  font-family: Consolas, monospace;
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

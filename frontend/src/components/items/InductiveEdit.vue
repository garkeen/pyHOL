<template>
  <form>
    <span>
      <label class="keyword">
        {{local.ty === 'def.ind' ? 'fun' : 'inductive'}}
      </label>
      <ExpressionEdit v-model="local.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="local.type" min-width="50" single-line/>
      <label class="keyword" style="margin-left:10px">where</label>
    </span>
    <div style="margin-top:3px">
      <ExpressionEdit v-model="local.rules"/>
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

// Convert rules array to string for editing
const rulesToString = (r) => {
  if (typeof r === 'string') return r
  if (Array.isArray(r)) {
    return r.map(rule => {
      if (typeof rule === 'string') return rule
      if (rule.name) return rule.name + ': ' + (rule.prop || '')
      return rule.prop || ''
    }).join('\n')
  }
  return ''
}

// Convert rules string back to array for saving
const rulesToArray = (s) => {
  if (!s || typeof s !== 'string') return []
  return s.split('\n').filter(l => l.trim()).map(line => {
    const colonIdx = line.indexOf(':')
    if (colonIdx > 0) {
      const name = line.substring(0, colonIdx).trim()
      const prop = line.substring(colonIdx + 1).trim()
      return { name, prop }
    }
    return { prop: line.trim() }
  })
}

const toStr = (v) => {
  if (typeof v === 'string') return v
  if (Array.isArray(v)) return v.map(item => item.text || String(item)).join('\n')
  if (v == null) return ''
  return String(v)
}

const local = reactive({
  ty: source.ty || 'def.ind',
  name: toStr(source.name),
  type: toStr(source.type),
  rules: rulesToString(source.rules)
})

defineExpose({
  getData: () => {
    const d = JSON.parse(JSON.stringify(local))
    d.rules = rulesToArray(d.rules)
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

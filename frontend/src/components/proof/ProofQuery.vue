<template>
  <div v-if="query !== undefined" class="pq-form">
    <div v-if="query.desc && (query.desc.thm || query.desc.result)" class="pq-desc">
      <div v-if="query.desc.thm" class="pq-desc-line">Thm: <span class="pq-thm">{{ query.desc.thm }}</span></div>
      <div v-if="query.desc.result" class="pq-desc-line">{{ query.desc.result }}</div>
    </div>
    <div v-if="query.fields && query.fields.length > 0" class="pq-needs">
      Fill in: <span v-for="(n, i) in query.fields" :key="i" class="pq-hl">{{ n }}</span>
    </div>
    <template v-for="(key, index) in (query.fields || [])" :key="index">
      <!-- List-type field: dynamic +/- inputs -->
      <div v-if="isList(key)" class="pq-list-field">
        <div class="pq-list-header">
          <label class="pq-label">{{ key }}:</label>
          <button class="pq-add-btn" @click="add_item(key)" :disabled="listCount(key) && list_vals[key].length >= listCount(key)">+ add</button>
        </div>
        <div v-for="(v, i) in list_vals[key]" :key="i" class="pq-row pq-list-row">
          <span class="pq-idx">{{ i + 1 }}</span>
          <ExpressionEdit min-width="200" v-model="list_vals[key][i]"/>
          <button class="pq-rm-btn" @click="remove_item(key, i)" :disabled="list_vals[key].length <= 1">&minus;</button>
        </div>
      </div>
      <!-- Single field -->
      <div v-else class="pq-row">
        <label class="pq-label">{{ key }}:</label>
        <ExpressionEdit min-width="200" v-model="vals[key]"/>
      </div>
    </template>
    <div class="pq-buttons">
      <button class="pq-btn pq-ok" @click="handle_ok">OK</button>
      <button class="pq-btn pq-cancel" @click="handle_cancel">Cancel</button>
    </div>
  </div>
</template>

<script setup>
import { ref, watch } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  query: {
    type: Object,
    default: undefined
  }
})

const emit = defineEmits(['query-ok', 'query-cancel'])

const vals = ref({})
const list_vals = ref({})

const isList = (key) => {
  const lf = props.query && props.query.list_fields
  return Array.isArray(lf) && lf.includes(key)
}

const listCount = (key) => {
  const h = props.query && props.query.hints
  return h && h[key] && h[key].count
}

const add_item = (key) => {
  list_vals.value[key].push('')
}

const remove_item = (key, i) => {
  if (list_vals.value[key].length > 1) {
    list_vals.value[key].splice(i, 1)
  }
}

watch(() => props.query, (new_query) => {
  if (new_query === undefined) return

  vals.value = {}
  list_vals.value = {}
  if (new_query.fields) {
    for (let i = 0; i < new_query.fields.length; i++) {
      const f = new_query.fields[i]
      if (isList(f)) {
        const cnt = listCount(f)
        list_vals.value[f] = cnt ? Array(cnt).fill('') : ['']
      } else {
        vals.value[f] = ''
      }
    }
  }
}, { immediate: true })

const handle_ok = () => {
  const result = {}
  for (const k in vals.value) {
    result[k] = vals.value[k]
  }
  for (const k in list_vals.value) {
    result[k] = list_vals.value[k].filter(v => v && v.trim()).join(',')
  }
  emit('query-ok', result)
}

const handle_cancel = () => {
  emit('query-cancel')
}
</script>

<style scoped>
.pq-form { display: flex; flex-direction: column; gap: 10px; }
.pq-desc { background: #f5f7fa; border: 1px solid #e1e5eb; border-radius: 4px; padding: 8px 10px; font-size: 12px; }
.pq-desc-line { font-family: Consolas, monospace; }
.pq-thm { color: #0d6efd; }
.pq-needs { font-size: 12px; color: #b3541e; font-weight: 600; }
.pq-hl { background: #fff3cd; border: 1px solid #ffe08a; border-radius: 3px; padding: 1px 6px; margin-right: 4px; font-family: Consolas, monospace; font-weight: bold; }
.pq-row { display: flex; align-items: center; gap: 8px; }
.pq-label { font-weight: 600; min-width: 40px; font-size: 13px; }
.pq-list-field { border: 1px solid #e1e5eb; border-radius: 4px; padding: 8px; background: #fafbfc; }
.pq-list-header { display: flex; align-items: center; justify-content: space-between; margin-bottom: 6px; }
.pq-list-row { margin-top: 4px; }
.pq-idx { font-size: 12px; color: #888; min-width: 16px; text-align: right; }
.pq-add-btn { background: #e8f5e9; border: 1px solid #81c784; border-radius: 3px; padding: 2px 10px; font-size: 12px; cursor: pointer; color: #2e7d32; }
.pq-add-btn:hover { background: #c8e6c9; }
.pq-add-btn:disabled { opacity: 0.4; cursor: not-allowed; }
.pq-rm-btn { background: #fbe9e7; border: 1px solid #e57373; border-radius: 3px; padding: 2px 10px; font-size: 14px; cursor: pointer; color: #c62828; line-height: 1; }
.pq-rm-btn:hover { background: #ffcdd2; }
.pq-rm-btn:disabled { opacity: 0.4; cursor: not-allowed; }
.pq-buttons { display: flex; justify-content: flex-end; gap: 8px; margin-top: 6px; }
.pq-btn { padding: 5px 16px; border: none; border-radius: 4px; font-size: 13px; cursor: pointer; }
.pq-ok { background: #0d6efd; color: #fff; }
.pq-ok:hover { background: #0b5ed7; }
.pq-cancel { background: #e9ecef; color: #333; }
.pq-cancel:hover { background: #dde0e3; }
</style>

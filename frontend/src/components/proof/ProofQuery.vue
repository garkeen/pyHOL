<template>
  <div v-if="query !== undefined" class="pq-form">
    <div v-if="query.desc && (query.desc.thm || query.desc.result)" class="pq-desc">
      <div v-if="query.desc.thm" class="pq-desc-line">Thm: <span class="pq-thm">{{ query.desc.thm }}</span></div>
      <div v-if="query.desc.result" class="pq-desc-line">{{ query.desc.result }}</div>
    </div>
    <div v-if="query.fields && query.fields.length > 0" class="pq-needs">
      Fill in: <span v-for="(n, i) in query.fields" :key="i" class="pq-hl">{{ n }}</span>
    </div>
    <div v-for="(key, index) in query.fields" :key="index" class="pq-row">
      <label class="pq-label">{{ key }}:</label>
      <ExpressionEdit min-width="200" v-model="vals[key]"/>
    </div>
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

watch(() => props.query, (new_query) => {
  if (new_query === undefined) return

  vals.value = {}
  if (new_query.fields) {
    for (let i = 0; i < new_query.fields.length; i++) {
      vals.value[new_query.fields[i]] = ''
    }
  }
}, { immediate: true })

const handle_ok = () => {
  emit('query-ok', vals.value)
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
.pq-buttons { display: flex; justify-content: flex-end; gap: 8px; margin-top: 6px; }
.pq-btn { padding: 5px 16px; border: none; border-radius: 4px; font-size: 13px; cursor: pointer; }
.pq-ok { background: #0d6efd; color: #fff; }
.pq-ok:hover { background: #0b5ed7; }
.pq-cancel { background: #e9ecef; color: #333; }
.pq-cancel:hover { background: #dde0e3; }
</style>

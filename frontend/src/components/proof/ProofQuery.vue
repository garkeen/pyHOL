<template>
  <div v-if="query !== undefined">
    <div>{{query.title}}</div>
    <form>
      <div style="margin-top:5px" v-for="(key, index) in query.fields" :key="index">
        <label>{{key}}:</label>
        <ExpressionEdit min-width="200" style="margin-left:10px" v-model="vals[key]"/>
      </div>
    </form>
    <button style="margin:5px" @click="handle_ok">OK</button>
    <button style="margin:5px" @click="handle_cancel">Cancel</button>
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

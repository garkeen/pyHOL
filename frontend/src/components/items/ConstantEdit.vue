<template>
  <form>
    <span>
      <label class="keyword">constant</label>
      <ExpressionEdit v-model="local.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="local.type" min-width="100" single-line/>
    </span>
  </form>
</template>

<script setup>
import { reactive } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  item: { type: Object, required: true },
  old_item: { type: Object, default: null }
})

const source = props.item || props.old_item
const local = reactive({
  name: typeof source.name === 'string' ? source.name : '',
  type: typeof source.type === 'string' ? source.type : ''
})

defineExpose({
  getData: () => ({ ty: 'def.ax', name: local.name, type: local.type })
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
</style>

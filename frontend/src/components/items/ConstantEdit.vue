<template>
  <form>
    <span>
      <label class="keyword">constant</label>
      <ExpressionEdit v-model="item.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="item.type" min-width="100" single-line/>
    </span>
  </form>
</template>

<script setup>
import { reactive } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  old_item: {
    type: Object,
    required: true
  }
})

const item = reactive(
  Object.assign(
    {
      name: "",
      type: ""
    },
    JSON.parse(JSON.stringify(props.old_item))
  )
)

defineExpose({
  getData: () => JSON.parse(JSON.stringify(item))
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

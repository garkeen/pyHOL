<template>
  <form>
    <span>
      <label class="keyword">
        {{item.ty === 'def.ind' ? 'fun' : 'inductive'}}
      </label>
      <ExpressionEdit v-model="item.name" min-width="50" single-line/>
      <span class="form-element">::</span>
      <ExpressionEdit v-model="item.type" min-width="50" single-line/>
      <label class="keyword" style="margin-left:10px">where</label>
    </span>
    <div style="margin-top:3px">
      <ExpressionEdit v-model="item.rules"/>
    </div>
    <pre class="ext-output" v-if="ext">{{ext}}</pre>
  </form>
</template>

<script setup>
import { reactive, computed } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  old_item: {
    type: Object,
    required: true
  },
  ext: {
    type: [String, Array],
    default: ''
  }
})

const item = reactive(
  Object.assign(
    {
      attributes: [],
      name: "",
      type: "",
      rules: ""
    },
    JSON.parse(JSON.stringify(props.old_item))
  )
)

const id = computed(() => {
  return props.old_item.ty + '.' + props.old_item.name
})

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

.ext-output {
  margin-top: 5px;
  padding: 5px;
  background: #f5f5f5;
  border: 1px solid #ddd;
  font-size: 12px;
  font-family: Consolas, monospace;
}
</style>

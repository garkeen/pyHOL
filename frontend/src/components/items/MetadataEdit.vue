<template>
  <form>
    <div>
      <label class="keyword">theory</label>
      <span>{{name}}</span>
    </div>
    <div>
      <label class="keyword">imports</label>
      <ExpressionEdit v-model="imports"/>
    </div>
    <div style="margin-top:5px">
      <label class="keyword">Description:</label><br>
      <ExpressionEdit v-model="description"/>
    </div>
  </form>
</template>

<script setup>
import { ref } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  theory: {
    type: Object,
    required: true
  }
})

const name = ref(props.theory.name)
const imports = ref(props.theory.imports.join('\n'))
const description = ref(props.theory.description)

defineExpose({
  getData: () => ({
    name: name.value,
    imports: imports.value.split('\n').map(s => s.trim()).filter(s => s),
    description: description.value
  })
})
</script>

<style scoped>
.keyword {
  font-weight: bold;
  color: #006000;
  margin-right: 5px;
}
</style>

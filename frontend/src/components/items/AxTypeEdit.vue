<template>
  <div>
    <span>
      <label class="keyword">type</label>
      <input class="form-control form-control-sm d-inline-block ms-2" style="width:200px" v-model="local.name" placeholder="type name"/>
      <label class="keyword ms-2">args</label>
      <input class="form-control form-control-sm d-inline-block ms-2" style="width:200px" v-model="local.args_str" placeholder="'a, 'b"/>
    </span>
  </div>
</template>

<script setup>
import { reactive } from 'vue'

const props = defineProps({ item: { type: Object, required: true } })

const local = reactive({
  name: typeof props.item.name === 'string' ? props.item.name : '',
  args_str: Array.isArray(props.item.args) ? props.item.args.join(', ') : ''
})

defineExpose({
  getData: () => ({
    ty: 'type.ax',
    name: local.name,
    args: local.args_str.split(',').map(s => s.trim()).filter(Boolean)
  })
})
</script>

<style scoped>
.keyword { font-weight: bold; color: #006000; margin-right: 5px; }
</style>

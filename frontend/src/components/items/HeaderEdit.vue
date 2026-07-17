<template>
  <div>
    <span>
      <label class="keyword">header</label>
      <input class="form-control form-control-sm d-inline-block w-auto" v-model.number="local.depth" type="number" min="0" max="5"/>
      <input class="form-control form-control-sm d-inline-block ms-2" style="width:300px" v-model="local.name" placeholder="Section title"/>
    </span>
  </div>
</template>

<script setup>
import { reactive } from 'vue'

const props = defineProps({ item: { type: Object, required: true } })

const local = reactive({ depth: props.item.depth || 0, name: props.item.name || '' })

defineExpose({ getData: () => ({ ty: 'header', depth: local.depth, name: local.name }) })
</script>

<style scoped>
.keyword { font-weight: bold; color: #006000; margin-right: 5px; }
</style>

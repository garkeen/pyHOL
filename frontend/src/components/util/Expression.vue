<template>
  <span class="item-text">
    <template v-if="Array.isArray(line)">
      <ExpressionNode v-for="(node, index) in line" :key="index" :node="node" :editor="editor"/>
    </template>
    <template v-else>
      {{ line }}
    </template>
  </span>
</template>

<script setup>
import ExpressionNode from './ExpressionNode.vue'

defineProps({
  line: {
    type: [Array, String],
    required: true
  },
  editor: {
    type: Object,
    default: null
  }
})
</script>

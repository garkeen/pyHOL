<template>
  <span class="item-text">
    <template v-if="Array.isArray(line)">
      <ExpressionNode v-for="(node, index) in line" :key="index" :node="node"/>
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
  }
})
</script>

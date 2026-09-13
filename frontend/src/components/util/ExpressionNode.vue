<template>
  <template v-if="typeof node === 'string'">
    <span>{{ node }}</span>
  </template>
  <template v-else>
    <span class="expr-node" :style="{color: get_color(node.color)}">{{ node.text }}</span>
  </template>
</template>

<script setup>
const props = defineProps({
  node: {
    type: Object,
    required: true
  }
})

const get_color = (x) => {
  if (x === 0) return 'black'
  else if (x === 1) return '#006000'
  else if (x === 2) return 'blue'
  else if (x === 3) return 'purple'
  else if (x === 4) return 'silver'
  else if (x === 5) return 'red'
  else if (x === 6) return 'green'
  return 'black'
}
</script>

<style scoped>
.expr-node { white-space: pre; }
</style>

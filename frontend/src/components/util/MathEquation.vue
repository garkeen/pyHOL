<template>
  <span ref="mathJaxEl" v-html="data" class="e-mathjax"></span>
</template>

<script setup>
import { ref, watch, onMounted, onUpdated, nextTick } from 'vue'

const props = defineProps({
  data: {
    type: String,
    default: ''
  }
})

const mathJaxEl = ref(null)

const renderMathJax = () => {
  nextTick(() => {
    if (window.MathJax && window.MathJax.Hub && mathJaxEl.value) {
      window.MathJax.Hub.processSectionDelay = 0
      window.MathJax.Hub.Queue(["Typeset", window.MathJax.Hub, mathJaxEl.value])
    }
  })
}

watch(() => props.data, () => {
  renderMathJax()
})

onMounted(() => {
  renderMathJax()
})

onUpdated(() => {
  renderMathJax()
})
</script>

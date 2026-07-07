<template>
  <div align=left v-if="message !== undefined">
    <pre :class="{'message-error': message.type === 'error'}">{{message.data}}</pre>
    <a href="#" v-if="'trace' in message" @click.prevent="show_trace = !show_trace">
      {{show_trace ? 'Hide stack trace' : 'Show stack trace'}}
    </a>
    <pre v-if="show_trace">{{message.trace}}</pre>
  </div>
</template>

<script setup>
import { ref } from 'vue'

defineProps({
  message: {
    type: Object,
    default: undefined
  }
})

const show_trace = ref(false)
</script>

<style scoped>
.message-error {
  color: red
}
</style>

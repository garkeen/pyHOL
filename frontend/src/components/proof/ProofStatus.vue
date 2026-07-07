<template>
  <div>
    <div>
      <span class="item-text">{{ status }}</span>
      <a href="#" v-if="trace !== undefined" @click.prevent="show_trace = !show_trace">
        {{ show_trace ? 'Hide stack trace' : 'Show stack trace' }}
      </a>
      <pre v-if="trace !== undefined && show_trace">{{trace}}</pre>
    </div>
    <div v-if="instr_no">
      <a href="#" @click.prevent="ref_proof && typeof ref_proof.step_backward === 'function' && ref_proof.step_backward()">&lt;</a>
      <span id="instruction-number" v-html="instr_no"/>
      <a href="#" @click.prevent="ref_proof && typeof ref_proof.step_forward === 'function' && ref_proof.step_forward()">&gt;</a>
      <Expression style="margin-left:10pt" :line="instr"/>
    </div>
    <div class="thm-content">
      <div v-for="(res, i) in search_res" :key="i"
           @click="handle_click(i)">
        <Expression v-if="res.display" :line="res.display"/>
        <span v-else>{{res.method_name}}</span>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref } from 'vue'
import Expression from '../util/Expression.vue'

const props = defineProps({
  ref_proof: {
    type: Object,
    default: null
  }
})

const status = ref('')
const trace = ref(undefined)
const show_trace = ref(false)
const instr = ref([])
const instr_no = ref('')
const search_res = ref([])

const setStatus = (data) => {
  if (data.status !== undefined) status.value = data.status
  if (data.trace !== undefined) trace.value = data.trace
  if (data.instr !== undefined) instr.value = data.instr
  if (data.instr_no !== undefined) instr_no.value = data.instr_no
  if (data.search_res !== undefined) search_res.value = data.search_res
}

const handle_click = (i) => {
  if (props.ref_proof && typeof props.ref_proof.apply_thm_tactic === 'function') {
    props.ref_proof.apply_thm_tactic(i)
  } else {
    console.warn('ref_proof.apply_thm_tactic is not available:', props.ref_proof)
  }
}

defineExpose({
  setStatus
})
</script>

<style scoped>
.item-text {
  font-family: Consolas, monospace;
}

.thm-content {
  margin-top: 10px;
  margin-left: 5px;
}

.thm-content div {
  margin: 5px;
  cursor: pointer;
}

.thm-content div:hover {
  background-color: yellow;
}
</style>

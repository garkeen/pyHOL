<template>
  <div style="margin-left:10px;margin-top:10px">
    <div style="font-size:18px;margin-bottom:5px">Variables</div>
    <div style="height:70px;overflow-y:scroll">
      <div style="margin-left:10px" v-for="(T, nm, index) in ctxt" :key="index">
        <span class="item-text">{{nm}}</span> ::
        <Expression v-if="Array.isArray(T)" :line="T"/>
        <span v-else class="item-text">{{T}}</span>
      </div>
    </div>
    <div style="margin-top:10px;margin-bottom:5px;font-size:18px">History</div>
    <div>
      <Expression style="margin-left:5px"
          :line="[{color: 0, text: 'Initial'}]"
          @click.exact="handleSelect(0)"
          @click.shift="handleShiftSelect(0)"
          :class="{
            'step-entry': true,
            'step-selected': isSelected(0)}"/>
      <div v-for="(line, index) in steps" :key="index"
           style="white-space:nowrap">
        <Expression style="margin-left:5px" :line="line.step_output || []" 
            @click.exact="handleSelect(index+1)"
            @click.shift="handleShiftSelect(index+1)"
            :class="{
              'step-entry': true,
              'step-selected': isSelected(index+1),
              'step-error': line.error !== undefined}"/>
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

const ctxt = ref({})
const steps = ref([])
const selected_start = ref(0)
const selected_end = ref(0)

const isSelected = (index) => {
  if (selected_start.value <= selected_end.value) {
    return selected_start.value <= index && index <= selected_end.value
  } else {
    return selected_end.value <= index && index <= selected_start.value
  }
}

const handleSelect = (index) => {
  selected_start.value = index
  selected_end.value = index
  if (props.ref_proof && typeof props.ref_proof.gotoStep === 'function') {
    props.ref_proof.gotoStep(index, false)
  } else {
    console.warn('ref_proof.gotoStep is not available:', props.ref_proof)
  }
}

const handleShiftSelect = (index) => {
  selected_end.value = index
  if (props.ref_proof && typeof props.ref_proof.gotoStep === 'function') {
    props.ref_proof.gotoStep(index, false)
  }
}

const deleteStep = () => {
  let start = Math.max(0, selected_start.value - 1)
  let end = Math.max(0, selected_end.value - 1)
  if (start > end) {
    [start, end] = [end, start]
  }
  selected_start.value = start
  selected_end.value = start
  if (props.ref_proof && typeof props.ref_proof.deleteStep === 'function') {
    props.ref_proof.deleteStep(start, end)
  }
}

const setContext = (data) => {
  if (data.ctxt !== undefined) ctxt.value = data.ctxt
  if (data.steps !== undefined) steps.value = data.steps
  if (data.selected_start !== undefined) selected_start.value = data.selected_start
  if (data.selected_end !== undefined) selected_end.value = data.selected_end
}

defineExpose({
  setContext,
  deleteStep
})
</script>

<style scoped>
.item-text {
  font-family: Consolas, monospace;
}

.step-entry {
  cursor: pointer;
}

.step-selected {
  border: 1px solid black;
}

.step-error {
  background-color: red;
}
</style>

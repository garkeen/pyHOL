<template>
  <div>
    <input :value="modelValue"
           @input="$emit('update:modelValue', $event.target.value)"
           style="width:500px"/><br/>
    <MathEquation :data="'\\(' + latex_value + '\\)'"/>
  </div>
</template>

<script setup>
import { ref, watch, onMounted } from 'vue'
import api from '../../api'
import MathEquation from '../util/MathEquation.vue'

const props = defineProps({
  modelValue: {
    type: String,
    default: ''
  }
})

const emit = defineEmits(['update:modelValue'])

const latex_value = ref(undefined)

const update_latex_value = async (val) => {
  if (val === '' || val === undefined) {
    latex_value.value = undefined
    return
  }
  try {
    const response = await api.post('/query-expr', { expr: val })
    if (response.data.status === 'ok') {
      latex_value.value = response.data.latex_expr
    } else {
      latex_value.value = undefined
    }
  } catch (err) {
    latex_value.value = undefined
  }
}

watch(() => props.modelValue, (val) => {
  update_latex_value(val)
})

onMounted(() => {
  update_latex_value(props.modelValue)
})
</script>

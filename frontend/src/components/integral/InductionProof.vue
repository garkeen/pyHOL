<template>
  <div>
    <span class="math-text">by induction on </span>
    <MathEquation :data="'\\(' + item.induct_var + '\\)'"/>
    <span v-if="item.finished" style="color: green; font-weight: bold;"> ✓</span>
    <span v-else style="color: red; font-weight: bold;"> ✗</span><br/>
    <span class="math-text">{{ label }}1. Base case: </span>
    <span @click="$emit('select', label + '1.')"
          :class="{selected: selected_item === label + '1.'}">
      <MathEquation :data="'\\(' + item.base_case.latex_goal + '\\)'"/><br/>
    </span>
    <CalculationProof v-if="'proof' in item.base_case"
                      :item="item.base_case.proof" :label="label + '1.'"
                      :selected_item="selected_item"
                      :selected_facts="selected_facts"
                      @select="(lbl) => $emit('select', lbl)"/>
    <span class="math-text">{{ label }}2. Induction case: </span>
    <span @click="$emit('select', label + '2.')"
          :class="{selected: selected_item === label + '2.'}">
      <MathEquation :data="'\\(' + item.induct_case.latex_goal + '\\)'"/><br/>
    </span>
    <CalculationProof v-if="'proof' in item.induct_case"
                      :item="item.induct_case.proof" :label="label + '2.'"
                      :selected_item="selected_item"
                      :selected_facts="selected_facts"
                      @select="(lbl) => $emit('select', lbl)"/>
  </div>
</template>

<script setup>
import MathEquation from '../util/MathEquation.vue'
import CalculationProof from './CalculationProof.vue'

defineProps({
  item: Object,
  label: String,
  selected_item: [String, Number],
  selected_facts: Object
})

defineEmits(['select'])
</script>

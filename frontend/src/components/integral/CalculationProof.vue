<template>
  <div>
    <span class="math-text">by calculation</span>
    <span v-if="item.finished" style="color: green; font-weight: bold;"> ✓</span>
    <span v-else style="color: red; font-weight: bold;"> ✗</span><br/>
    <span class="math-text">{{ label }}1.</span>&nbsp;
    <span class="math-text">LHS: </span>
    <Calculation :item="item.lhs_calc" :label="label + '1.'"
                 :selected_item="selected_item"
                 :selected_facts="selected_facts"
                 @select="(lbl) => $emit('select', lbl)"/>
    <span class="math-text">{{ label }}2.</span>&nbsp;
    <span class="math-text">RHS: </span>
    <Calculation :item="item.rhs_calc" :label="label + '2.'"
                 :selected_item="selected_item"
                 :selected_facts="selected_facts"
                 @select="(lbl) => $emit('select', lbl)"/>
  </div>
</template>

<script setup>
import Calculation from './Calculation.vue'

defineProps({
  item: Object,
  label: String,
  selected_item: [String, Number],
  selected_facts: Object
})

defineEmits(['select'])
</script>

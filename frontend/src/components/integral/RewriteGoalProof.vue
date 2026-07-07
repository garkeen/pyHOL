<template>
  <div>
    <span class="math-text">by rewrite goal</span>
    <span v-if="item.finished" style="color: green; font-weight: bold;"> ✓</span>
    <span v-else style="color: red; font-weight: bold;"> ✗</span><br/>
    <span class="math-text">{{ label }}1.</span>&nbsp;
    <span class="math-text">Proof: </span>
    <Calculation :item="item.start" :label="label + '1.'"
                 :selected_item="selected_item"
                 :selected_facts="selected_facts"
                 :is_rewrite_goal_proof="true"
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

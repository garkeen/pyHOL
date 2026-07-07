<template>
  <div>
    <span @click.exact="$emit('select', label)"
          @click.ctrl="$emit('select_fact', label)"
          :class="{selected: selected_item === label,
                   'selected-fact': label in selected_facts}">
      <MathEquation v-if="is_rewrite_goal_proof && step.latex_res" :data="'\\(\\Rightarrow ' + step.latex_res + '\\)'" class="indented-text"/>
      <MathEquation v-else-if="step.latex_res" :data="'\\(=' + step.latex_res + '\\)'" class="indented-text"/>
      <span v-else class="indented-text">= {{ step.res }}</span>
    </span>
    <span v-if="step.rule && 'latex_str' in step.rule">
      &nbsp;<MathEquation :data="'(' + step.rule.latex_str + ')'" class="math-text"/>
    </span>
    <span v-else-if="step.rule" class="math-text">&nbsp;({{ step.rule.str }})</span>
  </div>
</template>

<script setup>
import MathEquation from '../util/MathEquation.vue'

defineProps({
  step: Object,
  label: String,
  selected_item: [String, Number],
  selected_facts: Object,
  is_rewrite_goal_proof: Boolean
})

defineEmits(['select', 'select_fact'])
</script>

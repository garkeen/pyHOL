<template>
  <div>
    <div>
      &nbsp;&nbsp;&nbsp;
      <span @click.exact="$emit('select', label)"
            @click.ctrl="$emit('select_fact', label)"
            :class="{selected: selected_item === label,
                     'selected-fact': label in selected_facts}">
        <MathEquation :data="'\\(' + item.latex_start + '\\)'" class="indented-text"/>
      </span>
    </div>
    <div v-for="(step, index) in item.steps" :key="index">
      <div v-if="step.type === 'CalculationStep'">
        <CalculationStep :step="step" :label="label + (index + 1) + '.'"
                         :selected_item="selected_item"
                         :selected_facts="selected_facts"
                         :is_rewrite_goal_proof="is_rewrite_goal_proof"
                         @select="(lbl) => $emit('select', lbl)"
                         @select_fact="(lbl) => $emit('select_fact', lbl)"/>
      </div>
    </div>
  </div>
</template>

<script setup>
import MathEquation from '../util/MathEquation.vue'
import CalculationStep from './CalculationStep.vue'

defineProps({
  item: Object,
  label: String,
  selected_item: [String, Number],
  selected_facts: Object,
  is_rewrite_goal_proof: Boolean
})

defineEmits(['select', 'select_fact'])
</script>

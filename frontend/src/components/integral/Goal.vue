<template>
  <div class="indented-label">
    <span class="math-text">{{ label }}</span>&nbsp;
    <div>
      <span class="math-text">Show</span>
      <span v-if="item.finished" style="color: green; font-weight: bold;"> ✓</span>
      <span v-else style="color: red; font-weight: bold;"> ✗</span>
      <div @click.exact="$emit('select', label)"
           @click.ctrl="$emit('select_fact', label)"
           :class="{selected: selected_item === label,
                    'selected-fact': label in selected_facts}">
        <MathEquation :data="'\\(' + item.latex_goal + '\\)'" class="indented-text"/>
        <span v-if="'conds' in item && item.conds.length > 0">
          <span class="math-text indented-text">for &nbsp;</span>
          <span v-for="(cond, index) in item.conds" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation :data="'\\(' + cond.latex_cond + '\\)'"/>
          </span>
        </span>
        <span v-if="'wellformed' in item && item.wellformed === false"
              title="Unable to show wellformed">
          ⚠
        </span>
      </div>
      <div v-if="'proof' in item">
        <div v-if="item.proof.type === 'CalculationProof'">
          <CalculationProof :item="item.proof" :label="label"
                            :selected_item="selected_item"
                            :selected_facts="selected_facts"
                            @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'InductionProof'">
          <InductionProof :item="item.proof" :label="label"
                          :selected_item="selected_item"
                          :selected_facts="selected_facts"
                          @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'RewriteGoalProof'">
          <RewriteGoalProof :item="item.proof" :label="label"
                            :selected_item="selected_item"
                            :selected_facts="selected_facts"
                            @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'CaseProof'">
          <CaseProof :item="item.proof" :label="label"
                     :selected_item="selected_item"
                     :selected_facts="selected_facts"
                     @select="(lbl) => $emit('select', lbl)"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
import MathEquation from '../util/MathEquation.vue'
import CalculationProof from './CalculationProof.vue'
import InductionProof from './InductionProof.vue'
import RewriteGoalProof from './RewriteGoalProof.vue'
import CaseProof from './CaseProof.vue'

defineProps({
  item: Object,
  label: String,
  selected_item: [String, Number],
  selected_facts: Object
})

defineEmits(['select', 'select_fact'])
</script>

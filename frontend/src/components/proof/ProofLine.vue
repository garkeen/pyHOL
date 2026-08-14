<template>
  <div v-if="line !== undefined && line.rule !== 'intros'" 
       style="font-size:14px;white-space:nowrap"
       :style="styleObject" 
       @mouseenter="hover = can_select"
       @mouseleave="hover = false">
    <span style="display:inline-block;width:40px">#{{line.id || line.sid}}</span>
    <span class="item-text" v-html="indent"/>
    <span v-if="line.rule === 'assume'">
      <span class="item-text keyword2">assume </span>
      <span class="sid-inline">[{{line.sid}}]</span>
      <span :class="{'fact-clickable': can_select, 'fact-selected': is_fact}" @click.stop="$emit('select-fact')">
        <Expression v-if="propDisplay" :line="propDisplay"/>
      </span>
    </span>
    <span v-else-if="line.rule === 'variable'">
      <span class="item-text keyword2">fix </span>
      <span class="sid-inline">[{{line.sid}}]</span>
      <Expression v-if="argDisplay" :line="argDisplay"/>
    </span>
    <span v-else-if="line.rule === 'subproof'">
      <span v-if="line.case" class="item-text keyword3">case {{line.case}}: </span>
      <span class="item-text keyword1">have </span>
      <span class="sid-inline">[{{line.sid}}]</span>
      <span :class="{'fact-clickable': can_select, 'fact-selected': is_fact}" @click.stop="$emit('select-fact')">
        <Expression v-if="propDisplay" :line="propDisplay"/>
      </span>
      <span class="item-text keyword1"> with</span>
    </span>
    <span v-else-if="line.rule === 'obtain'">
      <span class="item-text keyword2">obtain </span>
      <span class="sid-inline">[{{line.sid}}]</span>
      <span class="item-text">{{line.args}}</span>
      <span v-if="line.prevs && line.prevs.length > 0">
        <span class="item-text keyword3"> from </span>
        <span class="item-text">[{{line.prevs.join(', ')}}]</span>
      </span>
    </span>
    <span v-else>
      <span v-if="line.case" class="item-text keyword3">case {{line.case}}: </span>
      <span v-if="line.origin === 'cut'" class="item-text keyword2">cut </span>
      <span v-else-if="line.goal_pos !== false" class="item-text keyword2">show </span>
      <span v-else class="item-text keyword1">have </span>
      <span class="sid-inline">[{{line.sid}}]</span>
      <span :class="{'fact-clickable': can_select, 'fact-selected': is_fact}" @click.stop="$emit('select-fact')">
        <Expression v-if="propDisplay" :line="propDisplay"/>
      </span>
      <span class="item-text keyword3"> by </span>
      <span v-if="line.rule === 'sorry'" class="sorry-clickable" 
            :class="{'sorry-goal': is_goal}"
            @click.stop="$emit('select-goal')">{{line.origin === 'cut' ? 'cut' : 'sorry'}}</span>
      <span v-else-if="!APPLY_THEOREM_RULES.includes(line.rule)" class="item-text">{{line.rule}} </span>
      <span v-if="argDisplay">
        <Expression :line="argDisplay"/>
      </span>
      <span v-if="line.prevs && line.prevs.length > 0">
        <span class="item-text keyword3"> from </span>
        <span class="item-text">[{{line.prevs.join(', ')}}]</span>
      </span>
    </span>
  </div>
</template>

<script setup>
import { ref, computed } from 'vue'
import Expression from '../util/Expression.vue'

const props = defineProps({
  line: {
    type: Object,
    required: true
  },
  is_goal: {
    type: Boolean,
    default: false
  },
  is_fact: {
    type: Boolean,
    default: false
  },
  can_select: {
    type: Boolean,
    default: false
  }
})

defineEmits(['select-fact', 'select-goal'])

const hover = ref(false)

const APPLY_THEOREM_RULES = ['apply_theorem', 'apply_theorem_for', 'apply_theorem_inst', 'rewrite_fact', 'rewrite_fact_sym', 'resolve_theorem']

const indent = computed(() => {
  let result = ''
  if (props.line && props.line.indent !== undefined) {
    for (let i = 0; i < props.line.indent; i++) {
      result += '&nbsp;&nbsp;'
    }
  }
  return result
})

// New stable-ID backend sends plain-text th/args (no th_hl/args_hl highlights).
const propDisplay = computed(() => {
  const line = props.line
  if (!line) return ''
  if (line.th_hl) return line.th_hl
  return line.th || ''
})

const argDisplay = computed(() => {
  const line = props.line
  if (!line) return ''
  if (line.args_hl) return line.args_hl
  if (line.args === undefined || line.args === null) return ''
  if (Array.isArray(line.args)) return line.args.join(', ')
  return String(line.args)
})

const styleObject = computed(() => {
  if (hover.value && props.can_select) {
    return {backgroundColor: '#f8f9fa'}
  } else {
    return {}
  }
})
</script>

<style scoped>
.sid-inline { color: #888; font-size: 10px; }
.fact-clickable { cursor: pointer; border-radius: 2px; padding: 0 2px; }
.fact-clickable:hover { background: #e8f0fe; }
.fact-selected { background: #ffd54f; font-weight: 600; }
.sorry-clickable { cursor: pointer; padding: 0 4px; border-radius: 2px; font-weight: bold; color: #c0392b; }
.sorry-clickable:hover { background: #ffe0e0; }
.sorry-goal { background: #ff6b6b; color: white; }
.keyword1 {
  color: darkblue;
  font-weight: bold;
}

.keyword2 {
  color: darkcyan;
  font-weight: bold;
}

.keyword3 {
  color: black;
  font-weight: bold;
}
</style>

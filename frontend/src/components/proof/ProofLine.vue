<template>
  <div v-if="line !== undefined && line.rule !== 'intros'" 
       style="font-size:14px;white-space:nowrap"
       :style="styleObject" 
       @click="$emit('select')"
       @mouseenter="hover = can_select"
       @mouseleave="hover = false">
    <span style="display:inline-block;width:40px">{{line.id}}</span>
    <span class="item-text" v-html="indent"/>
    <span v-if="line.rule === 'assume'">
      <span class="item-text keyword2">assume </span>
      <Expression v-if="line.args_hl" :line="line.args_hl"/>
    </span>
    <span v-else-if="line.rule === 'variable'">
      <span class="item-text keyword2">fix </span>
      <Expression v-if="line.args_hl" :line="line.args_hl"/>
    </span>
    <span v-else-if="line.rule === 'subproof'">
      <span class="item-text keyword1">have </span>
      <Expression v-if="line.th_hl" :line="line.th_hl"/>
      <span class="item-text keyword1"> with</span>
    </span>
    <span v-else>
      <span v-if="is_last_id" class="item-text keyword2">show </span>
      <span v-else class="item-text keyword1">have </span>
      <Expression v-if="line.th_hl" :line="line.th_hl"/>
      <span class="item-text keyword3"> by </span>
      <span v-if="line.rule === 'sorry' && is_goal" class="item-text" style="background-color:red">sorry</span>
      <span v-else class="item-text">{{line.rule}} </span>
      <span v-if="line.args_hl && line.args_hl.length > 0">
        <Expression :line="line.args_hl"/>
      </span>
      <span v-if="line.prevs && line.prevs.length > 0">
        <span class="item-text keyword3"> from </span>
        <span class="item-text">{{line.prevs.join(', ')}}</span>
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
  is_last_id: {
    type: Boolean,
    default: false
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

defineEmits(['select'])

const hover = ref(false)

const indent = computed(() => {
  let result = ''
  if (props.line && props.line.id) {
    for (let i = 0; i < props.line.id.length; i++) {
      if (props.line.id[i] === '.') {
        result += '&nbsp;&nbsp;'
      }
    }
  }
  return result
})

const styleObject = computed(() => {
  if (props.is_fact) {
    return {backgroundColor: 'yellow'}
  } else if (hover.value) {
    return {backgroundColor: 'lightYellow'}
  } else {
    return {}
  }
})
</script>

<style scoped>
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

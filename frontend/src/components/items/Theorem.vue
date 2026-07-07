<template>
  <div>
    <span class="keyword">theorem</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:
    <a href="#" @click.prevent="$emit('edit')" title="edit" class="edit-icon">
      &#9998;
    </a>
    <a href="#" @click.prevent="$emit('proof')" style="margin-left:10px">
      <span v-if="proof === undefined" style="color:red" title="no proof">&#10008;</span>
      <span v-else-if="num_gaps > 0" style="color:orange" :title="num_gaps + ' gap(s)'">&#10008;</span>
      <span v-else style="color:green" title="qed">&#10004;</span>
    </a>
    <br>
    <span v-if="display && display.prop">
      <span v-for="(line, i) in display.prop" :key="i">
        <Expression class="indented-text" :line="line" :editor="editor"/><br>
      </span>
    </span>
    <span v-else>
      <span class="indented-text">{{item.prop}}</span>
    </span>
  </div>
</template>

<script setup>
import Expression from '../util/Expression.vue'

const props = defineProps({
  item: {
    type: Object,
    required: true
  },
  display: {
    type: Object,
    default: null
  },
  proof: {
    type: Object,
    default: undefined
  },
  num_gaps: {
    type: Number,
    default: 0
  },
  editor: {
    type: Object,
    default: null
  }
})

defineEmits(['edit', 'proof'])
</script>

<style scoped>
.edit-icon {
  margin-left: 10px;
  color: #6c757d;
  text-decoration: none;
  font-size: 16px;
  padding: 2px 5px;
  border-radius: 3px;
  transition: all 0.2s ease;
}

.edit-icon:hover {
  color: #007bff;
  background-color: #e9ecef;
  text-decoration: none;
}
</style>

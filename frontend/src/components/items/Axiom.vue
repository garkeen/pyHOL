<template>
  <div>
    <span class="keyword">axiom</span>&nbsp;
    <span class="item-text">{{item.name}}</span>:&nbsp;
    <a href="#" title="edit" @click.prevent="$emit('edit')" class="edit-icon">
      &#9998;
    </a>
    <br>
    <span v-if="'prop' in item">
      <span v-for="(line, i) in item.prop" :key="i">
        <Expression class="indented-text" :line="line" :editor="editor"/><br>
      </span>
    </span>
  </div>
</template>

<script setup>
import Expression from '../util/Expression.vue'

defineProps({
  item: {
    type: Object,
    required: true
  },
  editor: {
    type: Object,
    default: null
  }
})

defineEmits(['edit'])
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

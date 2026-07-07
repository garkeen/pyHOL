<template>
  <div>
    <span class="keyword">{{item.ty === 'def.ind' ? 'fun' : 'inductive'}}</span>&nbsp;
    <span class="item-text">{{item.name}}</span> ::
    <Expression :line="item.type" :editor="editor"/>&nbsp;
    <span class="keyword">where</span>
    <a href="#" @click.prevent="$emit('edit')" title="edit" class="edit-icon">&#9998;</a>
    <span v-for="(v, i) in item.rules" :key="i">
      <br><Expression :line="v" :editor="editor" class="indented-text"/>
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

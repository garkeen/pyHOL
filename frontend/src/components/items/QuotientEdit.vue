<template>
  <form>
    <div class="qrow">
      <label class="keyword">quotient</label>
      <input class="form-control form-control-sm d-inline-block ms-2" style="width:140px"
             v-model="local.name" placeholder="new type name"/>
      <span class="form-element">(</span>
      <input class="form-control form-control-sm d-inline-block" style="width:120px"
             v-model="local.abs" placeholder="abs"/>
      <span class="form-element">,</span>
      <input class="form-control form-control-sm d-inline-block" style="width:120px"
             v-model="local.rep" placeholder="rep"/>
      <span class="form-element">)</span>
    </div>
    <div class="qrow">
      <label class="keyword">relation</label>
      <ExpressionEdit v-model="local.rel" min-width="240" single-line/>
    </div>
    <div class="hint">
      Relation must have type <code>A ⇒ A ⇒ bool</code>; its type variables fix the arity.
      Annotate it when the type is not inferable, e.g.
      <code>(equals :: 'a ⇒ 'a ⇒ bool)</code> — the parentheses are required.
    </div>
    <div v-if="props.item.type" class="hint">Type: {{ props.item.type }}</div>
  </form>
</template>

<script setup>
import { reactive } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({ item: { type: Object, required: true } })

const local = reactive({
  name: typeof props.item.name === 'string' ? props.item.name : '',
  abs: typeof props.item.abs === 'string' ? props.item.abs : '',
  rep: typeof props.item.rep === 'string' ? props.item.rep : '',
  rel: typeof props.item.rel === 'string' ? props.item.rel : ''
})

defineExpose({
  getData: () => ({
    ty: 'type.quot',
    name: local.name,
    abs: local.abs,
    rep: local.rep,
    rel: local.rel
  })
})
</script>

<style scoped>
.keyword { font-weight: bold; color: #006000; margin-right: 5px; }
.form-element { margin: 0 4px; font-family: Consolas, monospace; }
.qrow { display: flex; align-items: center; gap: 2px; margin-bottom: 6px; }
.hint { font-size: 11px; color: #888; margin-top: 4px; }
code { font-family: Consolas, monospace; }
</style>

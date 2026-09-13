<template>
  <form>
    <span>
      <label class="keyword">typeabbrev</label>
      <input class="form-control form-control-sm d-inline-block ms-2" style="width:160px"
             v-model="local.name" placeholder="synonym name"/>
      <label class="keyword ms-2">args</label>
      <input class="form-control form-control-sm d-inline-block ms-2" style="width:140px"
             v-model="local.args_str" placeholder="'a, 'b"/>
      <span class="form-element">=</span>
      <ExpressionEdit v-model="local.def" min-width="200" single-line/>
    </span>
    <div class="hint">Names an existing type expression; introduces no new type and no axioms.</div>
  </form>
</template>

<script setup>
import { reactive } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({ item: { type: Object, required: true } })

const local = reactive({
  name: typeof props.item.name === 'string' ? props.item.name : '',
  args_str: Array.isArray(props.item.args) ? props.item.args.join(', ') : '',
  def: typeof props.item.def === 'string' ? props.item.def : ''
})

defineExpose({
  getData: () => ({
    ty: 'type.abbrev',
    name: local.name,
    args: local.args_str.split(',').map(s => s.trim()).filter(Boolean),
    def: local.def
  })
})
</script>

<style scoped>
.keyword { font-weight: bold; color: #006000; margin-right: 5px; }
.form-element { margin: 0 4px; font-family: Consolas, monospace; }
.hint { font-size: 11px; color: #888; margin-top: 4px; }
</style>

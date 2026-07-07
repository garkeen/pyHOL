<template>
  <form>
    <span>
      <label class="keyword">{{item.ty === 'thm.ax' ? 'axiom' : 'theorem'}}</label>
      <ExpressionEdit v-model="item.name" single-line/>
    </span>
    <div style="margin-top:5px">
      <label class="keyword">fixes</label>
      <ExpressionEdit v-model="item.vars"/>
    </div>
    <div style="margin-top:5px">
      <label class="keyword">shows</label>
      <ExpressionEdit v-model="item.prop"/>
    </div>
    <div style="margin-top:10px">
      <span class="hint-element" title="Used as backward rule: conclusion matches goal">
        <input type="checkbox" :id="'backward-check' + id" value="hint_backward"
               v-model="item.attributes">
        <label :for="'backward-check' + id">Backward</label>
      </span>
      <span class="hint-element" title="Used as backward rule with priority">
        <input type="checkbox" :id="'backward1-check' + id" value="hint_backward1"
               v-model="item.attributes">
        <label :for="'backward1-check' + id">Backward1</label>
      </span>
      <span class="hint-element" title="Used as forward rule: premises match known facts">
        <input type="checkbox" :id="'forward-check' + id" value="hint_forward"
               v-model="item.attributes">
        <label :for="'forward-check' + id">Forward</label>
      </span>
      <span class="hint-element" title="Used as rewrite rule: replaces LHS with RHS">
        <input type="checkbox" :id="'rewrite-check' + id" value="hint_rewrite"
               v-model="item.attributes">
        <label :for="'rewrite-check' + id">Rewrite</label>
      </span>
      <span class="hint-element" title="Used as symmetric rewrite rule: replaces RHS with LHS">
        <input type="checkbox" :id="'rewrite-sym-check' + id" value="hint_rewrite_sym"
               v-model="item.attributes">
        <label :for="'rewrite-sym-check' + id">Rewrite (sym)</label>
      </span>
      <span class="hint-element" title="Used for resolution with goal">
        <input type="checkbox" :id="'resolve-check' + id" value="hint_resolve"
               v-model="item.attributes">
        <label :for="'resolve-check' + id">Resolve</label>
      </span>
    </div>
  </form>
</template>

<script setup>
import { reactive, computed } from 'vue'
import ExpressionEdit from '../util/ExpressionEdit.vue'

const props = defineProps({
  old_item: {
    type: Object,
    required: true
  }
})

const item = reactive(
  Object.assign(
    {
      attributes: [],
      name: "",
      vars: "",
      prop: ""
    },
    JSON.parse(JSON.stringify(props.old_item))
  )
)

const id = computed(() => {
  return props.old_item.ty + '.' + props.old_item.name
})

defineExpose({
  getData: () => JSON.parse(JSON.stringify(item))
})
</script>

<style scoped>
.keyword {
  font-weight: bold;
  color: #006000;
  margin-right: 5px;
}

.hint-element {
  margin-right: 10px;
}

.hint-element label {
  margin-left: 3px;
}
</style>

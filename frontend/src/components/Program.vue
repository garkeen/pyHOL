<template>
  <div>
    <div v-for="(line, index) in lines" :key="index" class="program-line">
      <div v-if="line.ty === 'com'">
        <span class="display-con">{{'&nbsp;'.repeat(line.indent)}}</span>
        <span class="display-con">{{line.str}}</span>
      </div>
      <div v-else-if="line.ty === 'inv'">
        <span class="display-con">{{'&nbsp;'.repeat(line.indent)}}</span>
        <span class="line-comment">inv:&nbsp;</span>
        <span class="display-con">{{line.str}}</span>
      </div>
      <div v-else>
        <span class="display-con">{{'&nbsp;'.repeat(line.indent)}}</span>
        <span class="line-comment">vc:&nbsp;&nbsp;&nbsp;</span>
        <span class="display-con">{{line.str}}</span>
        <span v-if="line.smt" style="margin-left:30px;color:green">OK</span>
        <a href="#" v-else style="margin-left:30px;color:red"
           @click.prevent="on_proof = index">Failed</a>
        <div v-if="on_proof === index" style="margin:10px 0; padding:10px; background:#f9f9f9; border:1px solid #ddd">
          <ProofArea theory_name="hoare" thm_name=""
                    :vars="line.vars" :prop="line.prop"
                    :editor="editor"
                    :ref="(el) => { proofRef = el }"
                    @set-message="$emit('set-message', $event)"
                    @set-status="handle_set_status"
                    @set-context="handle_set_context"
                    @query="handle_query"/>
          <div style="margin-top:10px">
            <button class="btn btn-sm btn-success" @click="save_proof">Save</button>
            <button class="btn btn-sm btn-warning" style="margin-left:5px" @click="reset_proof">Reset</button>
            <button class="btn btn-sm btn-secondary" style="margin-left:5px" @click="cancel_proof">Cancel</button>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref, watch, nextTick } from 'vue'
import ProofArea from './proof/ProofArea.vue'

const props = defineProps({
  lines: {
    type: Array,
    default: () => []
  },
  editor: {
    type: Object,
    default: null
  },
  ref_status: {
    type: Object,
    default: null
  },
  ref_context: {
    type: Object,
    default: null
  }
})

const emit = defineEmits(['set-proof', 'query', 'save-proof', 'set-message'])

const on_proof = ref(undefined)
let proofRef = null

const init_lines = () => {
  for (let i = 0; i < props.lines.length; i++) {
    if (!props.lines[i].smt) {
      on_proof.value = i
      break
    }
  }
}

const handle_set_status = (data) => {
  if (props.ref_status) {
    props.ref_status.setStatus(data)
  }
}

const handle_set_context = (data) => {
  if (props.ref_context) {
    props.ref_context.setContext(data)
  }
}

const handle_query = (query) => {
  emit('query', query)
}

const save_proof = () => {
  if (!proofRef) return
  
  let output_proof = undefined
  if (proofRef.steps && proofRef.steps.value && proofRef.steps.value.length !== 0) {
    if (proofRef.proof && proofRef.proof.value) {
      output_proof = []
      for (let i = 0; i < proofRef.proof.value.length; i++) {
        const line = JSON.parse(JSON.stringify(proofRef.proof.value[i]))
        delete line.th_hl
        delete line.args_hl
        output_proof.push(line)
      }
    }
  }

  emit('save-proof', output_proof)
  on_proof.value = undefined
}

const reset_proof = () => {
  if (proofRef && typeof proofRef.init_proof === 'function') {
    proofRef.init_proof()
  }
}

const cancel_proof = () => {
  on_proof.value = undefined
}

watch(() => props.lines, () => {
  init_lines()
})

watch(() => on_proof.value, () => {
  nextTick(() => {
    if (proofRef) {
      emit('set-proof', proofRef)
    }
  })
})
</script>

<style scoped>
.line-comment {
  font-size: 12px;
  margin-right: 2px;
}

.program-line {
  margin-left: 20px;
}

.display-con {
  font-size: 18px;
  font-family: Consolas, monospace;
}
</style>

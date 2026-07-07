<template>
  <span class="expression-edit-wrapper">
    <pre class="test-width" ref="test_width"></pre>
    <input v-if="singleLine"
        spellcheck="false" class="form-element"
        @input="handle_input($event)"
        @keydown="replace_unicode($event)"
        :value="displayValue"
        ref="input"/>
    <textarea v-else
        spellcheck="false" class="form-element form-textarea"
        @input="handle_input($event)"
        @keydown="replace_unicode($event)"
        :value="displayValue"
        :rows="rows"
        ref="input"/>
  </span>
</template>

<script setup>
import { ref, computed, onMounted } from 'vue'

const props = defineProps({
  minWidth: {
    default: "300",
    type: String
  },
  singleLine: {
    default: false,
    type: Boolean
  },
  modelValue: {
    default: '',
    type: [String, Array]
  }
})

const emit = defineEmits(['update:modelValue'])

const input = ref(null)
const test_width = ref(null)

const displayValue = computed(() => {
  if (Array.isArray(props.modelValue)) {
    return props.modelValue.map(item => {
      if (typeof item === 'object' && item.text) return item.text
      return String(item)
    }).join('\n')
  }
  return props.modelValue || ''
})

const rows = computed(() => {
  return Math.max(1, displayValue.value.split('\n').length)
})

const replace_obj = [
  ["\\lambda", "λ"],
  ["%", "λ"],
  ["\\forall", "∀"],
  ["!", "∀"],
  ["\\exists", "∃"],
  ["?", "∃"],
  ["\\and", "∧"],
  ["&", "∧"],
  ["\\or", "∨"],
  ["|", "∨"],
  ["<-->", "⟷"],
  ["-->", "⟶"],
  ["~", "¬"],
  ["\\not", "¬"],
  ["=>", "⇒"],
  ["\\empty", "∅"],
  ["\\Inter", "⋂"],
  ["\\inter", "∩"],
  ["\\Union", "⋃"],
  ["\\union", "∪"],
  ["\\circ", "∘"],
  ["\\in", "∈"],
  ["\\subset", "⊆"],
  ["<=", "≤"],
  [">=", "≥"],
]

const adjust_input_size = () => {
  if (!input.value || !test_width.value) return
  const text = input.value.value
  test_width.value.textContent = text
  test_width.value.style.display = 'inline-block'
  const width = test_width.value.offsetWidth
  test_width.value.style.display = 'none'
  input.value.style.width = width + 'px'
  if (width < Number(props.minWidth)) {
    input.value.style.width = props.minWidth + 'px'
  }
  input.value.rows = Math.max(1, text.split('\n').length)
}

const handle_input = (event) => {
  emit('update:modelValue', event.target.value)
  adjust_input_size()
}

const replace_unicode = (event) => {
  if (!input.value) return
  const content = input.value.value.trim()
  let pos = input.value.selectionStart
  if (pos !== 0 && event.keyCode === 9) {
    let len = ''
    for (let i = 0; i < replace_obj.length; i++) {
      const s = replace_obj[i][0]
      const repl_s = replace_obj[i][1]
      const l = s.length
      if (content.substring(pos - l, pos) === s) {
        if (event && event.preventDefault) {
          event.preventDefault()
        } else {
          window.event.returnValue = false
        }
        len = l
        const new_content = content.slice(0, pos - len) + repl_s + content.slice(pos)
        input.value.value = new_content
        input.value.setSelectionRange(pos - len + 1, pos - len + 1)
      }
    }
  }
}

onMounted(() => {
  adjust_input_size()
})
</script>

<style scoped>
.expression-edit-wrapper {
  display: inline;
}

.form-element {
  margin: 0 3px;
  padding: 4px 8px;
  font-family: Consolas, monospace;
  font-size: 14px;
  border: 1px solid #ced4da;
  border-radius: 4px;
  background-color: #fff;
  vertical-align: middle;
}

.form-textarea {
  display: block;
  min-width: 400px;
  max-width: 100%;
  box-sizing: border-box;
  min-height: 28px;
  resize: vertical;
  margin-top: 4px;
}

.form-element:focus {
  outline: none;
  border-color: #80bdff;
  box-shadow: 0 0 0 0.2rem rgba(0, 123, 255, 0.25);
}

.test-width {
    display: none;
    padding: 10px;
    font-family: Consolas, monospace;
    font-size: 14px;
}
</style>

<template>
  <template v-if="typeof node === 'string'">
    <span>{{ node }}</span>
  </template>
  <template v-else>
    <span :style="{color: get_color(node.color)}"
          v-html="node.text.replace(/ /g, '&nbsp;')"
          @click.ctrl="handleClick($event)"
          @mouseenter.ctrl="handleMouseEnter"
          @mouseleave="handleMouseLeave"
          :class="{onhover: hover}"/>
  </template>
</template>

<script setup>
import { ref } from 'vue'
import api from '../../api'

const props = defineProps({
  node: {
    type: Object,
    required: true
  },
  editor: {
    type: Object,
    default: null
  }
})

const hover = ref(false)

const handleMouseEnter = () => {
  if ('link_ty' in props.node)
    hover.value = true
}

const handleMouseLeave = () => {
  if ('link_ty' in props.node)
    hover.value = false
}

const get_color = (x) => {
  if (x === 0) return 'black'
  else if (x === 1) return '#006000'
  else if (x === 2) return 'blue'
  else if (x === 3) return 'purple'
  else if (x === 4) return 'silver'
  else if (x === 5) return 'red'
  else if (x === 6) return 'green'
  return 'black'
}

const handleClick = async () => {
  if ('link_ty' in props.node && props.editor) {
    let name = props.node.link_name
    if (name === '') {
      name = props.node.text
    }
    const data = {
      filename: props.editor.filename,
      ext_ty: props.node.link_ty,
      name: name
    }
    const response = await api.post('/find-link', data)
    if ('filename' in response.data) {
      props.editor.handleGoToLink(response.data.filename, response.data.index)
    }
  }
}
</script>

<style scoped>
.onhover {
  text-decoration: underline;
  cursor: pointer;
}
</style>

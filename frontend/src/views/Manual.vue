<template>
  <div class="manual-container">
    <nav class="navbar navbar-expand navbar-dark bg-dark">
      <div class="container-fluid">
        <span class="navbar-brand" style="padding-left: 44px">HOLPy</span>
        <div class="ms-auto d-flex align-items-center gap-3">
          <router-link :to="{name: 'main'}" class="btn btn-sm btn-outline-light">Home</router-link>
        </div>
      </div>
    </nav>

    <div class="main-content">
      <FileSidebar title="Manual" :files="file_names" :active="current" :show-actions="false" @open="load_file"/>

      <div class="manual-body">
        <div v-if="loading" class="loading-state"><div class="spinner"></div><p>Loading...</p></div>
        <div v-else-if="html" class="manual-content" @click="on_click" v-html="html"></div>
        <div v-else class="empty-state"><h4>Select a file</h4></div>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref, computed, onMounted } from 'vue'
import api from '../api/index'
import FileSidebar from '../components/FileSidebar.vue'

const files = ref([])
const current = ref('')
const html = ref('')
const loading = ref(false)

const file_names = computed(() => files.value.map(f => f.name))

const load_file = async (name) => {
  current.value = name
  loading.value = true
  try {
    const res = await api.post('/manual-load', { name })
    html.value = res.data.ok ? render_markdown(res.data.text) : `<div class="alert alert-danger">${escape_html(res.data.error || '')}</div>`
  } catch (e) {
    html.value = '<div class="alert alert-danger">Failed to load manual</div>'
  } finally {
    loading.value = false
  }
}

const on_click = (e) => {
  const a = e.target.closest('a')
  if (!a) return
  const href = a.getAttribute('href') || ''
  if (href.endsWith('.md')) {
    e.preventDefault()
    load_file(href.slice(0, -3))
  }
}

onMounted(async () => {
  const res = await api.post('/manual-list', {})
  files.value = res.data.files || []
  if (files.value.length) load_file(files.value[0].name)
})

// ── tiny markdown renderer (no formulas, no HTML passthrough) ──────────

const escape_html = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')

const inline = (s) => {
  let out = escape_html(s)
  out = out.replace(/`([^`]+)`/g, (m, c) => `<code>${c}</code>`)
  out = out.replace(/\*\*([^*]+)\*\*/g, (m, c) => `<strong>${c}</strong>`)
  out = out.replace(/\*([^*]+)\*/g, (m, c) => `<em>${c}</em>`)
  out = out.replace(/\[([^\]]+)\]\(([^)]+)\)/g, (m, t, u) => `<a href="${u}" target="_blank" rel="noopener">${t}</a>`)
  return out
}

const render_markdown = (md) => {
  const lines = md.split('\n')
  const out = []
  let i = 0

  const flush_list = () => {
    if (!list_stack.length) return
    while (list_stack.length) {
      out.push('</li></ul>')
      list_stack.pop()
    }
  }

  let list_stack = []

  while (i < lines.length) {
    const line = lines[i]

    // Fenced code block
    if (/^```/.test(line)) {
      flush_list()
      const buf = []
      i++
      while (i < lines.length && !/^```/.test(lines[i])) {
        buf.push(escape_html(lines[i]))
        i++
      }
      i++
      out.push(`<pre><code>${buf.join('\n')}</code></pre>`)
      continue
    }

    // Heading
    const hm = line.match(/^(#{1,6})\s+(.*)$/)
    if (hm) {
      flush_list()
      const lvl = hm[1].length
      out.push(`<h${lvl}>${inline(hm[2])}</h${lvl}>`)
      i++
      continue
    }

    // Horizontal rule
    if (/^\s*(---|\*\*\*)\s*$/.test(line)) {
      flush_list()
      out.push('<hr/>')
      i++
      continue
    }

    // Blockquote
    if (/^>\s?/.test(line)) {
      flush_list()
      const buf = []
      while (i < lines.length && /^>\s?/.test(lines[i])) {
        buf.push(lines[i].replace(/^>\s?/, ''))
        i++
      }
      out.push(`<blockquote>${inline(buf.join(' '))}</blockquote>`)
      continue
    }

    // Table
    if (line.includes('|') && i + 1 < lines.length && /^\s*\|?[\s:|-]+\|?\s*$/.test(lines[i + 1]) && lines[i + 1].includes('-')) {
      flush_list()
      const header = line.split('|').map(c => c.trim()).filter((c, idx, arr) => !(idx === 0 && c === '') && !(idx === arr.length - 1 && c === ''))
      i += 2
      const rows = []
      while (i < lines.length && lines[i].includes('|')) {
        rows.push(lines[i].split('|').map(c => c.trim()).filter((c, idx, arr) => !(idx === 0 && c === '') && !(idx === arr.length - 1 && c === '')))
        i++
      }
      let t = '<table><thead><tr>'
      for (const h of header) t += `<th>${inline(h)}</th>`
      t += '</tr></thead><tbody>'
      for (const r of rows) {
        t += '<tr>'
        for (const c of r) t += `<td>${inline(c)}</td>`
        t += '</tr>'
      }
      out.push(t + '</tbody></table>')
      continue
    }

    // Unordered / ordered list
    const ulm = line.match(/^(\s*)([-*])\s+(.*)$/)
    const olm = line.match(/^(\s*)(\d+)[.)]\s+(.*)$/)
    if (ulm || olm) {
      const indent = (ulm || olm)[1].length
      const ordered = !!olm
      const content = (ulm || olm)[3]
      while (list_stack.length && list_stack[list_stack.length - 1].indent > indent) {
        out.push('</li></ul>')
        list_stack.pop()
      }
      if (!list_stack.length || list_stack[list_stack.length - 1].indent < indent) {
        out.push(`<ul class="${ordered ? 'list-ordered' : ''}">`)
        list_stack.push({ indent })
      } else {
        out.push('</li>')
      }
      out.push(`<li>${inline(content)}`)
      i++
      continue
    }

    // Blank line: end paragraph / list
    if (/^\s*$/.test(line)) {
      flush_list()
      i++
      continue
    }

    // Paragraph: collect consecutive lines
    flush_list()
    const buf = []
    while (i < lines.length && !/^\s*$/.test(lines[i]) &&
           !/^```/.test(lines[i]) && !/^#{1,6}\s/.test(lines[i]) &&
           !/^>\s?/.test(lines[i]) && !/^(\s*)([-*]|\d+[.)])\s+/.test(lines[i])) {
      buf.push(lines[i])
      i++
    }
    out.push(`<p>${inline(buf.join(' '))}</p>`)
  }

  flush_list()
  return out.join('\n')
}
</script>

<style scoped>
.manual-container { height: 100vh; display: flex; flex-direction: column; }
.main-content { flex: 1; display: flex; min-height: 0; }
.manual-body { flex: 1; overflow-y: auto; min-width: 0; }
.manual-content {
  max-width: 900px; margin: 0 auto; padding: 28px 40px 60px 40px;
  line-height: 1.7; font-size: 15px;
}
.manual-content :deep(h1) { font-size: 26px; border-bottom: 1px solid #dee2e6; padding-bottom: 8px; margin: 28px 0 16px 0; }
.manual-content :deep(h1:first-child) { margin-top: 0; }
.manual-content :deep(h2) { font-size: 21px; border-bottom: 1px solid #e9ecef; padding-bottom: 6px; margin: 26px 0 14px 0; }
.manual-content :deep(h3) { font-size: 17px; margin: 22px 0 10px 0; }
.manual-content :deep(h4) { font-size: 15.5px; margin: 18px 0 8px 0; }
.manual-content :deep(p) { margin: 10px 0; }
.manual-content :deep(code) {
  font-family: Consolas, monospace; font-size: 13px;
  background: #f0f2f5; padding: 1px 5px; border-radius: 3px;
}
.manual-content :deep(pre) {
  background: #f6f8fa; border: 1px solid #e1e4e8; border-radius: 6px;
  padding: 12px 16px; overflow-x: auto; margin: 12px 0;
}
.manual-content :deep(pre code) { background: none; padding: 0; font-size: 13px; line-height: 1.5; }
.manual-content :deep(table) { border-collapse: collapse; margin: 12px 0; width: 100%; }
.manual-content :deep(th), .manual-content :deep(td) {
  border: 1px solid #dee2e6; padding: 6px 12px; font-size: 14px;
}
.manual-content :deep(th) { background: #f6f8fa; }
.manual-content :deep(blockquote) {
  border-left: 4px solid #dee2e6; margin: 12px 0; padding: 2px 16px; color: #555;
}
.manual-content :deep(hr) { margin: 24px 0; border-top: 1px solid #dee2e6; }
.manual-content :deep(ul) { padding-left: 24px; margin: 8px 0; }
.manual-content :deep(ol) { padding-left: 24px; margin: 8px 0; }
.manual-content :deep(li) { margin: 3px 0; }
.manual-content :deep(a) { color: #0d6efd; text-decoration: none; }
.manual-content :deep(a:hover) { text-decoration: underline; }
.loading-state { display: flex; flex-direction: column; align-items: center; justify-content: center; height: 100%; color: #6c757d; }
.spinner {
  width: 28px; height: 28px; border: 3px solid #dee2e6; border-top-color: #0d6efd;
  border-radius: 50%; animation: spin 0.8s linear infinite; margin-bottom: 10px;
}
@keyframes spin { to { transform: rotate(360deg); } }
.empty-state { display: flex; align-items: center; justify-content: center; height: 100%; color: #6c757d; }
</style>

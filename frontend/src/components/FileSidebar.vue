<template>
  <div class="fs-root">
    <!-- Hamburger toggle -->
    <button class="fs-hamburger" @click="open = true" title="Files">☰</button>

    <!-- Backdrop -->
    <Transition name="fs-fade">
      <div v-if="open" class="fs-backdrop" @click="open = false"></div>
    </Transition>

    <!-- Drawer -->
    <Transition name="fs-slide">
      <aside v-if="open" class="fs-drawer">
        <div class="fs-header">
          <span class="fs-title">{{ title }}</span>
          <button class="fs-close" @click="open = false" title="Close">✕</button>
        </div>

        <div v-if="showCreate" class="fs-actions">
          <button class="btn btn-sm btn-outline-primary" @click="$emit('create')">+ New</button>
        </div>

        <ul class="fs-list">
          <li v-for="f in files" :key="f" :class="{ 'fs-active': f === active }"
              @click="open = false; $emit('open', f)" :title="f">
            <span class="fs-name">{{ f }}</span>
            <span class="fs-item-actions" @click.stop>
              <button class="fs-act" title="Rename" @click="$emit('rename', f)">✎</button>
              <button class="fs-act fs-act-danger" title="Delete" @click="$emit('delete', f)">✕</button>
            </span>
          </li>
          <li v-if="!files.length" class="fs-empty">No files</li>
        </ul>
      </aside>
    </Transition>
  </div>
</template>

<script setup>
import { ref } from 'vue'

defineProps({
  title: { type: String, default: 'Files' },
  files: { type: Array, default: () => [] },
  active: { type: String, default: null },
  showCreate: { type: Boolean, default: false }
})

defineEmits(['open', 'create', 'rename', 'delete'])

const open = ref(false)
</script>

<style scoped>
.fs-root { display: contents; }

.fs-hamburger {
  position: fixed;
  top: 8px;
  left: 10px;
  z-index: 1049;
  border: none;
  background: transparent;
  color: #fff;
  font-size: 24px;
  line-height: 1;
  padding: 4px 6px;
  cursor: pointer;
  border-radius: 4px;
}

.fs-hamburger:hover {
  background: rgba(255, 255, 255, 0.15);
}

.fs-backdrop {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.45);
  z-index: 1050;
}

.fs-drawer {
  position: fixed;
  top: 0;
  left: 0;
  bottom: 0;
  width: 280px;
  max-width: 85vw;
  background: #fff;
  box-shadow: 2px 0 12px rgba(0, 0, 0, 0.25);
  z-index: 1060;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

.fs-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px 14px;
  background: #343a40;
  color: #fff;
}

.fs-title {
  font-weight: 700;
  font-size: 14px;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.fs-close {
  border: none;
  background: transparent;
  color: #fff;
  font-size: 18px;
  cursor: pointer;
  line-height: 1;
  padding: 2px 6px;
  border-radius: 4px;
}

.fs-close:hover {
  background: rgba(255, 255, 255, 0.15);
}

.fs-actions {
  display: flex;
  gap: 6px;
  padding: 10px 12px;
  border-bottom: 1px solid #eee;
}

.fs-actions .btn {
  font-size: 12px;
  padding: 2px 8px;
}

.fs-list {
  list-style: none;
  margin: 0;
  padding: 8px;
  flex: 1;
  overflow-y: auto;
}

.fs-list li {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 6px;
  padding: 6px 8px;
  border-radius: 4px;
  cursor: pointer;
  font-family: Consolas, monospace;
  font-size: 13px;
}

.fs-list li:hover {
  background: #e9ecef;
}

.fs-list .fs-active {
  background: #0d6efd;
  color: #fff;
}

.fs-name {
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  flex: 1;
}

.fs-item-actions {
  display: none;
  gap: 2px;
  flex-shrink: 0;
}

.fs-list li:hover .fs-item-actions {
  display: inline-flex;
}

.fs-act {
  border: none;
  background: transparent;
  color: #6c757d;
  font-size: 13px;
  line-height: 1;
  padding: 2px 4px;
  cursor: pointer;
  border-radius: 3px;
}

.fs-act:hover {
  background: rgba(0, 0, 0, 0.08);
  color: #212529;
}

.fs-act-danger:hover {
  background: #fdecea;
  color: #dc3545;
}

.fs-empty {
  color: #adb5bd;
  font-style: italic;
  cursor: default;
  padding-left: 10px;
}

.fs-fade-enter-active,
.fs-fade-leave-active {
  transition: opacity 0.2s ease;
}

.fs-fade-enter-from,
.fs-fade-leave-to {
  opacity: 0;
}

.fs-slide-enter-active,
.fs-slide-leave-active {
  transition: transform 0.25s ease;
}

.fs-slide-enter-from,
.fs-slide-leave-to {
  transform: translateX(-100%);
}
</style>
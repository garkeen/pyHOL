import { createRouter, createWebHistory } from 'vue-router'

const routes = [
  {
    path: '/',
    name: 'main',
    component: () => import('./views/Index.vue')
  },
  {
    path: '/ide',
    name: 'editor',
    component: () => import('./views/Editor.vue')
  },
  {
    path: '/program',
    name: 'program',
    component: () => import('./views/ProgramIDE.vue')
  },
  {
    path: '/manual',
    name: 'manual',
    component: () => import('./views/Manual.vue')
  }
]

const router = createRouter({
  history: createWebHistory(),
  routes
})

export default router

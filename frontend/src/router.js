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
    path: '/saint',
    name: 'saint',
    component: () => import('./views/SaintIDE.vue')
  },
  {
    path: '/program',
    name: 'program',
    component: () => import('./views/ProgramIDE.vue')
  }
]

const router = createRouter({
  history: createWebHistory(),
  routes
})

export default router

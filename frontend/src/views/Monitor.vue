<template>
  <div class="monitor-container">
    <!-- Menu -->
    <nav class="navbar navbar-light bg-info">
      <div class="container-fluid">
        <span class="navbar-brand">Monitor</span>
        <div class="navbar-nav flex-row">
          <div class="nav-item me-2">
            <input class="form-control" v-model="input_filename" type="text" placeholder="Theory name" style="width:200px"/>
          </div>
          <div class="nav-item me-2">
            <button class="btn btn-primary" @click="checkInputTheory">Check</button>
          </div>
          <div class="nav-item me-2">
            <button class="btn btn-primary" @click="checkAllTheory">Check All</button>
          </div>
          <div class="nav-item">
            <div class="form-check">
              <input class="form-check-input" type="checkbox" v-model="rewrite_file" id="rewrite-check">
              <label class="form-check-label" for="rewrite-check">Rewrite</label>
            </div>
          </div>
        </div>
      </div>
    </nav>
    
    <div style="margin:10px">
      <div v-if="infos.length > 0" style="margin-bottom:10px">
        <span>Checked {{infos.length}} of {{num_theories}} theories</span>
        <a href="#" @click.prevent="unfoldAll" style="margin-left:10px">Unfold all</a>
        <a href="#" @click.prevent="foldAll" style="margin-left:10px">Fold all</a>
      </div>
      
      <div v-for="(info, index) in infos" :key="index" style="margin-bottom:10px">
        <div v-if="info.stat !== undefined" class="card">
          <div class="card-header d-flex justify-content-between align-items-center">
            <span>
              <strong>{{info.filename}}</strong>:
              <span class="badge bg-success me-1">OK {{info.stat.OK}}</span>
              <span class="badge bg-warning me-1">Partial {{info.stat.Partial}}</span>
              <span class="badge" :class="info.stat.Failed > 0 ? 'bg-danger' : 'bg-secondary'">Failed {{info.stat.Failed}}</span>
              <span class="badge bg-info me-1">NoSteps {{info.stat.NoSteps}}</span>
              <span class="badge bg-success me-1">ProofOK {{info.stat.ProofOK}}</span>
              <span class="badge" :class="info.stat.ProofFail > 0 ? 'bg-danger' : 'bg-secondary'">ProofFail {{info.stat.ProofFail}}</span>
              <span class="badge bg-success me-1">ParseOK {{info.stat.ParseOK}}</span>
              <span class="badge" :class="info.stat.ParseFail > 0 ? 'bg-danger' : 'bg-secondary'">ParseFail {{info.stat.ParseFail}}</span>
              <span class="badge" :class="info.stat.EditFail > 0 ? 'bg-danger' : 'bg-secondary'">EditFail {{info.stat.EditFail}}</span>
            </span>
            <span>
              <a href="#" @click.prevent="info.unfold = !info.unfold" class="me-2">{{info.unfold ? 'Fold' : 'Unfold'}}</a>
              <a href="#" @click.prevent="recheckTheory(index)">Recheck</a>
            </span>
          </div>
          <div v-if="info.unfold" class="card-body p-0">
            <table class="table table-sm table-striped mb-0">
              <thead>
                <tr>
                  <th>Name</th>
                  <th>Status</th>
                  <th>Details</th>
                </tr>
              </thead>
              <tbody>
                <tr v-for="(line, lineIndex) in info.data" :key="lineIndex"
                    :style="{background: getBackground(line)}">
                  <td>{{line.name}}</td>
                  <td>{{line.status}}</td>
                  <td>
                    <span v-if="line.status==='Failed'">{{line.err_type + ' ' + line.err_str}}</span>
                    <span v-if="line.status==='OK'">{{line.num_steps + ' steps'}}</span>
                    <span v-if="line.status==='Partial'">{{line.num_steps + ' steps'}}</span>
                  </td>
                </tr>
              </tbody>
            </table>
          </div>
        </div>
        <div v-else class="card">
          <div class="card-header">
            <span>{{info.filename}}: <span class="text-danger">Server error</span></span>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
import { ref, onMounted } from 'vue'
import api from '../api'

const files = ref([])
const input_filename = ref('')
const num_theories = ref(0)
const infos = ref([])
const rewrite_file = ref(false)

const foldAll = () => {
  for (let i = 0; i < infos.value.length; i++) {
    infos.value[i].unfold = false
  }
}

const unfoldAll = () => {
  for (let i = 0; i < infos.value.length; i++) {
    infos.value[i].unfold = true
  }
}

const checkInputTheory = async () => {
  num_theories.value = 1
  infos.value = []
  await checkTheory(input_filename.value)
}

const checkTheory = async (filename) => {
  try {
    const response = await api.post('/check-theory', {
      filename: filename,
      rewrite: rewrite_file.value
    })
    infos.value.push({
      filename: filename,
      data: response.data.data,
      stat: response.data.stat,
      unfold: num_theories.value === 1
    })
  } catch (err) {
    infos.value.push({
      filename: filename,
      message: 'Server error'
    })
  }
}

const recheckTheory = async (index) => {
  const filename = infos.value[index].filename
  try {
    const response = await api.post('/check-theory', {
      filename: filename,
      rewrite: rewrite_file.value
    })
    infos.value[index] = {
      filename: filename,
      data: response.data.data,
      stat: response.data.stat,
      unfold: infos.value[index].unfold
    }
  } catch (err) {
    infos.value[index] = {
      filename: filename,
      message: 'Server error'
    }
  }
}

const checkAllTheory = async () => {
  try {
    const response = await api.post('/find-files')
    const filelist = response.data.theories
    num_theories.value = filelist.length
    infos.value = []
    for (let i = 0; i < filelist.length; i++) {
      await checkTheory(filelist[i])
    }
  } catch (err) {
    console.error('Failed to load file list')
  }
}

const getBackground = (line) => {
  if (line.status === 'OK' || line.status === 'ProofOK' || line.status === 'ParseOK') {
    return '#90EE90'
  } else if (line.status === 'NoSteps') {
    return '#87CEEB'
  } else if (line.status === 'Failed' || line.status === 'ProofFail' ||
             line.status === 'ParseFail' || line.status === 'EditFail') {
    return '#FF6B6B'
  } else if (line.status === 'Partial') {
    return '#FFD700'
  }
  return 'transparent'
}

onMounted(() => {
  // Don't auto-load, let user click Open or Check All
})
</script>

<style scoped>
.monitor-container {
  min-height: 100vh;
  background: #f8f9fa;
}

.card {
  margin-bottom: 10px;
}

.badge {
  font-size: 0.75em;
}
</style>

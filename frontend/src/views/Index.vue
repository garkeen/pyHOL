<template>
  <div class="container py-5">
    <header class="text-center mb-5">
      <h1 class="display-4 mb-3">HOLPY</h1>
      <p class="lead text-secondary mb-1">Interactive theorem proving in the browser</p>
      <p class="text-secondary">Edit HOL theories, verify proofs, and run integrated CAS & program-verification demos.</p>
    </header>

    <div class="row g-4 justify-content-center">
      <div class="col-md-4">
        <div class="card h-100 shadow-sm">
          <div class="card-body d-flex flex-column">
            <h2 class="h5 mb-2">Theory Editor</h2>
            <p class="text-secondary flex-grow-1 mb-3">Browse and edit predefined theories, inspect theorem proofs, and validate the library step by step.</p>
            <router-link :to="{name: 'editor'}" class="btn btn-primary">Edit theories</router-link>
          </div>
        </div>
      </div>

      <div class="col-md-4">
        <div class="card h-100 shadow-sm">
          <div class="card-body d-flex flex-column">
            <h2 class="h5 mb-2">Program Verification</h2>
            <p class="text-secondary flex-grow-1 mb-3">Verify imperative programs against Hoare-style specifications with the built-in prover.</p>
            <router-link :to="{name: 'program'}" class="btn btn-primary">Program Verification</router-link>
          </div>
        </div>
      </div>

      <div class="col-md-4">
        <div class="card h-100 shadow-sm">
          <div class="card-body d-flex flex-column">
            <h2 class="h5 mb-2">Manual</h2>
            <p class="text-secondary flex-grow-1 mb-3">Read the holpy documentation: HOL logic, kernel, macros, tactics, methods and system overview.</p>
            <router-link :to="{name: 'manual'}" class="btn btn-primary">Read the manual</router-link>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup>
</script>
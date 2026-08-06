<template>
  <div style="margin:10px">
    <h3>HOLPY</h3>
    <ul>
      <li><router-link :to="{name: 'editor'}">Edit theories</router-link></li>
      <li><router-link :to="{name: 'saint'}">SAINT Integral CAS</router-link></li>
      <li><router-link :to="{name: 'program'}">Program Verification</router-link></li>
    </ul>
  </div>
</template>

<script setup>
</script>

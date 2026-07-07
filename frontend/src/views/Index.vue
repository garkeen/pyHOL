<template>
  <div style="margin:10px">
    <h3>HOLPY</h3>
    <ul>
      <li><router-link :to="{name: 'editor'}">Edit theories</router-link></li>
      <li><router-link :to="{name: 'integral'}">Integral</router-link></li>
      <li><router-link :to="{name: 'program'}">Program Verification</router-link></li>
      <li><router-link :to="{name: 'monitor'}">Check theories</router-link></li>
    </ul>
  </div>
</template>

<script setup>
</script>

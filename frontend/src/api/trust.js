import { ref } from 'vue'

// Session-level computation-oracle trust set (audit §7.1).
//
// The /api/v2/* endpoints are stateless: every request replays the proof
// from scratch, so the admitted-oracle set must travel with each one.
//
// `null` means "use the backend default" (core.verify.COMPUTATION_ORACLES,
// the same set validate_library.py uses) -- the frontend does not need to
// know that list to get the default.  Once the user edits the checkboxes
// we send the explicit list; an empty list is strict (reject every
// oracle), which makes "add it to the trust set" failures reproducible.
export const trustOverride = ref(null)

// The oracle names last reported by the backend (state.known_oracles).
export const knownOracles = ref([])

// The trust set the backend reported it used for the current proof.
export const effectiveTrust = ref(null)

export function setKnownOracles(names) {
  knownOracles.value = Array.isArray(names) ? [...names] : []
}

export function setEffectiveTrust(names) {
  effectiveTrust.value = Array.isArray(names) ? [...names] : null
}

export function currentTrust() {
  if (trustOverride.value !== null) return [...trustOverride.value]
  if (effectiveTrust.value !== null) return [...effectiveTrust.value]
  return null
}

export function isAdmitted(name) {
  const t = currentTrust()
  return t === null ? true : t.includes(name)
}

export function toggleOracle(name) {
  const base = currentTrust() ?? [...knownOracles.value]
  const next = base.includes(name)
    ? base.filter(n => n !== name)
    : [...base, name]
  // Keep a stable order for readability / reproducibility.
  const order = knownOracles.value
  trustOverride.value = order.filter(n => next.includes(n))
}

export function resetTrust() {
  trustOverride.value = null
}

// Add the trust field to a request payload only when the session has an
// explicit override; otherwise the backend default applies.
export function withTrust(payload) {
  const t = currentTrust()
  if (t === null) return payload
  return { ...payload, trust: t }
}

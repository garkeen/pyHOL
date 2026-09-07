"""Verification pipeline: proof-status judgement for theory files.

This is the core half of verify (audit §7.4): the four-state machine
for theorem entries, run by library validation and the IDE.  The
status of a theorem entry is an output of the verification pipeline,
not data of the logical kernel.

States (contract, the last three are all failures):
  VALID       full proof, zero gaps after replay
  DEP_FAILED  proof intact but references a failed-state theorem
  STEP_FAILED proof exists but replay fails or leaves open goals
  UNPROVED    no proof at all (no steps)

Only 'thm' entries participate.  'thm.ax' entries are theory content
admitted by the axiom rule -- recorded as 'AXIOM' for display, not a
state.

The replay itself goes through the method layer's stable-ID pipeline
(injected at load via set_replay_fn -- framework must not import the
method layer).  The cache format (.cache/<theory>.json keyed on source
mtime) is unchanged from the monitor-era implementation.
"""

from kernel import theory
from framework import basic
from framework import context


# ---------------------------------------------------------------------------
# Replay injection: server.stable_state.StableProofState lives above
# this layer.  The method layer wires it at import time; until then
# validate_theory raises instead of silently skipping proofs.
# ---------------------------------------------------------------------------

_replay_fn = None


def set_replay_fn(fn):
    """Register the proof replay function.

    fn(item, name) must replay item.steps under item.vars and return
    the number of open goals (0 for a complete proof), raising on any
    replay failure.
    """
    global _replay_fn
    _replay_fn = fn


def _replay(item, name):
    assert _replay_fn is not None, (
        "verify: replay function not registered -- "
        "import server.stable_state (the method layer) first")
    return _replay_fn(item, name)


# ---------------------------------------------------------------------------
# Dependency-status resolution (cross-file, along the import DAG).
# ---------------------------------------------------------------------------

_FAILED_STATES = ('STEP_FAILED', 'DEP_FAILED', 'UNPROVED')


def _import_statuses(filename, seen=None):
    """Collect the cached statuses of theorems in the theories that
    filename imports (transitively), for cross-file dependency checks.

    Reads the .json status caches via load_status data; theories whose
    cache does not exist contribute nothing (validation of this file
    will still record their failures once they are validated
    themselves).
    """
    import json
    import os
    statuses = {}
    if seen is None:
        seen = {filename}
    for imp in basic.theory_cache.get(filename, {}).get('imports', []):
        if imp in seen:
            continue
        seen.add(imp)
        path = basic.status_cache_file(imp)
        if os.path.exists(path):
            try:
                with open(path, encoding='utf-8') as f:
                    data = json.load(f)
                for nm, st in data.get('theorems', {}).items():
                    statuses.setdefault(nm, st)
            except (OSError, ValueError):
                pass
        # transitive imports
        for nm, st in _import_statuses(imp, seen).items():
            statuses.setdefault(nm, st)
    return statuses


# ---------------------------------------------------------------------------
# Four-state judgement.
# ---------------------------------------------------------------------------

def validate_theory(filename, *, force=False):
    """Validate all theorems in a theory file.

    Uses the .json cache: if the .pyhol file has not changed, returns
    cached statuses without re-validating.  If force=True, ignores the
    cache and re-validates everything.

    Returns (statuses, errors): statuses maps theorem names to states
    ('VALID', 'STEP_FAILED', 'DEP_FAILED', 'AXIOM', 'UNPROVED');
    errors maps failed theorems to a message.
    """
    if not force and basic.is_cache_valid(filename):
        basic.load_theory(filename)
        return theory.get_all_statuses(), theory.get_all_errors()

    basic.load_theory(filename)
    content = basic.theory_cache[filename]['content']
    statuses = {}
    errors = {}

    # Cross-file dependency status: cached states of imported theories
    # (fixes the monitor-era deviation where imported failures were
    # never checked -- audit §7.4 deviation 2).
    imported = _import_statuses(filename)

    for item in content:
        name = item.name

        if item.ty == 'thm.ax':
            statuses[name] = 'AXIOM'
            theory.thy.set_status(name, 'AXIOM')
            theory.thy.set_error(name, None)
            continue

        if item.ty != 'thm':
            continue

        if not item.steps:
            statuses[name] = 'UNPROVED'
            theory.thy.set_status(name, 'UNPROVED')
            theory.thy.set_error(name, None)
            continue

        # Check whether any referenced theorem has a failed state --
        # in this file (already judged) or an imported one (cached).
        # All three failure states count, including UNPROVED: a proof
        # that depends on an unproved theorem is dependency-failed
        # (audit §7.4 deviation 1 -- the monitor version only treated
        # STEP_FAILED/DEP_FAILED as failures).
        dep_failed = False
        for step in item.steps:
            dep = step.get('theorem')
            if not dep:
                continue
            dep_status = statuses.get(dep, imported.get(dep))
            if dep_status in _FAILED_STATES:
                dep_err = errors.get(dep, '')
                errors[name] = ('depends on %s which is %s%s'
                                % (dep, dep_status,
                                   (': ' + dep_err) if dep_err else ''))
                dep_failed = True
                break

        if dep_failed:
            statuses[name] = 'DEP_FAILED'
            theory.thy.set_status(name, 'DEP_FAILED')
            theory.thy.set_error(name, errors[name])
            continue

        # Replay the proof via the injected stable-ID pipeline.
        try:
            with theory.fresh_theory():
                context.set_context(filename, limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name)
            statuses[name] = 'VALID' if gaps == 0 else 'STEP_FAILED'
            errors[name] = None if gaps == 0 else 'proof has %d open goal(s)' % gaps
        except Exception as e:
            statuses[name] = 'STEP_FAILED'
            errors[name] = '%s: %s' % (e.__class__.__name__, str(e))

        theory.thy.set_status(name, statuses[name])
        theory.thy.set_error(name, errors[name])

    basic.save_status(filename, statuses)
    return statuses, errors

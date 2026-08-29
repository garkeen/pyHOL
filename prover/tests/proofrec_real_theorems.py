"""Full reconstruction on REAL pyhol library theorems.

For each stored library theorem this runner performs the complete
workflow that an empty (trusted) proof would have to satisfy:

  1. read the theorem's statement from the loaded theory,
  2. universally quantify its free variables (z3 needs a closed goal),
  3. obtain a z3 proof for the goal,
  4. reconstruct it with proofrec (kernel ProofTerms),
  5. verify the reconstructed conclusion matches the quantified
     statement EXACTLY,
  6. bridge back to the free-variable schematic form via forall_elim,
  7. compare against the stored statement and run kernel check_proof.

CLOSED = exact match on both levels + gap-free + check_proof passes;
this is the criterion for discharging a trusted pyhol theorem.
"""

import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# real statements from the library (smt theory imports int/real/function)
THEOREMS = ['r146', 'int_add_comm', 'int_add_assoc', 'real_add_comm',
            'int_power_1']


def run_theorem(name, timeout):
    env = os.environ.copy()
    env['PYTHONPATH'] = REPO_ROOT + os.pathsep + env.get('PYTHONPATH', '')
    cmd = [sys.executable, os.path.abspath(__file__), '--one', name]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout, env=env, cwd=REPO_ROOT)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', '%ss limit' % timeout
    out = proc.stdout.strip().splitlines()
    last = out[-1] if out else ''
    if last.startswith('{'):
        import json
        d = json.loads(last)
        return d['result'], d.get('detail', '')
    err = proc.stderr.strip().splitlines()
    return 'FAIL', (err[-1] if err else 'no output')[:160]


def theorem_result(name):
    try:
        import functools
        from framework import basic
        from framework import logic
        from kernel.theory import get_theorem
        from kernel.term import Forall, Implies
        from kernel import theory
        from prover import z3wrapper
        basic.load_theory('smt')

        thm = get_theorem(name, svar=False)
        prop = thm.prop
        fvs = prop.get_vars()
        quantified = Forall(*fvs, prop) if fvs else prop

        pt = z3wrapper.solve_and_reconstruct(quantified)
        if pt.rule == 'sorry' or len(pt.gaps) != 0:
            return 'GAP', 'rule=%s gaps=%d' % (pt.rule, len(pt.gaps))
        # exact match against the stripped statement solve_core proves
        names = logic.get_forall_names(quantified, svar=False)
        fresh, As, C = logic.strip_all_implies(quantified, names, svar=False)
        st = C
        for a in reversed(As):
            st = Implies(a, st)
        if pt.prop != st:
            return 'MISMATCH', 'reconstructed prop differs from stripped statement'
        # bridge the fresh variables back to the theorem's own variables
        for v_orig, v_fresh in zip(fvs, fresh):
            pt = pt.forall_intr(v_fresh).forall_elim(v_orig)
        if pt.prop != prop:
            return 'MISMATCH', 'schematic prop differs from stored statement'
        theory.check_proof(pt.export())
        return 'CLOSED', 'kernel-checked, matches stored statement'
    except Exception as e:
        return 'FAIL', '%s: %s' % (type(e).__name__, str(e)[:120])


def main():
    args = sys.argv[1:]
    timeout = int(os.environ.get('PROOFREC_TIMEOUT', '40'))
    if '--one' in args:
        name = args[args.index('--one') + 1]
        result, detail = theorem_result(name)
        import json
        print(json.dumps({'name': name, 'result': result, 'detail': detail}))
        return
    closed = 0
    for name in THEOREMS:
        result, detail = run_theorem(name, timeout)
        if result == 'CLOSED':
            closed += 1
        print('%-16s %-9s %s' % (name, result, detail))
    print('--- %d/%d CLOSED' % (closed, len(THEOREMS)))
    sys.exit(0 if closed == len(THEOREMS) else 1)


if __name__ == '__main__':
    main()

"""Full reconstruction on REAL pyhol library theorems.

For each stored library theorem this runner performs the complete
workflow that an empty (trusted) proof would have to satisfy:

  1. read the theorem's statement from the loaded theory (free
     schematic variables stay free -- they are arbitrary constants for
     z3, so a valid statement refutes its negation without
     quantifiers),
  2. obtain a z3 proof for the negated statement,
  3. reconstruct the proof DAG with proofrec (kernel ProofTerms),
  4. close the stripped sequent back to the statement (close_sequent),
  5. verify the conclusion equals the stored statement EXACTLY and run
     kernel verify.

CLOSED = gap-free + exact statement match + kernel verify passes;
this is the criterion for discharging a trusted pyhol theorem.
"""

import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# real statements from the library (smt theory imports int/real/function)
THEOREMS = ['int_add_comm', 'int_add_assoc', 'real_add_comm',
            'r146', 'r149', 'r151', 'r152', 'r155', 'r156',
            'int_power_1']

# documented boundary: Z3 proves integer power through internal
# ToReal/real-power steps; translating those needs a real-power layer
XFAIL = {'int_power_1': 'Z3 routes int power through real-power steps'}


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
        from core import basic
        from core import verify as core_verify
        from kernel.theory import get_theorem
        from solvers import z3wrapper
        basic.load_theory('smt')

        thm = get_theorem(name, svar=False)
        pt = z3wrapper.solve_and_reconstruct(thm.prop)
        if pt.rule == 'sorry' or len(pt.gaps) != 0:
            return 'GAP', 'rule=%s gaps=%d' % (pt.rule, len(pt.gaps))
        if pt.prop != thm.prop:
            return 'MISMATCH', 'reconstructed prop differs from statement'
        # Level-0 oracles used by reconstructed real/integer arithmetic
        # proofs (numeral evaluation; audit §7.1 default is empty).
        core_verify.verify(
            pt.export(),
            trust=frozenset({'int_eval', 'real_eval', 'real_compare',
                             'real_eq_comparison', 'real_const_eq'}))
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
    unexpected = 0
    for name in THEOREMS:
        result, detail = run_theorem(name, timeout)
        if result == 'CLOSED':
            closed += 1
        elif result == 'GAP' and name in XFAIL:
            result = 'XFAIL'
        elif result != 'CLOSED':
            unexpected += 1
        print('%-16s %-9s %s' % (name, result, detail))
    print('--- %d/%d CLOSED (+%d xfail)' %
          (closed, len(THEOREMS), len(THEOREMS) - closed - unexpected))
    sys.exit(0 if unexpected == 0 else 1)


if __name__ == '__main__':
    main()

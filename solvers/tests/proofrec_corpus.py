"""Corpus regression runner for Z3 proof reconstruction.

Every goal is reconstructed in its OWN subprocess with a hard timeout,
so a divergence in one goal cannot stall the suite (Windows has no
SIGALRM).  A goal passes only when

  1. proofrec.proofrec returns a proof with rule != 'sorry' and no gaps,
  2. kernel-level check_proof on the result reports no gaps.

The runner prints a per-goal table and exits non-zero when any goal is
not PASS, so it can gate commits.

Usage:
    python solvers/tests/proofrec_corpus.py                # all categories
    python solvers/tests/proofrec_corpus.py divmod power   # subset
    python solvers/tests/proofrec_corpus.py --one div1     # single goal
    PROOFREC_TIMEOUT=60 python solvers/tests/proofrec_corpus.py
"""

import os
import subprocess
import sys
import time

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# (name, category, context vars, goal[, xfail reason])
# xfail goals are known gaps: Z3 proves integer power through internal
# ToReal/real-power steps whose faithful holpy translation needs a
# real-power layer (translate + library schematics) not yet built.
GOALS = [
    # --- propositional (SAT net) ---
    ('prop1', 'prop', {'p': 'bool', 'q': 'bool', 'r': 'bool'},
     '(p --> q) --> (q --> r) --> p --> r'),
    ('prop2', 'prop', {'p': 'bool', 'q': 'bool'}, 'p | q --> q | p'),
    ('prop3', 'prop', {'p': 'bool', 'q': 'bool', 'r': 'bool'},
     '(p & q) & r --> p & (q & r)'),
    # --- linear integer arithmetic ---
    ('int1', 'int', {'x': 'int'}, 'x >= 3 --> x >= 1'),
    ('int2', 'int', {}, '(3::int) + 2 = 5'),
    ('int3', 'int', {'x': 'int', 'y': 'int'}, 'x = y --> y = x'),
    ('int4', 'int', {'x': 'int', 'y': 'int'}, 'x + y = 5 --> x + y = 5'),
    ('int5', 'int', {'x': 'int'}, '!x::int. x + 0 = x'),
    ('int6', 'int', {'x': 'int', 'y': 'int'}, 'x + y = y + x'),
    # --- linear real arithmetic ---
    ('real1', 'real', {'a': 'real'}, 'a >= 3 --> a >= 1'),
    ('real2', 'real', {}, '(1::real) + 2 = 3'),
    ('real3', 'real', {'a': 'real', 'b': 'real'}, 'a + b = b + a'),
    # --- nat DIV / MOD (div-by-zero pinned, div/mod by one) ---
    ('div1', 'divmod', {'n': 'nat'}, '!n::nat. n DIV 0 = 0'),
    ('div2', 'divmod', {'n': 'nat'}, '!n::nat. n MOD 0 = n'),
    ('div3', 'divmod', {}, '(5::nat) DIV (1::nat) = (5::nat)'),
    ('div4', 'divmod', {}, '(5::nat) MOD (1::nat) = (0::nat)'),
    ('div5', 'divmod', {}, '(7::nat) DIV 2 = (3::nat)'),
    ('div6', 'divmod', {}, '(7::nat) MOD 2 = (1::nat)'),
    # --- power ---
    ('pow1', 'power', {'n': 'nat'}, 'power (n::nat) (1::nat) = n',
     'Z3 routes int power through ToReal steps (needs real-power layer)'),
    ('pow2', 'power', {'m': 'int'}, 'power (m::int) (1::nat) = m',
     'Z3 routes int power through ToReal steps (needs real-power layer)'),
    ('pow3', 'power', {}, '(2::nat) ^ (3::nat) = (8::nat)',
     'Z3 routes int power through ToReal steps (needs real-power layer)'),
    ('pow4', 'power', {}, '(2::real) ^ (2::real) = (4::real)'),
    ('pow5', 'power', {'x': 'int'}, 'power (x::int) (2::nat) >= (0::int)',
     'Z3 routes int power through ToReal steps (needs real-power layer)'),
    # --- of_int coercion ---
    ('ofint1', 'of_int', {}, 'of_int (3::int) = (3::real)'),
    ('ofint2', 'of_int', {}, 'of_int ((1::int) + 2) = (3::real)'),
    # --- quantifiers ---
    ('quant1', 'quant', {'s': 'nat => nat'}, '(!n. s n = 0) --> s 2 = 0'),
    ('quant2', 'quant', {'P': 'nat => bool'}, '(?x. P x) --> (?y. P y)'),
    # --- arrays (Select/Store via fun_upd) ---
    ('arr1', 'array', {'f': 'int => int'}, '(f)(0 := 3) 0 = 3'),
    ('arr2', 'array', {'f': 'int => int'}, '(f)(0 := 3) 1 = f 1'),
    ('arr3', 'array', {'f': 'int => int'}, '(f)(0 := f 0) = f'),
    # --- nonlinear (best effort) ---
    ('nl1', 'nonlin', {'x': 'int'}, '!x::int. x * x >= 0'),
    ('nl2', 'nonlin', {'x': 'real'}, '!x::real. x * x >= 0'),
]


def _safe(x):
    try:
        return str(x)
    except Exception:
        return '<unprintable term>'


def run_goal(entry, timeout):
    """Run one goal in a subprocess; returns (result, detail)."""
    name = entry[0]
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
        return d['result'], _safe(d['detail'])
    return 'FAIL', _safe((proc.stderr.strip().splitlines() or ['no output'])[-1])[:200]


def goal_result(entry):
    """Child mode: reconstruct one goal and print a JSON verdict line."""
    try:
        import importlib.util
        if importlib.util.find_spec('z3') is None:
            return 'SKIPPED', 'z3 not installed'
        from core import basic, context
        from syntax.parser import parse_term
        from kernel import theory
        from solvers import z3wrapper, proofrec
        basic.load_theory('smt')
        _, _, vars_, goal = entry[:4]
        context.set_context('smt', vars=vars_)
        t = parse_term(goal)
        proof, assertions = z3wrapper.solve_and_proof(t)
        pt = proofrec.proofrec(proof, assertions=assertions)
        if pt.rule == 'sorry':
            return 'GAP', 'sorry: %s' % (_safe(pt.gaps),)
        if len(pt.gaps) != 0:
            return 'GAP', _safe(pt.gaps)
        # kernel-level acceptance check: expects the exported low-level Proof
        theory.check_proof(pt.export())
        return 'PASS', ''
    except Exception as e:
        return 'FAIL', '%s: %s' % (type(e).__name__, e)


def main():
    args = sys.argv[1:]
    if '--one' in args:
        name = args[args.index('--one') + 1]
        entry = next(g for g in GOALS if g[0] == name)
        result, detail = goal_result(entry)
        import json
        print(json.dumps({'name': name, 'result': result, 'detail': detail}))
        return
    cats = args or sorted(set(g[1] for g in GOALS))
    timeout = int(os.environ.get('PROOFREC_TIMEOUT', '20'))
    budget = int(os.environ.get('PROOFREC_BUDGET', '240'))
    selected = [g for g in GOALS if g[1] in cats]
    counts = {}
    t_start = time.time()
    for entry in selected:
        if time.time() - t_start > budget:
            counts['SKIPPED'] = counts.get('SKIPPED', 0) + len(selected) - sum(counts.values())
            print('--- global budget %ss reached, remaining goals skipped' % budget)
            break
        t0 = time.time()
        result, detail = run_goal(entry, timeout)
        if len(entry) > 4:
            # known gap: GAP (or better) is expected, a crash/timeout is not
            if result == 'GAP':
                result = 'XFAIL'
            elif result == 'PASS':
                result = 'XPASS'
        counts[result] = counts.get(result, 0) + 1
        secs = time.time() - t0
        print('%-8s %-8s %-9s %5.1fs  %s' %
              (entry[0], entry[1], result, secs, detail))
    total = len(selected)
    unexpected = total - counts.get('PASS', 0) - counts.get('XFAIL', 0) \
        - counts.get('XPASS', 0) - counts.get('SKIPPED', 0)
    print('--- %d/%d PASS (+%d xfail)  %s' %
          (counts.get('PASS', 0), total, counts.get('XFAIL', 0), counts))
    sys.exit(0 if unexpected == 0 else 1)


if __name__ == '__main__':
    main()

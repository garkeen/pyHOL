"""
Every time you motherfucker run all the library test wastes lot of time!!!!!
Its expensive!!!!!
Don't fucking run this code without the permission of the user!!!!!!
"""


"""
Validate library theorems using the unified validate_theory function.
"""



import sys
import os

sys.path.insert(0, os.path.dirname(__file__))


def main():
    # --force: ignore .json proof-status cache, re-validate every theory
    # from its .pyhol source.  Use this after editing definitions or axioms
    # that other theories depend on, so downstream theories are re-validated
    # instead of returning stale cached results.
    force = '--force' in sys.argv

    # --selfcheck: confirm every incremental-cache hit by re-deriving the
    # line and comparing.  Restores the "every line re-derived on every
    # pass" audit property at the pre-memo replay cost; use it for an
    # audit run, not for normal development.
    from core import verify as _verify_mod
    _verify_mod.memo_selfcheck = '--selfcheck' in sys.argv

    from core import basic
    import method.stable_state  # wires the replay pipeline
    import solvers.z3wrapper  # noqa: F401 -- injects the z3 backend into
    #     the z3 oracle macro (z3_loaded / solve).  Without this the
    #     z3 method steps in stored proofs fail with "not installed".
    from core.verify import validate_theory, COMPUTATION_ORACLES

    # Computation-oracle macros admitted in library proofs (audit §7.1
    # trust set; audit line 366 "computation is oracle" debt).  The
    # canonical set lives in core/verify.py so the CLI validator and the
    # backend IDE endpoints default to the same names.
    LIBRARY_ORACLES = COMPUTATION_ORACLES

    basic.load_metadata()
    depend_list = basic.get_import_order(sorted(basic.theory_cache.keys()))
    for fn in depend_list:
        basic.load_theory_cache(fn)

    total_ok = total_fail = total_gaps = 0
    failures = []

    for filename in depend_list:
        cache = basic.theory_cache.get(filename)
        if not cache or 'content' not in cache:
            continue
        if not any(it.ty == 'thm' and it.steps for it in cache['content']):
            continue

        print("\n=== %s ===" % filename)
        sys.stdout.flush()

        statuses, errors = validate_theory(filename, force=force,
                                           trust=LIBRARY_ORACLES)
        for name, status in statuses.items():
            if status == 'VALID':
                total_ok += 1
                print("  OK: %s" % name)
            elif status == 'STEP_FAILED':
                total_fail += 1
                print("  FAIL: %s%s" % (name, ("  [" + errors.get(name, '') + "]") if errors.get(name) else ""))
                failures.append((filename, name, status))
            elif status == 'DEP_FAILED':
                total_gaps += 1
                print("  DEP_FAILED: %s" % name)
                failures.append((filename, name, status))
        sys.stdout.flush()

    print("\n" + "=" * 60)
    print("TOTAL: %d | OK: %d | DEP_FAILED: %d | FAIL: %d" % (
        total_ok + total_fail + total_gaps, total_ok, total_gaps, total_fail))
    if failures:
        print("\nFAILURES:")
        for fn, nm, st in failures:
            print("  [%s] %s: %s" % (st, fn, nm))


if __name__ == '__main__':
    main()

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

    from framework import basic
    from server.monitor import validate_theory

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

        statuses, errors = validate_theory(filename, force=force)
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

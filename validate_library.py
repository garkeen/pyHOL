"""Validate library theorems. Single-process, sequential, with alarm-based timeout."""

import sys
import os
import time
import signal

sys.path.insert(0, os.path.dirname(__file__))

# Timeout handler (Unix only)
def _timeout_handler(signum, frame):
    raise TimeoutError("Theorem check timed out")

if hasattr(signal, 'SIGALRM'):
    signal.signal(signal.SIGALRM, _timeout_handler)


def check_theorem(filename, item, timeout=30):
    """Check one theorem. Returns (name, status, msg)."""
    try:
        from kernel import theory
        from logic import basic, context
        from server import server
        from server.methods.core import apply_method

        if hasattr(signal, 'SIGALRM'):
            signal.alarm(timeout)

        with theory.fresh_theory():
            context.set_context(filename, limit=('thm', item.name), vars=dict(item.vars) if item.vars else {})
            state = server.parse_init_state(item.prop)
            for step_idx, step in enumerate(item.steps):
                apply_method(state, step)
                state.check_proof(compute_only=True)
            gaps = len(state.rpt.gaps)
            if hasattr(signal, 'SIGALRM'):
                signal.alarm(0)
            if gaps > 0:
                return (item.name, "GAPS", "%d gaps" % gaps)
            return (item.name, "OK", "")

    except TimeoutError:
        return (item.name, "TIMEOUT", ">%ds" % timeout)
    except Exception as e:
        if hasattr(signal, 'SIGALRM'):
            signal.alarm(0)
        try:
            msg = str(e)[:200]
        except Exception:
            msg = repr(e)[:200]
        return (item.name, "FAIL", msg)


def main():
    from logic import basic

    basic.load_metadata()
    depend_list = basic.get_import_order(sorted(basic.theory_cache.keys()))
    for fn in depend_list:
        basic.load_theory_cache(fn)

    total_ok = total_fail = total_gaps = total_timeout = total_thms = 0
    failures = []

    for filename in depend_list:
        cache = basic.theory_cache.get(filename)
        if not cache or 'content' not in cache:
            continue
        thm_items = [it for it in cache['content'] if it.ty == 'thm' and it.steps]
        if not thm_items:
            continue

        # Load theory once per file
        basic.load_theory(filename)

        print("\n=== %s ===" % filename)
        sys.stdout.flush()

        for item in thm_items:
            total_thms += 1
            name, status, msg = check_theorem(filename, item, timeout=30)

            if status == "OK":
                total_ok += 1
                print("  OK: %s" % name)
            elif status == "GAPS":
                total_gaps += 1
                print("  GAPS: %s - %s" % (name, msg))
                failures.append((filename, name, status, msg))
            elif status == "TIMEOUT":
                total_timeout += 1
                total_fail += 1
                print("  TIMEOUT: %s" % name)
                failures.append((filename, name, status, msg))
            else:
                total_fail += 1
                print("  FAIL: %s - %s" % (name, msg))
                failures.append((filename, name, status, msg))
            sys.stdout.flush()

    print("\n" + "=" * 60)
    print("TOTAL: %d | OK: %d | GAPS: %d | FAIL: %d | TIMEOUT: %d" % (
        total_thms, total_ok, total_gaps, total_fail, total_timeout))
    if failures:
        print("\nFAILURES:")
        for fn, nm, st, msg in failures:
            print("  [%s] %s/%s: %s" % (st, fn, nm, msg))


if __name__ == '__main__':
    main()

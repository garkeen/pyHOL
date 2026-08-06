"""Replay every proof book against the SAINT engine and report OK/FAIL.

The engine consumes .calc files only.

Run from the repo root:  python SAINT/tools/replay_books.py
"""
import sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from SAINT import rules
from SAINT.calcfmt import load_calc_file
from SAINT.run_slagle import test_cases, file_names

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")

ok, fail = [], []
for filename in file_names:
    data = load_calc_file(os.path.join(EXAMPLES, filename + ".calc"))
    for item in data["content"]:
        if item["name"] not in test_cases[filename]:
            continue
        target = test_cases[filename][item["name"]]
        try:
            rules.check_item(item, target)
            ok.append((filename, item["name"]))
        except AssertionError as e:
            fail.append((filename, item["name"], str(e).splitlines()[0] if str(e) else "?"))
        except Exception as e:
            fail.append((filename, item["name"], "EXC:%s: %s" % (type(e).__name__, str(e).splitlines()[0])))

print("\nOK: %d" % len(ok))
for f, n in ok:
    print("  ", f, n)
print("\nFAIL: %d" % len(fail))
for f, n, err in fail:
    print("  ", f, n, "::", err)

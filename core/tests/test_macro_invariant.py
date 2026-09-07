# Step 3 invariant lint (ARCHITECTURE_AUDIT.md §8 step 3, §7.3):
#
#   1. A macro class that defines get_proof_term must NOT define a
#      custom eval: eval derives from the expansion via the Macro base
#      class (sorry prevs -> get_proof_term -> th). Custom evals on
#      expandable macros were parallel implementations with drift risk
#      and are all removed; eval-only macros (level-0 oracles such as
#      nat_eval, int_eval, z3) define no get_proof_term.
#
#   2. No undefined names in macro modules. Guards against the
#      b947a8a7 class of bug: macros moved between modules without
#      their imports, producing NameError on paths that broad except
#      blocks silently swallowed.

import ast
import io
import os
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

MACRO_FILES = [
    'core/macros/registry.py',
    'core/macros/z3.py',
    'core/auto.py',
    'kernel/bootstrap.py',
    'theories/nat/macro.py',
    'theories/integer/macro.py',
    'theories/real/macro.py',
    'theories/logic/macro.py',
    'theories/expr/macro.py',
]


class MacroEvalInvariantTest(unittest.TestCase):
    def testExpandableMacrosHaveNoCustomEval(self):
        for rel in MACRO_FILES:
            path = os.path.join(ROOT, rel)
            tree = ast.parse(io.open(path, encoding='utf-8').read())
            for node in ast.walk(tree):
                if not isinstance(node, ast.ClassDef):
                    continue
                bases = [getattr(b, 'id', getattr(b, 'attr', '?')) for b in node.bases]
                if 'Macro' not in bases:
                    continue
                funcs = {item.name for item in node.body
                         if isinstance(item, ast.FunctionDef)}
                if 'get_proof_term' in funcs and 'eval' in funcs:
                    self.fail("%s: %s defines both eval and get_proof_term "
                              "(parallel implementation; eval must derive "
                              "from the expansion via the base class)" % (rel, node.name))


class MacroUndefinedNameTest(unittest.TestCase):
    def testNoUndefinedNames(self):
        paths = [os.path.join(ROOT, rel) for rel in MACRO_FILES]
        res = subprocess.run([sys.executable, '-m', 'pyflakes'] + paths,
                             capture_output=True, text=True)
        undefined = [line for line in res.stdout.splitlines()
                     if "undefined name" in line]
        self.assertEqual(undefined, [])


if __name__ == "__main__":
    unittest.main()

# Rewrite step 2 lint (ARCHITECTURE_AUDIT.md §8: "每步加 import 方向
# lint（AST 扫描），白名单逐步缩短").
#
# Locks the dissolution of the tactic<->auto import cycle:
#   - framework/tactic.py must not reference framework.auto (the cycle
#     came from simp_sweep's lazy auto import; simp_sweep now lives in
#     framework/macro/simp.py).
#   - framework/macro/ (macro layer) must not import framework.tactic
#     (tactic sits above macro; imports only go downward).

import ast
import io
import os
import unittest

FRAMEWORK_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def imports_of(path):
    """All module names imported (top-level or lazy) by the file."""
    tree = ast.parse(io.open(path, encoding='utf-8').read())
    mods = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            mods.update(a.name for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            mods.add(node.module)
    return mods


class ImportDirectionTest(unittest.TestCase):
    def testTacticDoesNotImportAuto(self):
        """framework/tactic.py must not import framework.auto, at any
        nesting level (step 2: tactic<->auto cycle dissolved)."""
        mods = imports_of(os.path.join(FRAMEWORK_DIR, 'tactic.py'))
        bad = [m for m in mods if m == 'framework.auto' or m.startswith('framework.auto.')]
        self.assertEqual(bad, [])

    def testMacroLayerDoesNotImportTactic(self):
        """framework/macro/ must not import framework.tactic (macro
        layer is below the tactic layer)."""
        macro_dir = os.path.join(FRAMEWORK_DIR, 'macro')
        for fname in os.listdir(macro_dir):
            if not fname.endswith('.py'):
                continue
            mods = imports_of(os.path.join(macro_dir, fname))
            bad = [m for m in mods if m == 'framework.tactic'
                   or m.startswith('framework.tactic.')]
            self.assertEqual(bad, [], "%s imports tactic layer: %s" % (fname, bad))


if __name__ == "__main__":
    unittest.main()

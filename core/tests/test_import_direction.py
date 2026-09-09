# Rewrite step 2 lint (ARCHITECTURE_AUDIT.md §8: "每步加 import 方向
# lint（AST 扫描），白名单逐步缩短").
#
# Locks the dissolution of the tactic<->auto import cycle:
#   - framework/tactic.py must not reference core.auto (the cycle
#     came from simp_sweep's lazy auto import; simp_sweep now lives in
#     framework/macro/simp.py).
#   - framework/macro/ (macro layer) must not import core.tactic
#     (tactic sits above macro; imports only go downward).

import ast
import io
import os
import unittest

FRAMEWORK_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(FRAMEWORK_DIR)


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


def py_files_under(*dirs):
    for d in dirs:
        base = os.path.join(ROOT, d)
        for dirpath, _, filenames in os.walk(base):
            for fn in filenames:
                if fn.endswith('.py'):
                    yield os.path.join(dirpath, fn)


class ImportDirectionTest(unittest.TestCase):
    def testTacticDoesNotImportAuto(self):
        """framework/tactic.py must not import core.auto, at any
        nesting level (step 2: tactic<->auto cycle dissolved)."""
        mods = imports_of(os.path.join(FRAMEWORK_DIR, 'tactic.py'))
        bad = [m for m in mods if m == 'core.auto' or m.startswith('core.auto.')]
        self.assertEqual(bad, [])

    def testMacroLayerDoesNotImportTactic(self):
        """framework/macro/ must not import core.tactic (macro
        layer is below the tactic layer)."""
        macro_dir = os.path.join(FRAMEWORK_DIR, 'macro')
        for fname in os.listdir(macro_dir):
            if not fname.endswith('.py'):
                continue
            mods = imports_of(os.path.join(macro_dir, fname))
            bad = [m for m in mods if m == 'core.tactic'
                   or m.startswith('core.tactic.')]
            self.assertEqual(bad, [], "%s imports tactic layer: %s" % (fname, bad))

    def testFrameworkDoesNotImportServer(self):
        """framework/ must not import method.* (step 5: items/defcheck
        live in framework; the framework layer never depends on the
        method/session layer above it)."""
        offenders = []
        for path in py_files_under('core'):
            rel = os.path.relpath(path, ROOT).replace('\\', '/')
            mods = imports_of(path)
            bad = [m for m in mods if m == 'server' or m.startswith('method.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testSolversDoNotImportServer(self):
        """solvers/ must not import method.* (step 6: solvers are pure
        algorithm cores consumed by theories/macros; they never see the
        method/session layer)."""
        offenders = []
        for path in py_files_under('solvers'):
            rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
            mods = imports_of(path)
            bad = [m for m in mods if m == 'server' or m.startswith('method.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testSyntaxDoesNotImportUpperLayers(self):
        """syntax/ (excluding tests) must not import core/server/
        domains/solvers (audit §9.5: syntax only depends on kernel+util;
        tests are consumers and stay exempt)."""
        offenders = []
        for path in py_files_under('syntax'):
            rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
            if rel.startswith('syntax/tests/'):
                continue
            mods = imports_of(path)
            bad = [m for m in mods
                   if m == 'framework' or m.startswith('core.')
                   or m == 'server' or m.startswith('method.')
                   or m == 'domains' or m.startswith('theories.')
                   or m == 'solvers' or m.startswith('solvers.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testTheoriesDoNotImportServer(self):
        """theories/ and imperative/ must not import method.* (step 4:
        method registration goes through core.method; the method
        layer reads the registry, it is not a dependency of theories).

        The whitelist is empty (was: imp_compile_test.py wiring the
        method-layer replay). That cross-layer integration test moved
        to the top level (test_imp_validate.py) per AGENTS.md
        "跨模块的才放顶层"; the unit compile tests stayed in
        imperative/tests/ without the assembly import."""
        offenders = []
        for path in py_files_under('theories', 'imperative'):
            rel = os.path.relpath(path, ROOT).replace('\\', '/')
            mods = imports_of(path)
            bad = [m for m in mods if m == 'server' or m.startswith('method.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testGoalConsumptionFace(self):
        """The goal concept (core.goal.Goal) lives only where tactics open
        subgoals. Allowed consumers outside tests:
          - core/goal.py     (the single definition point)
          - core/tactic.py  (the tactic layer)
          - method/**        (L3 proof language: ProofState opens goals)
          - imperative/**    (hoare-domain tactic content)
        The solver-glue files (solvers/proofrec.py, solvers/congc.py)
        mint goals while building proofs and are the documented deferred
        debt (audit §8 step 6 supplement: "solver 胶水 6 文件"). They are
        the only whitelist entries; shrinking them is part of that task.
        New leaks (a fresh solver file, a conv file, a theories/conv)
        are caught here."""
        whitelist = {'solvers/proofrec.py', 'solvers/congc.py'}
        offenders = []
        for path in py_files_under('core', 'method', 'imperative',
                                   'theories', 'solvers', 'backend', 'syntax'):
            rel = os.path.relpath(path, ROOT).replace('\\', '/')
            if rel.endswith('/tests/') or '/tests/' in rel + '/' \
                    or rel == 'core/goal.py' or rel == 'core/tactic.py' \
                    or rel.startswith('method/') or rel.startswith('imperative/') \
                    or rel in whitelist:
                continue
            mods = imports_of(path)
            bad = [m for m in mods
                   if m == 'core.goal' or m.startswith('core.goal.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])


if __name__ == "__main__":
    unittest.main()

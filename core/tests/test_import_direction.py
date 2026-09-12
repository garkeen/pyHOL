# Rewrite step 2 lint (ARCHITECTURE_AUDIT.md §8: "每步加 import 方向
# lint（AST 扫描），白名单逐步缩短").
#
# Locks the dissolution of the tactic<->auto import cycle:
#   - tactic/steps.py must not reference core.auto (the cycle
#     came from simp_sweep's lazy auto import; simp_sweep now lives in
#     core/macro/simp.py).
#   - core/macro/ (macro layer) must not import tactic
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
        """tactic/steps.py must not import core.auto, at any
        nesting level (step 2: tactic<->auto cycle dissolved; the
        simp_sweep dependency lives in core.macro.simp)."""
        mods = imports_of(os.path.join(ROOT, 'tactic', 'steps.py'))
        bad = [m for m in mods if m == 'core.auto' or m.startswith('core.auto.')]
        self.assertEqual(bad, [])

    def testMacroLayerDoesNotImportTactic(self):
        """core/macro/ must not import tactic (macro layer is below the
        tactic layer)."""
        macro_dir = os.path.join(FRAMEWORK_DIR, 'macro')
        for fname in os.listdir(macro_dir):
            if not fname.endswith('.py'):
                continue
            mods = imports_of(os.path.join(macro_dir, fname))
            bad = [m for m in mods if m == 'tactic'
                   or m.startswith('tactic.')]
            self.assertEqual(bad, [], "%s imports tactic layer: %s" % (fname, bad))

    def testCoreDoesNotImportMethod(self):
        """core/ must not import method.* (step 5: items/defcheck
        live in core; the core layer never depends on the
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
        """The goal concept (tactic.goal.Goal) lives only where tactics open
        subgoals. Allowed consumers outside tests:
          - tactic/goal.py    (the single definition point)
          - tactic/steps.py   (the L2 tactic layer)
          - method/**        (L3 proof language: ProofState opens goals)
          - imperative/**    (hoare-domain tactic content)
        The solver-glue files used to mint goals while building proofs
        (documented debt, audit §8 step 6).  They now leave a gap through
        the kernel's Thm.sorry + ProofTerm.sorry instead, so the
        whitelist is empty: solvers never import tactic at all (locked by
        testSolversDoNotImportTactic).  New leaks are caught here."""
        offenders = []
        for path in py_files_under('core', 'tactic', 'method', 'imperative',
                                   'theories', 'solvers', 'backend', 'syntax'):
            rel = os.path.relpath(path, ROOT).replace('\\', '/')
            if rel.endswith('/tests/') or '/tests/' in rel + '/' \
                    or rel == 'tactic/goal.py' or rel == 'tactic/steps.py' \
                    or rel.startswith('method/') or rel.startswith('imperative/'):
                continue
            mods = imports_of(path)
            bad = [m for m in mods
                   if m == 'tactic.goal' or m.startswith('tactic.goal.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testSolversDoNotImportTactic(self):
        """solvers/ (excluding tests) must not import tactic.* (audit §3
        dependency law: tactics sit above the content layer that consumes
        solvers, so a solver importing tactic is an upward reference).
        This locks the closed goal-consumption debt: a solver that needs
        to leave a gap mints the hole from the kernel's Thm.sorry +
        ProofTerm.sorry, never from Goal."""
        offenders = []
        for path in py_files_under('solvers'):
            rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
            if '/tests/' in rel + '/':
                continue
            mods = imports_of(path)
            bad = [m for m in mods if m == 'tactic' or m.startswith('tactic.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testSolversDoNotImportTheories(self):
        """solvers/ (excluding tests) must not import theories.*
        (audit §3 dependency law: solvers are a bypass pure-algorithm
        service consumed by theories/*/macro.py, they never import a
        domain).

        The whitelist is empty.  Task E (2026-09-11) dissolved the two
        thin glue files; task H (2026-09-12) finished the rest:
          - solvers/omega.py -- split: the factoid/solver core stays
            here, proof assembly + registration moved to
            theories/integer/omega.py;
          - solvers/simplex.py, solvers/simplex_strict.py,
            solvers/proofrec.py -- moved into the content layer
            (theories/real/, theories/z3rec.py) because their algorithm
            IS domain proof construction.
        New leaks are caught here; the whitelist must stay empty."""
        offenders = []
        for path in py_files_under('solvers'):
            rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
            if '/tests/' in rel + '/':
                continue
            mods = imports_of(path)
            bad = [m for m in mods
                   if m == 'theories' or m.startswith('theories.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])


if __name__ == "__main__":
    unittest.main()

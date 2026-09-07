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

    def testFrameworkDoesNotImportServer(self):
        """framework/ must not import server.* (step 5: items/defcheck
        live in framework; the framework layer never depends on the
        method/session layer above it)."""
        offenders = []
        for path in py_files_under('framework'):
            rel = os.path.relpath(path, ROOT).replace('\\', '/')
            mods = imports_of(path)
            bad = [m for m in mods if m == 'server' or m.startswith('server.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testSolversDoNotImportServer(self):
        """solvers/ must not import server.* (step 6: solvers are pure
        algorithm cores consumed by theories/macros; they never see the
        method/session layer)."""
        offenders = []
        for path in py_files_under('solvers'):
            rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
            mods = imports_of(path)
            bad = [m for m in mods if m == 'server' or m.startswith('server.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testSyntaxDoesNotImportUpperLayers(self):
        """syntax/ (excluding tests) must not import framework/server/
        domains/solvers (audit §9.5: syntax only depends on kernel+util;
        tests are consumers and stay exempt)."""
        offenders = []
        for path in py_files_under('syntax'):
            rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
            if rel.startswith('syntax/tests/'):
                continue
            mods = imports_of(path)
            bad = [m for m in mods
                   if m == 'framework' or m.startswith('framework.')
                   or m == 'server' or m.startswith('server.')
                   or m == 'domains' or m.startswith('domains.')
                   or m == 'solvers' or m.startswith('solvers.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])

    def testTheoriesDoNotImportServer(self):
        """domains/ and imperative/ must not import server.* (step 4:
        method registration goes through framework.method; the method
        layer reads the registry, it is not a dependency of theories)."""
        # Whitelist shrinks over the migration steps:
        #  - imperative/tests/imp_compile_test.py wires the
        #    method-layer replay into core/verify (server.stable_state).
        #    The monitor reference promised at step 4 is gone; this
        #    assembly import disappears at step 9 when server -> method.
        whitelist = {'imperative/tests/imp_compile_test.py'}
        offenders = []
        for path in py_files_under('domains', 'imperative'):
            rel = os.path.relpath(path, ROOT).replace('\\', '/')
            if rel in whitelist:
                continue
            mods = imports_of(path)
            bad = [m for m in mods if m == 'server' or m.startswith('server.')]
            if bad:
                offenders.append("%s: %s" % (rel, bad))
        self.assertEqual(offenders, [])


if __name__ == "__main__":
    unittest.main()

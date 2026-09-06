# Step 1 regression test (ARCHITECTURE_AUDIT.md §8 step 1):
#
#   The real macros moved from conv.py to macro.py. Registration is
#   by decorator at import time -- this test guards against the move
#   dropping a registration, and against conv.py re-growing macros.

import unittest

from kernel.theory import global_macros


REAL_MACROS = [
    'real_eval',
    'real_norm',
    'real_const_eq',
    'real_compare',
    'real_const_ineq',
    'real_eq_comparison',
    'non_strict_simplex',
]


class RealMacroRegistrationTest(unittest.TestCase):
    def testAllRegistered(self):
        import domains.real  # noqa: F401  (triggers registration)
        missing = [name for name in REAL_MACROS if name not in global_macros]
        self.assertEqual(missing, [])

    def testConvHasNoMacros(self):
        """conv.py must not define Macro subclasses (audit iron law:
        conv 不得出现宏名)."""
        import domains.real.conv as real_conv
        from kernel.macro import Macro
        for name in dir(real_conv):
            obj = getattr(real_conv, name)
            if isinstance(obj, type) and issubclass(obj, Macro):
                self.fail("conv.py defines macro class: %s" % name)

    def testConvDoesNotImportServer(self):
        """domains must not import server (audit misplaced-layer table)."""
        import ast, io
        import domains.real.conv as real_conv
        src = io.open(real_conv.__file__, encoding='utf-8').read()
        tree = ast.parse(src)
        bad = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                bad += [a.name for a in node.names if a.name.startswith('server')]
            elif isinstance(node, ast.ImportFrom) and node.module:
                if node.module.startswith('server'):
                    bad.append(node.module)
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()

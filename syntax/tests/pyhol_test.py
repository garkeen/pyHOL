"""Unit test for pyhol export direction metadata.

pyhol self-describes method directions (_BACKWARD_METHODS /
_FORWARD_METHODS) so that syntax does not import the method layer
(audit §9.5).  These tests lock the copy against drift from
server.stable_state, which owns the semantics.
"""

import unittest


class PyholDirectionTest(unittest.TestCase):
    def testBackwardForwardInSyncWithStableState(self):
        from syntax import pyhol
        from server.stable_state import BACKWARD, FORWARD

        self.assertEqual(pyhol._BACKWARD_METHODS, BACKWARD)
        self.assertEqual(pyhol._FORWARD_METHODS, FORWARD)

    def testPyholDoesNotImportServerOrFramework(self):
        """syntax/pyhol.py must not import server.* or framework.*
        at any nesting level (audit §9.5: syntax only depends on
        kernel+util)."""
        import ast
        import io
        import os

        path = os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            'pyhol.py')
        tree = ast.parse(io.open(path, encoding='utf-8').read())
        mods = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                mods.update(a.name for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                mods.add(node.module)
        bad = [m for m in mods
               if m == 'server' or m.startswith('server.')
               or m == 'framework' or m.startswith('framework.')
               or m == 'domains' or m.startswith('domains.')]
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()

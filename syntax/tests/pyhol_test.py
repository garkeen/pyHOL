"""Unit test for pyhol export direction metadata and item text.

pyhol self-describes method directions (_BACKWARD_METHODS /
_FORWARD_METHODS) so that syntax does not import the method layer
(audit §9.5).  These tests lock the copy against drift from
method.stable_state, which owns the semantics.  The text level of a
`fun` block (its `and` continuations) is checked here too: it is the
parser's and the exporter's shared shape.
"""

import unittest


class PyholFunBlockTest(unittest.TestCase):
    """`fun ... and ...` parses into one item and exports back."""

    def testMutualBlockRoundTrip(self):
        from syntax import pyhol
        src = ("theory t\nimports\n\n"
               "fun even2 :: nat => bool\n"
               "  | even2 0 = true\n"
               "  | even2 (Suc n) = odd2 n\n"
               "and odd2 :: nat => bool\n"
               "  | odd2 0 = false\n"
               "  | odd2 (Suc n) = even2 n\n")
        item = pyhol.parse_pyhol(src)['content'][0]
        self.assertEqual(item['ty'], 'def.ind')
        self.assertEqual([g['name'] for g in item['groups']],
                         ['even2', 'odd2'])
        self.assertEqual([len(g['rules']) for g in item['groups']], [2, 2])

        text = pyhol.export_pyhol(pyhol.parse_pyhol(src))
        self.assertIn('fun even2 :: nat ⇒ bool', text)
        self.assertIn('and odd2 :: nat ⇒ bool', text)
        self.assertIn('| odd2 (Suc n) = even2 n', text)
        again = pyhol.parse_pyhol(text)['content'][0]
        self.assertEqual(again, item)

    def testSingleFunctionKeepsTheFlatShape(self):
        from syntax import pyhol
        src = ("theory t\nimports\n\n"
               "fun f :: nat => nat\n"
               "  measure n\n"
               "  | f 0 = 0\n"
               "  | f (Suc n) = f n\n")
        item = pyhol.parse_pyhol(src)['content'][0]
        self.assertNotIn('groups', item)
        self.assertEqual(item['name'], 'f')
        self.assertEqual(item['measure'], ['n'])
        text = pyhol.export_pyhol(pyhol.parse_pyhol(src))
        self.assertIn('fun f :: nat ⇒ nat', text)
        self.assertNotIn('and ', text)

    def testMutualBlockStopsAtTheNextItem(self):
        from syntax import pyhol
        src = ("theory t\nimports\n\n"
               "fun even2 :: nat => bool\n"
               "  | even2 0 = true\n"
               "and odd2 :: nat => bool\n"
               "  | odd2 (Suc n) = even2 n\n"
               "theorem th\n  prop true\n")
        d = pyhol.parse_pyhol(src)
        self.assertEqual(len(d['content']), 2)
        self.assertEqual(d['content'][1]['name'], 'th')


class PyholDirectionTest(unittest.TestCase):
    def testBackwardForwardInSyncWithStableState(self):
        from syntax import pyhol
        from method.stable_state import BACKWARD, FORWARD

        self.assertEqual(pyhol._BACKWARD_METHODS, BACKWARD)
        self.assertEqual(pyhol._FORWARD_METHODS, FORWARD)

    def testPyholDoesNotImportServerOrFramework(self):
        """syntax/pyhol.py must not import method.* or core.*
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
               if m == 'server' or m.startswith('method.')
               or m == 'framework' or m.startswith('core.')
               or m == 'domains' or m.startswith('theories.')]
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()

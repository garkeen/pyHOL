# Tests for the product type: library/prod.pyhol plus its syntax.

"""Active: the theory validates, `'a × 'b` parses to the product type and
round-trips through the printer, `(a, b)` parses to `Pair a b`, and a
`fixes` line with a multi-parameter type parses.  Passive: a broken type
expression is rejected.
"""

import unittest

from kernel import theory
from kernel.type import TConst, TVar
from core import basic, context
from core.verify import validate_theory, COMPUTATION_ORACLES


class ProdTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        for fn in basic.get_import_order(['prod']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('prod', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(statuses.get('Pair_fst_snd'), 'VALID', errors)
        self.assertEqual([n for n, s in statuses.items() if s == 'STEP_FAILED'],
                         [])

    def testTypeNotation(self):
        context.set_context('prod')
        from syntax import parser
        a, b = TVar('a'), TVar('b')
        self.assertEqual(parser.parse_type("'a × 'b"), TConst('prod', a, b))
        # Right associative, and type application binds tighter than ×.
        self.assertEqual(parser.parse_type("'a × 'b × 'c"),
                         TConst('prod', a, TConst('prod', b, TVar('c'))))
        self.assertEqual(parser.parse_type("'a × 'b ⇒ bool"),
                         TConst('fun', TConst('prod', a, b), TConst('bool')))

    def testTypePrintRoundTrip(self):
        context.set_context('prod')
        from syntax import parser, printer
        from syntax.settings import global_setting
        for s in ["'a × 'b", "('a ⇒ 'b) × bool", "'a × 'b ⇒ bool"]:
            T = parser.parse_type(s)
            with global_setting(unicode=True):
                out = printer.print_type(T)
            self.assertEqual(parser.parse_type(out), T)

    def testTupleTerm(self):
        context.set_context('prod', vars={'a': "'a", 'b': "'b"})
        t = context.parse_term('(a, b)')
        self.assertTrue(t.is_comb('Pair', 2))
        self.assertEqual(t.checked_get_type(), TConst('prod', TVar('a'), TVar('b')))
        # Nested tuple is right-nested pairing.
        t3 = context.parse_term('(a, b, a)')
        self.assertTrue(t3.is_comb('Pair', 2))
        self.assertTrue(t3.args[1].is_comb('Pair', 2))

    def testFixesWithMultiParamType(self):
        """A fixes line may carry a comma inside a type."""
        from syntax import pyhol
        src = ("theory t\nimports\n\naxiom ax\n"
               "  fixes p :: ('a,'b) prod, q :: nat\n  prop q = q\n")
        d = pyhol.parse_pyhol(src)
        body = d['content'][0]
        self.assertEqual(sorted(body['vars']), ['p', 'q'])

    def testBrokenTypeRejected(self):
        context.set_context('prod')
        from syntax import parser
        with self.assertRaises(Exception):
            parser.parse_type("('a × 'b")


if __name__ == '__main__':
    unittest.main()

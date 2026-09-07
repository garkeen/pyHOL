# Step 3 regression test (ARCHITECTURE_AUDIT.md §8 step 3):
#
#   The integer omega-family macros were moved from conv.py to macro.py
#   in b947a8a7 without their full imports (refl, rewr_conv, matcher,
#   ConvException). Any get_proof_term call on them raised NameError --
#   silently swallowed by proofrec's broad except and masked by fallback
#   paths. These tests exercise the paths directly: they failed with
#   NameError before the import fix and must pass now.

import unittest

import core.basic as basic
from syntax import parser
from theories.integer import macro as integer_macro


class OmegaMacroPathsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        basic.load_theory('logic_base')
        basic.load_theory('nat')
        basic.load_theory('int')

    def P(self, s):
        return parser.parse_term(s)

    def testIntEqComparison(self):
        pt = integer_macro.int_eq_comparison_macro().get_proof_term(
            self.P('(a::int) <= b <--> 0 <= b - a'))
        self.assertEqual(str(pt.prop), 'a <= b <--> 0 <= b - a')

    def testIntEqMacro(self):
        pt = integer_macro.int_eq_macro().get_proof_term(
            self.P('((a::int) = b + 3) = (a - 3 = b)'), [])
        self.assertEqual(str(pt.prop), 'a = b + 3 <--> a - 3 = b')

    def testIntIneq(self):
        pt = integer_macro.int_ineq_macro().get_proof_term(
            self.P('(a::int) + 3 <= 7'))
        self.assertEqual(str(pt.prop), 'a + 3 <= 7 <--> -4 + 1 * a ^ (1::nat) < 1')


if __name__ == "__main__":
    unittest.main()

# Step 1 regression test (ARCHITECTURE_AUDIT.md §8 step 1):
#
#   int_neq_false_conv / int_gcd_compares no longer emit the
#   int_const_ineq macro node themselves: the sign fact (|- c > 0 or
#   |- c < 0) is injected by the caller (mk_premise), keeping the conv
#   layer free of macro names. Also guards the inst_theorem import fix
#   (b947a8a7 swapped apply_theorem -> inst_theorem here without adding
#   the import, so any call was a latent NameError).
#
#   Active cases: with a factory, both convs derive correctly.
#   Passive cases: without a factory, the convs must fail loudly
#   (AssertionError) with no proof produced.

import unittest

import framework.basic as basic
from syntax import parser
from kernel.term import Term
from syntax.numeral import IntType, Int, greater, less
from kernel.proofterm import ProofTerm
from domains.integer.conv import int_neq_false_conv, int_gcd_compares


def mk_int_const_ineq_pt(value):
    """Test-local stand-in for the prover-layer factory (prover/
    proofrec.py:mk_int_const_ineq_pt): emits the int_const_ineq oracle
    node for the sign fact of an integer constant."""
    if value > 0:
        return ProofTerm('int_const_ineq', greater(IntType)(Int(value), Int(0)))
    else:
        return ProofTerm('int_const_ineq', less(IntType)(Int(value), Int(0)))


class ConvPremiseInjectionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        basic.load_theory('logic_base')
        basic.load_theory('nat')
        basic.load_theory('int')

    def P(self, s):
        return parser.parse_term(s)

    def testNeqFalseWithPremise(self):
        pt = int_neq_false_conv(mk_int_const_ineq_pt).get_proof_term(self.P('(5::int) = 0'))
        self.assertEqual(str(pt.prop), '(5::int) = 0 <--> false')

    def testNeqFalseNegativeConst(self):
        pt = int_neq_false_conv(mk_int_const_ineq_pt).get_proof_term(self.P('(-(3::int)) = 0'))
        self.assertEqual(str(pt.prop), '-(3::int) = 0 <--> false')

    def testNeqFalseWithoutPremiseFails(self):
        conv = int_neq_false_conv()
        with self.assertRaises(AssertionError) as ctx:
            conv.get_proof_term(self.P('(5::int) = 0'))
        self.assertIn('mk_premise', str(ctx.exception))

    def testGcdComparesWithPremise(self):
        pt = int_gcd_compares(mk_int_const_ineq_pt).get_proof_term(
            self.P('4 * (x::int) + 6 * (y::int) < 8'))
        self.assertEqual(str(pt.prop), '4 * x + 6 * y < 8 <--> 0 <= -2 * x + -3 * y + 3')

    def testGcdComparesCoprimeUnchanged(self):
        # gcd of coefficients is 1: no premise needed, refl suffices.
        t = self.P('(2::int) * x + 3 * y < 5')
        pt = int_gcd_compares(mk_int_const_ineq_pt).get_proof_term(t)
        self.assertEqual(str(pt.prop), '2 * x + 3 * y < 5 <--> 2 * x + 3 * y < 5')

    def testGcdComparesWithoutPremiseFails(self):
        conv = int_gcd_compares()
        with self.assertRaises(AssertionError) as ctx:
            conv.get_proof_term(self.P('4 * (x::int) + 6 * (y::int) < 8'))
        self.assertIn('mk_premise', str(ctx.exception))

    def testConvHasNoMacroEmission(self):
        """The two restructured convs must not contain macro-name
        emissions (audit iron law: conv 不得出现宏名)."""
        import inspect
        for conv_cls in (int_neq_false_conv, int_gcd_compares):
            src = inspect.getsource(conv_cls)
            self.assertNotIn("'int_const_ineq'", src, conv_cls.__name__)
            self.assertNotIn('"int_const_ineq"', src, conv_cls.__name__)
            self.assertNotIn('ProofTerm(', src, conv_cls.__name__)


if __name__ == "__main__":
    unittest.main()

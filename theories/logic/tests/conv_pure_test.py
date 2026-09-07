# Author: Bohua Zhan
# Step 1a acceptance test (ARCHITECTURE_AUDIT.md §8 step 1):
#
#   Convs must not emit macro nodes. sort_conj/norm_full build their
#   proofs via the theorem-application helper; the exported proof must
#   contain ONLY primitive / theorem / sorry / variable lines -- no
#   apply_theorem (or any other macro) lines.
#
# Before the inst_theorem primitive-linking helper this test fails:
# sort_conj emitted apply_theorem macro lines.

import unittest

from kernel.type import TVar, BoolType
from kernel.term import Var, Term
from syntax.logicops import And, Or, Not
from kernel.thm import Thm, primitive_deriv
from kernel.proof import Proof
from kernel.report import ProofReport
from kernel import theory
from core import basic, context
from theories.logic.conv import sort_conj, norm_full


class ConvPurityTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        context.set_context('logic')

    @classmethod
    def tearDownClass(cls):
        context.set_context(None)

    def assertPure(self, pt):
        """Every exported line of pt is a primitive or theorem line."""
        prf = pt.export()
        for item in prf.items:
            self.assertIn(item.rule, list(primitive_deriv) + ["theorem"],
                          "conv proof contains non-primitive line: %s (%s)"
                          % (item.rule, item))

    def testSortConjPure(self):
        """sort_conj's exported proof has no macro lines."""
        a = Var("a", BoolType)
        b = Var("b", BoolType)
        c = Var("c", BoolType)
        t = And(c, And(a, b))
        pt = sort_conj().get_proof_term(t)
        self.assertPure(pt)
        # The result is still checked by the kernel.
        prf = pt.export()
        th = theory.check_proof(prf, ProofReport(), no_gaps=True)
        self.assertEqual(th.prop, pt.th.prop)

    def testNormFullPure(self):
        """norm_full over a mixed formula exports only primitives."""
        a = Var("a", BoolType)
        b = Var("b", BoolType)
        t = Not(And(a, Or(a, b)))
        pt = norm_full().get_proof_term(t)
        self.assertPure(pt)
        prf = pt.export()
        theory.check_proof(prf, ProofReport(), no_gaps=True)


if __name__ == "__main__":
    unittest.main()

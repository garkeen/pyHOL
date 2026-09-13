# Tests for theories/integer/omega.py (the proof-assembly half).
#
# Moved from solvers/tests/omega_test.py so the tests follow the module
# after the algorithm/assembly split.  The algorithm tests (factoids,
# solve_matrix) stay with solvers/omega.py.

import unittest

from syntax import numeral
from kernel import proofterm
from kernel.proofterm import TacticException
from syntax.numeral import Int, IntType, less
from core import context
from theories.integer.omega import OmegaHOL
from theories.integer import omega as omega_solve_mod
from solvers.omega import factoid_to_term, term_to_factoid


class OmegaConstantGoalTest(unittest.TestCase):
    """Regression: a variable-free (constant-only) goal used to crash the
    decision procedure (exact_var/least_coeff_var return None, then the
    code indexed a factoid with None)."""

    def setUp(self):
        # omega_solve rewrites with int theorems, so it needs the ambient
        # theory to be int.  Set it explicitly rather than relying on the
        # import of theories.integer having set the global theory.
        context.set_context('int')

    def testConstantTrueGoal(self):
        # 0 < 1: the negated goal 1 <= 0 normalizes to the trivially
        # false factoid 0 <= -1, which is the contradiction.
        pt = omega_solve_mod.omega_solve(less(IntType)(Int(0), Int(1)), [])
        self.assertEqual(pt.prop, less(IntType)(Int(0), Int(1)))
        self.assertEqual(pt.hyps, ())

    def testConstantFalseGoal(self):
        # 1 < 0: the negated goal 0 <= 1 is trivially true, so the goal
        # is not provable.  Must fail honestly, not crash.
        with self.assertRaises(TacticException):
            omega_solve_mod.omega_solve(less(IntType)(Int(1), Int(0)), [])



class OmegaHOLTest(unittest.TestCase):
    def testHOLRealCombine(self):
        test_data = [
            ([2, 1, -5], [-3, -1, 6], 1, 1, [-1, 0, 1]),
            ([1, -5, 0, 0, 0, 3, 4, 0, -7, -7, 1], [0, 0, 0, 0, 0, 5, -3, 6, 0, 2, 0],
                        3, 4, [3, -15, 0, 0, 0, 29, 0, 24, -21, -13, 3])
        ]

        context.set_context('int')
        vars = numeral.IntVars('x0 x1 x2 x3 x4 x5 x6 x7 x8 x9')
        hol = OmegaHOL([])
        for first, second, m1, m2, res in test_data:
            hol = OmegaHOL([])
            len_fact = len(first)
            first, second = factoid_to_term(vars[:len_fact-1], first), factoid_to_term(vars[:len_fact - 1], second)
            after_combine = hol.real_combine_pt(proofterm.ProofTerm.assume(first), proofterm.ProofTerm.assume(second), m1, m2)
            after_combine_fact = term_to_factoid(vars[:len_fact-1], after_combine.prop)
            self.assertEqual(res, list(after_combine_fact.coeff))

    def testHOLGCD(self):
        test_data = [
            ([5, 0, -8], [1, 0, -2]),
            ([5, 0, 8], [1, 0, 1]),
            ([2, 4, 6, 5], [1, 2, 3, 2]),
            ([2, 4, 6, -5], [1, 2, 3, -3]),
            ([7, 0], [1, 0]),
            ([3, 6, -3], [1, 2, -1])
        ]

        context.set_context('int')
        vars = numeral.IntVars('x0 x1 x2')
        hol = OmegaHOL([])
        for r, res in test_data:
            len_fact = len(r)
            r, res = factoid_to_term(vars[:len_fact-1], r), factoid_to_term(vars[:len_fact-1], res)
            after_gcd = hol.gcd_pt(vars[:len_fact-1], proofterm.ProofTerm.assume(r))
            self.assertEqual(res, after_gcd.prop)


if __name__ == "__main__":
    unittest.main()

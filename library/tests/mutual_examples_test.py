# Tests for the mutual blocks beyond the smallest sample
# (library/mutual_examples.pyhol).

"""The shapes the encoding has to cover besides "two functions, one
argument each, one call per clause":

* three functions -- the sum is a tree of two `either`s, so the path to
  the last leaf is two steps deep and every projection over it walks it;
* a clause with two recursive calls -- its premise in the mutual
  induction rule is two hypotheses, one per call;
* two arguments each -- the descent is lexicographic (`(n, Suc m)` is no
  smaller than `(Suc n, m)`), which the sum's measure carries as one
  column per argument position;
* two result types -- the encoded function returns the sum of them, the
  definitions go through the result projection, and a call inside an
  expression is the projection of the callee's side.

Active: the theory replays VALID, and each block's functions have their
equations and the four rules.
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES

# What each block leaves behind: the encoding's own rules and, per
# function, the equations and the four projected rules.  The names are the
# ones the encoding derives (`<a>_<b>_sum`), so a block that changes shape
# changes them.
THREE = ['cycle3a_cycle3b_cycle3c_sum_def_1', 'cycle3a_cycle3b_cycle3c_sum_induct',
         'cycle3a_induct', 'cycle3b_induct', 'cycle3c_induct',
         'cycle3a_elims', 'cycle3b_elims', 'cycle3c_elims',
         'cycle3a_cases', 'cycle3b_cases', 'cycle3c_cases',
         'cycle3a_exhaustive', 'cycle3b_exhaustive', 'cycle3c_exhaustive']
TWO_ARGS = ['zipf_zipg_sum_def_2', 'zipf_zipg_sum_induct',
            'zipf_def_1', 'zipf_def_2', 'zipg_def_1', 'zipg_def_2',
            'zipf_elims', 'zipg_elims', 'zipf_induct', 'zipg_induct']
MIXED = ['cnt_pos_sum_def_2', 'cnt_pos_sum_def_4',
         'cnt_def_1', 'cnt_def_2', 'pos_def_1', 'pos_def_2',
         'cnt_elims', 'pos_elims', 'cnt_induct', 'pos_induct']
HETERO = ['half_tally_sum_def_2', 'half_tally_sum_induct',
          'half_def_2', 'tally_def_2', 'half_elims', 'tally_elims',
          'half_induct', 'tally_induct',
          # the measures: each leaf's own at its own argument position
          'half_m1_def', 'tally_m1_def', 'half_tally_sum_m1_def']


class MutualExamplesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every emitted item of the three blocks is VALID after replay."""
        for fn in basic.get_import_order(['mutual_examples']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('mutual_examples', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testProjectedItemsAreThere(self):
        basic.load_theory('mutual_examples')
        for name in THREE + TWO_ARGS + MIXED + HETERO:
            self.assertIsNotNone(theory.get_theorem(name), name)

    def testThreeFunctionsShareOneTree(self):
        """The three-function group's rules carry all three predicates.

        The sum is `(nat, (nat, nat) either) either`; each function's
        projected rule states the whole group's clauses, which is what
        makes a proof about one of them usable for the others -- the tree
        is what the projections walk.
        """
        basic.load_theory('mutual_examples')
        self.assertIsNotNone(theory.get_theorem('cycle3a_cycle3b_cycle3c_sum_induct'))
        for name in ['cycle3a_induct', 'cycle3b_induct', 'cycle3c_induct']:
            text = str(theory.get_theorem(name).prop)
            self.assertIn('P1', text)
            self.assertIn('P2', text)
            self.assertIn('P3', text)

    def testTheTwoCallClauseGetsTwoHypotheses(self):
        """`cycle3c (Suc n) = cycle3a n + cycle3c n` is one premise with two
        induction hypotheses, in the order the calls appear."""
        basic.load_theory('mutual_examples')
        text = str(theory.get_theorem('cycle3c_induct').prop)
        self.assertIn('P1 n', text)
        self.assertIn('P3 n', text)
        self.assertIn('P3 (Suc n)', text)

    def testTwoArgumentMeasureIsOneColumnPerPosition(self):
        """The group's measure is the argument positions, not the tuple.

        `zipf (Suc n) m = zipg n (Suc m)` keeps the tuple's size, so what
        carries the recursion is the first argument's own measure -- the
        k-th column of the sum, one per position.
        """
        basic.load_theory('mutual_examples')
        text = str(theory.get_theorem('zipf_zipg_sum_m1_def').prop)
        self.assertIn('either_case', text)
        text = str(theory.get_theorem('zipf_m1_def').prop)
        self.assertIn('fst', text)
        text = str(theory.get_theorem('zipf_m2_def').prop)
        self.assertIn('snd', text)

    def testLeavesWithDifferentArgumentTypesKeepTheirOwnMeasures(self):
        """The tree's leaves need not have the same argument type.

        `half` takes a number and `tally` a list, so the column that
        measures them is the identity on one side and the list's size on
        the other -- each leaf's own measure at its own argument position.
        """
        basic.load_theory('mutual_examples')
        self.assertEqual(str(theory.get_theorem('half_m1_def').prop),
                         'half_m1 ?p = ?p')
        text = str(theory.get_theorem('tally_m1_def').prop)
        self.assertIn('list_size', text)
        text = str(theory.get_theorem('half_tally_sum_m1_def').prop)
        self.assertIn('either_case', text)
        self.assertIn('half_m1', text)
        self.assertIn('tally_m1', text)

    def testResultTypesAreSummed(self):
        """`cnt` is `nat` and `pos` is `bool`: the encoded function returns
        `(nat, bool) either`, and each definition is the projection out of
        its own side."""
        basic.load_theory('mutual_examples')
        text = str(theory.get_theorem('cnt_def').prop)
        self.assertIn('either_Left_1', text)
        self.assertIn('cnt_pos_sum', text)
        text = str(theory.get_theorem('pos_def').prop)
        self.assertIn('either_Right_1', text)


if __name__ == '__main__':
    unittest.main()

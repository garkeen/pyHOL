# Tests for the mutual blocks whose clauses are completed before emission
# (library/mutual_completion.pyhol).

"""A block's clauses are completed the way a lone definition's are.

`_complete_equations` runs on each function of the group before anything
is emitted, so a hole becomes an `= undefined` clause and a clause an
earlier one eats into is subtracted rather than refused -- and the
encoded definition *and* every projected item (the equations, the
coverage and case rules, the elimination and induction rules) are read
off that completed set.  What that has to mean for the emitted items:

* the hole's fill is an equation of the function like any other clause:
  `hsum_def_3` is `hsum (Suc 0) = undefined`, the encoded
  `hsum_htake_sum_def_3` is the same clause on the sum, and the fill has
  a disjunct in `hsum_exhaustive`, a branch in `hsum_elims` and a premise
  in `hsum_induct`;
* an overlapped clause is narrowed, not dropped: the second clause of
  `osum`/`otake` states `osum (Suc n) 0 = Suc n`, which is what its
  `_def_2` says and what the second premise of `osum_induct` concludes.

Active: the theory replays VALID, and each function of both blocks has
its equations and the four rules.
"""

import unittest

from kernel import theory
from kernel.theory import TheoryException
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES

# What the two blocks leave behind: the encoded definition's items, the
# projected equations and the four rules of each function.
HOLE = ['hsum_htake_sum_def_1', 'hsum_htake_sum_def_2', 'hsum_htake_sum_def_3',
        'hsum_htake_sum_def_4', 'hsum_htake_sum_def_5',
        'hsum_htake_sum_exhaustive', 'hsum_htake_sum_cases',
        'hsum_htake_sum_elims', 'hsum_htake_sum_induct',
        'hsum_def_1', 'hsum_def_2', 'hsum_def_3',
        'hsum_exhaustive', 'hsum_cases', 'hsum_elims', 'hsum_induct',
        'htake_def_1', 'htake_def_2',
        'htake_exhaustive', 'htake_cases', 'htake_elims', 'htake_induct']
OVERLAP = ['osum_otake_sum_def_1', 'osum_otake_sum_def_2',
           'osum_otake_sum_def_3', 'osum_otake_sum_def_4',
           'osum_otake_sum_def_5', 'osum_otake_sum_def_6',
           'osum_otake_sum_exhaustive', 'osum_otake_sum_cases',
           'osum_otake_sum_elims', 'osum_otake_sum_induct',
           'osum_def_1', 'osum_def_2', 'osum_def_3',
           'osum_exhaustive', 'osum_cases', 'osum_elims', 'osum_induct',
           'otake_def_1', 'otake_def_2', 'otake_def_3',
           'otake_exhaustive', 'otake_cases', 'otake_elims', 'otake_induct']


class MutualCompletionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every emitted item of both blocks is VALID after replay."""
        for fn in basic.get_import_order(['mutual_completion']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('mutual_completion', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testProjectedItemsAreThere(self):
        basic.load_theory('mutual_completion')
        for name in HOLE + OVERLAP:
            self.assertIsNotNone(theory.get_theorem(name), name)

    def testAHoleBecomesAClauseOfItsOwn(self):
        """`hsum` has no clause for `Suc 0`; the emitter's fill is one.

        The clause is `hsum (Suc 0) = undefined` -- the input the
        definition leaves undefined, which is what the single-function
        path emits for a hole as well -- and the rules below are read off
        the completed set, so the fill is not a gap in them.
        """
        basic.load_theory('mutual_completion')
        self.assertEqual(str(theory.get_theorem('hsum_def_3').prop),
                         'hsum (Suc 0) = undefined')
        text = str(theory.get_theorem('hsum_exhaustive').prop)
        self.assertIn('p = Suc 0', text)
        text = str(theory.get_theorem('hsum_elims').prop)
        self.assertIn('y = undefined', text)
        text = str(theory.get_theorem('hsum_induct').prop)
        self.assertIn('P1 (Suc 0)', text)
        # `htake` has no hole, and its own items are untouched by the
        # first function's.
        self.assertEqual(str(theory.get_theorem('htake_def_2').prop),
                         'htake (Suc ?n) = hsum ?n')

    def testAnOverlappedClauseIsNarrowed(self):
        """The second clause of each function is what the subtraction left.

        `osum n 0 = n` is covered at `0 0` by `osum 0 m = m`, so the
        clause the block has is `osum (Suc n) 0 = Suc n` (a fresh variable
        for the narrowed position, and the same term in the right hand
        side), and that is what the second premise of `osum_induct`
        concludes.
        """
        basic.load_theory('mutual_completion')
        # The narrowed pattern carries a fresh variable for the position
        # the subtraction split, and the same term in the right hand side.
        self.assertRegex(str(theory.get_theorem('osum_def_2').prop),
                         r'^osum \(Suc \?\w+\) 0 = Suc \?\w+$')
        self.assertRegex(str(theory.get_theorem('otake_def_2').prop),
                         r'^otake \(Suc \?\w+\) 0 = 0$')
        text = str(theory.get_theorem('osum_induct').prop)
        self.assertIn('Suc', text)
        self.assertIn('P1', text)
        self.assertIn('P2', text)

    def testTheEncodedDefinitionHasTheCompletedClauses(self):
        """One equation per completed clause, group by group.

        `hsum` needs a third clause and gets a third encoded equation;
        the overlap blocks need none, so their encoded definitions stop at
        the sixth (three clauses each) -- the clause-to-equation mapping
        the projections are written against.
        """
        basic.load_theory('mutual_completion')
        self.assertIsNotNone(theory.get_theorem('hsum_htake_sum_def_3'))
        self.assertIsNotNone(theory.get_theorem('osum_otake_sum_def_6'))
        with self.assertRaises(TheoryException):
            theory.get_theorem('osum_otake_sum_def_7')


if __name__ == '__main__':
    unittest.main()

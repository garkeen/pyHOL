# Tests for the mutual block sample (library/mutual_example.pyhol).

"""`fun ... and ...`: the group is encoded into one function over the sum
of the argument tuples (`either`), the single-function machinery proves
*that*, and each function gets its definition, its equations and the
mutual induction rule back.

Active: the theory replays VALID, every projected item is there -- the
encoded function's own rules and, per function, the definition, the
equations and the induction rule -- and the rule is used once
(`even2_or_odd2`).
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES

# What the block is supposed to leave behind: the encoding's own rules
# (they are what the projections are proved from) and the per-function
# items -- equations and the mutual induction rule, whose premises are the
# whole group's clauses and whose conclusion is this function's side.
API = ['even2_odd2_sum_def_1', 'even2_odd2_sum_def_2',
       'even2_odd2_sum_exhaustive', 'even2_odd2_sum_cases',
       'even2_odd2_sum_elims', 'even2_odd2_sum_induct',
       'even2_def_1', 'even2_def_2', 'even2_induct',
       'even2_exhaustive', 'even2_cases',
       'odd2_def_1', 'odd2_def_2', 'odd2_induct',
       'odd2_exhaustive', 'odd2_cases',
       # the rule used once: every number is even or odd
       'even2_or_odd2']


class MutualExampleTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every emitted item of the block is VALID after full replay."""
        for fn in basic.get_import_order(['mutual_example']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('mutual_example', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testProjectedItemsAreThere(self):
        basic.load_theory('mutual_example')
        for name in API:
            self.assertIsNotNone(theory.get_theorem(name))

    def testInductionRuleIsTheMutualOne(self):
        """`even2_induct` carries the group's clauses, not just this side.

        Its hypotheses are the other function's as well -- that is what
        makes it the rule a proof about a mutual definition uses, and what
        the encoding's own induction rule is projected down to.
        """
        basic.load_theory('mutual_example')
        th = theory.get_theorem('even2_induct')
        text = str(th.prop)
        self.assertIn('P2', text)
        self.assertIn('P1', text)


if __name__ == '__main__':
    unittest.main()

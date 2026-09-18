# Tests for the either theory (library/either.pyhol).

"""Disjoint sums: the type, its case combinator and the relation built
from one relation per side -- the encoding a mutual definition goes
through (Isabelle's `Sum_Type.thy`; the type is called `either` here
because `sum` is the set sum of library/sums.pyhol, whose `sum_cases`
would shadow a datatype's own case rule).

Active: the theory replays VALID, the datatype's and the case
combinator's generated items are present, the expansion of the case
combinator is the one the `fun` machinery derives (no axioms left), and
the relation lemmas `wf_either_rel` reads are all there.
Passive: `Left a = Right b` is not derivable, and the failed attempt
leaves the gap count unchanged.
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES

# The API: the datatype's own rules, the projections datgen generates for
# its two arguments, the case combinator's expansion, and the relation
# lemmas -- the two injections a descent obligation is built from, the
# two reverses it is read back with, the two mixed-side facts that make
# the cross cases vacuous, and the well-foundedness of the relation the
# encoding lifts its termination relation to.
API = ['either_induct', 'either_cases', 'either_Left_Right_neq',
       'either_Left_inject', 'either_Left_1_rule', 'either_Right_1_rule',
       'either_case_def_1', 'either_case_def_2', 'either_case_rel_wf',
       'either_case_exhaustive', 'either_case_cases', 'either_case_elims',
       'either_case_induct', 'either_rel_LeftI', 'either_rel_RightI',
       'either_rel_LeftD', 'either_rel_RightD', 'either_rel_Left_Right_neq',
       'either_rel_Right_Left_neq', 'wf_either_rel']


class EitherTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every theorem of the theory is VALID after full replay."""
        for fn in basic.get_import_order(['either']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('either', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testApiPresent(self):
        basic.load_theory('either')
        for name in API:
            self.assertIsNotNone(theory.get_theorem(name))

    def testCaseCombinatorIsDerived(self):
        """The case combinator is expanded, not axiomatized.

        A `fun` definition's equations are derived from well-foundedness
        (`core/fungen.py`), and this one has nothing to descend through --
        neither equation calls the function -- so its relation is the
        empty one and the well-foundedness it reads is `wf_false`.  A
        definition that kept its axioms instead would show up as a
        `def.ind` item here.
        """
        basic.load_theory('either')
        for item in basic.theory_cache['either']['content']:
            if item.name == 'either_case':
                self.assertEqual(item.ty, 'def',
                                 'either_case is still axiomatized')

    def testLeftNotRight(self):
        """Left a = Right b is not derivable."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('either')
        repl.cmd_var('a \'a')
        repl.cmd_var('b \'b')
        repl.cmd_goal('Left a = Right b')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← refl goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)


if __name__ == '__main__':
    unittest.main()

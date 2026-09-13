# Tests for the lists_ex theory (library/lists_ex.pyhol), the port of auto2's
# Lists_Ex.thy: strict_sorted (and, later, ordered_insert).

"""Active: the theory replays VALID; the ported API is present; the generic
lemma instantiates at `nat` once the two class premises are discharged with the
instance theorems from library/order.pyhol.

Passive: at a naked type variable the lemma still applies, but its class
premises remain open -- the constraint is a real obligation, not decoration.
"""

import unittest

from kernel import theory
from core import basic, context, items
from core.verify import validate_theory, COMPUTATION_ORACLES
from syntax.settings import global_setting


STRICT_SORTED_LEMMAS = ['strict_sorted_appendE1', 'strict_sorted_append_head',
                        'strict_sorted_append_tail', 'strict_sorted_appendE2']


class ListsExTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        for fn in basic.get_import_order(['lists_ex']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('lists_ex', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testApiPresent(self):
        basic.load_theory('lists_ex')
        self.assertTrue(theory.thy.has_term_sig('strict_sorted'))
        for name in STRICT_SORTED_LEMMAS:
            self.assertIsNotNone(theory.get_theorem(name))

    def testItemLayerInjectsBothClassPremises(self):
        """`'a::linorder list` contributes one premise per operation (`≤` and
        `<`); a `strict_sorted` statement needs the strict one."""
        for fn in basic.get_import_order(['lists_ex']):
            basic.load_theory_cache(fn)
        basic.load_theory('lists_ex')
        context.set_context('lists_ex')
        obj = items.parse_item({'ty': 'thm', 'name': 'strict_probe',
                                'vars': {'xs': "'a::linorder list"},
                                'prop': 'strict_sorted xs'})
        self.assertIsNone(obj.error)
        with global_setting(unicode=False):
            prop = str(obj.prop)
        self.assertIn('linorder (less_eq', prop)
        self.assertIn('linorder_lt (less', prop)
        self.assertEqual(str(obj.vars['xs']), "'a list")

    def testLemmaIsUsableAtNat(self):
        """The generic lemma instantiates at `nat`, with both class premises
        discharged by the instance theorems."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('lists_ex')
        repl.cmd_var('xs nat list')
        repl.cmd_var('ys nat list')
        repl.cmd_goal('strict_sorted (xs @ ys) ⟶ strict_sorted xs & strict_sorted ys')
        repl.run_line('← intro goal=0')
        repl.run_line('→ forward nat_linorder goal=@')
        repl.run_line('→ forward nat_linorder_lt goal=@')
        # #1 the hypothesis, #2 the goal, #3/#4 the two instance facts.
        repl.run_line('← rule strict_sorted_appendE1 goal=@ facts=[3,4,1]')
        self.assertFalse(repl.failed)
        self.assertEqual(repl.sps.num_gaps, 0)

    def testClassPremisesAreRealObligations(self):
        """Without the annotation the lemma still applies, but its class
        premises become open goals: nothing says an arbitrary list type is
        linearly ordered."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('lists_ex')
        repl.cmd_var("xs 'a list")
        repl.cmd_var("ys 'a list")
        repl.cmd_goal('strict_sorted (xs @ ys) ⟶ strict_sorted xs & strict_sorted ys')
        repl.run_line('← intro goal=0')
        repl.run_line('← rule strict_sorted_appendE1 goal=@')
        self.assertFalse(repl.failed)
        with global_setting(unicode=False):
            goals = [str(th.prop) for _, th in repl.sps.get_open_goals()]
        self.assertEqual(len(goals), 2)
        self.assertTrue(all('linorder' in prop for prop in goals), goals)


if __name__ == '__main__':
    unittest.main()

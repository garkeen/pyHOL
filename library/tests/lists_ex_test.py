# Tests for the lists_ex theory (library/lists_ex.pyhol), the port of auto2's
# Lists_Ex.thy: strict_sorted, ordered_insert, remove_elt_list, and `sorted`
# (the `<=` version, from Isabelle's List.thy).

"""Active: the theory replays VALID; the ported API is present; the generic
lemmas instantiate at `nat` once the two class premises are discharged with the
instance theorems from library/order.pyhol.

Passive: without the annotation the lemmas still apply, but their class
premises remain open -- the constraint is a real obligation, not decoration;
and a conditional lemma (`remove_elt_idem`) whose hypothesis is not available
leaves the gap count unchanged.
"""

import unittest

from kernel import theory
from core import basic, context, items
from core.verify import validate_theory, COMPUTATION_ORACLES
from syntax.settings import global_setting


STRICT_SORTED_LEMMAS = ['strict_sorted_appendI', 'strict_sorted_appendE1',
                        'strict_sorted_append_head', 'strict_sorted_append_tail',
                        'strict_sorted_appendE2', 'strict_sorted_cons_head',
                        'strict_sorted_cons_tail', 'strict_sorted_distinct']

ORDERED_INSERT_LEMMAS = ['ordered_insert_set', 'ordered_insert_sorted']

REMOVE_ELT_LEMMAS = ['remove_elt_list_mem', 'remove_elt_list_set',
                     'remove_elt_list_sorted', 'remove_elt_idem']

SORTED_LEMMAS = ['sorted_cons_head', 'sorted_cons_tail', 'sorted_appendI',
                 'sorted_appendE1']

ALL_LEMMAS = (STRICT_SORTED_LEMMAS + ORDERED_INSERT_LEMMAS +
              REMOVE_ELT_LEMMAS + SORTED_LEMMAS)


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
        for name in ['strict_sorted', 'ordered_insert', 'remove_elt_list',
                     'sorted']:
            self.assertTrue(theory.thy.has_term_sig(name),
                            'missing constant %s' % name)
        for name in ALL_LEMMAS:
            self.assertIsNotNone(theory.get_theorem(name),
                                 'missing theorem %s' % name)

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

    def testStrictAppendIIsUsableAtNat(self):
        """The backward direction: the three hypotheses (strict_sorted xs,
        strict_sorted ys, and the cross-order property) give strict_sorted
        (xs @ ys)."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('lists_ex')
        repl.cmd_var('xs nat list')
        repl.cmd_var('ys nat list')
        repl.cmd_goal('strict_sorted xs & strict_sorted ys & '
                      '(∀a. a ∈ set xs ⟶ (∀b. b ∈ set ys ⟶ a < b)) ⟶ '
                      'strict_sorted (xs @ ys)')
        repl.run_line('← intro goal=0')
        repl.run_line('→ forward nat_linorder goal=@')
        repl.run_line('→ forward nat_linorder_lt goal=@')
        # #1 the conjunction hypothesis, #2 the goal, #3/#4 the instances.
        repl.run_line('← rule strict_sorted_appendI goal=@ facts=[3,4,1]')
        self.assertFalse(repl.failed)
        self.assertEqual(repl.sps.num_gaps, 0)

    def testOrderedInsertAndRemoveEltListPreserveSortedAtNat(self):
        """Both list surgery lemmas are usable at `nat` with the two class
        premises discharged by the instance theorems."""
        from repl.repl import Repl
        for name, lemma in [('ordered_insert', 'ordered_insert_sorted'),
                            ('remove_elt_list', 'remove_elt_list_sorted')]:
            repl = Repl()
            repl.cmd_theory('lists_ex')
            repl.cmd_var('x nat')
            repl.cmd_var('ys nat list')
            repl.cmd_goal('strict_sorted ys ⟶ strict_sorted (%s x ys)' % name)
            repl.run_line('← intro goal=0')
            repl.run_line('→ forward nat_linorder goal=@')
            repl.run_line('→ forward nat_linorder_lt goal=@')
            repl.run_line('← rule %s goal=@ facts=[3,4,1]' % lemma)
            self.assertFalse(repl.failed, lemma)
            self.assertEqual(repl.sps.num_gaps, 0, lemma)

    def testSortedAppendIIsUsableAtNat(self):
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('lists_ex')
        repl.cmd_var('xs nat list')
        repl.cmd_var('ys nat list')
        repl.cmd_goal('sorted xs & sorted ys & '
                      '(∀a. a ∈ set xs ⟶ (∀b. b ∈ set ys ⟶ a <= b)) ⟶ '
                      'sorted (xs @ ys)')
        repl.run_line('← intro goal=0')
        repl.run_line('→ forward nat_linorder goal=@')
        repl.run_line('→ forward nat_linorder_lt goal=@')
        repl.run_line('← rule sorted_appendI goal=@ facts=[3,4,1]')
        self.assertFalse(repl.failed)
        self.assertEqual(repl.sps.num_gaps, 0)

    def testRemoveEltListSetUsesMinusNotation(self):
        """The statement follows auto2 literally (`set ys - {x}`): set.pyhol
        gives the overloaded operator `minus` a set instance, so `-` is set
        difference.  See PROGRAM_VERIFICATION_PORT.md §13.4."""
        basic.load_theory('lists_ex')
        with global_setting(unicode=False):
            prop = str(theory.get_theorem('remove_elt_list_set').prop)
        self.assertIn(' - ', prop)
        self.assertNotIn('diff', prop)

    def testRemoveEltListMemClassifiesMembership(self):
        """`remove_elt_list_mem` unfolds a membership in the deleted list, so
        the two halves of the conjunction become usable facts."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('lists_ex')
        repl.cmd_var('x nat')
        repl.cmd_var('ys nat list')
        repl.cmd_var('z nat')
        repl.cmd_goal('z ∈ set (remove_elt_list x ys) ⟶ z ∈ set ys')
        repl.run_line('← rewrite remove_elt_list_mem goal=0')
        repl.run_line('← intro goal=1')
        # #2 is the conjunction hypothesis (the rewritten goal's assumption).
        repl.run_line('→ forward conjD1 goal=3 facts=[2]')
        self.assertFalse(repl.failed)
        self.assertEqual(repl.sps.num_gaps, 0)

    def testClassPremisesAreRealObligations(self):
        """Without the annotation the lemma still applies, but its class
        premises become open goals: nothing says an arbitrary list type is
        linearly ordered."""
        from repl.repl import Repl
        for prop, lemma in [
                ('strict_sorted (xs @ ys) ⟶ strict_sorted xs & strict_sorted ys',
                 'strict_sorted_appendE1'),
                ('sorted xs & sorted ys & '
                 '(∀a. a ∈ set xs ⟶ (∀b. b ∈ set ys ⟶ a <= b)) ⟶ '
                 'sorted (xs @ ys)', 'sorted_appendI')]:
            repl = Repl()
            repl.cmd_theory('lists_ex')
            repl.cmd_var("xs 'a list")
            repl.cmd_var("ys 'a list")
            repl.cmd_goal(prop)
            repl.run_line('← intro goal=0')
            # The conjunction premise is discharged by the hypothesis; the two
            # class premises are left as subgoals.
            repl.run_line('← rule %s goal=@' % lemma)
            self.assertFalse(repl.failed, lemma)
            with global_setting(unicode=False):
                goals = [str(th.prop) for _, th in repl.sps.get_open_goals()]
            self.assertEqual(len(goals), 2, (lemma, goals))
            self.assertTrue(all('linorder' in prop for prop in goals),
                            (lemma, goals))

    def testRemoveEltIdemNeedsItsHypothesis(self):
        """`remove_elt_idem` is conditional: rewriting with it where the
        non-membership fact is missing fails outright and leaves no trace."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('lists_ex')
        repl.cmd_var('x nat')
        repl.cmd_var('ys nat list')
        repl.cmd_goal('remove_elt_list x ys = ys')
        gaps = repl.sps.num_gaps
        repl.run_line('← rewrite remove_elt_idem goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps)


if __name__ == '__main__':
    unittest.main()

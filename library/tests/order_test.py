# Tests for the order theory (library/order.pyhol) and the class sugar.

"""Orders as explicit relations, and the `'a::C` sugar end to end.

Active: the order theory replays VALID; the predicates, the class laws and the
nat instances are present; the item layer injects the class premise into a
statement that carries the annotation.
Passive: at a type variable without the annotation, `x <= x` leaves the class
premise owing -- the constraint is a real obligation, not decoration.
"""

import unittest

from kernel import theory
from core import basic, context, items
from core.verify import validate_theory, COMPUTATION_ORACLES
from syntax.settings import global_setting


ORDER_LEMMAS = ['preorder_refl', 'preorder_trans', 'order_preorder',
                'order_antisym', 'linorder_order', 'linorder_total',
                'linorder_refl', 'linorder_trans', 'linorder_antisym',
                'nat_preorder', 'nat_order', 'nat_linorder',
                'linorder_le_refl', 'nat_le_refl']


class OrderTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        for fn in basic.get_import_order(['order']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('order', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testApiPresent(self):
        basic.load_theory('order')
        for name in ORDER_LEMMAS:
            self.assertIsNotNone(theory.get_theorem(name))
        for name in ['preorder', 'order', 'linorder']:
            self.assertTrue(theory.thy.has_term_sig(name),
                            'missing constant %s' % name)

    def testItemLayerInjectsPremise(self):
        """`fixes x :: 'a::linorder` becomes a premise of the statement."""
        for fn in basic.get_import_order(['order']):
            basic.load_theory_cache(fn)
        basic.load_theory('order')
        context.set_context('order')
        obj = items.parse_item({'ty': 'thm', 'name': 'sugar_probe',
                                'vars': {'x': "'a::linorder"},
                                'prop': 'x <= x'})
        self.assertIsNone(obj.error)
        with global_setting(unicode=False):
            prop = str(obj.prop)
        self.assertIn('linorder', prop)
        self.assertIn('less_eq', prop)
        # The annotation is dropped from the parsed fixes: the type is 'a.
        self.assertEqual(str(obj.vars['x']), "'a")

    def testConstraintIsARealObligation(self):
        """Without the annotation, `x <= x` at a type variable is not
        closable: nothing in the theory says an arbitrary relation is
        reflexive, so the class law does not apply."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('order')
        repl.cmd_var("x 'a")
        repl.cmd_goal('x <= x')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← rule linorder_refl goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)


if __name__ == '__main__':
    unittest.main()

# Tests for the list theory (library/list.pyhol).

"""Active: the theory replays VALID and the ported list API is present
(take/drop with their cons equations, map with its length/append laws,
sublist, last/butlast, itrev, list_update, list_swap, remdups).

Passive: `take n (x # xs) = x # take n xs` is *not* the definitional
equation of `take` (that one is guarded by `Suc`), so rewriting it with
`take_cons` must fail and leave the gap count unchanged.
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES


# The ported API: functions auto2's Program_Verification actually uses
# (counted over Functional/ + Imperative/: map 45, last 35, list_swap 26,
# take 16, butlast 15, list_update 11, drop 10, itrev 8, filter 2) plus
# the definitions the report asks for even where auto2's usage is zero.
API = ['take', 'drop', 'sublist', 'last', 'butlast', 'map', 'filter',
       'foldr', 'foldl', 'concat', 'zip', 'itrev', 'list_update',
       'list_swap', 'remdups']


class ListTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        for fn in basic.get_import_order(['list']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('list', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testApiPresent(self):
        basic.load_theory('list')
        for name in API:
            self.assertTrue(theory.thy.has_term_sig(name),
                            'missing constant %s' % name)
        for name in ['take_nil', 'take_cons', 'drop_nil', 'drop_cons',
                     'append_take_drop_id', 'length_map', 'map_append',
                     'nth_append_lt', 'nth_list_update_same',
                     'list_update_nil', 'list_update_zero', 'list_update_cons',
                     'length_list_update', 'length_list_swap',
                     'nth_map', 'sublist_0',
                     'length_filter_le', 'length_take_le',
                     'length_take', 'length_drop', 'length_sublist',
                     'itrev_rev_gen', 'itrev_eq_rev', 'set_map',
                     'append_singleton_neq_nil', 'last_append',
                     'butlast_append',
                     'set_append', 'member_set_append',
                     'member_set_append_left', 'member_set_append_right',
                     'member_set_cons', 'mem_set_cons_self',
                     'mem_set_cons_weak']:
            self.assertIsNotNone(theory.get_theorem(name),
                                 'missing theorem %s' % name)

    def testTakeConsOnlyInSucForm(self):
        """take_cons is guarded by Suc n, so it cannot rewrite take n (x # xs)."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('list')
        for nm, ty in [('n', 'nat'), ('x', "'a"), ('xs', "'a list")]:
            repl.cmd_var('%s %s' % (nm, ty))
        repl.cmd_goal('take n (x # xs) = x # take n xs')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← rewrite take_cons goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)


if __name__ == '__main__':
    unittest.main()

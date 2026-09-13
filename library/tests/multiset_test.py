# Tests for the multiset theory (library/multiset.pyhol).

"""Multisets as counting functions ('a multiset = 'a => nat), enough for
auto2's program-verification port: only mset, singleton and union are
actually used (16 occurrences of `mset`, `{#x#} + mset xs`); count/set_mset/
difference were measured at 0 uses.

Active: the theory replays VALID and the ported API is present.
Passive: `mset xs = mset ys` is not derivable for arbitrary xs, ys (it is
multiset equality, i.e. permutation), and the failed attempt leaves the gap
count unchanged.
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES


API = ['empty_mset', 'single_mset', 'union_mset', 'count', 'set_mset', 'mset']
THEOREMS = ['count_union_mset', 'count_empty_mset',
            'count_single_mset_same', 'count_single_mset_other',
            'union_mset_empty_left', 'union_mset_empty_right',
            'union_mset_comm', 'union_mset_assoc',
            'mset_append', 'mset_rev']


class MultisetTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        for fn in basic.get_import_order(['multiset']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('multiset', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testApiPresent(self):
        basic.load_theory('multiset')
        for name in API:
            self.assertTrue(theory.thy.has_term_sig(name),
                            'missing constant %s' % name)
        for name in THEOREMS:
            self.assertIsNotNone(theory.get_theorem(name),
                                 'missing theorem %s' % name)

    def testPermutationNotEquality(self):
        """mset xs = mset ys is multiset equality, not list equality."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('multiset')
        for nm in ['xs', 'ys']:
            repl.cmd_var('%s \'a list' % nm)
        repl.cmd_goal('mset xs = mset ys')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← refl goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)


if __name__ == '__main__':
    unittest.main()

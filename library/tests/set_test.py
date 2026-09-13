# Tests for the set theory (library/set.pyhol).

"""Subset/finite-set/cardinality closure lemmas.

Active: the newly proved subset, finite-set and cardinality lemmas replay
VALID, and the stub list (the remaining axiom debt) is pinned exactly.
Passive: `insert a (delete A a) = A` needs its hypothesis, `finite A` cannot
be had from the insert lemma alone, `card_insert` needs the non-membership
hypothesis, and `insert x A Sub B` needs the subset hypothesis.
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES


# Lemmas proved by this batch.  They are the foundation of the finite-set
# block: `finite_induct`/`finite_insert_imp`/`insert_delete` are what gets
# facts back out of the `finite_def` encoding.
NEW_LEMMAS = ['subsetE', 'subset_refl', 'subset_trans', 'subset_diff',
              'subset_insert', 'subset_insert_imp', 'delete_subset_insert',
              'subset_insert_delete', 'subset_inter_left', 'subset_inter_right',
              'subset_delete', 'inter_comm', 'union_comm', 'union_insert',
              'insert_delete',
              'finite_induct', 'finite_insert_imp', 'finite_fin_sub',
              'finite_subset', 'finite_insert', 'finite_union_imp',
              'finite_inter', 'finite_image', 'finite_delete', 'finite_diff',
              'image_insert',
              'image_combine', 'insert_absorb',
              'less_than_eq_empty', 'less_than_eq_insert', 'less_than_finite',
              'less_than_card',
              'lfp_lowerbound', 'lfp_greatest', 'lfp_fix_upper', 'lfp_fix_lower']

# The cardinality layer: `card_image_inj` (the P-instantiation of
# `finite_def`), the monotonicity facts, and element-level helpers whose
# extra hypotheses are *not* redundant (see the passive tests below).
CARD_LEMMAS = ['card_image_inj', 'card_mono', 'card_image_le',
               'card_subset_eq', 'insert_subset_imp',
               'card_le_bound_empty', 'not_mem_delete_self',
               'delete_subset_insert_imp']

# Still unproved: the deliberate `set_equal_iff` axiom plus the remaining
# stubs.  Pinned so that proving one of them fails this test loudly and the
# list gets updated, instead of the debt silently growing.
EXPECTED_NON_GREEN = {
    # deliberate axioms: set extensionality, and the card recursion (see the
    # comment above `axiom card_empty` in set.pyhol for why card is axiomatized)
    'set_equal_iff': 'AXIOM',
    'card_empty': 'AXIOM',
    'card_insert': 'AXIOM',
    'surjective_iff_injective': 'UNPROVED',
}


class SetTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testNewLemmasValid(self):
        """Every lemma of this batch is VALID after full replay."""
        for fn in basic.get_import_order(['set']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('set', force=True,
                                           trust=COMPUTATION_ORACLES)
        for name in NEW_LEMMAS + CARD_LEMMAS:
            self.assertEqual(statuses.get(name), 'VALID', errors)
        self.assertEqual({k: v for k, v in statuses.items() if v != 'VALID'},
                         EXPECTED_NON_GREEN, errors)

    def testApiPresent(self):
        basic.load_theory('set')
        for name in NEW_LEMMAS + CARD_LEMMAS:
            self.assertIsNotNone(theory.get_theorem(name))

    def testInsertDeleteNeedsHypothesis(self):
        """`insert a (delete A a) = A` is not definitionally true: without
        the hypothesis `a Mem A` the equation does not close."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('set')
        repl.cmd_var("A 'a set")
        repl.cmd_var("a 'a")
        repl.cmd_goal('insert a (delete A a) = A')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← refl goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)

    def testFiniteNotDerivableFromVar(self):
        """`finite A` holds for no arbitrary A: the insert lemma cannot
        close it."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('set')
        repl.cmd_var("A 'a set")
        repl.cmd_var("a 'a")
        repl.cmd_goal('finite A')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← rule finite_insert_imp goal=0')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)

    def testCardInsertNeedsNonMem(self):
        """`card (insert a A) = Suc (card A)` needs `~(a Mem A)` as well as
        `finite A`; the finiteness fact alone leaves `~(a Mem A)` on the
        fact's premise, so the goal stays open."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('set')
        repl.cmd_var("A 'a set")
        repl.cmd_var("a 'a")
        repl.cmd_goal('finite A --> card (insert a A) = Suc (card A)')
        repl.run_line('← intro goal=0')
        gaps_before = repl.sps.num_gaps
        repl.run_line('→ forward card_insert goal=2 facts=[1]')
        self.assertEqual(repl.sps.num_gaps, gaps_before)

    def testInsertSubsetNeedsSubsetHypothesis(self):
        """`insert x A Sub B` needs `A Sub B` as well as `x Mem B`: the
        element hypothesis alone leaves the subset premise undischarged."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('set')
        repl.cmd_var("A 'a set")
        repl.cmd_var("B 'a set")
        repl.cmd_var("x 'a")
        repl.cmd_goal('x Mem B --> insert x A Sub B')
        repl.run_line('← intro goal=0')
        gaps_before = repl.sps.num_gaps
        repl.run_line('→ forward insert_subset_imp goal=2 facts=[1]')
        self.assertEqual(repl.sps.num_gaps, gaps_before)


if __name__ == '__main__':
    unittest.main()

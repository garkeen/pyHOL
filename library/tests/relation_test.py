# Tests for the relation theory (library/relation.pyhol).

"""Relations as sets of pairs, ported from auto2's Partial_Equiv_Rel.

Active: every proof replays VALID and the ported API names are present.
Passive: the converse of per_union membership is not derivable, and the
failed attempt leaves the gap count unchanged.
"""

import unittest

from kernel import theory
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES


# The ported API: everything auto2's Partial_Equiv_Rel.thy uses, plus
# per_union_iff, the set-membership characterisation the port builds on.
API = (
    ['sym_def', 'trans_def', 'part_equiv_def',
     'part_equivI', 'part_equivD1', 'part_equivD2',
     'per_union_def', 'per_union_iff',
     'per_union_memI1', 'per_union_memI2', 'per_union_memI3', 'per_union_memD',
     'per_union_is_sym', 'per_union_is_trans', 'per_union_is_part_equiv']
    + ['per_union_case_%d%d' % (i, j) for i in (1, 2, 3) for j in (1, 2, 3)]
)


class RelationTheoryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every theorem of the theory is VALID after full replay."""
        for fn in basic.get_import_order(['relation']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('relation', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testApiPresent(self):
        basic.load_theory('relation')
        for name in API:
            self.assertIsNotNone(theory.get_theorem(name))

    def testConverseNotProvable(self):
        """per_union membership does not imply R membership."""
        from repl.repl import Repl
        repl = Repl()
        repl.cmd_theory('relation')
        for nm, ty in [('R', "('a × 'a) set"), ('a', "'a"), ('b', "'a"),
                       ('x', "'a"), ('y', "'a")]:
            repl.cmd_var('%s %s' % (nm, ty))
        repl.cmd_goal('(x,y) ∈ per_union R a b ⟶ (x,y) ∈ R')
        gaps_before = repl.sps.num_gaps
        repl.run_line('← intro goal=0')
        repl.run_line('← rule per_union_memI1 goal=1')
        self.assertTrue(repl.failed)
        self.assertEqual(repl.sps.num_gaps, gaps_before)


if __name__ == '__main__':
    unittest.main()

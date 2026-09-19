# Tests for the mutual block that descends through the file's own relation
# (library/mutual_relation.pyhol).

"""A block can carry a relation, not just measures.

The relation is the file's, over the *sum* the encoding builds (`msum` of
the side the element came from), and it comes with the two clauses a single
function's relation takes: `wf` names the theorem proving it well founded,
`descent` the lemmas discharging the calls' obligations.  The obligations
are stated on the encoded calls -- `msum (Right (Pair n m)) < msum (Left
(Pair (Suc m) n))` -- and the encoding proves the definition from them.

The sample's descent is one no inferred measure carries: each call swaps
the two arguments, so the sum decreases by one while neither argument does
(the search compares one position at a time), and recursion on the sum is
not structural either.  Without the relation the block has nothing to
descend through.

Active: the theory replays VALID -- the relation's well-foundedness, the
two descent lemmas, the encoded definition and every projected item -- and
no measure function is generated (the columns belong to the other route).
"""

import unittest

from kernel import theory
from kernel.theory import TheoryException
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES

# What the block leaves behind: the encoded definition's own items, the
# two functions' equations and their four rules.  There is no `<f>_m<k>`
# among them: a relation needs no column.  The constants the encoding
# defines (`_H`, `_rel`, `_in`, the encoded function, each function) are
# named by their definitional equations, which is the theorem a `def`
# item registers.
ENCODED = ['swapf_swapg_sum_H_def', 'swapf_swapg_sum_rel_def',
           'swapf_swapg_sum_in_def', 'swapf_swapg_sum_def',
           'swapf_def', 'swapg_def',
           'swapf_swapg_sum_rel_wf',
           'swapf_swapg_sum_def_1', 'swapf_swapg_sum_def_2',
           'swapf_swapg_sum_def_3', 'swapf_swapg_sum_def_4',
           'swapf_swapg_sum_exhaustive', 'swapf_swapg_sum_cases',
           'swapf_swapg_sum_elims', 'swapf_swapg_sum_induct']
PROJECTED = ['swapf_def_1', 'swapf_def_2', 'swapf_exhaustive', 'swapf_cases',
             'swapf_elims', 'swapf_induct',
             'swapg_def_1', 'swapg_def_2', 'swapg_exhaustive', 'swapg_cases',
             'swapg_elims', 'swapg_induct']
NO_MEASURES = ['swapf_m1', 'swapf_m2', 'swapg_m1', 'swapg_m2',
               'swapf_swapg_sum_m1']


class MutualRelationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every item of the file is VALID after replay."""
        for fn in basic.get_import_order(['mutual_relation']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('mutual_relation', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testTheEncodedItemsAreThere(self):
        """The block expands; the lemmas above it are the file's own work."""
        basic.load_theory('mutual_relation')
        for name in ENCODED + PROJECTED:
            self.assertIsNotNone(theory.get_theorem(name), name)

    def testTheRelationIsTheFilesOwn(self):
        """The encoded relation is the constant the file wrote.

        `_rel_body` puts the relation the clause names straight into the
        definition (`<sum>_rel = msum`), so everything the encoding proves
        about its order is a theorem about the file's relation -- and its
        well-foundedness is the file's `wf` lemma, not a measure chain's
        `wf_mlex`/`wf_measure`.
        """
        basic.load_theory('mutual_relation')
        text = str(theory.get_theorem('swapf_swapg_sum_rel_def').prop)
        self.assertIn('swapf_swapg_sum_rel = ', text)
        self.assertIn('msum', text)
        self.assertIsNotNone(theory.get_theorem('swapf_swapg_sum_rel_wf'))
        self.assertEqual(str(theory.get_theorem('msum_lt_wf').prop),
                         'wf (%p. %q. msum p < msum q)')

    def testNoMeasureColumnIsBuilt(self):
        """The relation route generates no measure function.

        A measure chain would name the columns' functions (`swapf_m1`,
        `swapf_swapg_sum_m1`, ...); with a relation there is nothing to
        measure, and the definition is proved from the file's `descent`
        lemmas instead -- which is what the two obligations in the file
        are, stated on the encoded calls.
        """
        basic.load_theory('mutual_relation')
        for name in NO_MEASURES:
            with self.assertRaises(TheoryException):
                theory.get_theorem(name)
        self.assertIsNotNone(theory.get_theorem('swapf_dec_1'))
        self.assertIsNotNone(theory.get_theorem('swapg_dec_1'))

    def testTheProjectedRulesCarryTheGroup(self):
        """Each function's rules are about the whole group, as ever."""
        basic.load_theory('mutual_relation')
        for name in ('swapf_induct', 'swapg_induct'):
            text = str(theory.get_theorem(name).prop)
            self.assertIn('P1', text)
            self.assertIn('P2', text)
        # The premises call the other function's predicate: the swap is
        # what makes the block mutual.
        text = str(theory.get_theorem('swapf_induct').prop)
        self.assertIn('P2', text)


if __name__ == '__main__':
    unittest.main()

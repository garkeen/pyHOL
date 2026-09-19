# Tests for the mutually recursive types (library/mutual_datatype.pyhol).

"""`datatype ... and ...`: two types declared as one family.

The members are registered together -- a constructor of one holds the
other -- and their induction rules are mutual: each carries one predicate
per member, and a constructor's hypothesis is about the predicate of the
member its argument has (`MNode l f` assumes the statement about the
forests).  A proof by `mtree_induct` therefore discharges the *whole*
family's premises, which is what the family is for.

What a family does *not* get yet is a subterm relation and a size: a
descent that crosses the family is not structural on one member, and the
relation that covers it is the family's own, over the sum of its members
(`PROGRAM_VERIFICATION_PORT.md`).  A `fun` that recurses over a family
therefore keeps its axioms; the members' destructors (which pattern
matching needs) are generated, and the test pins both.

Active: the file replays VALID -- the generated destructors and the two
proofs by the family's induction rules -- and the rules themselves have
the mutual shape.
"""

import unittest

from kernel import theory
from kernel.theory import TheoryException
from core import basic
from core.verify import validate_theory, COMPUTATION_ORACLES

# What the family's block leaves behind: one induction and one case rule
# per member, the constructor axioms of each, and the destructors of the
# constructor arguments.
GENERATED = ['mtree_induct', 'mforest_induct', 'mtree_cases', 'mforest_cases',
             'mtree_MLeaf_MNode_neq', 'mforest_MNil_MCons_neq',
             'mtree_MNode_inject', 'mforest_MCons_inject',
             'mtree_MNode_1_rule', 'mtree_MNode_2_rule',
             'mforest_MCons_1_rule', 'mforest_MCons_2_rule']
PROOFS = ['mtree_ctor_form', 'mforest_ctor_form']
# The boundary: neither is generated for a family.
NOT_GENERATED = ['mtree_size', 'mforest_size', 'mtree_wf_subterm',
                 'mforest_wf_subterm']


class MutualDatatypeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        """Every item of the file is VALID after replay."""
        for fn in basic.get_import_order(['mutual_datatype']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('mutual_datatype', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testTheGeneratedItemsAreThere(self):
        basic.load_theory('mutual_datatype')
        for name in GENERATED + PROOFS:
            self.assertIsNotNone(theory.get_theorem(name), name)

    def testTheInductionRulesAreMutual(self):
        """One predicate per member, in the family's order.

        `mtree_induct` is the rule for the trees and `mforest_induct` the
        one for the forests: the premises are the whole family's in both
        (the four constructors), and what differs is the predicate the
        conclusion names.
        """
        basic.load_theory('mutual_datatype')
        tree = str(theory.get_theorem('mtree_induct').prop)
        forest = str(theory.get_theorem('mforest_induct').prop)
        for text in (tree, forest):
            self.assertIn('P1 MLeaf', text)
            self.assertIn('P1 (MNode l f)', text)
            self.assertIn('P2 f', text)
            self.assertIn('P2 (MCons t f)', text)
        self.assertTrue(tree.endswith('P1 ?x'), tree)
        self.assertTrue(forest.endswith('P2 ?x'), forest)
        # A single datatype's rule would have concluded `?P ?x`: the
        # family's is not offered to the `induct` method, which
        # instantiates one predicate with the goal.
        self.assertNotIn('var_induct',
                         theory.thy.get_attributes('mtree_induct'))

    def testTheProofsUseBothRules(self):
        """The file's two theorems are proofs by the family's induction.

        Both halves of "every term is a constructor application" are
        proved, one from each rule: the premises the rule leaves are the
        family's own, so each proof discharges the other member's
        constructors as well -- which is what a mutual induction has to
        do, and what the rule is for.
        """
        basic.load_theory('mutual_datatype')
        from core import basic as basic_mod
        content = basic_mod.theory_cache['mutual_datatype']['content']
        steps = {}
        for item in content:
            if item.name in PROOFS:
                steps[item.name] = [s for s in (item.steps or [])
                                    if s.get('method_name') == 'rule']
        self.assertIn('mtree_induct',
                      [s.get('theorem') for s in steps['mtree_ctor_form']])
        self.assertIn('mforest_induct',
                      [s.get('theorem') for s in steps['mforest_ctor_form']])

    def testAFamilyHasNoSizeAndNoSubtermRelation(self):
        """The registered boundary, pinned.

        Both belong to the family rather than to one member (a size would
        be mutual, and the relation would relate the members to each
        other), and neither is generated yet.  A `fun` that recurses over
        a family therefore has nothing to descend through.
        """
        basic.load_theory('mutual_datatype')
        for name in NOT_GENERATED:
            with self.assertRaises(TheoryException):
                theory.get_theorem(name)


if __name__ == '__main__':
    unittest.main()

import unittest

from kernel.term import Var, Eq, BoolType
from kernel.thm import Thm
from kernel.proofterm import ProofTerm
from core.goal import Goal

A = Var("A", BoolType)
B = Var("B", BoolType)


class GoalTest(unittest.TestCase):
    def testStatement(self):
        """Goal.th mints the hole statement (equal to the raw shape)."""
        self.assertEqual(Goal(Eq(A, A), A).th, Thm(Eq(A, A), A))

    def testSorry(self):
        """Goal.sorry opens a sorry node carrying the goal statement."""
        pt = Goal(Eq(A, A), A).sorry()
        self.assertEqual(pt.rule, "sorry")
        self.assertEqual(pt.th, Thm(Eq(A, A), A))

    def testHypsFlatten(self):
        """Hyps flatten like Thm: Term or tuple entries."""
        self.assertEqual(Goal(A, A, (A, B)).th, Thm(A, A, (A, B)))
        self.assertEqual(Goal(A).th, Thm(A))


if __name__ == '__main__':
    unittest.main()

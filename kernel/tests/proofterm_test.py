# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun
from kernel.term import Var, Term, Eq
from kernel.thm import Thm
from kernel.proof import Proof, ItemID
from kernel import theory
from kernel.proofterm import ProofTerm

Ta = TVar("a")
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", TFun(Ta,Ta,Ta))

class ProofTermTest(unittest.TestCase):
    def setUp(self):
        theory.thy = theory.EmptyTheory()

    def testExport(self):
        """Basic case."""
        pt1 = ProofTerm.assume(Eq(x,y))
        pt2 = ProofTerm.assume(Eq(y,z))
        pt3 = pt1.transitive(pt2)

        prf = pt3.export()
        self.assertEqual(len(prf.items), 3)
        self.assertEqual(theory.verify(prf), pt3.th)

    def testExport2(self):
        """Repeated theorems."""
        pt1 = ProofTerm.assume(Eq(x,y))
        pt2 = ProofTerm.reflexive(f)
        pt3 = pt2.combination(pt1)  # f x = f y
        pt4 = pt3.combination(pt1)  # f x x = f y y

        prf = pt4.export()
        self.assertEqual(len(prf.items), 4)
        self.assertEqual(theory.verify(prf), pt4.th)

    def testExport3(self):
        """Case with atoms."""
        pt1 = ProofTerm.atom(0, Thm(Eq(x,y)))
        pt2 = ProofTerm.atom(1, Thm(Eq(y,z)))
        pt3 = pt1.transitive(pt2)

        prf = Proof()
        prf.add_item(0, rule="sorry", th=Thm(Eq(x,y)))
        prf.add_item(1, rule="sorry", th=Thm(Eq(y,z)))
        pt3.export(prf=prf)

        self.assertEqual(theory.verify(prf), Thm(Eq(x,z)))

    def testExportAtomRoot(self):
        """An atom root exports as a pure reference line: it re-cites the
        item it came from and derives nothing of its own, so the kernel
        replays it as a citation."""
        pt = ProofTerm.atom(0, Thm(Eq(x, y)))

        prf = Proof()
        prf.add_item(0, rule="sorry", th=Thm(Eq(x, y)))
        prf = pt.export(prefix=ItemID(1), prf=prf)

        ref = prf.items[1]
        self.assertEqual(ref.rule, "reference")
        self.assertEqual(ref.args, None)
        self.assertEqual(ref.prevs, [ItemID(0)])
        self.assertEqual(ref.th, Thm(Eq(x, y)))
        self.assertEqual(theory.verify(prf), Thm(Eq(x, y)))


if __name__ == "__main__":
    unittest.main()

# Author: Bohua Zhan

"""Tests for the core half of verify (core/verify.py).

Moved out of kernel/tests/theory_test.py when the kernel half was
slimmed to a pure primitive replay (audit §7.1): the report counts and
the derivation error messages asserted here are produced by the core
expander, not by the kernel. The kernel half no longer accepts a report
or any macro-aware option.

"""

import unittest

from kernel.type import TVar, TFun, BoolType
from kernel.term import SVar, Var, Eq, Implies, Inst
from kernel.thm import Thm
from kernel.proof import Proof
from kernel import theory
from kernel.theory import CheckProofException
from kernel.report import ProofReport
from core import verify as core_verify


Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", Tab)
A = Var("A", BoolType)
B = Var("B", BoolType)


class VerifyTest(unittest.TestCase):
    def setUp(self):
        theory.thy = theory.EmptyTheory()

    def testCheckProof(self):
        """Proof of [A, A --> B] |- B."""
        A_to_B = Implies(A, B)
        prf = Proof(A_to_B, A)
        prf.add_item(2, "implies_elim", prevs=[0, 1])

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt), Thm(B, (A_to_B, A)))
        self.assertEqual(rpt.steps, 3)

    def testCheckProof2(self):
        """Proof of |- A --> A."""
        prf = Proof(A)
        prf.add_item(1, "implies_intr", args=A, prevs=[0])

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt), Thm(Implies(A, A)))
        self.assertEqual(rpt.steps, 2)

    def testCheckProof3(self):
        """Proof of [x = y, y = z] |- f z = f x."""
        x_eq_y = Eq(x, y)
        y_eq_z = Eq(y, z)
        prf = Proof(x_eq_y, y_eq_z)
        prf.add_item(2, "transitive", prevs=[0, 1])
        prf.add_item(3, "symmetric", prevs=[2])
        prf.add_item(4, "reflexive", args=f)
        prf.add_item(5, "combination", prevs=[4, 3])

        rpt = ProofReport()
        th = Thm(Eq(f(z), f(x)), (x_eq_y, y_eq_z))
        self.assertEqual(core_verify.verify(prf, rpt), th)
        self.assertEqual(rpt.steps, 6)

    def testCheckProof4(self):
        """Proof of |- x = y --> x = y by instantiating an existing theorem."""
        theory.thy.add_theorem("trivial", Thm(Implies(A, A)))

        x_eq_y = Eq(x, y)
        prf = Proof()
        prf.add_item(0, "theorem", args="trivial")
        prf.add_item(1, "substitution", args=Inst(A=x_eq_y), prevs=[0])

        rpt = ProofReport()
        th = Thm(Implies(x_eq_y, x_eq_y))
        self.assertEqual(core_verify.verify(prf, rpt), th)
        self.assertEqual(rpt.steps, 2)

    def testCheckProof5(self):
        """Empty instantiation."""
        theory.thy.add_theorem("trivial", Thm(Implies(A, A)))

        prf = Proof()
        prf.add_item(0, "theorem", args="trivial")
        prf.add_item(1, "substitution", args=Inst(), prevs=[0])

        rpt = ProofReport()
        th = Thm(Implies(SVar('A', BoolType), SVar('A', BoolType)))
        self.assertEqual(core_verify.verify(prf, rpt), th)
        self.assertEqual(rpt.steps_stat(), (1, 1, 0))
        self.assertEqual(rpt.th_names, {"trivial"})

    def testCheckProofFail2(self):
        """Invalid derivation."""
        prf = Proof(A)
        prf.add_item(1, "symmetric", prevs=[0])

        self.assertRaisesRegex(
            CheckProofException, "invalid derivation", core_verify.verify, prf)

    def testCheckProofFail3(self):
        """Invalid input to derivation."""
        prf = Proof(A)
        prf.add_item(1, "implies_intr", prevs=[0])

        self.assertRaisesRegex(
            CheckProofException,
            "invalid input to derivation", core_verify.verify, prf)

    def testCheckProofFail8(self):
        """Proof method not found."""
        prf = Proof()
        prf.add_item(0, "random")

        self.assertRaisesRegex(
            CheckProofException,
            "proof method not found", core_verify.verify, prf)

    def testCheckProofGap(self):
        """Check proof with gap."""
        prf = Proof()
        prf.add_item(0, "sorry", th=Thm(Implies(A, B)))
        prf.add_item(1, "sorry", th=Thm(A))
        prf.add_item(2, "implies_elim", prevs=[0, 1])

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt), Thm(B))
        self.assertEqual(rpt.gaps, [Thm(Implies(A, B)), Thm(A)])


if __name__ == "__main__":
    unittest.main()

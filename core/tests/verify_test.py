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

    def testOracleTrusted(self):
        """Oracle line admitted by the trust set: the proof verifies and
        the trust report records the oracle (audit §7.2)."""
        prf = Proof()
        prf.add_item(0, "oracle", args="dummy_solver", th=Thm(A, A))

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt, trust={'dummy_solver'}),
                         Thm(A, A))
        self.assertEqual(rpt.oracles, {'dummy_solver'})

    def testOracleUntrusted(self):
        """Oracle line without a trust declaration is a hard failure
        (audit §7.1: the strict default rejects every oracle)."""
        prf = Proof()
        prf.add_item(0, "oracle", args="dummy_solver", th=Thm(A, A))

        self.assertRaisesRegex(
            CheckProofException, "not trusted", core_verify.verify, prf)

    def testAxiomHole(self):
        """A theorem line naming an axiom is recorded in the trust
        report (audit §7.2); without the axiom declaration the same
        line is an ordinary theorem and records no hole."""
        theory.thy.add_theorem("some_axiom", Thm(Implies(A, A)))
        axiom_th = theory.thy.get_theorem("some_axiom")
        prf = Proof()
        prf.add_item(0, "theorem", args="some_axiom")

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt, axioms={'some_axiom'}),
                         axiom_th)
        self.assertEqual(rpt.axioms, {'some_axiom'})

        rpt2 = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt2), axiom_th)
        self.assertEqual(rpt2.axioms, set())

    def testAutoCloseMacro(self):
        """auto_close (level None) expands to a reference: exact citation
        verifies end-to-end with the macro recorded as expanded."""
        import core.macro.registry  # noqa: F401 -- registers auto_close
        prf = Proof(A)                      # line 0: assume A
        prf.add_item(1, "auto_close", prevs=[0], th=Thm(A, A))

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt), Thm(A, A))
        self.assertIn('auto_close', rpt.macros_expand)

    def testSubproofExpanded(self):
        """A subproof line is flattened: its items are emitted inline and
        the enclosing line stands as a reference citable by later lines."""
        inner = Proof()
        inner.add_item((1, 0), "assume", args=A)
        inner.add_item((1, 1), "implies_elim", prevs=[(0,), (1, 0)])

        prf = Proof(Implies(A, B))          # line (0,): assume A --> B
        prf.add_item(1, "subproof", th=Thm(B, (Implies(A, B), A)))
        prf.items[1].subproof = inner
        prf.add_item(2, "implies_intr", args=A, prevs=[(1,)])

        rpt = ProofReport()
        self.assertEqual(core_verify.verify(prf, rpt),
                         Thm(Implies(A, B), (Implies(A, B),)))


if __name__ == "__main__":
    unittest.main()

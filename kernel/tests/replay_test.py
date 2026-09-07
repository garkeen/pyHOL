# Author: Bohua Zhan
# Step 0 acceptance test (ARCHITECTURE_AUDIT.md §8 step 0):
#
#   Prove a theorem using ONLY kernel + syntax (no framework/core,
#   no domains, no solvers), with a macro, and close it via pure
#   primitive replay.
#
# The macro must expand to a pure primitive stream that kernel/replay.py
# can re-verify. Everything runs in an EmptyTheory -- no library theories,
# no macros registered by framework/macros (their proof machinery lives
# in core.conv).
#
# This test is the "kernel断奶" acceptance test: it must pass without
# importing anything from core.

import io
import json
import os
import subprocess
import sys
import unittest

from kernel.type import TVar, TFun, BoolType
from kernel.term import Var, Implies, Eq, Forall, Const
from kernel.thm import Thm
from kernel.proof import Proof
from kernel import theory
from kernel import replay


Ta = TVar("a")
x = Var("x", Ta)
A = Var("A", BoolType)
B = Var("B", BoolType)
C = Var("C", BoolType)
A_to_B = Implies(A, B)
B_to_C = Implies(B, C)


def And(a, b):
    conj = Const("conj", TFun(BoolType, BoolType, BoolType))
    return conj(a, b)


class NoFrameworkImportTest(unittest.TestCase):
    def testNoFrameworkLoaded(self):
        """Importing the kernel in a fresh interpreter must not pull in
        the core. Checked in a subprocess so the verdict does not
        depend on what other tests imported earlier in this process."""
        code = (
            "import sys, json; import kernel; "
            "print(json.dumps(sorted(m for m in sys.modules "
            "if m == 'framework' or m.startswith('core.'))))"
        )
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        res = subprocess.run([sys.executable, '-c', code], capture_output=True,
                             text=True, cwd=root)
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertEqual(json.loads(res.stdout), [])


class PurePrimitiveReplayTest(unittest.TestCase):
    def setUp(self):
        theory.thy = theory.EmptyTheory()

    def testImpliesTrans(self):
        """[A --> B, B --> C, A] |- B by hand in primitives."""
        prf = Proof(A_to_B, B_to_C)
        prf.add_item(2, "assume", args=A)
        prf.add_item(3, "implies_elim", prevs=[0, 2])       # B, hyps A-->B, A
        prf.add_item(4, "implies_elim", prevs=[1, 3])      # C, hyps ...

        th, holes = replay.replay(prf)
        self.assertEqual(th, Thm(C, (A_to_B, B_to_C, A)))
        self.assertEqual(holes, [])

    def testGap(self):
        """A proof with a gap: replay yields the derived theorem plus
        the assumption-rule list."""
        prf = Proof()
        prf.add_item(0, "sorry", th=Thm(A_to_B))
        prf.add_item(1, "sorry", th=Thm(A))
        prf.add_item(2, "implies_elim", prevs=[0, 1])

        th, holes = replay.replay(prf)
        self.assertEqual(th, Thm(B))
        self.assertEqual(holes, [("sorry", None, Thm(A_to_B)),
                                 ("sorry", None, Thm(A))])

    def testTheorem(self):
        """Theorem lines replay through the theory."""
        theory.thy.add_theorem("triv", Thm(Implies(A, A)))
        prf = Proof()
        prf.add_item(0, "theorem", args="triv")

        th, holes = replay.replay(prf)
        self.assertEqual(th, theory.thy.get_theorem("triv"))
        self.assertEqual(holes, [])

    def testAxiomHole(self):
        """A theorem line referencing an axiom enters the hole list."""
        theory.thy.add_theorem("ax1", Thm(A_to_B))
        theory.thy.set_status("ax1", "AXIOM")
        prf = Proof()
        prf.add_item(0, "theorem", args="ax1")

        th, holes = replay.replay(prf)
        self.assertEqual(th, theory.thy.get_theorem("ax1"))
        self.assertEqual(len(holes), 1)
        self.assertEqual(holes[0][0], "axiom")
        self.assertEqual(holes[0][1], "ax1")

    def testForall(self):
        """|- !x. x = x via forall_intr."""
        prf = Proof()
        prf.add_item(0, "reflexive", args=x)
        prf.add_item(1, "forall_intr", args=x, prevs=[0])

        th, holes = replay.replay(prf)
        self.assertEqual(th, Thm(Forall(x, Eq(x, x))))
        self.assertEqual(holes, [])

    def testUnknownRule(self):
        """An unknown rule is an error: the rule set is closed."""
        prf = Proof(A)
        prf.add_item(1, "random_rule", prevs=[0])
        self.assertRaises(replay.ReplayException, replay.replay, prf)

    def testMacroLineRejected(self):
        """Macro lines are rejected: expand first (closed rule set)."""
        prf = Proof()
        prf.add_item(0, "intros", prevs=[])
        self.assertRaises(replay.ReplayException, replay.replay, prf)


class BootstrapMacroTest(unittest.TestCase):
    """The full step-0 scenario: a theorem proved through a kernel-only
    macro, expanded into a pure primitive stream and re-verified by
    replay -- without any framework import."""

    def setUp(self):
        theory.thy = theory.EmptyTheory()
        import kernel.bootstrap  # noqa: F401  (registers bootstrap macros)

    def testIntrosEndToEnd(self):
        """|- A --> B --> A ∧ B closed by the bootstrap intros macro.

        Stream: assume A, assume B, sorry (the conjunction goal), then
        the macro line expands to implies_intr over the sorry-derived
        statement.
        """
        from kernel.bootstrap import expand_macro_proof

        goal = Implies(A, Implies(B, And(A, B)))
        prf = Proof()
        prf.add_item(0, "assume", args=A)
        prf.add_item(1, "assume", args=B)
        prf.add_item(2, "sorry", th=Thm(And(A, B), A, B))

        # Expand: intros over [A assumed, B assumed, gap].
        expanded = expand_macro_proof(
            prf, "intros", args=None,
            prevs=[Thm(A, A), Thm(B, B), Thm(And(A, B), A, B)],
            prev_ids=[0, 1, 2])
        self.assertNotEqual(expanded, None)

        # Every appended line is a primitive.
        for item in expanded.items:
            self.assertNotIn(item.rule, ("intros",))
            if item.rule:
                from kernel.thm import primitive_deriv
                self.assertTrue(item.rule in primitive_deriv
                                or item.rule in ("sorry", "theorem",
                                                 "variable", "assume"))

        th, holes = replay.replay(expanded)
        self.assertEqual(th, Thm(goal))
        # The gap was consumed by implies_intr but remains a hole: the
        # proof is only complete once every sorry is discharged.
        self.assertEqual(holes, [("sorry", None, Thm(And(A, B), A, B))])

    def testTrivialEndToEnd(self):
        """|- A --> B --> A closed by the bootstrap trivial macro."""
        from kernel.bootstrap import expand_macro_proof

        goal = Implies(A, Implies(B, A))
        prf = Proof()
        prf.add_item(0, "trivial", args=goal)
        # Replace the macro line by its primitive expansion.
        prf.items = prf.items[:0]
        base = Proof()
        expanded = expand_macro_proof(
            base, "trivial", args=goal, prevs=[], prev_ids=[])
        self.assertNotEqual(expanded, None)

        th, holes = replay.replay(expanded)
        self.assertEqual(th, Thm(goal))
        self.assertEqual(holes, [])

    def testFrameworkMacroRejected(self):
        """Framework macros are not bootstrap macros: the kernel-side
        expander returns None for them (no fallback to framework)."""
        from kernel.bootstrap import expand_macro_proof
        prf = Proof()
        res = expand_macro_proof(prf, "rewrite_goal", args=None,
                                 prevs=[], prev_ids=[])
        self.assertIsNone(res)


if __name__ == "__main__":
    unittest.main()

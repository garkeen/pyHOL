# Author: Bohua Zhan

import unittest
from core import auto
from kernel.proofterm import TacticException
from theories.logic.tests.logic_test import test_macro


class AutoTest(unittest.TestCase):
    def testSolve(self):
        test_data = [
            ("A --> B --> A & B"),
            ("A & B --> B & A"),
            ("A | B --> B | A"),
            ("A & B & C --> (A & B) & C"),
            ("A | B | C --> (A | B) | C")
        ]

        vars = {'A': 'bool', 'B': 'bool'}
        for expr in test_data:
            test_macro(self, 'logic_base', 'auto', vars=vars, args=expr, res=expr)

    def testBackchain(self):
        # Modus ponens on assumptions: B follows from A --> B and A.
        test_macro(self, 'logic_base', 'auto',
                   vars={'A': 'bool', 'B': 'bool'},
                   assms=["A --> B", "A"], args="B", res="B")
        # Backward chaining over hint_backward theorems: iffI closes
        # A <--> B from the two implications.
        test_macro(self, 'logic_base', 'auto',
                   vars={'A': 'bool', 'B': 'bool'},
                   assms=["A --> B", "B --> A"], args="A <--> B", res="A <--> B")

    def testCannotSolve(self):
        # Bare variable with no assumptions and no matching theorem:
        # solve must honestly fail with TacticException.
        test_macro(self, 'logic_base', 'auto',
                   vars={'C': 'bool'}, args="C", failed=TacticException)

    def testSympyRegistered(self):
        # Loading any theory must register the solvers into the generic
        # auto engine: 8 sympy + 4 omega comparison heads, 2 sympy
        # negated equalities + 4 omega negated comparisons.
        self.assertEqual(len(auto.global_autos), 12)
        self.assertEqual(len(auto.global_autos_neg), 6)

    def testSympySolve(self):
        # Real comparisons closed by the sympy decision procedure.
        # The proof expands to the sympy level-0 oracle (computation
        # without derivation: audit §7.1 trust set).
        test_macro(self, 'real', 'auto', args="sqrt 2 >= 1", res="sqrt 2 >= 1",
                   oracles=frozenset({'sympy'}))
        test_macro(self, 'real', 'auto', args="~((1::real) = 2)",
                   res="~((1::real) = 2)",
                   oracles=frozenset({'sympy'}))
        # Non-arithmetic variable goal still fails honestly.
        test_macro(self, 'real', 'auto',
                   vars={'C': 'bool'}, args="C", failed=TacticException)

    def testOmegaSolve(self):
        # Integer comparisons closed by the omega decision procedure.
        # The proof expands to the int_const_ineq / int_eval level-0
        # oracles (computation without derivation: audit §7.1 trust set).
        test_macro(self, 'int', 'auto',
                   vars={'x': 'int', 'y': 'int'},
                   assms=["x < y"], args="~(y <= x)", res="~(y <= x)",
                   oracles=frozenset({'int_const_ineq', 'int_eval'}))
        test_macro(self, 'int', 'auto',
                   vars={'x': 'int', 'y': 'int'},
                   assms=["y < x", "x < y"], args="x <= y", res="x <= y",
                   oracles=frozenset({'int_const_ineq', 'int_eval'}))
        # Satisfiable input fails honestly.
        test_macro(self, 'int', 'auto',
                   vars={'x': 'int', 'y': 'int'},
                   assms=["y < x"], args="x <= y", failed=TacticException)

    def testLoopClosesAfterSimp(self):
        # Needs simplify-then-solve: simp rewrites to true, solve closes.
        test_macro(self, 'logic', 'auto',
                   vars={'A': 'bool', 'B': 'bool'},
                   args="(if A then B else B) = B",
                   res="(if A then B else B) = B")

    def testLoopHonestFailure(self):
        # Loop exhausts without progress: still TacticException, no gaps.
        test_macro(self, 'logic', 'auto',
                   vars={'A': 'bool', 'B': 'bool', 'C': 'bool'},
                   args="C", failed=TacticException)

    def testConditionalRewrite(self):
        # Conditional rewrite if_P discharges P from assumptions, then
        # the goal closes by reflexivity.
        test_macro(self, 'nat', 'auto',
                   vars={'P': 'bool', 'x': 'nat', 'y': 'nat'},
                   assms=["P"], args="(if P then x else y) = x",
                   res="(if P then x else y) = x")
        # Without the assumption the premise cannot be discharged.
        test_macro(self, 'nat', 'auto',
                   vars={'P': 'bool', 'x': 'nat', 'y': 'nat'},
                   args="(if P then x else y) = x", failed=TacticException)

    def testIntNorm(self):
        # int_norm closes polynomial equalities by normalization.
        test_macro(self, 'int', 'int_norm',
                   vars={'x': 'int', 'y': 'int'},
                   args="x + 0 = x", res="x + 0 = x")
        test_macro(self, 'int', 'int_norm',
                   vars={'x': 'int', 'y': 'int'},
                   args="x + y = y + x", res="x + y = y + x")
        # Non-theorem fails honestly.
        from kernel.proofterm import TacticException as TE
        test_macro(self, 'int', 'int_norm',
                   vars={'x': 'int'},
                   args="x + 1 = x + 2", failed=AssertionError)


if __name__ == "__main__":
    unittest.main()

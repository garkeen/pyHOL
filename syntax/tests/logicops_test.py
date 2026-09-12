# Tests for syntax/logicops.py recognition predicates.
#
# These predicates were methods installed on Term until the C2 fix
# (ARCHITECTURE_AUDIT.md task F). testStripConj/testStripDisj moved here
# from kernel/tests/term_test.py so the tests follow the module; the
# remaining cases cover the other five predicates.

import unittest

from kernel.type import TVar, TFun, BoolType
from kernel.term import Term, Var, Const
from syntax.logicops import (
    And, Or, Not, Exists, is_not, is_conj, strip_conj,
    is_disj, strip_disj, is_exists, strip_exists,
)

Ta = TVar("a")
Tb = TVar("b")
a = Var("a", Ta)
b = Var("b", Tb)
x = Var("x", Ta)
y = Var("y", Ta)
P = Const("P", TFun(Ta, BoolType))


class LogicOpsTest(unittest.TestCase):
    def testNoMethodInstallation(self):
        """The predicates are plain functions, not Term methods.

        C2 fix: importing syntax.logicops must not install anything on
        kernel.Term, so predicate availability can never depend on
        import order again.
        """
        for name in ('is_not', 'is_conj', 'strip_conj', 'is_disj',
                     'strip_disj', 'is_exists', 'strip_exists'):
            self.assertFalse(hasattr(Term, name), name)

    def testIsNot(self):
        self.assertTrue(is_not(Not(a)))
        self.assertFalse(is_not(a))
        self.assertFalse(is_not(And(a, b)))

    def testIsConj(self):
        self.assertTrue(is_conj(And(a, b)))
        self.assertFalse(is_conj(a))
        self.assertFalse(is_conj(Or(a, b)))

    def testStripConj(self):
        test_data = [
            (a, [a]),
            (And(a, b, a), [a, b, a])
        ]

        for t, res in test_data:
            self.assertEqual(strip_conj(t), res)

    def testIsDisj(self):
        self.assertTrue(is_disj(Or(a, b)))
        self.assertFalse(is_disj(a))
        self.assertFalse(is_disj(And(a, b)))

    def testStripDisj(self):
        test_data = [
            (a, [a]),
            (Or(a, b, a), [a, b, a])
        ]

        for t, res in test_data:
            self.assertEqual(strip_disj(t), res)

    def testIsExists(self):
        self.assertTrue(is_exists(Exists(x, P(x))))
        self.assertFalse(is_exists(a))
        self.assertFalse(is_exists(Not(a)))

    def testStripExists(self):
        ex = Exists(x, P(x))
        vars, body = strip_exists(ex)
        self.assertEqual(vars, [x])
        self.assertEqual(body, P(x))

        # Nested quantification strips outermost-first.
        ex2 = Exists(x, Exists(y, P(x)))
        vars, body = strip_exists(ex2)
        self.assertEqual(vars, [x, y])

        # num bounds how many quantifiers are stripped.
        vars, body = strip_exists(ex2, num=1)
        self.assertEqual(vars, [x])
        self.assertTrue(is_exists(body))


if __name__ == "__main__":
    unittest.main()

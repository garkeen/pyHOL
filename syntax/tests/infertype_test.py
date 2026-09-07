# Author: Bohua Zhan

import unittest
from functools import partial

from kernel.type import TVar, TFun, BoolType
from syntax.numeral import NatType
from kernel.term import Term, Var, Const, Comb, Abs, Bound, Implies, Lambda, Eq
from core import basic
from core import logic
from theories.nat import util_nat as nat
from util.list import ListType, cons, mk_append, nil
from core import context
from syntax.infertype import type_infer, infer_printed_type, TypeInferenceException

Ta = TVar("a")


class InferTypeTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('list')
        context.ctxt = context.Context(vars={
            "A" : BoolType,
            "P" : TFun(Ta, BoolType),
            "a" : Ta,
            "b" : Ta,
        })

    def testInferType(self):
        test_data = [
            # A1 --> A2
            (Const("implies", None)(Var("A1", None), Var("A2", None)),
             Implies(Var("A1", BoolType), Var("A2", BoolType))),
            # A1 = A2
            (Const("equals", None)(Var("A1", BoolType), Var("A2", None)),
             Eq(Var("A1", BoolType), Var("A2", BoolType))),
            # a = b
            (Const("equals", None)(Var("a", None), Var("b", None)),
             Const("equals", TFun(Ta, Ta, BoolType))(Var("a", Ta), Var("b", Ta))),
            # %x. P x
            (Abs("x", None, Var("P", None)(Bound(0))),
             Abs("x", Ta, Var("P", TFun(Ta, BoolType))(Bound(0)))),
            # %x y. x = y
            (Abs("x", Ta, Abs("y", None, Const("equals", None)(Bound(1), Bound(0)))),
             Abs("x", Ta, Abs("y", Ta, Const("equals", TFun(Ta, Ta, BoolType))(Bound(1), Bound(0))))),
            # [a]
            (Const("cons", None)(Var("a", None), Const("nil", None)),
             cons(Ta)(Var("a", Ta), Const("nil", ListType(Ta)))),
        ]

        for t, res in test_data:
            self.assertEqual(type_infer(t, ctxt=context.ctxt), res)

    def testInferTypeFail(self):
        test_data = [
            (Const("implies", None)(Var("A1", NatType), Var("A2", None))),
            (Const("equals", None)(Var("A", None), Var("a", None)))
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Unable to unify", partial(type_infer, t, ctxt=context.ctxt))

    def testInferTypeFail2(self):
        # Free variables with no type constraint are reported as undeclared.
        t = Abs("x", None, Abs("y", None, Const("equals", None)(Var("x", None), Var("y", None))))
        self.assertRaisesRegex(TypeInferenceException, "not declared", partial(type_infer, t, ctxt=context.ctxt))

        # A polymorphic constant with no type annotation cannot be resolved.
        self.assertRaisesRegex(TypeInferenceException, "Cannot determine the type",
                               partial(type_infer, Const("nil", None), ctxt=context.ctxt))

    def testInferTypeFail3(self):
        test_data = [
            Var('s', None)(Var('s', None)),
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Infinite loop", partial(type_infer, t, ctxt=context.ctxt))

    def testInferPrintedType(self):
        t = Const("nil", ListType(Ta))
        infer_printed_type(t, ctxt=context.ctxt)
        self.assertTrue(hasattr(t, "print_type"))

        t = cons(Ta)(Var("a", Ta))
        infer_printed_type(t, ctxt=context.ctxt)
        self.assertFalse(hasattr(t.fun, "print_type"))

        t = Eq(Const("nil", ListType(Ta)), Const("nil", ListType(Ta)))
        infer_printed_type(t, ctxt=context.ctxt)
        self.assertFalse(hasattr(t.fun.fun, "print_type"))
        self.assertTrue(hasattr(t.arg1, "print_type"))
        self.assertFalse(hasattr(t.arg, "print_type"))

        t = Eq(mk_append(nil(Ta),nil(Ta)), nil(Ta))
        infer_printed_type(t, ctxt=context.ctxt)
        self.assertTrue(hasattr(t.arg1.arg1, "print_type"))
        self.assertFalse(hasattr(t.arg1.arg, "print_type"))
        self.assertFalse(hasattr(t.arg, "print_type"))

        t = Lambda(Var("x", Ta), Eq(Var("x", Ta), Var("x", Ta)))
        infer_printed_type(t, ctxt=context.ctxt)


if __name__ == "__main__":
    unittest.main()

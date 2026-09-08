# Author: Bohua Zhan

import unittest

from kernel.type import TConst, TVar, STVar, TFun, BoolType
from kernel.term import Term, Var, Const, Comb, Abs, Bound, Implies, Eq, TyInst
from kernel.thm import Thm
from kernel.proof import Proof, ItemID
from kernel import theory
from kernel.theory import Theory, TheoryException, CheckProofException
from kernel import extension
from kernel.report import ExtensionReport


Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", Tab)
A = Var("A", BoolType)
B = Var("B", BoolType)
C = Var("C", BoolType)


class TheoryTest(unittest.TestCase):
    def setUp(self):
        theory.thy = theory.EmptyTheory()

    def testRegisterMacroSetsName(self):
        """register_macro backfills the macro's registration name, which
        level-0 eval macros use to label their oracle holes."""
        from kernel.macro import Macro
        from kernel.theory import register_macro, get_macro

        @register_macro('dummy_oracle_test')
        class DummyOracleMacro(Macro):
            def __init__(self):
                self.level = 0
                self.sig = None
                self.limit = None

        try:
            self.assertEqual(get_macro('dummy_oracle_test').name,
                             'dummy_oracle_test')
        finally:
            del theory.global_macros['dummy_oracle_test']

    def testEmptyTheory(self):
        self.assertEqual(theory.thy.get_type_sig("bool"), 0)
        self.assertEqual(theory.thy.get_type_sig("fun"), 2)
        self.assertEqual(theory.thy.get_term_sig("equals"), TFun(Ta,Ta,BoolType))
        self.assertEqual(theory.thy.get_term_sig("implies"), TFun(BoolType,BoolType,BoolType))

    def testCheckType(self):
        test_data = [
            Ta,
            TFun(Ta, Tb),
            TFun(TFun(Ta, Ta), Tb),
            TFun(BoolType, BoolType),
            TFun(TFun(Ta, BoolType), BoolType),
        ]

        for T in test_data:
            self.assertEqual(theory.thy.check_type(T), None)

    def testCheckTypeFail(self):
        test_data = [
            TConst("bool", Ta),
            TConst("bool", Ta, Ta),
            TConst("fun"),
            TConst("fun", Ta),
            TConst("fun", Ta, Ta, Ta),
            TFun(TConst("bool", Ta), TConst("bool")),
            TFun(TConst("bool"), TConst("bool", Ta)),
            TConst("random")
        ]

        for T in test_data:
            self.assertRaises(TheoryException, theory.thy.check_type, T)

    def testCheckTerm(self):
        test_data = [
            x,
            Eq(x, y),
            Eq(f, f),
            Implies(A, B),
            Abs("x", Ta, Eq(x, y)),
        ]

        for t in test_data:
            self.assertEqual(theory.thy.check_term(t), None)

    def testCheckTermFail(self):
        test_data = [
            Const("random", Ta),
            Const("equals", TFun(Ta, Tb, BoolType)),
            Const("equals", TFun(Ta, Ta, Tb)),
            Const("implies", TFun(Ta, Ta, BoolType)),
            Comb(Const("random", Tab), x),
            f(Const("random", Ta)),
            Abs("x", Ta, Const("random", Ta)),
        ]

        for t in test_data:
            self.assertRaises(TheoryException, theory.thy.check_term, t)

    def testCheckProofFail(self):
        """Previous item not found."""
        prf = Proof()
        prf.add_item(0, "implies_intr", prevs=[1])

        self.assertRaisesRegex(CheckProofException, "id 0 cannot depend on 1", theory.verify, prf)

    def testCheckProofFail4(self):
        """Output does not match."""
        prf = Proof(A)
        prf.add_item(1, "implies_intr", args=A, prevs=[0], th = Thm(Implies(A,B)))

        self.assertRaisesRegex(CheckProofException, "output does not match", theory.verify, prf)

    def testCheckProofFail5(self):
        """Theorem not found."""
        prf = Proof()
        prf.add_item(0, "theorem", args="random")

        self.assertRaisesRegex(CheckProofException, "theorem not found", theory.verify, prf)

    def testCheckProofFail6(self):
        """Typing error: statement is not non-boolean."""
        prf = Proof(x)

        self.assertRaisesRegex(CheckProofException, "typing error", theory.verify, prf)

    def testCheckProofFail7(self):
        """Typing error: type-checking failed."""
        prf = Proof(Comb(Var("P", TFun(Tb, BoolType)), x))

        self.assertRaisesRegex(CheckProofException, "typing error", theory.verify, prf)

    def testAssumsSubset(self):
        """res_th is OK if assumptions is a subset of that of seq.th."""
        prf = Proof()
        prf.add_item(0, "assume", args=A, th=Thm(A, (A, B)))

        self.assertEqual(theory.verify(prf), Thm(A, (A, B)))

    def testAssumsSubsetFail(self):
        """res_th is not OK if assumptions is not a subset of that of seq.th."""
        prf = Proof()
        prf.add_item(0, "assume", args=A, th=Thm(A))

        self.assertRaisesRegex(CheckProofException, "output does not match", theory.verify, prf)

    def testUncheckedExtend(self):
        """Unchecked extension."""
        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))

        exts = [
            extension.Constant("id", TFun(Ta, Ta)),
            extension.Theorem("id_def", Thm(Eq(id_const, id_def))),
            extension.Theorem("id.simps", Thm(Eq(id_const, x)))
        ]

        self.assertEqual(theory.thy.unchecked_extend(exts), None)
        self.assertEqual(theory.thy.get_term_sig("id"), TFun(Ta, Ta))
        self.assertEqual(theory.get_theorem("id_def", svar=False), Thm(Eq(id_const, id_def)))
        self.assertEqual(theory.get_theorem("id.simps", svar=False), Thm(Eq(id_const, x)))

    def testCheckedExtend(self):
        """Checked extension: adding an axiom."""
        id_simps = Eq(Comb(Const("id", TFun(Ta,Ta)), x), x)
        exts = [extension.Theorem("id.simps", Thm(id_simps))]

        ext_report = theory.thy.checked_extend(exts)
        self.assertEqual(theory.get_theorem("id.simps", svar=False), Thm(id_simps))
        self.assertEqual(ext_report.get_axioms(), [("id.simps", Thm(id_simps))])

    def testCheckedExtend2(self):
        """Checked extension: proved theorem."""
        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        id_simps = Eq(id_const(x), x)

        # Proof of |- id x = x from |- id = (%x. x)
        prf = Proof()
        prf.add_item(0, "theorem", args="id_def")  # id = (%x. x)
        prf.add_item(1, "subst_type", args=TyInst(a=TVar('a')), prevs=[0])  # id = (%x. x)
        prf.add_item(2, "reflexive", args=x)  # x = x
        prf.add_item(3, "combination", prevs=[1, 2])  # id x = (%x. x) x
        prf.add_item(4, "beta_conv", args=id_def(x))  # (%x. x) x = x
        prf.add_item(5, "transitive", prevs=[3, 4])  # id x = x

        exts = [
            extension.Constant("id", TFun(Ta, Ta)),
            extension.Theorem("id_def", Thm(Eq(id_const, id_def))),
            extension.Theorem("id.simps", Thm(id_simps), prf)
        ]

        ext_report = theory.thy.checked_extend(exts)
        self.assertEqual(theory.get_theorem("id.simps", svar=False), Thm(id_simps))
        self.assertEqual(ext_report.get_axioms(), [('id_def', Thm(Eq(id_const, id_def)))])

    def testCheckedExtend3(self):
        """Axiomatized constant."""
        exts = [
            extension.TConst("nat", 0),
            extension.Constant("id", TFun(Ta,Ta))
        ]
        ext_report = theory.thy.checked_extend(exts)
        self.assertEqual(theory.thy.get_type_sig("nat"), 0)
        self.assertEqual(theory.thy.get_term_sig("id"), TFun(Ta,Ta))


if __name__ == "__main__":
    unittest.main()

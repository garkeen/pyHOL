# logic/macros/expr.py - Expression evaluation macros

from kernel.type import TConst, TFun, BoolType, NatType
from kernel.term import Term, Const, Nat
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from logic.logic import apply_theorem
from domains.nat import util_nat as nat
from domains.function.conv import fun_upd_eval_conv
from util.expr import N, V, Plus, Times, avalI
from kernel.proofterm import ProofTerm


@register_macro('prove_avalI')
class prove_avalI_macro(Macro):
    """Prove a theorem of the form avalI s t n."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'avalI_times'

    def get_avalI_th(self, s, t):
        """Given state s and expression t, return the proof of a theorem
        of the form avalI s t n.

        """
        def helper(t):
            if t.head == N:
                n, = t.args
                return apply_theorem("avalI_const", concl=avalI(s, N(n), n))
            elif t.head == V:
                x, = t.args
                pt = apply_theorem("avalI_var", concl=avalI(s, V(x), s(x)))
                return pt.on_arg(fun_upd_eval_conv())
            elif t.head == Plus:
                a1, a2 = t.args
                pt = apply_theorem("avalI_plus", helper(a1), helper(a2))
                return pt.on_arg(nat.nat_conv())
            elif t.head == Times:
                a1, a2 = t.args
                pt = apply_theorem("avalI_times", helper(a1), helper(a2))
                return pt.on_arg(nat.nat_conv())
        return helper(t)

    def get_avalI(self, s, t):
        """Given state s and expression t, return the integer n such that
        avalI s t n holds.

        """
        def helper(t):
            if t.head == N:
                return t.args[0].dest_number()
            elif t.head == V:
                x, = t.args
                res = fun_upd_eval_conv().eval(s(x)).prop.rhs
                assert res.is_number(), "get_avalI"
                return res.dest_number()
            elif t.head == Plus:
                a1, a2 = t.args
                return helper(a1) + helper(a2)
            elif t.head == Times:
                a1, a2 = t.args
                return helper(a1) * helper(a2)

        return helper(t)

    def eval(self, goal, ths):
        assert isinstance(goal, Term), "prove_avalI_macro"
        assert len(ths) == 0, "prove_avalI_macro"
        s, t, n = goal.args
        res = self.get_avalI(s, t)
        assert n == Nat(res), "prove_avalI_macro: wrong result"
        return Thm(goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "prove_avalI_macro"
        if goal.head != avalI or len(goal.args) != 3:
            return False
        s, t, n = goal.args
        try:
            res = self.get_avalI(s, t)
        except AssertionError:
            return False

        return n == Nat(res)

    def get_proof_term(self, goal, pts):
        assert isinstance(goal, Term), "prove_avalI_macro"
        assert len(pts) == 0, "prove_avalI_macro"
        s, t, n = goal.args
        pt = self.get_avalI_th(s, t)
        assert n == pt.prop.arg, "prove_avalI_macro: wrong result."
        return pt

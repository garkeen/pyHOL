# logic/conv/function.py - Function update conversions

from kernel.type import TFun
from kernel import term
from kernel.term import Term, Const, Abs
from kernel.macro import Macro
from kernel.theory import register_macro
from logic.conv import Conv, rewr_conv, then_conv, arg_conv, argn_conv
from kernel.proofterm import ProofTerm, refl
from util.function import is_fun_upd


class fun_upd_eval_conv(Conv):
    """Evaluate the function (f)(a1 := b1, a2 := b2, ...) on an input."""

    def get_proof_term(self, t):
        from domains.nat import util_nat as nat
        if not t.is_comb():
            return refl(t)

        f, c = t.fun, t.arg
        if is_fun_upd(f):
            f1, a, b = f.args
            if a == c:
                return rewr_conv("fun_upd_same").get_proof_term(t)
            else:
                # Only evaluate when both indices are constants.
                # Non-constant indices (e.g. array access base+i) are
                # left for z3 to handle.
                try:
                    neq = nat.nat_const_ineq(c, a)
                    eq = rewr_conv("fun_upd_other", conds=[neq]).get_proof_term(t)
                    return eq.on_arg(self)
                except Exception:
                    return refl(t)
        elif f.is_abs():
            return ProofTerm.beta_conv(t)
        else:
            return refl(t)


class fun_upd_norm_one_conv(Conv):
    """Normalize a function update (f)(a1 := b1, ...)(an := bn) by moving
    the last update to the right position, combining if necessary.

    """
    def get_proof_term(self, t):
        from domains.nat import util_nat as nat
        pt = refl(t)
        if is_fun_upd(t) and is_fun_upd(t.args[0]):
            f, a, b = t.args
            f2, a2, b2 = f.args
            if a.dest_number() < a2.dest_number():
                neq = nat.nat_const_ineq(a, a2)
                return pt.on_rhs(rewr_conv("fun_upd_twist", conds=[neq]), argn_conv(0, self))
            elif a.dest_number() == a2.dest_number():
                return pt.on_rhs(rewr_conv("fun_upd_upd"))
            else:
                return pt
        else:
            return pt


class fun_upd_norm_conv(Conv):
    """Normalize a function update of the form (f)(a1 := b1, a2 := b2, ...).

    This sorts the updates according to the key (provided in the constructor),
    and combines updates on the same key.

    """
    def get_proof_term(self, t):
        pt = refl(t)
        if is_fun_upd(t):
            return pt.on_rhs(argn_conv(0, self), fun_upd_norm_one_conv())
        else:
            return pt

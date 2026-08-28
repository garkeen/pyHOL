# domains/nat/macro.py - Nat Macro classes

from kernel.type import TFun, BoolType
from syntax.numeral import NatType
from kernel import term
from kernel.term import Term, Const, Eq, Inst
from syntax.numeral import Binary, Nat
from syntax.logicops import Not
from kernel.thm import Thm
from kernel import theory
from kernel.theory import register_macro
from kernel.macro import Macro
from kernel.proofterm import ProofTerm, refl
from framework import auto
from framework.logic import apply_theorem
from framework.conv import arg_conv, binop_conv, rewr_conv
from domains.nat.conv import (
    Suc, plus, minus, times, zero, one,
    is_bit0, is_bit1,
    nat_eval, nat_eval_conv, nat_conv, rewr_of_nat_conv,
    norm_full, compare_atom, compare_monomial,
    Suc_conv, add_conv, mult_conv,
    swap_add_r, norm_add_atom_1, norm_add_1,
    swap_times_r, norm_mult_atom, norm_mult_monomial,
    to_coeff_form, from_coeff_form, combine_monomial,
    norm_add_monomial, norm_add_polynomial,
    norm_mult_poly_monomial, norm_mult_polynomial,
)


@register_macro('nat_eval')
class nat_eval_macro(Macro):
    """Simplify all arithmetic operations."""
    def __init__(self):
        self.level = 0  # No expand implemented
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "nat_eval_macro: no conditions expected"
        assert goal.is_equals(), "nat_eval_macro: goal must be an equality"
        assert nat_eval(goal.lhs) == nat_eval(goal.rhs), "nat_eval_macro: two sides are not equal"

        return Thm(goal)


# Auto registrations for nat_eval
auto.add_global_autos_norm(Suc, nat_eval_conv())
auto.add_global_autos_norm(plus, nat_eval_conv())
auto.add_global_autos_norm(minus, nat_eval_conv())
auto.add_global_autos_norm(times, nat_eval_conv())


@register_macro('nat_norm')
class nat_norm_macro(Macro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'nat_nat_power_def_1'

    def eval(self, goal, pts):
        # Simply produce the goal.
        assert len(pts) == 0, "nat_norm_macro"
        return Thm(goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "nat_norm_macro"
        if not (goal.is_equals() and goal.lhs.get_type() == NatType):
            return False

        t1, t2 = goal.args
        pt1 = norm_full().get_proof_term(t1)
        pt2 = norm_full().get_proof_term(t2)
        return pt1.prop.rhs == pt2.prop.rhs

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0, "nat_norm_macro"
        assert goal.is_equals(), "nat_norm_macro: goal is not an equality."

        t1, t2 = goal.args
        pt1 = norm_full().get_proof_term(t1)
        pt2 = norm_full().get_proof_term(t2)
        assert pt1.prop.rhs == pt2.prop.rhs, "nat_norm_macro: normalization is not equal."
        return pt1.transitive(pt2.symmetric())


def ineq_zero_proof_term(n):
    """Returns the inequality n ~= 0."""
    assert n != 0, "ineq_zero_proof_term: n = 0"
    if n == 1:
        return ProofTerm.theorem("one_nonzero")
    elif n % 2 == 0:
        return apply_theorem("bit0_nonzero", ineq_zero_proof_term(n // 2))
    else:
        return apply_theorem("bit1_nonzero", inst=Inst(m=Binary(n // 2)))

def ineq_one_proof_term(n):
    """Returns the inequality n ~= 1."""
    assert n != 1, "ineq_one_proof_term: n = 1"
    if n == 0:
        return apply_theorem("ineq_sym", ProofTerm.theorem("one_nonzero"))
    elif n % 2 == 0:
        return apply_theorem("bit0_neq_one", inst=Inst(m=Binary(n // 2)))
    else:
        return apply_theorem("bit1_neq_one", ineq_zero_proof_term(n // 2))

def ineq_proof_term(m, n):
    """Returns the inequality m ~= n."""
    assert m != n, "ineq_proof_term: m = n"
    if n == 0:
        return ineq_zero_proof_term(m)
    elif n == 1:
        return ineq_one_proof_term(m)
    elif m == 0:
        return apply_theorem("ineq_sym", ineq_zero_proof_term(n))
    elif m == 1:
        return apply_theorem("ineq_sym", ineq_one_proof_term(n))
    elif m % 2 == 0 and n % 2 == 0:
        return apply_theorem("bit0_neq", ineq_proof_term(m // 2, n // 2))
    elif m % 2 == 1 and n % 2 == 1:
        return apply_theorem("bit1_neq", ineq_proof_term(m // 2, n // 2))
    elif m % 2 == 0 and n % 2 == 1:
        return apply_theorem("bit0_bit1_neq", inst=Inst(m=Binary(m // 2), n=Binary(n // 2)))
    else:
        return apply_theorem("ineq_sym", ineq_proof_term(n, m))


@register_macro('nat_const_ineq')
class nat_const_ineq_macro(Macro):
    """Given m and n, with m ~= n, return the inequality theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def can_eval(self, goal):
        assert isinstance(goal, Term), "nat_const_ineq_macro"
        if not (goal.is_not() and goal.arg.is_equals()):
            return False

        m, n = goal.arg.args
        return m.is_number() and n.is_number() and m.dest_number() != n.dest_number()

    def eval(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_ineq_macro"

        # Simply produce the goal.
        return Thm(goal)

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_ineq_macro"

        m, n = goal.arg.args
        pt = ineq_proof_term(m.dest_number(), n.dest_number())
        return pt.on_prop(arg_conv(binop_conv(rewr_of_nat_conv(sym=True))))

def nat_const_ineq(a, b):
    return ProofTerm("nat_const_ineq", Not(Eq(a, b)), [])


@register_macro('nat_const_less_eq')
class nat_const_less_eq_macro(Macro):
    """Given m and n, with m <= n, return the less-equal theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def can_eval(self, goal):
        assert isinstance(goal, Term), "nat_const_less_eq_macro"
        if not goal.is_less_eq():
            return False

        m, n = goal.args
        return m.is_number() and n.is_number() and m.dest_number() <= n.dest_number()

    def eval(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_less_eq_macro"

        # Simply produce the goal.
        return Thm(goal)

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0 and self.can_eval(goal), "nat_const_less_eq_macro"

        m, n = goal.args
        assert m.dest_number() <= n.dest_number()
        p = Nat(n.dest_number() - m.dest_number())
        eq = refl(m + p).on_rhs(norm_full()).symmetric()
        goal2 = rewr_conv('less_eq_exist').eval(goal).prop.rhs
        ex_eq = apply_theorem('exI', eq, concl=goal2)
        return ex_eq.on_prop(rewr_conv('less_eq_exist', sym=True))

def nat_less_eq(t1, t2):
    return ProofTerm("nat_const_less_eq", t1 <= t2)

@register_macro('nat_const_less')
class nat_const_less_macro(Macro):
    """Given m and n, with m < n, return the less-than theorem."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'bit1_neq_one'

    def get_proof_term(self, goal, pts):
        assert isinstance(goal, Term)
        assert len(pts) == 0, "nat_const_less_macro"
        m, n = goal.args
        assert m.dest_number() < n.dest_number()
        less_eq_pt = nat_const_less_eq_macro().get_proof_term(m <= n, [])
        ineq_pt = nat_const_ineq_macro().get_proof_term(Not(Eq(m, n)), [])
        return apply_theorem("less_lesseqI", less_eq_pt, ineq_pt)

def nat_less(t1, t2):
    return ProofTerm("nat_const_less", t1 < t2)

# domains/integer/macro.py - Integer macros.
# Importing this module registers int_norm (polynomial normalization
# for integer equalities), mirroring nat_norm in domains/nat/macro.py.

from math import gcd

from kernel.term import Term
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro, get_theorem
from kernel.proofterm import ProofTerm, refl
from syntax.numeral import IntType, Int, greater, less
from syntax.logicops import Not
from framework import matcher
from framework.conv import rewr_conv, ConvException
from framework.logic import apply_theorem
from domains.integer.conv import int_norm_conv, int_eval, collect_int_polynomial_coeff, \
    norm_eq, simp_full, omega_simp_full_conv, omega_form_conv


@register_macro('int_norm')
class int_norm_macro(Macro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'int_mul_1_l'

    def can_eval(self, goal):
        assert isinstance(goal, Term), "int_norm_macro"
        if not (goal.is_equals() and goal.lhs.get_type() == IntType):
            return False

        t1, t2 = goal.args
        pt1 = int_norm_conv().get_proof_term(t1)
        pt2 = int_norm_conv().get_proof_term(t2)
        return pt1.prop.rhs == pt2.prop.rhs

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0, "int_norm_macro"
        assert goal.is_equals(), "int_norm_macro: goal is not an equality."

        t1, t2 = goal.args
        pt1 = int_norm_conv().get_proof_term(t1)
        pt2 = int_norm_conv().get_proof_term(t2)
        assert pt1.prop.rhs == pt2.prop.rhs, "int_norm_macro: normalization is not equal."
        return pt1.transitive(pt2.symmetric())


# ---------------------------------------------------------------------------
# Integer macros (moved from conv.py, step 1b of the rewrite plan:
# macro definitions belong in macro.py; conv.py holds only convs).
# The macros import their conv machinery from domains.integer.conv --
# macro may use conv (audit §1), never the reverse.
# ---------------------------------------------------------------------------


@register_macro('int_eval')
class int_eval_macro(Macro):
    """Simplify integer expression"""
    def __init__(self):
        self.level = 0 # no expand implement
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "int_eval_macro: no conditions expected"
        assert goal.is_equals(), "int_eval_macro: goal must be an equality"
        assert int_eval(goal.lhs) == int_eval(goal.rhs), "int_eval_macro: two sides are not equal"

        return Thm(goal)


def int_eq_proof(goal, prevs):
    """Prove 2 integer equations(inequations) are equal.

    Example: a = b + 3 <==> a - 3 = b.
    """
    assert goal.is_equals(), "int_eq_norm, %s is not equation" % goal

    # Get normal form on both sides.
    pt1 = refl(goal.lhs).on_rhs(norm_eq())
    pt2 = refl(goal.rhs).on_rhs(norm_eq())

    assert pt1.rhs == pt2.rhs
    return pt1.transitive(pt2.symmetric())


@register_macro('int_eq_macro')
class int_eq_macro(Macro):
    """Thin adapter over int_eq_proof."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, prevs):
        return int_eq_proof(goal, prevs)


def int_ineq_proof(goal):
    """
    Convert all kinds of inequalities to less equalities.
    Method:
    1) First move all terms to lhs, normalize lhs
    2) c * x + ⋯ < 0, no conversion;
    3) c * x + ⋯ ≤ 0 --> c * x + ⋯ < 1;
    3) c * x + ⋯ > 0 --> (-c) * x + ⋯ < 0;
    4) c * x + ⋯ ≥ 0 --> (-c) * x + ⋯ < 1;
    """
    assert isinstance(goal, Term), "%s should be a hol term" % str(goal)
    assert goal.is_less() or goal.is_less_eq() or goal.is_greater() or goal.is_greater_eq(),\
        "%s should be an inequality term" % str(goal)

    norm_ineq_pt = norm_eq().get_proof_term(goal)
    # find the first monomial
    first_monomial = norm_ineq_pt.rhs
    while not first_monomial.is_times() and not first_monomial.is_number():
        first_monomial = first_monomial.arg1

    coeff = first_monomial.arg1 if first_monomial.is_times() else first_monomial
    assert coeff.is_int()
    coeff_value = int_eval(coeff)
    # normalize
    if norm_ineq_pt.rhs.is_less():
        return norm_ineq_pt
    elif norm_ineq_pt.rhs.is_less_eq():
        return norm_ineq_pt.on_rhs(rewr_conv('int_lesseq_0'))
    else:
        if norm_ineq_pt.rhs.is_greater():
            pt_less = norm_ineq_pt.on_rhs(rewr_conv('int_greater_less'))
        elif norm_ineq_pt.rhs.is_greater_eq():
            pt_less = norm_ineq_pt.on_rhs(rewr_conv('int_greatereq_less'))
        pt_norm_lhs = refl(pt_less.rhs.arg1).on_rhs(simp_full())
        return pt_less.transitive(refl(pt_less.rhs.head).combination(pt_norm_lhs).combination(refl(pt_less.rhs.arg)))


@register_macro('int_ineq')
class int_ineq_macro(Macro):
    """Thin adapter over int_ineq_proof."""
    def get_proof_term(self, goal):
        return int_ineq_proof(goal)


def int_ineq_mul_const_proof(prevs, args):
    """
    Multiply a constant on both side of an inequality.

    prevs is a list contain two proof term:
    1) m ⋈ n
    2) c ⋈ 0

    return a proof term like: c * m ⋈ c * n
    """
    assert isinstance(prevs, ProofTerm) and prevs.prop.arg1.is_int() and prevs.prop.arg.is_zero(), "Unexpected %s" % str(prevs)
    assert isinstance(args, Term) and (args.is_less() or args.is_less_eq() or args.is_greater or args.is_greater_eq())
    th_names = ['int_pos_mul_less', 'int_neg_mul_less', 'int_pos_mul_less_eq', 'int_neg_mul_less_eq',
                'int_pos_mul_greater', 'int_neg_mul_greater', 'int_pos_mul_greater_eq', 'int_neg_mul_greater_eq']
    for th in th_names:
        try:
            th1 = get_theorem(th)
            inst = matcher.first_order_match(th1.prop.arg.lhs, args)
            pt_concl = apply_theorem(th, prevs, inst=inst)
            return pt_concl
        except:
            continue

    raise NotImplementedError


@register_macro('int_ineq_mul_const')
class int_ineq_mul_const_macro(Macro):
    """Thin adapter over int_ineq_mul_const_proof."""
    def get_proof_term(self, prevs, args):
        return int_ineq_mul_const_proof(prevs, args)


@register_macro('int_const_ineq')
class int_const_ineq_macro(Macro):
    """Get an pure integer inequality"""
    def __init__(self):
        self.level = 0 # no expand implement
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "int_const_ineq: no conditions expected"

        if goal.is_not():
            goal = goal.arg

        assert (goal.is_compares() or goal.is_equals()) and goal.arg1.is_constant() and goal.arg.is_constant()\
            and goal.arg1.get_type() == IntType, repr(goal)
        lhs, rhs = int_eval(goal.arg1), int_eval(goal.arg)
        if goal.is_less():
            if lhs < rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_less_eq():
            if lhs <= rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_greater():
            if lhs > rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_greater_eq():
            if lhs >= rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_equals():
            if lhs == rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        else:
            raise NotImplementedError


def int_multiple_ineq_equiv_proof(prevs):
    """
    Give two inequalities:
    1) c1 * m ⋈ c1 * n
    2) c2 * m ⋈ c2 * n
    prove their equaivalence.
    """
    p1, p2 = prevs
    lhs_triple = collect_int_polynomial_coeff(p1.arg1)
    rhs_triple = collect_int_polynomial_coeff(p2.arg1)
    lhs_singleton = [(p[1], p[2]) for p in lhs_triple]
    rhs_singleton = [(p[1], p[2]) for p in rhs_triple]
    if lhs_singleton != rhs_singleton or len(lhs_singleton) != len(rhs_singleton):
        raise NotImplementedError

    lhs_coeff = [p[0] for p in lhs_triple]
    rhs_coeff = [p[0] for p in rhs_triple]

    ratios = [p1/p2 for p1, p2 in zip(lhs_coeff, rhs_coeff)]
    if len(set(ratios)) != 1:
        raise NotImplementedError

    lhs_mul = int(rhs_coeff[0] / gcd(lhs_coeff[0], rhs_coeff[0]))
    rhs_mul = int(lhs_coeff[0] / gcd(lhs_coeff[0], rhs_coeff[0]))

    if lhs_mul > 0:
        pt_lhs_mul = ProofTerm('int_const_ineq', greater(IntType)(Int(lhs_mul), Int(0)))

    if lhs_mul < 0:
        pt_lhs_mul = ProofTerm('int_const_ineq', less(IntType)(Int(lhs_mul), Int(0)))

    if rhs_mul > 0:
        pt_rhs_mul = ProofTerm('int_const_ineq', greater(IntType)(Int(rhs_mul), Int(0)))

    if rhs_mul < 0:
        pt_rhs_mul = ProofTerm('int_const_ineq', less(IntType)(Int(rhs_mul), Int(0)))

    pt_lhs_mul = int_ineq_mul_const_proof(pt_lhs_mul, p1)
    pt_rhs_mul = int_ineq_mul_const_proof(pt_rhs_mul, p2)

    # normalize both sides
    pt_lhs_mul_norm = pt_lhs_mul.transitive(norm_eq().get_proof_term(pt_lhs_mul.prop.rhs))
    pt_rhs_mul_norm = pt_rhs_mul.transitive(norm_eq().get_proof_term(pt_rhs_mul.prop.rhs))

    return pt_lhs_mul_norm.transitive(pt_rhs_mul_norm.symmetric())


@register_macro('int_multiple_ineq_equiv')
class int_multiple_ineq_equiv(Macro):
    """Thin adapter over int_multiple_ineq_equiv_proof."""
    def get_proof_term(self, prevs):
        return int_multiple_ineq_equiv_proof(prevs)


def omega_norm_int_ineq_proof(goal):
    """
    Convert all kinds of inequalities to less equalities.
    Method:
    1) First move all terms to lhs, normalize lhs
    2) c * x + ⋯ < 0, (-c) * x + ⋯ ≥ 1;
    3) c * x + ⋯ ≤ 0 --> (-c) * x + ⋯ ≥ 0;
    3) c * x + ⋯ > 0 --> c * x + ⋯ ≥ 1;
    4) c * x + ⋯ ≥ 0 --> no conversion;
    """
    assert isinstance(goal, Term), "%s should be a hol term" % str(goal)
    assert goal.is_less() or goal.is_less_eq() or goal.is_greater() or goal.is_greater_eq(),\
        "%s should be an inequality term" % str(goal)

    norm_ineq_pt = norm_eq().get_proof_term(goal)
    # find the first monomial
    first_monomial = norm_ineq_pt.rhs
    while not first_monomial.is_times() and not first_monomial.is_number():
        first_monomial = first_monomial.arg1

    coeff = first_monomial.arg1 if first_monomial.is_times() else first_monomial
    assert coeff.is_int()
    coeff_value = int_eval(coeff)
    # normalize
    if norm_ineq_pt.rhs.is_greater_eq():
        return norm_ineq_pt
    elif norm_ineq_pt.rhs.is_greater():
        return norm_ineq_pt.on_rhs(rewr_conv('int_great_to_geq'))
    else:
        if norm_ineq_pt.rhs.is_less():
            pt_great = norm_ineq_pt.on_rhs(rewr_conv('int_less_to_geq'))
        elif norm_ineq_pt.rhs.is_less_eq():
            pt_great = norm_ineq_pt.on_rhs(rewr_conv('int_leq_to_geq'))
        pt_norm_lhs = refl(pt_great.rhs.arg1).on_rhs(omega_simp_full_conv())
        return pt_great.transitive(refl(pt_great.rhs.head).combination(pt_norm_lhs).combination(refl(pt_great.rhs.arg)))


@register_macro('omega_norm_int_ineq')
class omega_norm_int_ineq_macro(Macro):
    """Thin adapter over omega_norm_int_ineq_proof."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal):
        return omega_norm_int_ineq_proof(goal)


def int_eq_comparison_proof(goal):
    """
    Prove two comparisons' equivalence.
    """
    assert goal.is_equals() and goal.lhs.is_compares() and goal.rhs.is_compares()

    pt1 = refl(goal.lhs).on_rhs(omega_form_conv())
    pt2 = refl(goal.rhs).on_rhs(omega_form_conv())

    if pt1.rhs != pt2.rhs:
        raise ConvException(str(goal))
    return pt1.transitive(pt2.symmetric())


@register_macro('int_eq_comparison')
class int_eq_comparison_macro(Macro):
    """Thin adapter over int_eq_comparison_proof."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal):
        return int_eq_comparison_proof(goal)

# domains/real/macro.py - Real macros.
# Macro definitions moved here from conv.py (rewrite step 1,
# ARCHITECTURE_AUDIT.md §8): macro.py defines, conv.py only converts.
# Importing this module registers the real macros.

import functools
import typing

from kernel.term import Term, Var, Eq
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import refl, ProofTerm
from syntax.numeral import RealType, Real
from syntax.logicops import true, false, Not, Exists
from framework import matcher
from framework import logic
from framework import auto
from framework.conv import rewr_conv, arg1_conv, arg_conv, top_conv, ConvException
from domains.real.conv import (
    real_eval,
    convert_to_poly,
    real_norm_comparison,
    norm_real_ineq_conv,
    replace_conv,
    greater_eq, less_eq, greater, less,
)


@register_macro('real_eval')
class real_eval_macro(Macro):
    """Simplify all arithmetic operations."""
    def __init__(self):
        self.level = 0  # No expand implemented
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "real_eval_macro: no conditions expected"
        assert goal.is_equals(), "real_eval_macro: goal must be an equality"
        assert real_eval(goal.lhs) == real_eval(goal.rhs), "real_eval_macro: two sides are not equal"

        return Thm(goal)


@register_macro('real_norm')
class real_norm_macro(Macro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 0  # proof term not implemented
        self.sig = Term
        self.limit = 'real_neg_0'

    def eval(self, goal, pts):
        assert len(pts) == 0, "real_norm_macro"
        assert self.can_eval(goal), "real_norm_macro"

        return Thm(goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "real_norm_macro"
        if not (goal.is_equals() and goal.lhs.is_real()):
            return False

        t1, t2 = goal.args
        return convert_to_poly(t1) == convert_to_poly(t2)

    def get_proof_term(self, goal, pts):
        raise NotImplementedError


@register_macro('real_const_eq')
class RealEqMacro(Macro):
    """Give an real constant (in)equation, prove it (in)correctness."""
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs=None):
        if len(goal.get_vars()) != 0:
            raise ConvException
        try:
            if goal.is_equals():
                if real_eval(goal.lhs) == real_eval(goal.rhs):
                    return Thm(Eq(goal, true))
                else:
                    return Thm(Eq(goal, false))
            else: # inequations
                lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
                if goal.is_less():
                    return Thm(Eq(goal, true)) if lhs < rhs else Thm(Eq(goal, false))
                elif goal.is_less_eq():
                    return Thm(Eq(goal, true)) if lhs <= rhs else Thm(Eq(goal, false))
                elif goal.is_greater():
                    return Thm(Eq(goal, true)) if lhs > rhs else Thm(Eq(goal, false))
                elif goal.is_greater_eq():
                    return Thm(Eq(goal, true)) if lhs >= rhs else Thm(Eq(goal, false))
                else:
                    raise NotImplementedError
        except:
            raise ConvException


@register_macro('real_compare')
class RealCompareMacro(Macro):
    """
    Compare two real numbers.
    """
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs=[]):
        assert goal.is_compares(), "real_compare_macro: Should be an inequality term"
        lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
        if goal.is_less():
            assert lhs < rhs, "%f !< %f" % (lhs, rhs)
        elif goal.is_less_eq():
            assert lhs <= rhs, "%f !<= %f" % (lhs, rhs)
        elif goal.is_greater():
            assert lhs > rhs, "%f !> %f" % (lhs, rhs)
        elif goal.is_greater_eq():
            assert lhs >= rhs, "%f !>= %f" % (lhs, rhs)

        return Thm(goal)


@register_macro('real_const_ineq')
class real_const_ineq_macro(Macro):
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
            and goal.arg1.get_type() == RealType, repr(goal)
        lhs, rhs = real_eval(goal.arg1), real_eval(goal.arg)
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


@register_macro("real_eq_comparison")
class RealCompEq(Macro):
    """Given two real comparisons, prove their equality."""
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, prevs=[]):
        assert goal.is_equals() and goal.lhs.is_compares() and goal.rhs.is_compares()

        pt_refl1, pt_refl2 = refl(goal.lhs).on_rhs(real_norm_comparison()), \
                refl(goal.rhs).on_rhs(real_norm_comparison())

        assert pt_refl1.rhs == pt_refl2.rhs

        return pt_refl1.transitive(pt_refl2.symmetric())


@register_macro('non_strict_simplex')
class relax_strict_simplex_macro(Macro):
    """
    Given a set of strict inequalities,
        x_1 > 0,
        x_2 > 0,
        ...
        x_n > 0,

    return a proof term: x_1 > b_1, ... , x_n > b_n ⊢ ∃δ. δ > 0 ∧ x_1 >= δ ∧ ... ∧ x_n >= δ
    """
    def __init__(self):
        self.level = 1
        self.sig = typing.List[Term]
        self.limit = None

    def handle_geq_stage1(self, pts):
        if not pts:
            return None, None, None

        # ⊢ min(min(...(min(x_1, x_2), x_3)...), x_n-1), x_n) > 0
        min_pos_pt = functools.reduce(lambda pt1, pt2: logic.apply_theorem("min_greater_0", pt1, pt2),
                        pts[1:], pts[0])

         # ⊢ 0 < 2
        two_pos_pt = ProofTerm("real_compare", Real(0) < Real(2))

        # ⊢ min(...) / 2 > 0
        min_divides_two_pos = logic.apply_theorem("real_lt_div",
                min_pos_pt.on_prop(rewr_conv("real_ge_to_le")), two_pos_pt).on_prop(rewr_conv("real_ge_to_le", sym=True))

        # ⊢ 2 ≥ 1
        two_larger_one = ProofTerm("real_compare", Real(2) >= Real(1))

        # ⊢ min(...) ≥ min(...) / 2
        larger_half_pt = logic.apply_theorem("real_divides_larger_1", two_larger_one, min_pos_pt)

        # ⊢ min(...) / 2 = δ_1
        delta_1 = Var("δ_1", RealType)
        pt_delta1_eq = ProofTerm.assume(Eq(larger_half_pt.prop.arg, delta_1))

        # ⊢ min(...) ≥ δ_1
        larger_half_pt_delta = larger_half_pt.on_prop(top_conv(replace_conv(pt_delta1_eq)))

        # ⊢ δ_1 > 0
        delta_1_pos = min_divides_two_pos.on_prop(arg1_conv(replace_conv(pt_delta1_eq)))

        return larger_half_pt_delta, delta_1_pos, pt_delta1_eq

    def handle_geq_stage2(self, pt_lower_bound, pts, delta):
        # get ⊢ x_i ≥ δ, i = 1...n
        geq_pt = []
        pt_a = pt_lower_bound
        d = set()

        for i in range(len(pts)):
            if i != len(pts) - 1:
                pt = logic.apply_theorem("both_geq_min", pt_a)
                pt_1, pt_2 = logic.apply_theorem("conjD1", pt), logic.apply_theorem("conjD2", pt)
            else:
                pt_2 = pt_a

            ineq = pt_2.prop

            if ineq.arg1.is_minus() and ineq.arg1.arg.is_number():
                # move all constant term from left to right in pt_2's prop
                num = ineq.arg1.arg
                expr = greater_eq(ineq.arg1.arg1, num+delta)

            else:
                expr = greater_eq(ineq.arg1, Real(0)+delta)

            pt_eq_comp = ProofTerm("real_eq_comparison", Eq(ineq, expr))
            geq_pt.insert(0, pt_2.on_prop(replace_conv(pt_eq_comp)))

            if i != len(pts) - 1:
                pt_a = pt_1

        return geq_pt

    def handle_leq_stage1(self, pts):
        if not pts:
            return None, None, None
        # ⊢ max(max(...(max(x_1, x_2), x_3)...), x_n-1), x_n) < 0
        max_pos_pt = functools.reduce(lambda pt1, pt2: logic.apply_theorem("max_less_0", pt1, pt2),
                        pts[1:], pts[0])

        # ⊢ 0 < 2
        two_pos_pt = ProofTerm("real_compare", Real(2) > Real(0))

        # ⊢ max(...) / 2 < 0
        max_divides_two_pos = logic.apply_theorem("real_neg_div_pos",
                max_pos_pt, two_pos_pt)

        # ⊢ 2 ≥ 1
        two_larger_one = ProofTerm("real_compare", Real(2) >= Real(1))

        # ⊢ max(...) ≤ max(...) / 2
        less_half_pt = logic.apply_theorem("real_neg_divides_larger_1", two_larger_one, max_pos_pt)

        # ⊢ max(...) / 2 = -δ
        delta_2 = Var("δ_2", RealType)
        pt_delta_eq = ProofTerm.assume(Eq(less_half_pt.prop.arg, -delta_2))

        # ⊢ δ > 0
        delta_pos_pt = max_divides_two_pos.on_prop(rewr_conv("real_le_gt"), top_conv(replace_conv(pt_delta_eq)),
                                                   auto.norm_conv())

        # max(...) ≤ -δ
        less_half_pt_delta = less_half_pt.on_prop(arg_conv(replace_conv(pt_delta_eq)))

        return less_half_pt_delta, delta_pos_pt, pt_delta_eq

    def handle_leq_stage2(self, pt_upper_bound, pts, delta):
        # get ⊢ x_i ≤ -δ, for i = 1...n
        leq_pt = []
        pt_b = pt_upper_bound

        for i in range(len(pts)):
            if i != len(pts) - 1:
                pt = logic.apply_theorem("both_leq_max", pt_b)
                pt_1, pt_2 = logic.apply_theorem("conjD1", pt), logic.apply_theorem("conjD2", pt)
            else:
                pt_2 = pt_b

            ineq = pt_2.prop

            if ineq.arg1.is_minus() and ineq.arg1.arg.is_number():
                num = ineq.arg1.arg
                expr = less_eq(ineq.arg1.arg1, num-delta)

            else:
                expr = less_eq(ineq.arg1, Real(0)-delta)

            pt_eq_comp = ProofTerm("real_eq_comparison", Eq(ineq, expr))
            leq_pt.insert(0, pt_2.on_prop(replace_conv(pt_eq_comp)))
            if i != len(pts) - 1:
                pt_b = pt_1

        return leq_pt

    def get_proof_term(self, args, prevs=None):
        """
        Let x_i denotes greater comparison, x__i denotes less comparison,
        for the greater comparison, find the smallest number x_min = min(x_1, ..., x_n), since x_min is positive,
        x_min/2 > 0 ==> x_min >= x_min / 2 ==> x_1, ..., x_n >= x_min / 2 ==> ∃δ. δ > 0 ∧ x_1 >= δ ∧ ... ∧ x_n >= δ.
        for the less comparison, find the largest number x_max = max(x__1, ..., x__n), since x_max is negative, x_max <
        x_max/2 ==> x__1, ..., x__n <= x_max/2;
        let δ = min(x_min/2, -x_max/2), then all x_i >= δ as well as all x__i <= -δ.
        """

        def need_convert(tm):
            return False if real_eval(tm.arg) != 0 else True

        original_ineq_pts = [ProofTerm.assume(ineq) for ineq in args]

        # record the ineq which rhs is not 0
        need_convert_pt = {arg for arg in args if need_convert(arg)}

        # record the args order
        order_args = {args[i].arg1: i for i in range(len(args))}

        # convert all ineqs to x_i > 0 or x_i < 0
        normal_ineq_pts = [pt.on_prop(norm_real_ineq_conv()) if pt.prop.arg != Real(0) else pt for pt in original_ineq_pts]

        # dividing less comparison and greater comparison
        greater_ineq_pts = [pt for pt in normal_ineq_pts if pt.prop.is_greater()]
        less_ineq_pts = [pt for pt in normal_ineq_pts if pt.prop.is_less()]

        # stage 1: get the max(min) pos bound
        # ⊢ min(...) ≥ δ_1, δ_1 > 0
        # ⊢ max(...) ≤ δ_2, δ_2 < 0
        pt_lower_bound, lower_bound_pos_pt, pt_assert_delta1 = self.handle_geq_stage1(greater_ineq_pts)
        pt_upper_bound, upper_bound_neg_pt, pt_assert_delta2 = self.handle_leq_stage1(less_ineq_pts)

        delta_1 = Var("δ_1", RealType)
        delta_2 = Var("δ_2", RealType)

        # generate the relaxed inequations
        if pt_lower_bound is None: # all comparisons are ≤
            pts = self.handle_leq_stage2(pt_upper_bound, less_ineq_pts, delta_2)
            bound_pt = upper_bound_neg_pt
            delta = delta_2
            pt_asserts = [pt_assert_delta2]
        elif pt_upper_bound is None: # all comparisons are ≥
            pts = self.handle_geq_stage2(pt_lower_bound, greater_ineq_pts, delta_1)
            bound_pt = lower_bound_pos_pt
            delta = delta_1
            pt_asserts = [pt_assert_delta1]
        else: # have both ≥ and ≤
            # ⊢ δ_1 ≥ min(δ_1, δ_2)
            pt_min_lower_bound = logic.apply_theorem("real_greater_min", inst=matcher.Inst(x=delta_1, y=delta_2))
            # ⊢ -δ_2 ≤ max(-δ_2, -δ_1)
            pt_max_upper_bound = logic.apply_theorem("real_less_max", inst=matcher.Inst(x=-delta_2, y=-delta_1))
            # ⊢ max(-δ_2, -δ_1) = -min(δ_1, δ_2)
            pt_max_min = logic.apply_theorem("max_min", inst=matcher.Inst(x=delta_1, y=delta_2))
            # ⊢ min(...) ≥ min(δ_1, δ_2)
            pt_new_lower_bound = logic.apply_theorem("real_geq_trans", pt_lower_bound, pt_min_lower_bound)
            # ⊢ -δ_2 ≤ -min(δ_1, δ_2)
            pt_max_upper_bound_1 = pt_max_upper_bound.on_prop(arg_conv(replace_conv(pt_max_min)))
            # ⊢ max(...) ≤ -min(δ_1, δ_2)
            pt_new_upper_bound = logic.apply_theorem("real_le_trans", pt_upper_bound, pt_max_upper_bound_1)
            # ⊢ min(δ_1, δ_2) > 0
            pt_new_lower_bound_pos = logic.apply_theorem("min_pos", lower_bound_pos_pt, upper_bound_neg_pt)
            # ⊢ min(δ_1, δ_2) = δ
            delta = Var("δ", RealType)
            pt_delta_eq = ProofTerm.assume(Eq(pt_min_lower_bound.prop.arg, delta))
            pt_asserts = [pt_delta_eq, pt_assert_delta1, pt_assert_delta2]
            # ⊢ min(...) ≥ δ
            pt_new_lower_bound_delta = pt_new_lower_bound.on_prop(arg_conv(replace_conv(pt_delta_eq)))
            # ⊢ max(...) ≤ -δ
            pt_new_upper_bound_delta = pt_new_upper_bound.on_prop(top_conv(replace_conv(pt_delta_eq)))
            # use new bound
            pts_leq = self.handle_leq_stage2(pt_new_upper_bound_delta, less_ineq_pts, delta)
            pts_geq = self.handle_geq_stage2(pt_new_lower_bound_delta, greater_ineq_pts, delta)
            pts = pts_leq + pts_geq
            bound_pt = pt_new_lower_bound_pos.on_prop(arg1_conv(replace_conv(pt_delta_eq)))

        # sort_pts = sorted(pts, key=lambda pt: order_args[pt.prop.arg1])

        pt_conj = functools.reduce(lambda x, y: logic.apply_theorem("conjI", y, x), reversed([bound_pt] + pts))

        # get ⊢∃δ. δ > 0 ∧ x_1 >= δ ∧ ... ∧ x_n >= δ
        th = ProofTerm.theorem("exI")
        inst = matcher.first_order_match(th.prop.arg, Exists(delta, pt_conj.prop))
        pt_conj_exists = logic.apply_theorem("exI", pt_conj, inst=inst)
        pt_final = pt_conj_exists
        for pt_subst in pt_asserts:
            lhs, rhs = pt_subst.prop.args
            if not rhs.is_uminus():
                pt_final = pt_final.implies_intr(pt_subst.prop).forall_intr(rhs).\
                            forall_elim(lhs).implies_elim(ProofTerm.reflexive(lhs))
            else:
                pt_final = pt_final.implies_intr(pt_subst.prop).forall_intr(rhs.arg).\
                    forall_elim(-lhs).on_prop(top_conv(rewr_conv("real_neg_neg"))).implies_elim(ProofTerm.reflexive(lhs))
        return pt_final

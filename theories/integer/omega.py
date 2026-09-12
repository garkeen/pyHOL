"""Omega Test proof assembly and registration (integer domain).

The omega decision procedure's pure algorithm core (factoids, the
simplex-style solver, derivation trees) lives in solvers/omega.py.
This module is the content half: it turns a derivation into a kernel
ProofTerm, exposes the omega auto entry, and registers it for integer
comparisons.  It lives in the integer domain because it assembles
proofs from integer convs (audit 3 dependency law: solvers must not
import theories).

Reference: implementation of Omega in HOL4
https://github.com/HOL-Theorem-Prover/HOL/blob/develop/src/integer/OmegaMLShadow.sml
"""

import collections
import functools
from math import gcd, floor

from kernel import proofterm
from kernel import term_ord
from syntax import numeral
from syntax.logicops import is_not
from core import basic, logic, conv
from core import auto as _auto_omega
from theories.integer import conv as integer
from solvers.omega import (ASM, Contr, DirectContr, GCDCheck, RealCombine,
                           factoid_to_term, is_integer_ineq, solve_matrix,
                           term_to_factoid)

basic.load_theory('int')


class OmegaHOL:
    """
    Handling omega test decision procedure in higher-order logic.
    """
    def __init__(self, ineqs):
        """
        Must guarantee the input inequalities are all integer terms.
        """
        assert isinstance(ineqs, collections.abc.Iterable) and all(is_integer_ineq(t) for t in ineqs)
        self.ineqs = ineqs
        
        # store all the normal form inequlities: 0 <= Σ ai * xi + c
        self.norm_pts = dict()
        self.norm_ineqs = list()
        occr_vars = set()
        for i in range(len(self.ineqs)):
            pt = proofterm.ProofTerm.assume(self.ineqs[i]).on_prop(integer.omega_form_conv())
            self.norm_pts[self.ineqs[i]] = pt
            self.norm_ineqs.append(pt.prop)
            # occr_vars |= set(self.ineqs[i].get_vars())
            norm_ineq = pt.prop
            occr_vars |= set([t.arg if t.is_times() else t for t in integer.strip_plus(norm_ineq.arg)])
        
        # store ordered vars
        self.vars = term_ord.sorted_terms(occr_vars)

        # convert inequalities to factoids
        self.factoids = [term_to_factoid(self.vars, t) for t in self.norm_ineqs]

        # mapping from factoids to HOL terms
        self.fact_hol = {f: factoid_to_term(self.vars, f) for f in self.factoids}

    def real_combine_pt(self, pt1, pt2, c1, c2):
        """
        pt1, pt2 are all proof terms which prop is a normal inequality,
        v is the variable index which will be elimated.
        c1, c2 are the coefficient pt1, pt2's prop need to multiply
        """
        def get_const_comp_pt(c):
            """
            c is a number, return a pt: c ⋈ 0
            """
            if c > 0:
                return proofterm.eval_macro('int_const_ineq', numeral.greater(numeral.IntType)(numeral.Int(c), numeral.Int(0)))
            else:
                return proofterm.eval_macro('int_const_ineq', numeral.less(numeral.IntType)(numeral.Int(c), numeral.Int(0)))
        
        def ineq_mul_const(c, pt):
            assert c != 0
            pt_c = get_const_comp_pt(c)
            if c > 0:
                return logic.apply_theorem('int_geq_zero_mul_pos', pt_c, pt)
            else:
                return logic.apply_theorem('int_geq_zero_mul_neg', pt_c, pt)
        
        pt1_mul_c1, pt2_mul_c2 = ineq_mul_const(c1, pt1), ineq_mul_const(c2, pt2)
        pt_final = logic.apply_theorem('int_pos_plus', pt1_mul_c1, pt2_mul_c2).on_prop(conv.arg_conv(integer.omega_simp_full_conv()))

        if pt_final.prop.arg.is_number(): # ⊢ 0 <= -3
            pt_less_zero = proofterm.eval_macro('int_const_ineq', numeral.less(numeral.IntType)(pt_final.prop.arg, numeral.Int(0)))
            return logic.apply_theorem('int_zero_less_eq_neg', pt_less_zero, pt_final)
        else:
            return pt_final

    def gcd_pt(self, vars, pt):
        fact = term_to_factoid(vars, pt.prop)
        g = functools.reduce(gcd, fact[:-1])
        assert g > 1
        pt1 = proofterm.eval_macro('int_const_ineq', numeral.Int(g) > numeral.Int(0))
        pt2 = pt
        elim_gcd_fact = [floor(i / g) for i in fact]
        if int(fact[-1] / g) != fact[-1] / g:    
            elim_gcd_no_constant = sum([c * v for c, v in zip(elim_gcd_fact[1:-1], vars[1:])], elim_gcd_fact[0] * vars[0])
            original_no_constant = sum([c * v for c, v in zip(fact[1:-1], vars[1:])], fact[0] * vars[0])
            
            elim_gcd_no_constant = integer.int_norm_conv().get_proof_term(elim_gcd_no_constant).rhs
            original_no_constant = integer.int_norm_conv().get_proof_term(original_no_constant).rhs

            pt3 = integer.int_norm_conv().get_proof_term(g * elim_gcd_no_constant).transitive(
                        integer.int_norm_conv().get_proof_term(original_no_constant).symmetric())
            n = floor(-fact[-1] / g)
            pt4 = proofterm.eval_macro('int_const_ineq', numeral.Int(g) * numeral.Int(n) + fact[-1] < 0)
            pt5 = proofterm.eval_macro('int_const_ineq', numeral.Int(g) * (numeral.Int(n) + numeral.Int(1)) + fact[-1] > 0)
            pt6 = integer.int_eval_conv().get_proof_term(-(numeral.Int(n) + numeral.Int(1)))
            return logic.apply_theorem('int_gcd', pt1, pt2, pt3, pt4, pt5).on_prop(
                conv.top_sweep_conv(conv.rewr_conv(pt6)),
                conv.arg_conv(integer.omega_simp_full_conv()))
        else:
            elim_gcd_term = factoid_to_term(vars, elim_gcd_fact)
            pt3 = integer.omega_simp_full_conv().get_proof_term(pt.prop.arg).transitive(\
                    integer.omega_simp_full_conv().get_proof_term(numeral.Int(g) * elim_gcd_term.arg).symmetric())
            return logic.apply_theorem('int_gcd_1', pt1, pt2, pt3)


    def direct_contr_pt(self, lower, upper):
        """When lower and upper's comparisons don't contain constant, we need to treat them carefully.
        """
        def norm_pt(pt):
            """If comparison in pt's prop does not contain constant, add a zero on the tail."""
            tm = factoid_to_term(self.vars, term_to_factoid(self.vars, pt.prop))
            pt1 = integer.omega_form_conv().get_proof_term(tm).symmetric()
            return pt.on_prop(conv.top_sweep_conv(conv.rewr_conv(pt1)))
       
        if lower.prop.arg.is_times():
            lower = norm_pt(lower)
        if upper.prop.arg.is_times():
            upper = norm_pt(upper)
        pos, neg = lower.prop.arg.arg1, upper.prop.arg.arg1
        pt_eq = integer.omega_simp_full_conv().get_proof_term(neg).\
            transitive(integer.omega_simp_full_conv().get_proof_term(numeral.Int(-1) * pos).symmetric())
        pt1 = lower
        pt2 = upper.on_prop(conv.top_sweep_conv(conv.rewr_conv(pt_eq)))
        lower_bound, upper_bound = -numeral.Int(integer.int_eval(lower.prop.arg.arg)), numeral.Int(integer.int_eval(upper.prop.arg.arg))
        pt3 = proofterm.eval_macro('int_const_ineq', numeral.greater(numeral.IntType)(lower_bound, upper_bound))
        return logic.apply_theorem('int_comp_contr', pt1, pt2, pt3)

    def handle_unsat_result(self, res):
        if isinstance(res, Contr):
            return self.handle_unsat_result(res.deriv)
        
        elif isinstance(res, ASM):
            pt = proofterm.ProofTerm.assume(self.fact_hol[res.t])
            if res.t.is_false_factoid():
                # A trivially false factoid 0 <= c (c < 0) is itself the
                # contradiction (constant-only system): close it to false
                # with the constant comparison, the same tail
                # real_combine_pt uses for a numeric result.
                pt_less_zero = proofterm.eval_macro(
                    'int_const_ineq',
                    numeral.less(numeral.IntType)(pt.prop.arg, numeral.Int(0)))
                return logic.apply_theorem('int_zero_less_eq_neg', pt_less_zero, pt)
            return pt
        
        elif isinstance(res, RealCombine):
            i, l1, l2 = res.i, self.handle_unsat_result(res.deriv1), self.handle_unsat_result(res.deriv2)
            c1, c2 = term_to_factoid(self.vars, l1.prop)[i], term_to_factoid(self.vars, l2.prop)[i]
            g = gcd(c1, c2)
            return self.real_combine_pt(l1, l2, int(c2/g), int(c1/g))
        
        elif isinstance(res, GCDCheck):
            return self.gcd_pt(self.vars, self.handle_unsat_result(res.deriv))
        
        elif isinstance(res, DirectContr):
            d1, d2 = self.handle_unsat_result(res.deriv1), self.handle_unsat_result(res.deriv2)
            return self.direct_contr_pt(d1, d2)

    def solve(self):
        res, value = solve_matrix(self.factoids)
        if res == "SAT":
            return value
        elif res == "UNSAT":
            pt_unsat = self.handle_unsat_result(value)
            # for the reason that the comparisons in hypothesis may have term like:
            # 0 <= Σ ai * xi + 0, but we don't want to keep the zero, so we need to
            # postprocess to normalize each comparisons again.
            hyps = pt_unsat.hyps
            pt_norm = pt_unsat
            for h in hyps:
                pt_norm = pt_norm.implies_intr(h)
            pt_norm = pt_norm.on_prop(conv.top_conv(integer.omega_form_conv()))
            premises, _ = pt_norm.prop.strip_implies()
            for p in premises:
                pt_norm = pt_norm.implies_elim(proofterm.ProofTerm.assume(p))
            return pt_norm


_FLIP_THEOREMS = {
    'less': 'int_not_less',
    'less_eq': 'int_not_less_eq',
    'greater': 'int_not_greater',
    'greater_eq': 'int_not_greater_eq',
}


def _flip_negated(pt):
    """Turn ~(a R b) into the positive comparison. Passes through
    positive comparisons unchanged. Raises TacticException otherwise."""
    from core.conv import rewr_conv
    p = pt.prop
    if is_integer_ineq(p):
        return pt
    if is_not(p) and is_integer_ineq(p.arg):
        ineq = p.arg
        if ineq.is_less():
            flip = _FLIP_THEOREMS['less']
        elif ineq.is_less_eq():
            flip = _FLIP_THEOREMS['less_eq']
        elif ineq.is_greater():
            flip = _FLIP_THEOREMS['greater']
        else:
            flip = _FLIP_THEOREMS['greater_eq']
        return pt.on_prop(rewr_conv(flip))
    raise proofterm.TacticException('omega: not an integer comparison: %s' % p)


def omega_solve(goal, pts):
    """Solve an integer-comparison goal by refutation with OmegaHOL.

    Hypotheses and the (negated) goal must be integer comparisons or
    their negations. Raises TacticException when out of scope or when
    omega reports satisfiable.
    """
    from syntax.logicops import Not

    if pts is None:
        pts = []

    try:
        pos_pts = [_flip_negated(pt) for pt in pts]
        if is_not(goal) and is_integer_ineq(goal.arg):
            neg_goal, neg_orig = goal.arg, goal
        elif is_integer_ineq(goal):
            neg_goal, neg_orig = _flip_negated(
                proofterm.ProofTerm.assume(Not(goal))).prop, Not(goal)
        else:
            raise proofterm.TacticException('omega: goal out of scope')
    except proofterm.TacticException:
        raise
    except Exception as e:
        raise proofterm.TacticException('omega: preprocessing failed: %s' % e)

    try:
        hol = OmegaHOL([pt.prop for pt in pos_pts] + [neg_goal])
        pt_false = hol.solve()
    except Exception as e:
        raise proofterm.TacticException('omega: %s' % e)
    if not isinstance(pt_false, proofterm.ProofTerm):
        raise proofterm.TacticException('omega: satisfiable')

    norm_pts = [hol.norm_pts[pt.prop] for pt in pos_pts]
    norm_neg = hol.norm_pts[neg_goal]
    # Full bridge from the original negated goal to its normal form:
    # when goal is itself a negation, neg_goal is already positive and
    # norm_neg starts from it; otherwise flip neg_orig to neg_goal first.
    if is_not(goal) and is_integer_ineq(goal.arg):
        neg_bridge = norm_neg
    else:
        flip_bridge = _flip_negated(proofterm.ProofTerm.assume(neg_orig))
        neg_bridge = norm_neg.implies_intr(neg_goal).implies_elim(flip_bridge)

    chain = pt_false
    for npt in [norm_neg] + list(reversed(norm_pts)):
        chain = chain.implies_intr(npt.prop)
    for npt in norm_pts:
        chain = chain.implies_elim(npt)
    chain = chain.implies_elim(neg_bridge)
    if is_not(goal) and is_integer_ineq(goal.arg):
        return logic.apply_theorem(
            'negI', chain.implies_intr(goal.arg), concl=goal)
    branch_neg = logic.apply_theorem(
        'falseE', chain, concl=goal).implies_intr(neg_orig)
    branch_pos = proofterm.ProofTerm.assume(goal).implies_intr(goal)
    return logic.apply_theorem(
        'classical_cases', branch_pos, branch_neg, concl=goal)


# Register the omega decision procedure for integer comparisons.
from core import auto as _auto_omega
_auto_omega.add_global_autos(numeral.less_eq(numeral.IntType), omega_solve)
_auto_omega.add_global_autos(numeral.less(numeral.IntType), omega_solve)
_auto_omega.add_global_autos(numeral.greater_eq(numeral.IntType), omega_solve)
_auto_omega.add_global_autos(numeral.greater(numeral.IntType), omega_solve)
_auto_omega.add_global_autos_neg(numeral.less_eq(numeral.IntType), omega_solve)
_auto_omega.add_global_autos_neg(numeral.less(numeral.IntType), omega_solve)
_auto_omega.add_global_autos_neg(numeral.greater_eq(numeral.IntType), omega_solve)
_auto_omega.add_global_autos_neg(numeral.greater(numeral.IntType), omega_solve)
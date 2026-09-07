# domains/logic/logic.py - Domain-dependent logic utilities
# These functions hardcode logic.pyhol theorem names

from typing import List, Tuple

from kernel.type import TVar, TFun, TyInst, BoolType
from kernel import term
from kernel.term import Term, SVar, Var, Const, Abs, Inst, Implies, Lambda, Eq
from syntax.logicops import Not, And, Or, true, false
from kernel.thm import Thm, InvalidDerivationException
from kernel import term_ord
from kernel import theory
from kernel.proofterm import ProofTerm, refl
from core.conv import Conv, then_conv, all_conv, arg_conv, binop_conv, rewr_conv, \
    top_conv, top_sweep_conv, beta_conv, beta_norm_conv, has_rewrite
from core import matcher
from core.logic import apply_theorem, strip_disj, strip_conj
from util import name
from util import typecheck


"""Normalization rules for logic (domain-dependent)."""

class norm_bool_expr(Conv):
    """Normalize a boolean expression."""
    def get_proof_term(self, t):
        if t.is_not():
            if t.arg == true:
                return rewr_conv("not_true").get_proof_term(t)
            elif t.arg == false:
                return rewr_conv("not_false").get_proof_term(t)
            else:
                return refl(t)
        else:
            return refl(t)

class norm_conj_assoc_clauses(Conv):
    """Normalize (A_1 & ... & A_n) & (B_1 & ... & B_n)."""
    def get_proof_term(self, t):
        if t.arg1.is_conj():
            return then_conv(
                rewr_conv("conj_assoc", sym=True),
                arg_conv(norm_conj_assoc_clauses())
            ).get_proof_term(t)
        else:
            return all_conv().get_proof_term(t)

class norm_conj_assoc(Conv):
    """Normalize conjunction with respect to associativity."""
    def get_proof_term(self, t):
        if t.is_conj():
            return then_conv(
                binop_conv(norm_conj_assoc()),
                norm_conj_assoc_clauses()
            ).get_proof_term(t)
        else:
            return all_conv().get_proof_term(t)

def conj_thms(*pts):
    assert len(pts) > 0, 'conj_thms: input list is empty.'
    if len(pts) == 1:
        return pts[0]
    else:
        return apply_theorem('conjI', pts[0], conj_thms(*pts[1:]))

def imp_conj_iff(goal: Term) -> ProofTerm:
    """Goal is of the form A_1 & ... & A_m <--> B_1 & ... & B_n, where
    the sets {A_1, ..., A_m} and {B_1, ..., B_n} are equal."""
    pt1 = ProofTerm('imp_conj', Implies(goal.lhs, goal.rhs))
    pt2 = ProofTerm('imp_conj', Implies(goal.rhs, goal.lhs))
    return ProofTerm.equal_intr(pt1, pt2)


def imp_disj_iff(goal: Term):
    """Goal is of the form A_1 | ... | A_m <--> B_1 | ... | B_n, where
    the sets {A_1, ..., A_m} and {B_1, ..., B_n} are equal."""
    pt1 = ProofTerm('imp_disj', Implies(goal.lhs, goal.rhs))
    pt2 = ProofTerm('imp_disj', Implies(goal.rhs, goal.lhs))
    return ProofTerm.equal_intr(pt1, pt2)

class disj_norm(Conv):
    """Normalize an disjunction."""
    def get_proof_term(self, t):
        goal = Eq(t, Or(*term_ord.sorted_terms(strip_disj(t))))
        return imp_disj_iff(goal)

class conj_norm(Conv):
    """Normalize an conjunction."""
    def get_proof_term(self, t):
        goal = Eq(t, And(*term_ord.sorted_terms(strip_conj(t))))
        return imp_conj_iff(goal)

def resolution(pt1, pt2):
    return ProofTerm('resolution', None, [pt1, pt2])

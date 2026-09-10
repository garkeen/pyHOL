# theories/logic/macro.py - Domain-dependent macros (hardcode logic.pyhol theorem names)

from typing import List, Tuple

from kernel.type import TVar, TFun, TyInst, BoolType
from kernel import term
from kernel.term import Term, SVar, Var, Const, Abs, Inst, Implies, Lambda, Eq
from syntax.logicops import Not, And, Or, true, false
from kernel.thm import InvalidDerivationException
from kernel import theory
from kernel.theory import register_macro
from kernel.macro import Macro
from core.conv import Conv, then_conv, all_conv, arg_conv, binop_conv, rewr_conv, \
    top_conv, top_sweep_conv, beta_conv, beta_norm_conv, has_rewrite
from kernel.proofterm import ProofTerm, refl
from core import matcher
from util import name
from util import typecheck

from core.logic import apply_theorem, get_forall_names, strip_all_implies, \
    strip_conj, strip_disj


@register_macro('imp_conj')
class imp_conj_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, pts):
        dct = dict()

        def traverse_A(pt):
            # Given proof term showing a conjunction, put proof terms
            # showing atoms of the conjunction in dct.
            if pt.prop.is_conj():
                cur_pt = pt
                while cur_pt.prop.is_conj():
                    pt1 = apply_theorem('conjD1', cur_pt)
                    traverse_A(pt1)
                    cur_pt = apply_theorem('conjD2', cur_pt)
                traverse_A(cur_pt)
            elif pt.prop == true:
                pass
            else:
                dct[pt.prop] = pt

        def traverse_C(t):
            # Return proof term with conclusion t
            if t.is_conj():
                ts = t.strip_conj()
                pt = traverse_C(ts[-1])
                for sub_t in reversed(ts[:-1]):
                    pt = apply_theorem('conjI', traverse_C(sub_t), pt)
                return pt
            elif t == true:
                return apply_theorem('trueI')
            else:
                assert t in dct.keys(), 'imp_conj_macro'
                return dct[t]

        A = goal.arg1
        traverse_A(ProofTerm.assume(A))
        return traverse_C(goal.arg).implies_intr(A)


@register_macro('imp_disj')
class imp_disj_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, pts):
        """Goal is of the form A_1 | ... | A_m --> B_1 | ...| B_n, where
        {A_1, ..., A_m} is a subset of {B_1, ..., B_n}."""

        # Dictionary from B_i to B_i --> B_1 | ... | B_n
        pts_B = dict()
        
        # Fills up pts_B.
        def traverse_C(pt):
            if pt.prop.arg1.is_disj():
                pt1 = apply_theorem('disjI1_syllogism', pt)
                pt2 = apply_theorem('disjI2_syllogism', pt)
                traverse_C(pt1)
                traverse_C(pt2)
            else:
                pts_B[pt.prop.arg1] = pt
        
        # Use pts_B to prove the implication
        def traverse_A(t):
            if t.is_disj():
                pt1 = traverse_A(t.arg1)
                pt2 = traverse_A(t.arg)
                return apply_theorem('disjE2', pt1, pt2)
            else:
                assert t in pts_B, "imp_disj: %s not found in conclusion" % t
                return pts_B[t]
            
        triv = apply_theorem('trivial', inst=Inst(A=goal.arg))
        traverse_C(triv)
        return traverse_A(goal.arg1)


@register_macro('resolution')
class resolution_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = 'resolution_right'

    def get_proof_term(self, arg, pts):
        """Input proof terms are A_1 | ... | A_m and B_1 | ... | B_n, where
        there is some i, j such that B_j = ~A_i or A_i = ~B_j."""
        
        # First, find the pair i, j such that B_j = ~A_i or A_i = ~B_j, the
        # variable side records the side of the positive literal.
        pt1, pt2 = pts
        disj1 = strip_disj(pt1.prop)
        disj2 = strip_disj(pt2.prop)
        
        side = None
        for i, t1 in enumerate(disj1):
            for j, t2 in enumerate(disj2):
                if t2 == Not(t1):
                    side = 'left'
                    break
                elif t1 == Not(t2):
                    side = 'right'
                    break
            if side is not None:
                break
                
        assert side is not None, "resolution: literal not found"
        
        # If side is wrong, just swap:
        if side == 'right':
            return self.get_proof_term(arg, [pt2, pt1])
        
        # Move items i and j to the front
        disj1 = [disj1[i]] + disj1[:i] + disj1[i+1:]
        disj2 = [disj2[j]] + disj2[:j] + disj2[j+1:]

        from theories.logic.logic import imp_disj_iff, disj_norm
        eq_pt1 = imp_disj_iff(Eq(pt1.prop, Or(*disj1)))
        eq_pt2 = imp_disj_iff(Eq(pt2.prop, Or(*disj2)))
        pt1 = eq_pt1.equal_elim(pt1)
        pt2 = eq_pt2.equal_elim(pt2)
        
        if len(disj1) > 1 and len(disj2) > 1:
            pt = apply_theorem('resolution', pt1, pt2)
        elif len(disj1) > 1 and len(disj2) == 1:
            pt = apply_theorem('resolution_left', pt1, pt2)
        elif len(disj1) == 1 and len(disj2) > 1:
            pt = apply_theorem('resolution_right', pt1, pt2)
        else:
            pt = apply_theorem('negE', pt2, pt1)

        return pt.on_prop(disj_norm())

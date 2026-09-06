# Author: Bohua Zhan
# Domain-independent macros (no hardcoded theorem/definition names)

from typing import List, Tuple

from kernel.type import TVar, TFun, TyInst, BoolType
from kernel import term
from kernel.term import Term, SVar, Var, Const, Abs, Inst, Implies, Lambda, Eq
from syntax.logicops import Not, And, Or, true, false  # noqa: F401  (re-export; installs Term methods)
from kernel.thm import Thm, InvalidDerivationException
from kernel import theory
from kernel.theory import register_macro
from kernel.macro import Macro
from framework.conv import Conv, then_conv, all_conv, arg_conv, binop_conv, rewr_conv, \
    top_conv, top_sweep_conv, beta_conv, beta_norm_conv, has_rewrite
from kernel.proofterm import ProofTerm, refl
from framework import matcher
from framework.macro.simp import simp_sweep
from util import name
from util import typecheck

# Import utility functions from framework.logic
from framework.logic import apply_theorem, get_forall_names, strip_all_implies, \
    strip_exists, strip_conj, strip_disj


class intros_macro(Macro):
    """Introduce assumptions and variables."""
    def __init__(self):
        self.level = 1
        self.sig = List[Term]
        self.limit = None

    def get_proof_term(self, args, prevs):
        assert len(prevs) >= 1, "intros_macro"
        if args is None:
            args = []
        pt, intros = prevs[-1], prevs[:-1]
        if len(prevs) == 1:
            return apply_theorem('trivial', pt)

        for intro in reversed(intros):
            if intro.th.prop.is_VAR():  # variable case
                pt = pt.forall_intr(intro.prop.arg)
            elif len(args) > 0 and intro.th.prop == args[0]:  # exists case
                assert intro.prop.is_exists(), "intros_macro"
                pt = apply_theorem('exE', intro, pt)
                args = args[1:]
            else:  # assume case
                assert len(intro.th.hyps) == 1 and intro.th.hyps[0] == intro.th.prop, \
                    "intros_macro"
                pt = pt.implies_intr(intro.prop)
        return pt


class resolve_theorem_macro(Macro):
    """Given a negation-shaped theorem (~A, A = false, or A --> false,
    C4 shape normalization) and a fact A, prove any goal."""
    def __init__(self):
        self.level = 1
        self.sig = Tuple[str, Term]
        self.limit = None

    def get_proof_term(self, args, pts):
        th_name, goal = args
        pt = ProofTerm.theorem(th_name)
        assert len(pts) == 1, "resolve_theorem_macro"

        # Shape normalization (C4): derive |- ~A from related shapes.
        if pt.prop.is_not():
            neg_pt = pt
        elif pt.prop.is_implies() and pt.prop.arg == false:
            # |- A --> false, combined with negI: |- (A --> false) --> ~A
            neg_pt = apply_theorem('negI', pt)
        elif pt.prop.is_equals() and pt.prop.rhs == false:
            # |- A = false. Under assumption A, rewrite A to false via
            # equal_elim, discharge to A --> false, then negI.
            A = pt.prop.lhs
            asm = ProofTerm.assume(A)
            false_pt = ProofTerm('equal_elim', None, [pt, asm])
            imp_pt = false_pt.implies_intr(A)
            neg_pt = apply_theorem('negI', imp_pt)
        else:
            raise AssertionError(
                "resolve_theorem_macro: %s is not a negation "
                "(accepted shapes: ~A, A --> false, A = false)" % th_name)

        # Match ~A against the fact, derive false, eliminate to the goal.
        inst = matcher.first_order_match(neg_pt.prop.arg, pts[0].prop)
        neg_pt = neg_pt.subst_type(inst.tyinst).substitution(inst)
        false_pt = apply_theorem('negE', neg_pt, pts[0])  # false
        return apply_theorem('falseE', false_pt, concl=goal)


class beta_norm_macro(Macro):
    """Given theorem th, return the normalization of th."""
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = None

    def eval(self, args, ths):
        assert args is None, "beta_norm_macro"
        eq_th = beta_norm_conv().eval(ths[0].prop)
        return Thm(eq_th.prop.arg, ths[0].hyps)

    def get_proof_term(self, args, pts):
        assert args is None, "beta_norm_macro"
        return pts[0].on_prop(beta_norm_conv())

class apply_theorem_inst_macro(Macro):
    """Apply a theorem with an explicit full instantiation, consuming
    no premises: the theorem's proposition directly proves the goal
    (whole-proposition closure). Expands to theorem + subst_type +
    substitution primitives, fully checked by the kernel.

    """
    def __init__(self):
        self.level = 1
        self.sig = Tuple[str, Inst]
        self.limit = None

    def get_proof_term(self, args, pts):
        name, inst = args
        assert len(pts) == 0, "apply_theorem_inst"
        pt = ProofTerm.theorem(name)
        if inst.tyinst:
            pt = pt.subst_type(inst.tyinst)
        if inst:
            pt = pt.substitution(inst)
        return pt

class apply_theorem_macro(Macro):
    """Apply existing theorem in the theory to a list of current
    results in the proof.
    If with_inst is set, the signature is (th_name, inst),
    where th_name is the name of the theorem, and inst are
    the instantiations of type and term variables.

    If with_inst is not set, the signature is th_name, where th_name
    is the name of the theorem.

    """
    def __init__(self, *, with_inst=False):
        self.level = 1
        self.with_inst = with_inst
        self.sig = Tuple[str, Inst] if with_inst else str
        self.limit = None

    def eval(self, args, prevs):
        if self.with_inst:
            name, inst = args
        else:
            name = args
            inst = Inst()
        th = theory.get_theorem(name)
        As, C = th.prop.strip_implies()

        assert len(prevs) <= len(As), "apply_theorem: too many prevs."

        # First attempt to match type variables
        svars = th.prop.get_svars()
        for v in svars:
            if v.name in inst:
                v.T.match_incr(inst[v.name].get_type(), inst.tyinst)

        pats = As[:len(prevs)]
        ts = [prev_th.prop for prev_th in prevs]
        inst = matcher.first_order_match_list(pats, ts, inst)

        # Check that all type variables are instantiated
        for stvar in th.prop.get_stvars():
            assert stvar.name in inst.tyinst, "apply_theorem: unmatched type variable %s" % stvar

        # If theorem is a first-order pattern, there is no need for beta_norm.
        if matcher.is_fo_pattern(th.prop):
            As, C = th.prop.subst(inst).strip_implies()
        else:
            As, C = th.prop.subst_norm(inst).strip_implies()
        new_prop = Implies(*(As[len(prevs):] + [C]))

        th = Thm(new_prop, th.hyps, *(prev.hyps for prev in prevs))

        # Obtain list of remaining schematic variables
        remain_svars = [t.subst_type(inst.tyinst) for t in svars if t.name not in inst]
        for v in reversed(remain_svars):
            th = Thm.forall_intr(v, th)
        return th

    def get_proof_term(self, args, pts):
        if self.with_inst:
            name, inst = args
        else:
            name = args
            inst = Inst()
        th = theory.get_theorem(name)
        As, C = th.prop.strip_implies()

        assert len(pts) <= len(As), "apply_theorem: too many prevs."

        # First attempt to match type variables
        svars = th.prop.get_svars()
        for v in svars:
            if v.name in inst:
                v.T.match_incr(inst[v.name].get_type(), inst.tyinst)

        pats = As[:len(pts)]
        ts = [pt.prop for pt in pts]
        inst = matcher.first_order_match_list(pats, ts, inst)

        pt = ProofTerm.theorem(name)
        pt = pt.subst_type(inst.tyinst).substitution(inst)

        # Apply beta_norm when theorem is a first-order pattern.
        if not matcher.is_fo_pattern(th.prop):
            pt = pt.on_prop(beta_norm_conv())
        pt = pt.implies_elim(*pts)

        # Check that all type variables are instantiated
        for stvar in th.prop.get_stvars():
            assert stvar.name in inst.tyinst, "apply_theorem: unmatched type variable %s" % stvar

        remain_svars = [t.subst_type(inst.tyinst) for t in svars if t.name not in inst]
        for v in reversed(remain_svars):
            pt = pt.forall_intr(v)

        return pt

class accept_macro(Macro):
    """Kernel expansion of the accept tactic's stage 1: assume the
    matched hypotheses, apply the instantiated theorem, and discharge
    its premises by implies_elim. Recorded as a single line.
    """
    def __init__(self):
        self.level = 1
        self.sig = Tuple[str, Inst, List[Term]]
        self.limit = None

    def get_proof_term(self, args, pts):
        th_name, inst, hyps = args
        assert len(pts) == 0, "accept_macro"
        pt = ProofTerm.theorem(th_name)
        if inst.tyinst:
            pt = pt.subst_type(inst.tyinst)
        if inst:
            pt = pt.substitution(inst)
        for h in hyps:
            pt = pt.implies_elim(ProofTerm.assume(h))
        return pt

class simp_macro(Macro):
    """Kernel expansion of the simp tactic: iterated rewriting with all
    unconditional hint_rewrite theorems of the current theory, to a
    fixed point. args = goal proposition; pts[0] (optional) is the
    new-goal sorry created by the tactic. Recorded as a single line.
    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        C = args
        cv_acc, current = simp_sweep(C)
        assert cv_acc is not None and current != C, \
            "simp_macro: nothing to simplify"
        pt = cv_acc.get_proof_term(C).symmetric()  # current = C
        if len(pts) == 0:
            # The result is reflexive: close with reflexivity.
            assert pt.prop.lhs.is_equals() and pt.prop.lhs.lhs == pt.prop.lhs.rhs, \
                "simp_macro: expected reflexive result"
            return pt.equal_elim(refl(pt.prop.lhs.lhs))
        assert len(pts) == 1 and pts[0].th.prop == current, \
            "simp_macro: sweep mismatch"
        return pt.equal_elim(pts[0])

class unfold_macro(Macro):
    """Kernel expansion of the unfold tactic: top-level rewriting with
    a definitional theorem (sym=True for fold). Recorded as a single
    line.
    """
    def __init__(self, *, sym=False):
        self.level = 1
        self.sig = Tuple[str, Term]
        self.sym = sym
        self.limit = None

    def get_proof_term(self, args, pts):
        th_name, C = args
        cv = then_conv(top_conv(rewr_conv(th_name, sym=self.sym)), beta_norm_conv())
        pt = cv.get_proof_term(C).symmetric()
        if len(pts) == 0:
            assert pt.prop.lhs.is_equals() and pt.prop.lhs.lhs == pt.prop.lhs.rhs, \
                "unfold_macro: expected reflexive result"
            return pt.equal_elim(refl(pt.prop.lhs.lhs))
        assert len(pts) == 1, "unfold_macro"
        return pt.equal_elim(pts[0])

class rewrite_goal_loc_macro(Macro):
    """Kernel expansion of position-specific goal rewriting (loc string
    selects the subterm). Recorded as a single line.
    """
    def __init__(self, *, sym=False):
        self.level = 1
        self.sig = Tuple[str, str, Term]
        self.sym = sym
        self.limit = None

    def get_proof_term(self, args, pts):
        from framework.conv import loc_conv
        th_name, loc, C = args
        cv = then_conv(loc_conv(loc, rewr_conv(th_name, sym=self.sym)),
                       beta_norm_conv())
        pt = cv.get_proof_term(C).symmetric()
        if len(pts) == 0:
            assert pt.prop.lhs.is_equals() and pt.prop.lhs.lhs == pt.prop.lhs.rhs, \
                "rewrite_goal_loc_macro: expected reflexive result"
            return pt.equal_elim(refl(pt.prop.lhs.lhs))
        assert len(pts) == 1, "rewrite_goal_loc_macro"
        return pt.equal_elim(pts[0])

class apply_induct_macro(Macro):
    """Apply induction. Directly invokes apply_theorem."""
    def __init__(self):
        self.level = 1
        self.sig = Tuple[str, Term, Term]
        self.limit = None

    def get_proof_term(self, args, pts):
        th_name, var, goal = args
        th = theory.get_theorem(th_name)
        f, th_args = th.concl.strip_comb()
        P = Lambda(var, goal)
        if len(th_args) != 1:
            raise NotImplementedError
        inst = matcher.first_order_match(th_args[0], var)
        inst[f.name] = P
        return apply_theorem(th_name, *pts, inst=inst)

class apply_fact_macro(Macro):
    """Apply a given fact to a list of facts. The first input fact is
    in the forall-implies form. Apply this fact to the remaining
    input facts. If with_inst is set, use the given sequence of terms
    as the instantiation.
    
    """
    def __init__(self, *, with_inst=False):
        self.level = 1
        self.with_inst = with_inst
        self.sig = List[Term] if with_inst else None
        self.limit = None

    def get_proof_term(self, args, pts):
        if not self.with_inst:
            assert len(pts) >= 2, "apply fact: too few prevs"

        pt, pt_prevs = pts[0], pts[1:]

        # First, obtain the patterns
        new_names = get_forall_names(pt.prop)

        new_vars, As, C = strip_all_implies(pt.prop, new_names)
        assert len(pt_prevs) <= len(As), "apply_fact: too many prevs"

        if self.with_inst:
            assert len(args) == len(new_names), "apply_fact_macro: wrong number of args."
            inst = Inst({nm: v for nm, v in zip(new_names, args)})
        else:
            inst = Inst()
            for idx, pt_prev in enumerate(pt_prevs):
                inst = matcher.first_order_match(As[idx], pt_prev.prop, inst)

        pt = pt.subst_type(inst.tyinst)
        for new_var in new_vars:
            if new_var.name in inst:
                pt = pt.forall_elim(inst[new_var.name])
            else:
                pt = pt.forall_elim(new_var)
        if pt.prop.beta_norm() != pt.prop:
            pt = pt.on_prop(beta_norm_conv())
        for prev_pt in pt_prevs:
            if prev_pt.prop != pt.assums[0]:
                prev_pt = prev_pt.on_prop(beta_norm_conv())
            pt = pt.implies_elim(prev_pt)
        for new_var in new_vars:
            if new_var.name not in inst:
                pt = pt.forall_intr(new_var)

        return pt

class rewrite_goal_macro(Macro):
    """Apply an existing equality theorem to rewrite a goal.

    The signature is (name, goal), where name is the name of the
    equality theorem. Goal is the statement of the goal.

    Rewrite the goal using the equality theorem. The result must
    be equal to prev[0].

    The remainder of prev are theorems to be used to discharge
    assumptions in conversion.
    
    sym - whether to apply the given equality in the backward direction.

    """
    def __init__(self, *, sym=False):
        self.level = 1
        self.sym = sym
        self.sig = Tuple[str, Term]
        self.limit = None

    def eval(self, args, ths):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal: signature"

        # Simply produce the goal
        _, goal = args
        return Thm(goal, *(th.hyps for th in ths))

    def get_proof_term(self, args, pts):
        assert isinstance(args, tuple) and len(args) == 2 and \
               isinstance(args[0], str) and isinstance(args[1], Term), "rewrite_goal: signature"

        name, goal = args
        eq_pt = ProofTerm.theorem(name)

        if len(pts) == len(eq_pt.assums):
            rewr_cv = rewr_conv(eq_pt, sym=self.sym, conds=pts)
        else:
            assert len(pts) == len(eq_pt.assums) + 1, "rewrite_goal: wrong number of prevs"
            rewr_cv = rewr_conv(eq_pt, sym=self.sym, conds=pts[1:])

        cv = then_conv(top_sweep_conv(rewr_cv), beta_norm_conv())
        pt = cv.get_proof_term(goal)  # goal = th.prop
        pt = pt.symmetric()           # th.prop = goal
        if pt.prop.lhs.is_equals() and pt.prop.lhs.lhs == pt.prop.lhs.rhs:
            pt = pt.equal_elim(refl(pt.prop.lhs.lhs))
        else:
            pt = pt.equal_elim(pts[0])  # goal

        return pt

class rewrite_fact_macro(Macro):
    """Rewrite a fact in the proof using a theorem."""
    def __init__(self, *, sym=False):
        self.level = 1
        self.sym = sym
        self.sig = str
        self.limit = None

    def get_proof_term(self, args, pts):
        assert isinstance(args, str), "rewrite_fact_macro: signature"

        th_name = args
        eq_pt = ProofTerm.theorem(th_name)

        assert len(pts) == len(eq_pt.assums) + 1, "rewrite_fact_macro: signature"

        # Check rewriting using the theorem has an effect
        if not has_rewrite(th_name, pts[0].prop, sym=self.sym, conds=pts[1:]):
            raise InvalidDerivationException("rewrite_fact using %s" % th_name)

        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt, sym=self.sym, conds=pts[1:])),
                       beta_norm_conv())
        res = pts[0].on_prop(cv)
        if res == pts[0]:
            raise InvalidDerivationException("rewrite_fact using %s" % th_name)
        return res

class rewrite_goal_with_prev_macro(Macro):
    """Given an input equality theorem and a goal, the macro rewrites
    the goal to a new form. The new goal, if it is not a reflexivity, is
    resolved using the second input theorem. The remaining input theorems
    are used to resolve conditions that arise when applying the equality.

    """
    def __init__(self, *, sym=False):
        self.level = 1
        self.sym = sym
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        assert isinstance(args, Term), "rewrite_goal_macro: signature"

        goal = args
        eq_pt = pts[0]

        new_names = get_forall_names(eq_pt.prop)
        new_vars, _, _ = strip_all_implies(eq_pt.prop, new_names)

        for new_var in new_vars:
            eq_pt = eq_pt.forall_elim(new_var)

        pts = pts[1:]

        cv = then_conv(top_sweep_conv(rewr_conv(eq_pt, sym=self.sym)),
                       beta_norm_conv())
        pt = cv.get_proof_term(goal)  # goal = th.prop
        pt = pt.symmetric()           # th.prop = goal
        if pt.prop.lhs.is_reflexive():
            pt = pt.equal_elim(refl(pt.prop.lhs.rhs))
        else:
            pt = pt.equal_elim(pts[0])
            pts = pts[1:]

        for A in pts:
            pt = pt.implies_intr(A.prop).implies_elim(A)
        return pt

class rewrite_fact_with_prev_macro(Macro):
    """This macro is provided with two input theorems. The first input
    theorem is an equality, which is used to rewrite the second input
    theorem.

    """
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = None

    def get_proof_term(self, args, pts):
        assert len(pts) == 2, "rewrite_fact_with_prev"

        eq_pt, pt = pts

        # In general, we assume eq_pt has forall quantification
        # First, obtain the patterns
        new_names = get_forall_names(eq_pt.prop)
        new_vars, eq_As, eq_C = strip_all_implies(eq_pt.prop, new_names)

        # First fact must be an equality
        assert len(eq_As) == 0 and eq_C.is_equals(), "rewrite_fact_with_prev"

        for new_var in new_vars:
            eq_pt = eq_pt.forall_elim(new_var)

        # Check rewriting using eq_pt has an effect
        cv1 = top_sweep_conv(rewr_conv(eq_pt))
        assert not cv1.eval(pt.prop).is_reflexive(), "rewrite_fact_with_prev"

        cv = then_conv(cv1, beta_norm_conv())
        return pt.on_prop(cv)

class forall_elim_gen_macro(Macro):
    """Apply forall elimination."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        assert len(pts) == 1, "forall_elim_gen"
        assert isinstance(args, Term), "forall_elim_gen"
        s = args  # term to instantiate

        pt = pts[0].forall_elim(s)
        if pt.prop.beta_norm() != pt.prop:
            pt = pt.on_prop(beta_norm_conv())
        return pt

class trivial_macro(Macro):
    """Prove a proposition of the form A_1 --> ... --> A_n --> B, where
    B agrees with one of A_i.

    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def can_eval(self, args):
        new_names = get_forall_names(args)
        vars, As, C = strip_all_implies(args, new_names)
        return C in As

    def get_proof_term(self, args, pts):
        new_names = get_forall_names(args)
        vars, As, C = strip_all_implies(args, new_names)
        assert C in As, "trivial_macro"

        pt = ProofTerm.assume(C)
        for A in reversed(As):
            pt = pt.implies_intr(A)
        for v in reversed(vars):
            pt = pt.forall_intr(v)
        return pt

class auto_close_macro(Macro):
    """Explicit automatic closure line.

    rule: auto_close, prevs = [X]. The current line's goal is closed by
    reusing the existing proved item X. Semantics: the result is X's
    theorem; the can_prove (hyp subset) check in the checker adapts it
    to the current line's statement. No new information is derived;
    this line only records that the closure is automatic and happens
    explicitly and visibly in the linear proof.

    """
    def __init__(self):
        # An auto_close line only references an already-verified line.
        # No new derivation is performed, so it is trusted at level 0
        # (never expanded, always resolved by evaluation).
        self.level = 0
        self.sig = None
        self.limit = None

    def eval(self, args, ths):
        assert args is None and len(ths) == 1, "auto_close_macro"
        return ths[0]

    def get_proof_term(self, args, pts):
        assert args is None and len(pts) == 1, "auto_close_macro"
        return pts[0]


# Register all domain-independent core macros
theory.global_macros.update({
    "intros": intros_macro(),
    "resolve_theorem": resolve_theorem_macro(),
    "beta_norm": beta_norm_macro(),
    "apply_theorem": apply_theorem_macro(),
    "apply_theorem_for": apply_theorem_macro(with_inst=True),
    "apply_theorem_inst": apply_theorem_inst_macro(),
    "accept": accept_macro(),
    "simp": simp_macro(),
    "unfold": unfold_macro(),
    "unfold_sym": unfold_macro(sym=True),
    "rewrite_goal_loc": rewrite_goal_loc_macro(),
    "rewrite_goal_loc_sym": rewrite_goal_loc_macro(sym=True),
    "apply_induct": apply_induct_macro(),
    "apply_fact": apply_fact_macro(),
    "apply_fact_for": apply_fact_macro(with_inst=True),
    "rewrite_goal": rewrite_goal_macro(),
    "rewrite_goal_sym": rewrite_goal_macro(sym=True),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_macro(),
    "rewrite_goal_with_prev_sym": rewrite_goal_with_prev_macro(sym=True),
    "rewrite_fact": rewrite_fact_macro(),
    "rewrite_fact_sym": rewrite_fact_macro(sym=True),
    "rewrite_fact_with_prev": rewrite_fact_with_prev_macro(),
    "forall_elim_gen": forall_elim_gen_macro(),
    "trivial": trivial_macro(),
    "auto_close": auto_close_macro(),
})

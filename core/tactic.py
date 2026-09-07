# Author: Bohua Zhan

from copy import copy

from kernel.type import TyInst, TConst
from kernel import term
from kernel.term import Term, Implies, Lambda, Inst, Eq
from syntax.logicops import Not, false
from kernel.thm import Thm, InvalidDerivationException
from kernel import theory
from kernel.proofterm import ProofTerm, TacticException
from core import logic
from core import matcher
from core.goal import Goal
from core.conv import then_conv, top_conv, rewr_conv, beta_conv, beta_norm_conv, \
    top_sweep_conv, has_rewrite, loc_conv
from core.logic import apply_theorem
from core.macro.simp import simp_sweep


class Tactic:
    """Represents a tactic function.

    A tactic takes a target theorem, and returns a proof term
    containing zero or more sorries. Tactics can be combined in the
    usual manner.

    get_proof_term can be supplied with two more arguments: args
    for extra data provided to the tactic, and prevs for the list
    of existing facts to use.

    """
    def get_proof_term(self, *, args=None, prevs=None) -> ProofTerm:
        raise NotImplementedError


def _whole_prop_match(th_name: str, goal: Thm):
    """Try to match the whole proposition of the theorem against the
    goal proposition (MATCH_ACCEPT_TAC semantics). This handles goals
    with an object-level implication head, which the stripped-conclusion
    matching can never reach. Used by the accept tactic only.

    Returns a proof term of the instantiated theorem when successful,
    or None otherwise. The closure is recorded as a single
    apply_theorem_inst macro line, fully checked by the kernel.

    """
    th = theory.get_theorem(th_name)
    try:
        inst = matcher.first_order_match(th.prop, goal.prop, Inst())
    except matcher.MatchException:
        return None

    # All schematic (term and type) variables must be determined.
    unmatched = [v.name for v in term.get_svars([th.prop]) if v.name not in inst]
    if unmatched:
        raise theory.ParameterQueryException(list("param_" + name for name in unmatched))
    unmatched_ty = [v.name for v in th.prop.get_stvars() if v.name not in inst.tyinst]
    if unmatched_ty:
        raise theory.ParameterQueryException(list("param_" + name for name in unmatched_ty))

    # Single-line recording: the whole-proposition closure is committed
    # as one apply_theorem_inst macro line (expands to theorem +
    # subst_type + substitution on check), keeping the proof area free
    # of raw primitive reference lines.
    pt = ProofTerm('apply_theorem_inst', (th_name, inst), [])
    assert pt.th.prop == goal.prop, "_whole_prop_match: instantiation mismatch"
    return pt


def _backward_rule(th_name, goal, inst, prevs):
    """Backward application of a theorem to a goal. Shared logic for rule
    and inst_exists_goal. NOT a Tactic -- a module helper, so calling it is
    not a same-layer tactic call. Produces a ProofTerm proving goal by
    applying th_name; unmatched assumptions become sorry subgoals. Returns
    an apply_theorem / apply_theorem_for macro proof term (the macro does
    the mechanical implies_elim chaining).
    """
    th = theory.get_theorem(th_name)
    As, C = th.assums, th.concl
    assert len(prevs) <= len(As), "_backward_rule: too many previous facts"
    if inst is None:
        inst = Inst()

    # Match conclusion to goal and assumptions to prevs.
    if matcher.is_pattern(C, []):
        inst = matcher.first_order_match(C, goal.prop, inst)
        for pat, prev in zip(As, prevs):
            inst = matcher.first_order_match(pat, prev.prop, inst)
    else:
        for pat, prev in zip(As, prevs):
            inst = matcher.first_order_match(pat, prev.prop, inst)
        inst = matcher.first_order_match(C, goal.prop, inst)

    unmatched_vars = [v.name for v in term.get_svars(As + [C]) if v.name not in inst]
    if unmatched_vars:
        raise theory.ParameterQueryException(list("param_" + name for name in unmatched_vars))

    As, _ = th.prop.subst_norm(inst).strip_implies()
    goal_Alen = len(goal.assums)
    if goal_Alen > 0:
        As = As[:-goal_Alen]
    pts = prevs + [Goal(A, goal.hyps).sorry() for A in As[len(prevs):]]

    if set(term.get_svars(th.assums)) != set(th.prop.get_svars()) or set(term.get_stvars(th.assums)) != set(th.prop.get_stvars()) or not matcher.is_pattern_list(th.assums, []):
        return apply_theorem(th_name, *pts, inst=inst)
    else:
        return apply_theorem(th_name, *pts)


class rule(Tactic):
    """Apply a theorem in the backward direction.

    args is either a pair of theorem name and instantiation, or the
    theorem name alone.

    Stripped-conclusion matching only (MATCH_MP_TAC semantics): the
    object-level implications of the theorem become premises; the final
    conclusion is matched against the goal; unmatched premises become
    subgoals. There is NO whole-proposition fallback: an implication-
    shaped goal that is not yet introduced must be intro'd first, or
    closed directly with the accept tactic (MATCH_ACCEPT_TAC semantics,
    C6 whole-proposition fallback).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if isinstance(args, tuple):
            th_name, inst = args
        else:
            th_name, inst = args, None
        assert isinstance(th_name, str), "rule: theorem name must be a string"
        if prevs is None:
            prevs = []
        return _backward_rule(th_name, goal, inst, prevs)

class resolve(Tactic):
    """Given any goal, a theorem of the form ~A (or a theorem that can
    be normalized to ~A, see below), and an existing fact A, solve the
    goal.

    Accepted theorem shapes (C4 shape normalization):
    - ~A
    - A = false
    - A --> false

    All shapes are recorded as a single resolve_theorem macro line;
    the shape normalization and matching happen inside the macro.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert isinstance(args, str) and len(prevs) == 1, "resolve: type"
        th_name = args
        th = theory.get_theorem(th_name)

        assert (th.prop.is_not() or
                (th.prop.is_implies() and th.prop.arg == false) or
                (th.prop.is_equals() and th.prop.rhs == false)), \
            "resolve: theorem %s is not a negation " \
            "(accepted shapes: ~A, A --> false, A = false)" % th_name

        # Matching against the fact is done in the macro.
        return ProofTerm('resolve_theorem', (args, goal.prop), prevs)

class intros(Tactic):
    """Given a goal of form !x_1 ... x_n. A_1 --> ... --> A_n --> C,
    introduce variables for x_1, ..., x_n and assumptions for A_1, ..., A_n.
    
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if args is None:
            var_names = []
        else:
            var_names = args

        vars, As, C = logic.strip_all_implies(goal.prop, var_names, svar=False)
        
        pt = Goal(C, goal.hyps, tuple(As)).sorry()
        ptAs = [ProofTerm.assume(A) for A in As]
        ptVars = [ProofTerm.variable(var.name, var.T) for var in vars]
        return ProofTerm('intros', None, ptVars + ptAs + [pt])

class var_induct(Tactic):
    """Apply induction rule on a variable.

    The goal may start with forall quantifiers over OTHER variables
    (library proofs rely on this shape). It must NOT start with a
    quantifier binding the induction variable itself: in that case the
    variable is bound in the goal and the induction predicate would
    capture the whole quantified proposition (C10). Introduce such a
    quantifier's body first.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        th_name, var = args
        assert not (goal.prop.is_forall() and
                    goal.prop.arg.var_name == var.name), (
            "var_induct: the goal starts with a forall binding the "
            "induction variable %s; introduce it first, then apply "
            "induction on the body." % var.name)
        P = Lambda(var, goal.prop)
        th = theory.get_theorem(th_name)
        f, th_args = th.concl.strip_comb()
        if len(th_args) != 1:
            raise AssertionError(
                "var_induct: %s is not an induction theorem "
                "(its conclusion must have exactly one argument, got %s)"
                % (th_name, th.concl))
        inst = matcher.first_order_match(th_args[0], var)
        inst[f.name] = P
        # Get original assumption count before substitution
        orig_As, _ = th.prop.strip_implies()
        num_orig = len(orig_As)
        # After substitution, only take the same number of assumptions
        As, _ = th.prop.subst_norm(inst).strip_implies()
        As = As[:num_orig]
        pts = [Goal(A, goal.hyps).sorry() for A in As]
        return ProofTerm("apply_induct", (th_name, var, goal.prop), pts)

class simp(Tactic):
    """Simplify the goal by iterated rewriting with all unconditional
    hint_rewrite theorems of the current theory, to a fixed point
    (bounded). Must-change: fails when nothing can be simplified.

    The whole simplification is committed as a single visible simp
    macro line (the kernel expands the conv chain on check).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert len(prevs) == 0, "simp"
        cv_acc, new_goal = simp_sweep(goal.prop)
        assert cv_acc is not None and new_goal != goal.prop, \
            "simp: nothing to simplify"
        if new_goal.is_equals() and new_goal.lhs == new_goal.rhs:
            return ProofTerm('simp', goal.prop, [])
        return ProofTerm('simp', goal.prop,
                         [Goal(new_goal, goal.hyps).sorry()])


class rewrite_goal(Tactic):
    """Rewrite the goal using a theorem."""
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        th_name = args
        C = goal.prop

        # Check whether rewriting using the theorem has an effect
        assert has_rewrite(th_name, C, sym=self.sym, conds=prevs), \
            "rewrite: unable to apply theorem."

        cv = then_conv(top_sweep_conv(rewr_conv(th_name, sym=self.sym, conds=prevs)),
                       beta_norm_conv())
        eq_th = cv.eval(C)
        new_goal = eq_th.prop.rhs

        if self.sym:
            macro_name = 'rewrite_goal_sym'
        else:
            macro_name = 'rewrite_goal'
        if new_goal.is_equals() and new_goal.lhs == new_goal.rhs:
            return ProofTerm(macro_name, args=(th_name, C), prevs=prevs)
        else:
            new_goal = Goal(new_goal, goal.hyps).sorry()
            assert new_goal.prop != goal.prop, "rewrite: unable to apply theorem"
            return ProofTerm(macro_name, args=(th_name, C), prevs=[new_goal] + prevs)

class rewrite_goal_with_conv(Tactic):
    """Rewrite the goal using a pre-built Conv object."""
    def __init__(self, cv):
        self.cv = cv

    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        C = goal.prop
        eq_th = self.cv.eval(C)
        new_goal = eq_th.prop.rhs
        
        if new_goal == C:
            return ProofTerm.reflexive(C)
        
        new_goal_pt = Goal(new_goal, goal.hyps).sorry()
        return ProofTerm('equal_elim', None, [
            ProofTerm('symmetric', None, [self.cv.get_proof_term(C)]),
            new_goal_pt
        ])

class rewrite_goal_with_prev(Tactic):
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert isinstance(prevs, list) and len(prevs) == 1, "rewrite_goal_with_prev"
        pt = prevs[0]
        C = goal.prop

        # In general, we assume pt.th has forall quantification.
        # First, obtain the patterns
        new_names = logic.get_forall_names(pt.prop)
        new_vars, prev_As, prev_C = logic.strip_all_implies(pt.prop, new_names)

        # Fact used must be an equality
        assert len(prev_As) == 0 and prev_C.is_equals(), "rewrite_goal_with_prev"

        for new_var in new_vars:
            pt = pt.forall_elim(new_var)

        # Check whether rewriting using the theorem has an effect
        assert has_rewrite(pt.th, C), "rewrite_goal_with_prev"

        cv = then_conv(top_sweep_conv(rewr_conv(pt)),
                       beta_norm_conv())
        eq_th = cv.eval(C)
        new_goal = eq_th.prop.rhs

        prevs = list(prevs)
        if not new_goal.is_reflexive():
            prevs.append(Goal(new_goal, goal.hyps).sorry())
        return ProofTerm('rewrite_goal_with_prev', args=C, prevs=prevs)

class apply_prev(Tactic):
    """Applies an existing fact in the backward direction."""
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert isinstance(prevs, list) and len(prevs) >= 1, "apply_prev"
        pt, prev_pts = prevs[0], prevs[1:]

        # First, obtain the patterns
        new_names = logic.get_forall_names(pt.prop)
        new_vars, As, C = logic.strip_all_implies(pt.prop, new_names)
        assert len(prev_pts) <= len(As), "apply_prev: too many prev_pts"

        if args is None:
            inst = Inst()
        else:
            inst = args
        inst = matcher.first_order_match(C, goal.prop, inst)
        for idx, prev_pt in enumerate(prev_pts):
            inst = matcher.first_order_match(As[idx], prev_pt.prop, inst)

        unmatched_vars = [v for v in new_names if v not in inst]
        if unmatched_vars:
            raise theory.ParameterQueryException(list("param_" + name for name in unmatched_vars))

        pt = pt.subst_type(inst.tyinst)
        for new_name in new_names:
            pt = pt.forall_elim(inst[new_name])
        if pt.prop.beta_norm() != pt.prop:
            pt = pt.on_prop(beta_norm_conv())
        inst_As, inst_C = pt.prop.strip_implies()

        inst_arg = [inst[new_name] for new_name in new_names]
        new_goals = [Goal(A, goal.hyps).sorry() for A in inst_As[len(prev_pts):]]
        
        # When there are no remaining premises, the fact directly proves the goal.
        # Return the fact itself (possibly with forall/instantiation) without
        # going through apply_fact, which requires at least 2 prevs.
        if len(inst_As) == 0 and len(prev_pts) == 0:
            return pt
        
        if set(new_names).issubset({v.name for v in term.get_vars(As)}) and \
           matcher.is_pattern_list(As, []):
            return ProofTerm('apply_fact', args=None, prevs=prevs + new_goals)
        else:
            return ProofTerm('apply_fact_for', args=inst_arg, prevs=prevs + new_goals)

class cases(Tactic):
    """Case checking on an expression.

    Uses the classical_cases theorem by default. Pass a different theorem
    name via the 'cases_thm' key in args (as a tuple) to override.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        # args can be either a Term (the case expression) or a tuple
        # (case_expr, cases_thm_name) where cases_thm_name defaults to
        # 'classical_cases'.
        if isinstance(args, tuple):
            case_expr, cases_thm = args
        else:
            assert isinstance(args, Term), "cases"
            case_expr = args
            cases_thm = 'classical_cases'

        As = goal.hyps
        C = goal.prop
        goal1 = Goal(Implies(case_expr, C), goal.hyps).sorry()
        goal2 = Goal(Implies(Not(case_expr), C), goal.hyps).sorry()
        return apply_theorem(cases_thm, goal1, goal2)


class datatype_cases(Tactic):
    """Case analysis on an expression of an inductive datatype.

    Uses the <tyname>_cases theorem (generated by the datatype
    extension, one branch per constructor). The predicate P is
    instantiated to %x. goal, so the goal is covered by proving each
    constructor branch (var_induct structure, without induction
    hypotheses).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if isinstance(args, tuple):
            case_expr, cases_thm = args
        else:
            assert isinstance(args, Term), "datatype_cases"
            case_expr = args
            case_T = case_expr.get_type()
            assert isinstance(case_T, TConst) and not case_T.is_fun(), \
                "datatype_cases: expression type is not a datatype"
            cases_thm = case_T.name + '_cases'

        th = theory.get_theorem(cases_thm)
        f, th_args = th.concl.strip_comb()
        if len(th_args) != 1:
            raise AssertionError(
                "datatype_cases: %s is not a cases theorem "
                "(its conclusion must have exactly one argument, got %s)"
                % (cases_thm, th.concl))
        inst = matcher.first_order_match(th_args[0], case_expr)
        P = Lambda(case_expr, goal.prop)
        inst[f.name] = P
        # Get original assumption count before substitution
        orig_As, _ = th.prop.strip_implies()
        num_orig = len(orig_As)
        # After substitution, only take the same number of assumptions
        As, _ = th.prop.subst_norm(inst).strip_implies()
        As = As[:num_orig]
        pts = [Goal(A, goal.hyps).sorry() for A in As]
        return apply_theorem(cases_thm, *pts, inst=inst)

class inst_exists_goal(Tactic):
    """Instantiate an exists goal.

    Uses the exI theorem by default. Pass a different theorem name via
    the 'exists_intro_thm' key in args (as a tuple) to override.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        # args can be either a Term (the witness) or a tuple
        # (witness, exists_intro_thm_name) where exists_intro_thm_name
        # defaults to 'exI'.
        if isinstance(args, tuple):
            witness, exists_intro_thm = args
        else:
            assert isinstance(args, Term), "inst_exists_goal"
            witness = args
            exists_intro_thm = 'exI'

        C = goal.prop
        assert C.is_exists(), "inst_exists_goal: goal is not exists statement"
        argT = witness.get_type()
        assert C.arg.var_T == argT, "inst_exists_goal: incorrect type: expect %s, given %s" % (
            str(C.arg.var_T), str(argT)
        )

        # Apply exI backward via the shared helper (not a tactic call).
        return _backward_rule(exists_intro_thm, goal, Inst(P=C.arg, a=witness), [])


class unfold(Tactic):
    """Unfold (or fold, with sym=True) a definition by top-level
    rewriting with the definitional theorem. Recorded as a single
    unfold / unfold_sym macro line.
    """
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert len(prevs) == 0, "unfold"
        th_name = args
        assert isinstance(th_name, str), "unfold"
        theory.get_theorem(th_name)
        cv = then_conv(top_conv(rewr_conv(th_name, sym=self.sym)), beta_norm_conv())
        eq_th = cv.eval(goal.prop)
        new_goal = eq_th.prop.rhs
        assert new_goal != goal.prop, "unfold: no effect"
        macro_name = 'unfold_sym' if self.sym else 'unfold'
        if new_goal.is_equals() and new_goal.lhs == new_goal.rhs:
            return ProofTerm(macro_name, (th_name, goal.prop), [])
        return ProofTerm(macro_name, (th_name, goal.prop),
                         [Goal(new_goal, goal.hyps).sorry()])


class rewrite_goal_loc(Tactic):
    """Rewrite the goal at a specific subterm position (loc string).
    Recorded as a single rewrite_goal_loc macro line.
    """
    def __init__(self, *, sym=False, loc=''):
        self.sym = sym
        self.loc = loc

    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert len(prevs) == 0, "rewrite_goal_loc"
        th_name = args
        assert isinstance(th_name, str), "rewrite_goal_loc"
        theory.get_theorem(th_name)
        cv = then_conv(loc_conv(self.loc, rewr_conv(th_name, sym=self.sym)),
                       beta_norm_conv())
        eq_th = cv.eval(goal.prop)
        new_goal = eq_th.prop.rhs
        assert new_goal != goal.prop, "rewrite_goal_loc: no effect"
        macro_name = 'rewrite_goal_loc_sym' if self.sym else 'rewrite_goal_loc'
        if new_goal.is_equals() and new_goal.lhs == new_goal.rhs:
            return ProofTerm(macro_name, (th_name, self.loc, goal.prop), [])
        return ProofTerm(macro_name, (th_name, self.loc, goal.prop),
                         [Goal(new_goal, goal.hyps).sorry()])


class assumption(Tactic):
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if not goal.prop in goal.hyps:
            raise TacticException('assumption: prop does not appear in hyps')
        
        return ProofTerm.assume(goal.prop)

class reflexive(Tactic):
    """Prove |- t = t by the reflexive primitive rule."""
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if not goal.prop.is_equals() or goal.prop.arg1 != goal.prop.arg:
            raise TacticException('reflexive: goal is not of the form t = t')
        return ProofTerm.reflexive(goal.prop.arg1)

class equal_intr(Tactic):
    """Prove |- A = B by proving A --> B and B --> A separately."""
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if not goal.prop.is_equals():
            raise TacticException('equal_intr: goal is not an equality')
        A, B = goal.prop.arg1, goal.prop.arg
        pt_AB = Goal(Implies(A, B), goal.hyps).sorry()
        pt_BA = Goal(Implies(B, A), goal.hyps).sorry()
        return ProofTerm.equal_intr(pt_AB, pt_BA)


class trans(Tactic):
    """Prove |- s = t by choosing a middle term u and proving
    |- s = u and |- u = t separately (TRANS_TAC)."""
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        if not goal.prop.is_equals():
            raise TacticException('trans: goal is not an equality')
        u = args
        assert isinstance(u, Term), "trans"
        s, t = goal.prop.arg1, goal.prop.arg
        if u.get_type() != s.get_type():
            raise TacticException('trans: middle term has type %s, expect %s' % (
                str(u.get_type()), str(s.get_type())))
        pt_su = Goal(Eq(s, u), goal.hyps).sorry()
        pt_ut = Goal(Eq(u, t), goal.hyps).sorry()
        return pt_su.transitive(pt_ut)



class trivial(Tactic):
    """Close a trivial goal: A_1 --> ... --> A_n --> B where B agrees with some A_i.

    Backward tactic. Probes via the trivial macro: constructing the proof term
    raises if the goal is not trivially closeable.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        return ProofTerm('trivial', goal.prop, prevs[1:])

class elim_exists(Tactic):
    """Backward exists-elimination as a checked derivation.

    Derives the content of the rewired enclosing intros line for
    eliminating an exists fact: fresh variables, an assumption of the
    exists body, and the enclosing intros line rewired through exE.

    args = (names, exists_pt, wired_prev_pts, wired_args):
      names -- variable names for the eliminated existentials
      exists_pt -- the exists fact (proof term)
      wired_prev_pts -- the ALREADY-WIRED prevs of the enclosing
          intros line (shifted ids, exists fact / fresh variables /
          body assumption inserted before the continuation, extended
          theorems), subgoal last
      wired_args -- the args the intros line will carry (exists prop
          prepended to the original args)
    prevs = [goal_atom] (unused except for interface symmetry).

    Returns the intros proof term whose args/th prescribe the content
    of the rewired intros line; the kernel checks the derivation when
    the line is (re)checked.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        names, exists_pt, wired_prev_pts, wired_args = args
        return ProofTerm('intros', wired_args, list(wired_prev_pts))

class accept(Tactic):
    """Close the goal by direct reference to a theorem of the theory.

    The theorem's conclusion is unified (first-order matched) with the
    goal, and each premise of the theorem must be matched with one of
    the goal's assumptions. No subgoal (sorry) is produced: the goal is
    closed outright, recorded as an explicit line.

    This is the counterpart of HOL Light's MATCH_ACCEPT_TAC (a theorem
    whose instantiation directly proves the goal is accepted without
    going through backward chaining). It fails when the conclusion does
    not match, or when some premise is not matched by any assumption.

    Matching is attempted in two stages:
    1. Stripped-conclusion match: the theorem's conclusion is matched
       against the goal's proposition, each premise against one of the
       goal's assumptions (goals already introduced).
    2. Whole-proposition match (C6, fallback): the entire theorem
       proposition is first-order matched against the goal proposition,
       recording a single apply_theorem_inst macro line. This closes
       implication-shaped goals with implication-shaped theorems before
       any intro step (Isabelle / MATCH_ACCEPT_TAC semantics).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert isinstance(args, str), "accept: theorem name must be a string"
        th_name = args
        try:
            return self._stripped_accept(th_name, goal)
        except (TacticException, matcher.MatchException):
            if len(prevs) == 0:
                pt = _whole_prop_match(th_name, goal)
                if pt is not None:
                    return pt
            raise

    def _stripped_accept(self, th_name, goal):
        th = theory.get_theorem(th_name)
        As, C = th.assums, th.concl

        # First-order match the conclusion against the goal. Schematic
        # variables of the conclusion that remain unbound are
        # parameters: the goal is not an instance of the theorem.
        inst = Inst()
        try:
            inst = matcher.first_order_match(C, goal.prop, inst)
        except matcher.MatchException as e:
            raise TacticException(
                "accept: conclusion of %s does not match the goal: %s" % (th_name, e))

        if any(v.name not in inst for v in term.get_svars(C)):
            raise theory.ParameterQueryException(
                list("param_" + v.name for v in term.get_svars(C) if v.name not in inst))

        available = [h for h in goal.hyps]

        # Match each premise with some assumption, extending the
        # instantiation. Every premise must be matched: the goal should
        # be directly provable from the given assumptions.
        matched_hs = []
        for A in As:
            match_h = None
            for h in available:
                inst2 = copy(inst)
                try:
                    inst2 = matcher.first_order_match(A, h, inst2)
                except matcher.MatchException:
                    continue
                match_h = h
                inst = inst2
                break
            if match_h is None:
                raise TacticException(
                    "accept: premise of %s is not matched with any assumption: %s"
                    % (th_name, str(A)))
            matched_hs.append(match_h)

        # All type variables must be determined.
        unmatched_stvars = [v.name for v in th.prop.get_stvars()
                            if v.name not in inst.tyinst]
        if unmatched_stvars:
            raise theory.ParameterQueryException(
                list("param_" + name for name in unmatched_stvars))

        # Return the theorem application with the matched assumptions
        # recorded as premises, committed as a single accept macro line
        # (expands to assume + theorem + implies_elim chain on check).
        return ProofTerm('accept', (th_name, inst, matched_hs), [])

class apply_theorem_forward(Tactic):
    """Forward: apply a theorem to facts to derive a new fact. No goal.

    Mirrors rule (backward): does the forward matching (assumptions to
    facts) and param detection IN THE TACTIC. `provided` lists param names
    already supplied by the user (possibly empty-valued, meaning 'leave
    as forall' -- these are NOT raised). Returns apply_theorem (the macro
    does the full matching -- resolving type variables, which forward
    cannot determine without a goal -- and the mechanical chaining).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        if prevs is None:
            prevs = []
        if isinstance(args, tuple):
            th_name, user_inst, provided = args
        else:
            th_name, user_inst, provided = args, None, []
        assert isinstance(th_name, str), "apply_theorem_forward"
        th = theory.get_theorem(th_name)
        As, C = th.assums, th.concl
        assert len(prevs) <= len(As), "apply_theorem_forward: too many prevs"

        # Forward matching (for param detection). Mirror rule's detection.
        inst_check = Inst() if user_inst is None else user_inst
        for pat, prev in zip(As, prevs):
            inst_check = matcher.first_order_match(pat, prev.prop, inst_check)

        unmatched_vars = [v.name for v in term.get_svars(As + [C])
                          if v.name not in inst_check and v.name not in provided]
        if unmatched_vars:
            raise theory.ParameterQueryException(list("param_" + name for name in unmatched_vars))

        # Return apply_theorem with the user-provided inst only (the macro
        # performs the full matching, resolving type variables, and chaining).
        if user_inst is not None:
            return apply_theorem(th_name, *prevs, inst=user_inst)
        else:
            return apply_theorem(th_name, *prevs)


class rewrite_fact_forward(Tactic):
    """Forward: rewrite a fact using a theorem. No goal.

    Does the has_rewrite check (does the theorem apply to the fact) IN THE
    TACTIC. Returns rewrite_fact (the macro does the conv rewrite).
    """
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, *, args=None, prevs=None):
        if prevs is None:
            prevs = []
        assert isinstance(args, str), "rewrite_fact_forward"
        assert len(prevs) >= 1, "rewrite_fact_forward: need a fact to rewrite"
        # Reasoning: does the theorem actually rewrite the fact?
        if not has_rewrite(args, prevs[0].prop, sym=self.sym, conds=prevs[1:]):
            raise InvalidDerivationException("rewrite_fact using %s" % args)
        return ProofTerm('rewrite_fact_sym' if self.sym else 'rewrite_fact', args, prevs)


class apply_fact_forward(Tactic):
    """Forward: apply a forall/implies fact to other facts. No goal.

    Mirrors apply_fact_macro: does the forward matching (the fact's
    assumptions to the other facts) IN THE TACTIC. Returns apply_fact
    (the macro does forall_elim/implies_elim/forall_intr chaining).
    No param detection (unmatched vars are forall_intr'd by the macro).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        if prevs is None:
            prevs = []
        assert len(prevs) >= 2, "apply_fact_forward: too few prevs"
        pt_fact = prevs[0]
        pt_prevs = prevs[1:]
        new_names = logic.get_forall_names(pt_fact.prop)
        new_vars, As, C = logic.strip_all_implies(pt_fact.prop, new_names)
        assert len(pt_prevs) <= len(As), "apply_fact_forward: too many prevs"
        # Forward matching (mirror the macro).
        inst = Inst()
        for idx, pt_prev in enumerate(pt_prevs):
            inst = matcher.first_order_match(As[idx], pt_prev.prop, inst)
        # Return apply_fact (macro does forall_elim/implies_elim/forall_intr).
        if args:
            return ProofTerm('apply_fact_for', args, prevs)
        return ProofTerm('apply_fact', None, prevs)


class rewrite_fact_with_prev_forward(Tactic):
    """Forward: rewrite a fact using a previous equality. No goal.

    Mirrors rewrite_fact_with_prev_macro: does the forall-handling and
    has-effect check IN THE TACTIC. Returns rewrite_fact_with_prev (the
    macro does the conv rewrite).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        if prevs is None:
            prevs = []
        assert len(prevs) == 2, "rewrite_fact_with_prev_forward"
        eq_pt, pt = prevs[0], prevs[1]
        new_names = logic.get_forall_names(eq_pt.prop)
        new_vars, eq_As, eq_C = logic.strip_all_implies(eq_pt.prop, new_names)
        assert len(eq_As) == 0 and eq_C.is_equals(), "rewrite_fact_with_prev_forward"
        # forall_elim the equality (instantiate its forall vars)
        for new_var in new_vars:
            eq_pt = eq_pt.forall_elim(new_var)
        # has-effect check (rewriting must change the fact)
        cv1 = top_sweep_conv(rewr_conv(eq_pt))
        if cv1.eval(pt.prop).is_reflexive():
            raise InvalidDerivationException("rewrite_fact_with_prev: no effect")
        return ProofTerm('rewrite_fact_with_prev', args, prevs)


class forall_elim_forward(Tactic):
    """Forward: instantiate a forall fact with a term. No goal.

    Asserts the fact is a forall (the reasoning). Returns forall_elim_gen
    (the macro does forall_elim + beta_norm).
    """
    def get_proof_term(self, *, args=None, prevs=None):
        if prevs is None:
            prevs = []
        assert len(prevs) == 1, "forall_elim_forward"
        assert isinstance(args, Term), "forall_elim_forward"
        assert prevs[0].prop.is_forall(), "forall_elim_forward: fact is not forall"
        return ProofTerm('forall_elim_gen', args, prevs)

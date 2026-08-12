# Author: Bohua Zhan

from copy import copy

from kernel.type import TyInst
from kernel import term
from kernel.term import Term, Implies, Not, Lambda, Inst
from kernel.thm import Thm, InvalidDerivationException
from kernel import theory
from kernel.proofterm import ProofTerm, TacticException
from framework import logic
from framework import matcher
from framework.conv import then_conv, top_conv, rewr_conv, beta_conv, beta_norm_conv, \
    top_sweep_conv, has_rewrite
from framework.logic import apply_theorem


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


class MacroTactic(Tactic):
    """Construct a tactic from a macro.
    
    The name of the macro is provided at initialization. The first
    argument of the macro must be the goal statement. The remaining
    arguments are supplied by the tactic.
    
    """
    def __init__(self, macro):
        self.macro = macro

    def get_proof_term(self, *, args=None, prevs=None):
        assert prevs is not None and len(prevs) >= 1, "MacroTactic"
        goal = prevs[0].th
        prevs = prevs[1:]

        if args is None:
            args = goal.prop
        else:
            args = (goal.prop,) + args

        return ProofTerm(self.macro, args, prevs)

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
    pts = prevs + [ProofTerm.sorry(Thm(A, goal.hyps)) for A in As[len(prevs):]]

    if set(term.get_svars(th.assums)) != set(th.prop.get_svars()) or set(term.get_stvars(th.assums)) != set(th.prop.get_stvars()) or not matcher.is_pattern_list(th.assums, []):
        return apply_theorem(th_name, *pts, inst=inst)
    else:
        return apply_theorem(th_name, *pts)


class rule(Tactic):
    """Apply a theorem in the backward direction.

    args is either a pair of theorem name and instantiation, or the
    theorem name alone.
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
    """Given any goal, a theorem of the form ~A, and an existing fact A,
    solve the goal.
    
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert isinstance(args, str) and len(prevs) == 1, "resolve: type"
        th_name = args
        th = theory.get_theorem(th_name)

        assert th.prop.is_not(), "resolve: prop is not a negation"

        # Checking that the theorem matches the fact is done here.
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
        
        pt = ProofTerm.sorry(Thm(C, goal.hyps, tuple(As)))
        ptAs = [ProofTerm.assume(A) for A in As]
        ptVars = [ProofTerm.variable(var.name, var.T) for var in vars]
        return ProofTerm('intros', None, ptVars + ptAs + [pt])

class var_induct(Tactic):
    """Apply induction rule on a variable."""
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        th_name, var = args
        P = Lambda(var, goal.prop)
        th = theory.get_theorem(th_name)
        f, th_args = th.concl.strip_comb()
        if len(th_args) != 1:
            raise NotImplementedError
        inst = matcher.first_order_match(th_args[0], var)
        inst[f.name] = P
        # Get original assumption count before substitution
        orig_As, _ = th.prop.strip_implies()
        num_orig = len(orig_As)
        # After substitution, only take the same number of assumptions
        As, _ = th.prop.subst_norm(inst).strip_implies()
        As = As[:num_orig]
        pts = [ProofTerm.sorry(Thm(A, goal.hyps)) for A in As]
        return ProofTerm("apply_induct", (th_name, var, goal.prop), pts)

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
            new_goal = ProofTerm.sorry(Thm(new_goal, goal.hyps))
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
        
        new_goal_pt = ProofTerm.sorry(Thm(new_goal, goal.hyps))
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
            prevs.append(ProofTerm.sorry(Thm(new_goal, goal.hyps)))
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
        new_goals = [ProofTerm.sorry(Thm(A, goal.hyps)) for A in inst_As[len(prev_pts):]]
        
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
        goal1 = ProofTerm.sorry(Thm(Implies(case_expr, C), goal.hyps))
        goal2 = ProofTerm.sorry(Thm(Implies(Not(case_expr), C), goal.hyps))
        return apply_theorem(cases_thm, goal1, goal2)

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
        pt_AB = ProofTerm.sorry(Thm(Implies(A, B), goal.hyps))
        pt_BA = ProofTerm.sorry(Thm(Implies(B, A), goal.hyps))
        return ProofTerm.equal_intr(pt_AB, pt_BA)



class trivial(Tactic):
    """Close a trivial goal: A_1 --> ... --> A_n --> B where B agrees with some A_i.

    Backward tactic. Probes via the trivial macro: constructing the proof term
    raises if the goal is not trivially closeable.
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        return ProofTerm('trivial', goal.prop, prevs[1:])

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
    """
    def get_proof_term(self, *, args=None, prevs=None):
        goal = prevs[0].th
        prevs = prevs[1:]
        assert isinstance(args, str), "accept: theorem name must be a string"
        th_name = args
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
        # recorded as premises. This expands to an explicit apply line.
        assume_pts = [ProofTerm.assume(h) for h in matched_hs]
        return ProofTerm('apply_theorem_for', (th_name, inst), assume_pts)

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

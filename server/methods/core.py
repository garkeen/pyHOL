# Author: Bohua Zhan

from typing import Dict
import copy
import traceback

from kernel.type import TyInst
from kernel import term
from kernel.term import Term, Var, SVar, Inst, Implies
from kernel.thm import Thm, InvalidDerivationException
from kernel import report
from kernel.proof import ProofItem, ItemID, Proof, ProofStateException
from kernel import theory
from kernel.proofterm import ProofTerm, TacticException
from framework import matcher
from framework import logic
from framework import context
from framework import tactic
from framework import search as fw_search
from framework.tactic import Tactic, trivial
from framework import conv
from syntax import parser, printer, pprint
from syntax.settings import settings, global_setting


def _can_prove_match(fact_th, target_th):
    """Matching-based closure test (audit finding C7).

    The fact's proposition first-order-matches the target's proposition
    (schematic variables instantiated), and the fact's assumptions are a
    subset of the target's. This subsumes exact equality, so schematic
    facts can close concrete goals and alpha-variants. Used for EXPLICIT
    auto-close only; the kernel soundness check (kernel Thm.can_prove)
    is deliberately left strict.
    """
    if not matcher.can_first_order_match(fact_th.prop, target_th.prop):
        return False
    return set(fact_th.hyps).issubset(set(target_th.hyps))


def _branch_label(prop, covered_prop):
    """Case-branch label for a subgoal of a backward step.

    The subgoal is a branch of the covered goal when its prop is a
    leading-implication chain that ends at the covered goal (cases,
    disjE-style backward applications). Returns the list of the
    antecedent terms not part of the covered goal, or None.
    """
    As, C = prop.strip_implies()
    t = C
    for j in range(len(As), -1, -1):
        if t == covered_prop:
            extra = As[:j]
            return extra if extra else None
        if j > 0:
            t = Implies(As[j - 1], t)
    return None


def _induct_labels(th_name):
    """Constructor labels for the branches of an induction theorem.

    The branch subgoal props are beta-reduced (the predicate instantiation
    is applied), so the constructor term must be reconstructed from the
    theorem's premises: the final consequent of each premise, with a
    schematic head and a single argument, is a constructor application.
    Returns a list of label Terms (None for premises without one).
    """
    th = theory.get_theorem(th_name)
    orig_As, _ = th.prop.strip_implies()
    labels = []
    for A in orig_As:
        _, body = A.strip_forall()
        _, C = body.strip_implies()
        f, args = C.strip_comb()
        if isinstance(f, term.SVar) and len(args) == 1 and not args[0].is_var():
            labels.append(args[0])
        else:
            labels.append(None)
    return labels


class ProofState():
    """Represents proof state on the server side."""

    def __init__(self):
        """Empty proof state."""
        self.vars = []
        self.prf = Proof()
        self.rpt = None
        # Display metadata keyed by item id (str): 'origin' (cut),
        # 'manual' (apply_prev closure), 'fact' (forward line),
        # 'case' (list of Terms, the case-branch label).
        self.line_meta = {}

    def get_vars(self, id):
        """Obtain the context at the given id."""
        id = ItemID(id)
        vars = dict()
        for v in self.vars:
            vars[v.name] = v.T

        prf = self.prf
        try:
            for n in id.id:
                for item in prf.items[:n+1]:
                    if item.rule == "variable":
                        nm, T = item.args
                        vars[nm] = T
                prf = prf.items[n].subproof
            return vars
        except (AttributeError, IndexError):
            raise ProofStateException

    def __str__(self):
        vars = sorted(self.vars, key = lambda v: v.name)
        lines = "\n".join('var ' + v.name + ' :: ' + str(v.T) for v in vars)
        return lines + "\n" + str(self.prf)

    def __copy__(self):
        res = ProofState()
        res.vars = copy.copy(self.vars)
        res.prf = copy.copy(self.prf)
        res.rpt = copy.copy(self.rpt)
        res.line_meta = dict(self.line_meta)
        return res

    def export_proof(self):
        return sum([printer.export_proof_item(item) for item in self.prf.items], [])

    def json_data(self):
        """Export proof in json format."""
        with global_setting(unicode=True):
            vars = {v.name: printer.print_type(v.T) for v in self.vars}

        with global_setting(unicode=True, highlight=True):
            res = {
                "vars": vars,
                "proof": self.export_proof(),
                "num_gaps": len(self.rpt.gaps),
                "method_sig": get_method_sig(),
                "method_list_params": get_method_list_params(),
            }
        return res

    def check_proof(self, *, no_gaps=False, compute_only=False):
        """Check the given proof. Report is stored in rpt."""
        self.rpt = report.ProofReport()
        return theory.check_proof(self.prf, rpt=self.rpt, no_gaps=no_gaps, compute_only=compute_only)

    def add_line_before(self, id, n: int):
        """Add n lines before the given id."""
        id = ItemID(id)
        prf = self.prf.get_parent_proof(id)
        split = id.last()
        new_items = [ProofItem(id.incr_id(i), "") for i in range(n)]
        prf.items = prf.items[:split] + new_items + prf.items[split:]
        for item in prf.items[split+n:]:
            item.incr_proof_item(id, n)

        self.check_proof(compute_only=True)

    def remove_line(self, id):
        """Remove line with the given id."""
        id = ItemID(id)
        prf = self.prf.get_parent_proof(id)
        split = id.last()
        prf.items = prf.items[:split] + prf.items[split+1:]
        for item in prf.items[split:]:
            item.decr_proof_item(id)

        self.check_proof(compute_only=True)

    def set_line(self, id, rule, *, args=None, prevs=None, th=None):
        """Set the item with the given id to the following data."""
        id = ItemID(id)
        prf = self.prf.get_parent_proof(id)
        prf.items[id.last()] = ProofItem(id, rule, args=args, prevs=prevs, th=th)
        self.check_proof(compute_only=True)

    def get_proof_item(self, id):
        """Obtain the proof item with the given id."""
        return self.prf.find_item(ItemID(id))

    def replace_id(self, old_id, new_id):
        """Replace old_id with new_id in prevs."""
        def replace(prf: Proof):
            for item in prf.items:
                item.prevs = [new_id if id == old_id else id for id in item.prevs]
                if item.subproof:
                    replace(item.subproof)

        prf = self.prf.get_parent_proof(old_id)
        replace(prf)

        self.remove_line(old_id)

    def find_goal(self, concl, goal_id):
        """Determine if the given conclusion is already proved,
        for the purpose of showing goal_id.

        Proof items that can be used include all items with id
        whose length is at most that of goal_id, where all but
        the last number agrees with that of goal_id, and the
        last number is less than the corresponding number in goal_id.

        """
        prf = self.prf
        try:
            for n in goal_id.id:
                for item in prf.items[:n]:
                    if item.th is not None and _can_prove_match(item.th, concl):
                        return item.id
                prf = prf.items[n].subproof
        except (AttributeError, IndexError):
            raise ProofStateException

    def apply_search(self, id, method: "Method", prevs=None):
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        return method.search(self, id, prevs)
    
    def _finish_backward(self, id, pt):
        """Common tail for backward entries (apply_tactic / apply_macro).

        Export the proof term onto the goal line, then perform EXPLICIT
        auto-close: every gap already proved by a preceding line becomes
        a visible auto_close line, every trivial gap a visible trivial
        line. Implicit gap removal is forbidden by design (proof state
        is an immutable, fully visible line list).
        """
        # When the proof term is an atom, the fact directly proves the
        # goal. The goal line is rewritten in place as an auto_close line
        # (a witness line: same line, same count; no new goal/fact).
        if pt.rule == 'atom':
            fact_id = pt.args  # ItemID of the fact
            fact_item = self.get_proof_item(fact_id)
            if fact_item.th is not None and _can_prove_match(fact_item.th, self.get_proof_item(id).th):
                self.set_line(id, 'auto_close', prevs=[fact_id], th=self.get_proof_item(id).th)
                # Manual closure (user's apply_prev): record the marker
                # (merged, so a cut/case origin on the goal survives).
                self.line_meta.setdefault(str(id), {})['manual'] = True
            return None

        covered_th = self.get_proof_item(id).th
        covered_meta = self.line_meta.get(str(id))

        new_prf = pt.export(prefix=id, subproof=False)

        # The exported lines occupy id .. id+len-1; the original goal
        # line is covered by the last exported item (the conclusion),
        # keeping the line count unchanged.
        self.add_line_before(id, len(new_prf.items) - 1)
        for i, item in enumerate(new_prf.items):
            cur_id = item.id
            prf = self.prf.get_parent_proof(cur_id)
            prf.items[cur_id.last()] = item
        self.check_proof(compute_only=True)

        # The covered goal moved to id+len-1; its metadata entry at the
        # original id is stale (the position now holds the first exported
        # item) and is reattached to the covering item below.
        self.line_meta.pop(str(id), None)

        # Case-branch labels: subgoals of the expansion whose prop is a
        # leading-implication chain ending at the covered goal (cases,
        # disjE-style backward applications) are case branches.
        for item in new_prf.items:
            if item.rule == 'sorry' and item.th is not None:
                label = _branch_label(item.th.prop, covered_th.prop)
                if label:
                    self.line_meta[str(item.id)] = {'case': label}

        # Induction branches: reconstruct the constructor labels from
        # the induction theorem's premises (the branch props are
        # beta-reduced, so the constructor term is not in them).
        if pt.rule == 'apply_induct':
            labels = _induct_labels(pt.args[0])
            sorry_items = [item for item in new_prf.items if item.rule == 'sorry']
            if len(labels) == len(sorry_items):
                for item, label in zip(sorry_items, labels):
                    if label is not None and 'case' not in self.line_meta.get(str(item.id), {}):
                        self.line_meta[str(item.id)] = {'case': [label]}

        # The line covering the old goal (the item whose prop equals the
        # covered goal's, else the conclusion) inherits its metadata:
        # cut origin and case labels survive coverage.
        if covered_meta:
            cover_id = new_prf.items[-1].id
            for item in new_prf.items:
                if item.th is not None and item.th.prop == covered_th.prop:
                    cover_id = item.id
                    break
            self.line_meta[str(cover_id)] = covered_meta

        # Explicit auto-close: every gap of the expansion that is already
        # proved by a preceding line is closed by a visible auto_close
        # line (same line count as the previous gap line).
        for item in new_prf.items:
            if item.rule == 'sorry':
                self._find_and_close(item.id)

        # Explicit auto-close of trivial gaps: record a visible trivial line.
        for item in new_prf.items:
            if item.rule == 'sorry':
                try:
                    trivial().get_proof_term(prevs=[ProofTerm.atom(item.id, item.th)])
                    self.set_line(item.id, 'trivial', args=item.th.prop)
                except AssertionError:
                    pass

        return new_prf

    def apply_tactic(self, id, tactic: Tactic, args=None, prevs=None):
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        prevs = [ProofTerm.atom(prev, self.get_proof_item(prev).th) for prev in prevs]
        
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_tactic: id is not a gap"

        pt = tactic.get_proof_term(args=args, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)
        return self._finish_backward(id, pt)

    def apply_macro(self, id, macro_name: str, args=None, prevs=None):
        """Checked entry point for applying a single macro (derived rule)
        to a gap. This is the ONLY way methods may use macros (the
        generic MacroTactic adapter is gone): the macro is validated
        against the registry before use.

        args are extra macro arguments after the goal proposition.
        Auto-close follows the same explicit rules as apply_tactic.
        """
        assert theory.has_macro(macro_name), \
            "apply_macro: %s is not available." % macro_name
        macro = theory.get_macro(macro_name)
        if macro.limit is not None:
            assert theory.thy.has_theorem(macro.limit), \
                "apply_macro: %s is not available in this theory." % macro_name

        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        prevs = [ProofTerm.atom(prev, self.get_proof_item(prev).th) for prev in prevs]

        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_macro: id is not a gap"

        if args is None:
            macro_args = cur_item.th.prop
        else:
            macro_args = (cur_item.th.prop,) + tuple(args)

        pt = ProofTerm(macro_name, macro_args, prevs)
        return self._finish_backward(id, pt)

    def apply_forward(self, id, ftac, args=None, prevs=None):
        """Checked entry point for forward steps: the tactic derives a
        new fact, which is recorded as a visible line inserted before
        id. The line rule comes from the tactic's proof term (no method
        ever names a macro directly).         Auto-close of gaps the new fact
        proves is explicit (visible auto_close lines).
        """
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        prevs_pt = [ProofTerm.atom(prev, self.get_proof_item(prev).th) for prev in prevs]

        # Derive first: if the tactic fails, no line is inserted.
        pt = ftac.get_proof_term(args=args, prevs=prevs_pt)

        self.add_line_before(id, 1)
        self.set_line(id, pt.rule, args=pt.args, prevs=prevs, th=pt.th)
        self.line_meta[str(id)] = {'fact': True}

        id2 = id.incr_id(1)
        self._find_and_close(id2)
        return pt

    def _find_and_close(self, id2):
        """Explicit auto-close: if some preceding line proves the given
        gap, record the closure as a visible auto_close line."""
        new_id = self.find_goal(self.get_proof_item(id2).th, id2)
        if new_id is not None:
            self.set_line(id2, 'auto_close', prevs=[new_id],
                          th=self.get_proof_item(id2).th)


"""Global store for methods."""
global_methods: Dict[str, "Method"] = dict()

def has_method(name: str) -> bool:
    """Return whether the method with the given name exists and can be
    used in the current location of the theory.
    
    """
    if name in global_methods:
        method = global_methods[name]
        return method.limit is None or theory.thy.has_theorem(method.limit)
    else:
        return False

def get_method(name: str) -> "Method":
    """Return method with the given name."""
    assert has_method(name), "get_method: %s is not available" % name
    return global_methods[name]

def get_all_methods() -> Dict[str, "Method"]:
    """Return a dictionary mapping method names to methods."""
    res = dict()
    for name in global_methods:
        if has_method(name):
            res[name] = global_methods[name]
    return res

def get_method_sig():
    sig = dict()
    for name in global_methods:
        if has_method(name):
            sig[name] = global_methods[name].sig
    return sig

def get_method_list_params():
    """Return per-method list of params that are comma-separated lists.

    These are rendered as +/- dynamic fields in the frontend query dialog.
    Any Method subclass can declare ``list_params = {'names'}`` to opt in.
    """
    res = dict()
    for name in global_methods:
        if has_method(name):
            m = global_methods[name]
            lp = list(getattr(m, 'list_params', set()))
            if lp:
                res[name] = lp
    return res

def register_method(name):
    def decorator(method_cls):
        # Idempotent: skip if already registered (supports reloading theories).
        if name in global_methods:
            return method_cls
        global_methods[name] = method_cls()
        return method_cls
    return decorator


class Method:
    """Methods represent potential actions on the state."""
    list_params = set()  # param names that are comma-separated lists (rendered as +/- fields)
    def search(self, state: ProofState, id, prevs):
        """Search for parameters on which the method can be applied
        given the current proof state.
        
        """
        pass

    def display_step(self, state: ProofState, data):
        """Display the current step in pretty-printed form."""
        pass

    def apply(self, state: ProofState, id, args, prevs):
        """Apply the method on the current state using the given
        parameters. Return new proof state if successful.
        
        """
        pass


@register_method('cut')
class cut_method(Method):
    """Insert intermediate goal."""
    def __init__(self):
        self.sig = ['cut_goal']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        return []

    def display_step(self, state: ProofState, data):
        id = data['goal_id']
        with context.fresh_context(vars=state.get_vars(id)):
            goal = parser.parse_term(data.get('cut_goal', data.get('goal')))
        return pprint.N("have ") + printer.print_term(goal)

    def apply(self, state: ProofState, id, data, prevs):
        cur_item = state.get_proof_item(id)
        hyps = cur_item.th.hyps

        with context.fresh_context(vars=state.get_vars(id)):
            C = parser.parse_term(data.get('cut_goal', data.get('goal')))
            for v in C.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('Insert goal: extra variable %s' % v.name)

        state.add_line_before(id, 1)
        state.set_line(id, 'sorry', th=Thm(C, hyps))
        state.line_meta[str(id)] = {'origin': 'cut'}


@register_method('cases')
class cases_method(Method):
    """Case analysis."""
    def __init__(self):
        self.sig = ['case']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        return []

    def display_step(self, state: ProofState, data):
        id = data['goal_id']
        with context.fresh_context(vars=state.get_vars(id)):
            A = parser.parse_term(data['case'])
        return pprint.N("case ") + printer.print_term(A)

    def apply(self, state: ProofState, id, data, prevs):
        with context.fresh_context(vars=state.get_vars(id)):
            A = parser.parse_term(data['case'])
            for v in A.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('Apply case: extra variable %s' % v.name)

        state.apply_tactic(id, tactic.cases(), args=A)


@register_method('type_cases')
class type_cases_method(Method):
    """Case analysis on an expression of an inductive datatype.

    Uses the <tyname>_cases theorem generated by the datatype
    extension; one subgoal per constructor branch.

    data keys:
    - case: the case expression (must have a datatype type)
    - cases_thm: (optional) override the cases theorem name
    """
    def __init__(self):
        self.sig = ['case']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        return []

    def display_step(self, state: ProofState, data):
        id = data['goal_id']
        with context.fresh_context(vars=state.get_vars(id)):
            A = parser.parse_term(data['case'])
        return pprint.N("type cases ") + printer.print_term(A)

    def apply(self, state: ProofState, id, data, prevs):
        with context.fresh_context(vars=state.get_vars(id)):
            A = parser.parse_term(data['case'])
            for v in A.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('Apply type_cases: extra variable %s' % v.name)

        if data.get('cases_thm'):
            state.apply_tactic(id, tactic.datatype_cases(), args=(A, data['cases_thm']))
        else:
            state.apply_tactic(id, tactic.datatype_cases(), args=A)


@register_method('apply_prev')
class apply_prev(Method):
    """Apply previous fact."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        try:
            pt = tactic.apply_prev().get_proof_term(args=None, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)
            return [{"_goal": [gap.prop for gap in pt.gaps]}]
        except (AssertionError, matcher.MatchException):
            return []
        except theory.ParameterQueryException:
            # In this case, still suggest the result
            return [{}]

    def display_step(self, state: ProofState, data):
        return pprint.N("Apply fact (b)")

    def apply(self, state: ProofState, id, data, prevs):
        inst = Inst()
        with context.fresh_context(vars=state.get_vars(id)):
            for key, val in data.items():
                if key.startswith("param_"):
                    inst[key[6:]] = parser.parse_term(val)

        if inst:
            state.apply_tactic(id, tactic.apply_prev(), args=inst, prevs=prevs)
        else:
            state.apply_tactic(id, tactic.apply_prev(), prevs=prevs)


class rewrite_with_prev_impl(Method):
    """Rewrite using previous fact."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        try:
            cur_item = state.get_proof_item(id)
            prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
            pt = tactic.rewrite_goal_with_prev().get_proof_term(args=None, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)
        except (AssertionError, matcher.MatchException):
            return []
        else:
            return [{"_goal": [gap.prop for gap in pt.gaps]}]        

    def display_step(self, state: ProofState, data):
        return pprint.N("rewrite with fact")

    def apply(self, state: ProofState, id, args, prevs):
        state.apply_tactic(id, tactic.rewrite_goal_with_prev(), prevs=prevs)


class rewrite_thm_impl(Method):
    """Rewrite using a theorem."""
    def __init__(self):
        self.sig = ['theorem', 'sym']
        self.limit = None

    def search(self, state, id, prevs):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]

        results = []

        def search_thm(th_name, sym):
            try:
                sym_b = True if sym == 'true' else False
                pt = tactic.rewrite_goal(sym=sym_b).get_proof_term(args=th_name, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)
                th = theory.get_theorem(th_name, svar=False)
                results.append({"theorem": th_name, "sym": sym, "_goal": [gap.prop for gap in pt.gaps], "_thm": th.prop})
            except (AssertionError, matcher.MatchException) as e:
                pass

        # Pattern-net candidates (subterms of the goal), then dry-run.
        for th_name in fw_search.candidates_for(cur_item.th.prop, category='hint_rewrite'):
            search_thm(th_name, 'false')
        for th_name in fw_search.candidates_for(cur_item.th.prop, category='hint_rewrite_sym'):
            search_thm(th_name, 'true')

        return sorted(results, key=lambda d: d['theorem'])

    def display_step(self, state, data):
        if 'sym' in data and data['sym'] == 'true':
            return pprint.N(data['theorem'] + " (sym, r)")
        else:
            return pprint.N(data['theorem'] + " (r)")

    def apply(self, state, id, data, prevs):
        if 'sym' in data and data['sym'] == 'true':
            sym_b = True
        else:
            sym_b = False
        
        loc = data.get('loc', '')
        
        if loc:
            # Position-specific rewriting (single rewrite_goal_loc macro
            # line); loc format: "0" = function part, "1" = argument part,
            # "0.1" = argument of function, etc.
            state.apply_tactic(id, tactic.rewrite_goal_loc(sym=sym_b, loc=loc),
                               args=data['theorem'], prevs=prevs)
        else:
            # Full goal rewriting (original behavior)
            state.apply_tactic(id, tactic.rewrite_goal(sym=sym_b), args=data['theorem'], prevs=prevs)


class rewrite_fact_thm_impl(Method):
    """Rewrite fact using a theorem."""
    def __init__(self):
        self.sig = ['theorem', 'sym']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        results = []

        def search_thm(th_name, sym):
            try:
                sym_b = True if sym == 'true' else False
                pt = tactic.rewrite_fact_forward(sym=sym_b).get_proof_term(args=th_name, prevs=prevs)
                th = theory.get_theorem(th_name, svar=False)
                results.append({"theorem": th_name, "sym": sym, "_fact": [pt.th.prop], "_thm": th.prop})
            except (AssertionError, matcher.MatchException, InvalidDerivationException) as e:
                # print(e)
                pass

        # Pattern-net candidates (subterms of the fact being rewritten),
        # then dry-run.
        fact_prop = prevs[0].prop if prevs else None
        if fact_prop is not None:
            for th_name in fw_search.candidates_for(fact_prop, category='hint_rewrite'):
                search_thm(th_name, 'false')
            for th_name in fw_search.candidates_for(fact_prop, category='hint_rewrite_sym'):
                search_thm(th_name, 'true')

        return sorted(results, key=lambda d: d['theorem'])

    def display_step(self, state: ProofState, data):
        if 'sym' in data and data['sym'] == 'true':
            return pprint.N(data['theorem'] + " (sym, r)")
        else:
            return pprint.N(data['theorem'] + " (r)")

    def apply(self, state: ProofState, id, data, prevs):
        try:
            prev_pts = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
            sym_b = 'sym' in data and data['sym'] == 'true'
            tactic.rewrite_fact_forward(sym=sym_b).get_proof_term(args=data['theorem'], prevs=prev_pts)
        except InvalidDerivationException as e:
            raise e

        state.add_line_before(id, 1)
        if 'sym' in data and data['sym'] == 'true':
            state.set_line(id, 'rewrite_fact_sym', args=data['theorem'], prevs=prevs)
        else:
            state.set_line(id, 'rewrite_fact', args=data['theorem'], prevs=prevs)
        state.line_meta[str(id)] = {'fact': True}

        id2 = id.incr_id(1)
        state._find_and_close(id2)

class rewrite_fact_prev_impl(Method):
    """Rewrite fact using a previous equality."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        try:
            pt = tactic.rewrite_fact_with_prev_forward().get_proof_term(args=None, prevs=prevs)
            return [{"_fact": [pt.th.prop]}]
        except (AssertionError, matcher.MatchException):
            return []

    def display_step(self, state: ProofState, data):
        return pprint.N("rewrite fact with fact")

    def apply(self, state: ProofState, id, args, prevs):
        try:
            prev_pts = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
            tactic.rewrite_fact_with_prev_forward().get_proof_term(args=None, prevs=prev_pts)
        except AssertionError as e:
            raise e

        state.add_line_before(id, 1)
        state.set_line(id, 'rewrite_fact_with_prev', prevs=prevs)
        state.line_meta[str(id)] = {'fact': True}

        id2 = id.incr_id(1)
        state._find_and_close(id2)


class forward_thm_impl(Method):
    """Apply theorem in the forward direction."""
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]

        results = []

        def search_thm(th_name, min_prevs):
            if len(prevs) < min_prevs:
                return

            try:
                prev_pts = [ProofTerm.atom(p, t) for p, t in zip(prevs, prev_ths)]
                pt = tactic.apply_theorem_forward().get_proof_term(args=th_name, prevs=prev_pts)
                th = theory.get_theorem(th_name, svar=False)
                results.append({"theorem": th_name, "_fact": [pt.th.prop], "_thm": th.prop})
            except theory.ParameterQueryException as e:
                results.append({"theorem": th_name, "_needs_params": list(e.params)})
            except (AssertionError, matcher.MatchException):
                pass

        # Pattern-net candidates over the facts' subterms, then dry-run.
        cand = []
        seen = set()
        for prev_th in prev_ths:
            for th_name in fw_search.forward_candidates_for(prev_th.prop):
                if th_name not in seen:
                    seen.add(th_name)
                    cand.append(th_name)
        for th_name in cand:
            search_thm(th_name, min_prevs=1)

        return sorted(results, key=lambda d: d['theorem'])

    def display_step(self, state: ProofState, data):
        return pprint.N(data['theorem'] + " (f)")

    def apply(self, state: ProofState, id, data, prevs):
        inst = Inst()
        with context.fresh_context(vars=state.get_vars(id)):
            for key, val in data.items():
                if key.startswith("param_"):
                    if val != '':
                        inst[key[6:]] = parser.parse_term(val)

        provided = [k[6:] for k in data if k.startswith("param_")]
        prev_pts = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        pt = tactic.apply_theorem_forward().get_proof_term(
            args=(data['theorem'], inst, provided), prevs=prev_pts)

        state.add_line_before(id, 1)
        state.set_line(id, pt.rule, args=pt.args, prevs=prevs)
        state.line_meta[str(id)] = {'fact': True}

        id2 = id.incr_id(1)
        state._find_and_close(id2)


@register_method('rule')
class rule(Method):
    """Apply theorem in the backward direction."""
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]

        results = []

        def search_thm(th_name):
            try:
                pt = tactic.rule().get_proof_term(args=th_name, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)
                th = theory.get_theorem(th_name, svar=False)
                results.append({"theorem": th_name, "_goal": [gap.prop for gap in pt.gaps], "_thm": th.prop})
            except theory.ParameterQueryException:
                # In this case, still suggest the result
                results.append({"theorem": th_name})
            except (AssertionError, matcher.MatchException):
                pass

        # Pattern-net candidates (whole-goal skeleton), then dry-run.
        # Theorems carrying both hint_backward and hint_backward1 are
        # tried twice (matching the legacy behavior).
        for th_name in fw_search.candidates_for(cur_item.th.prop, category='hint_backward'):
            search_thm(th_name)
        if len(prevs) >= 1:
            for th_name in fw_search.candidates_for(cur_item.th.prop, category='hint_backward1'):
                search_thm(th_name)

        return sorted(results, key=lambda d: d['theorem'])

    def display_step(self, state: ProofState, data):
        return pprint.N(data['theorem'] + " (b)")

    def apply(self, state: ProofState, id, data, prevs):
        inst = Inst()
        with context.fresh_context(vars=state.get_vars(id)):
            for key, val in data.items():
                if key.startswith("param_"):
                    inst[key[6:]] = parser.parse_term(val)
        if inst:
            state.apply_tactic(id, tactic.rule(), args=(data['theorem'], inst), prevs=prevs)
        else:
            state.apply_tactic(id, tactic.rule(), args=data['theorem'], prevs=prevs)


@register_method('resolve')
class resolve(Method):
    """Resolve using a theorem ~A and a fact A."""
    def __init__(self):
        self.sig = ["theorem"]
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]

        results = []

        def search_thm(th_name):
            try:
                pt = tactic.resolve().get_proof_term(args=th_name, prevs=[ProofTerm.atom(id, cur_item.th)] + prevs)
                results.append({"theorem": th_name, "_goal": [gap.prop for gap in pt.gaps]})
            except (AssertionError, matcher.MatchException):
                pass

        for th_name in theory.thy.get_data("theorems"):
            if 'hint_resolve' in theory.thy.get_attributes(th_name):
                search_thm(th_name)

        return sorted(results, key=lambda d: d['theorem'])

    def display_step(self, state: ProofState, data):
        return pprint.N("Resolve using " + data['theorem'])

    def apply(self, state: ProofState, id, data, prevs):
        state.apply_tactic(id, tactic.resolve(), args=data['theorem'], prevs=prevs)


@register_method('accept')
class accept_method(Method):
    """Directly close the goal by referencing a theorem of the theory:
    conclusion unified with the goal, premises matched with the goal's
    assumptions, no subgoal produced. The closure is recorded as an
    explicit line.
    """
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        cur_item = state.get_proof_item(id)
        results = []

        def search_thm(th_name):
            try:
                pt = tactic.accept().get_proof_term(
                    args=th_name, prevs=[ProofTerm.atom(id, cur_item.th)])
                results.append({"theorem": th_name,
                                "_goal": [gap.prop for gap in pt.gaps]})
            except theory.ParameterQueryException as e:
                results.append({"theorem": th_name,
                                "_needs_params": list(e.params)})
            except (AssertionError, matcher.MatchException, TacticException):
                pass

        # Pattern-net candidates (whole-goal skeleton) across all hint
        # categories, deduplicated, then dry-run.
        cand = []
        seen = set()
        for c in fw_search.HINT_CATEGORIES:
            for th_name in fw_search.candidates_for(cur_item.th.prop, category=c):
                if th_name not in seen:
                    seen.add(th_name)
                    cand.append(th_name)
        for th_name in cand:
            search_thm(th_name)

        return sorted(results, key=lambda d: d['theorem'])

    def display_step(self, state: ProofState, data):
        return pprint.N("accept " + data['theorem'])

    def apply(self, state: ProofState, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("accept: theorem required")
        # The expansion covers the goal line with the apply line (the
        # conclusion), so the goal is closed by the exported lines.
        state.apply_tactic(id, tactic.accept(), args=thm_name, prevs=prevs)


@register_method('intro')
class intro(Method):
    """Introducing variables and assumptions."""
    list_params = {'names'}
    def __init__(self):
        self.sig = []
        self.limit = None
        self.no_order = True

    def search(self, state: ProofState, id, prevs):
        if len(prevs) > 0:
            return []

        goal_th = state.get_proof_item(id).th
        if goal_th.prop.is_forall():
            return [{}]
        elif goal_th.prop.is_implies():
            return [{"names": ""}]
        else:
            return []

    def display_step(self, state: ProofState, data):
        res = "introduction"
        if 'names' in data and data['names'] != "":
            names = [name.strip() for name in data['names'].split(',')]
            if len(names) > 1:
                res += " with names " + ", ".join(names)
            else:
                res += " with name " + ", ".join(names)
        return pprint.N(res)

    def apply(self, state: ProofState, id, data, prevs):
        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"

        prop = cur_item.th.prop
        assert prop.is_implies() or prop.is_forall(), "introduction"

        if prop.is_forall() and 'names' not in data:
            # Count nested foralls so frontend can pre-fill the right
            # number of name fields.
            count = 0
            p = prop
            while p.is_forall():
                count += 1
                p = p.arg.body
            raise theory.ParameterQueryException(['names'], hints={'names': {'count': count}})

        intros_tac = tactic.intros()
        if 'names' in data and data['names'] != '':
            names = [name.strip() for name in data['names'].split(",")]
        else:
            names = []
        pt = intros_tac.get_proof_term(args=names, prevs=[ProofTerm.atom(id, cur_item.th)])

        cur_item.rule = "subproof"
        cur_item.subproof = pt.export(prefix=id)
        state.check_proof(compute_only=True)

        # Exhibit auto-close of the subgoal lines: those already proved
        # Exhibit auto-close of the subgoal lines: those already proved
        # by a preceding line are recorded as visible auto_close lines.
        for item in cur_item.subproof.items:
            state._find_and_close(item.id)


@register_method('elim')
class elim(Method):
    """Make use of an exists fact."""
    list_params = {'names'}
    def __init__(self):
        self.sig = ['names']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            if prev_th.prop.is_exists():
                return [{}]

        return []

    def display_step(self, state: ProofState, data):
        return pprint.N("Instantiate exists fact")

    def apply(self, state: ProofState, id, data, prevs):
        assert len(prevs) == 1, "elim"

        # Parse the list of variable names
        with context.fresh_context(vars=state.get_vars(id)):
            names = [nm.strip() for nm in data['names'].split(',')]
            for nm in names:
                if nm in context.ctxt.vars:
                    raise AssertionError("elim: duplicate name %s" % nm)

        exists_item = state.get_proof_item(prevs[0])
        exists_prop = exists_item.th.prop
        assert exists_prop.is_exists(), "elim"

        vars, body = logic.strip_exists(exists_prop, names)

        # Gap theorem BEFORE its hyps are extended (needed by the
        # elim_exists tactic).
        gap_th = state.get_proof_item(id).th

        # Visible structure: one line per fresh variable plus the
        # assumption of the exists body, inserted before the gap.
        state.add_line_before(id, len(vars) + 1)
        for i, var in enumerate(vars):
            state.set_line(id.incr_id(i), 'variable', args=(var.name, var.T), prevs=[])
        state.set_line(id.incr_id(len(vars)), 'assume', args=body, prevs=[])

        # Locate the enclosing intros line; the lines in between
        # (including the gap) get their hyps extended with the body.
        intros_item = None
        i = len(vars) + 1
        while intros_item is None:
            try:
                item = state.get_proof_item(id.incr_id(i))
            except ProofStateException:
                raise AssertionError("elim: cannot find intros at the end")
            if item.rule == 'intros':
                intros_item = item
            else:
                state.set_line(id.incr_id(i), item.rule, args=item.args,
                               prevs=item.prevs,
                               th=Thm(item.th.prop, item.th.hyps, body))
                i += 1

        # Rewire the enclosing intros line: the exists fact, fresh
        # variables and the body assumption are inserted before the
        # continuation; the exists prop is prepended to the args.
        new_intros_ids = [prevs[0]] + [id.incr_id(k) for k in range(len(vars) + 1)]
        intros_item.args = [exists_prop] + \
            (list(intros_item.args) if intros_item.args else [])
        intros_item.prevs = intros_item.prevs[:-1] + new_intros_ids + \
            [intros_item.prevs[-1]]
        state.check_proof(compute_only=True)

        # Derive the rewired intros line as a CHECKED proof term and
        # assert the committed line matches it. The wiring above is the
        # only state-level part; its correctness is kernel-verified
        # here against the tactic-derived proof term.
        exists_pt = ProofTerm.atom(prevs[0], exists_item.th)
        wired_prev_pts = [ProofTerm.atom(p, state.get_proof_item(p).th)
                          for p in intros_item.prevs]
        pt = tactic.elim_exists().get_proof_term(
            args=(names, exists_pt, wired_prev_pts, intros_item.args),
            prevs=[ProofTerm.atom(id, gap_th)])
        assert intros_item.th.prop == pt.th.prop and \
            set(intros_item.th.hyps) == set(pt.th.hyps), \
            "elim: rewired intros line does not match derived proof term"


class inst_forall_impl(Method):
    """Elimination of forall statement."""
    def __init__(self):
        self.sig = ['s']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            if prev_th.prop.is_forall():
                return [{}]

        return []

    def display_step(self, state: ProofState, data):
        return pprint.N("Forall elimination")

    def apply(self, state: ProofState, id, data, prevs):
        with context.fresh_context(vars=state.get_vars(id)):
            t = parser.parse_term(data['s'])

            for v in t.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('Forall elimination: extra variable %s' % v.name)

        prev_pts = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        tactic.forall_elim_forward().get_proof_term(args=t, prevs=prev_pts)
        state.add_line_before(id, 1)
        state.set_line(id, 'forall_elim_gen', args=t, prevs=prevs)
        state.line_meta[str(id)] = {'fact': True}


class inst_exists_impl(Method):
    """Instantiate an exists goal."""
    def __init__(self):
        self.sig = ['s']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        if len(prevs) > 0:
            return []

        cur_th = state.get_proof_item(id).th
        if cur_th.prop.is_exists():
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("Instantiate exists goal")

    def apply(self, state: ProofState, id, data, prevs):
        with context.fresh_context(vars=state.get_vars(id)):
            t = parser.parse_term(data['s'])

            for v in t.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('Instantiate exists: extra variable %s' % v.name)

        state.apply_tactic(id, tactic.inst_exists_goal(), args=t, prevs=[])


@register_method('induct')
class induct(Method):
    """Apply induction."""
    def __init__(self):
        self.sig = ['theorem', 'var']
        self.limit = None
        self.no_order = True

    def search(self, state: ProofState, id, prevs):
        cur_th = state.get_proof_item(id).th
#        if len(cur_th.hyps) > 0:
#            return []

        results = []
        for name, th in theory.thy.get_data("theorems").items():
            if 'var_induct' not in theory.thy.get_attributes(name):
                continue

            var_T = th.concl.arg.T
            vars = [v for v in cur_th.prop.get_vars() if v.T == var_T]
            for v in vars:
                results.append({'theorem': name, 'var': v.name})
        return results

    def display_step(self, state: ProofState, data):
        if 'var' in data:
            return pprint.N("Induction " + data['theorem'] + " var: " + data['var'])
        else:
            return pprint.N("Induction " + data['theorem'])

    def apply(self, state: ProofState, id, data, prevs):
        # Find variable
        with context.fresh_context(vars=state.get_vars(id)):
            var_name = data.get('var') or data.get('param_var')
            assert var_name in context.ctxt.vars, "induction: cannot find variable."
            var = Var(var_name, context.ctxt.vars[var_name])

        thm_name = data.get('theorem') or data.get('param_theorem')
        state.apply_tactic(id, tactic.var_induct(), args=(thm_name, var))


@register_method('var')
class var(Method):
    """Create new variable."""
    def __init__(self):
        self.sig = ['name', 'type']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        return []

    def display_step(self, state: ProofState, data):
        T = parser.parse_type(data['type'])
        return pprint.N("Variable " + data['name'] + " :: ") + printer.print_type(T)

    def apply(self, state: ProofState, id, data, prevs):
        state.add_line_before(id, 1)
        T = parser.parse_type(data['type'])
        state.set_line(id, 'variable', args=(data['name'], T), prevs=[])


class forward_fact_impl(Method):
    """When one of the prevs is an forall/implies fact, apply that fact
    to the remaining prevs.

    """
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]

        try:
            prev_pts = [ProofTerm.atom(p, t) for p, t in zip(prevs, prev_ths)]
            pt = tactic.apply_fact_forward().get_proof_term(args=None, prevs=prev_pts)
            return [{"_fact": [pt.th.prop]}]
        except (AssertionError, matcher.MatchException):
            return []

    def display_step(self, state: ProofState, data):
        return pprint.N("Apply fact (f) %s onto %s" % (data['fact_ids'][0], ", ".join(data['fact_ids'][1:])))

    def apply(self, state: ProofState, id, data, prevs):
        prev_pts = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        tactic.apply_fact_forward().get_proof_term(args=None, prevs=prev_pts)
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_fact', prevs=prevs)
        state.line_meta[str(id)] = {'fact': True}


# ==================== Unified vocabulary methods ====================
# The interactive proof language: a small orthogonal set of methods.
# Legacy names recorded in .pyhol proofs resolve here through
# METHOD_ALIASES (replay only); the interactive surface exposes only
# these names. Methods derive proof content exclusively through the
# checked state entries: apply_tactic / apply_macro / apply_forward.

# Internal single-mode implementations, merged into the dispatchers
# below (kept verbatim for replay-exact behavior).
_rw_goal_thm = rewrite_thm_impl()
_rw_goal_prev = rewrite_with_prev_impl()
_rw_fact_thm = rewrite_fact_thm_impl()
_rw_fact_prev = rewrite_fact_prev_impl()
_fwd_step = forward_thm_impl()
_apply_fact = forward_fact_impl()
_inst_exists = inst_exists_impl()
_forall_elim = inst_forall_impl()


@register_method('rewrite')
class rewrite(Method):
    """Rewrite a goal or a fact.

    Mode is inferred from the state shape (recorded steps carry no
    mode markers): the line at id being a gap means goal mode; the
    absence of a theorem argument means the rewrite rule is a selected
    equality fact. Explicit 'target'/'source' keys override inference.
    NOTE: fact rewrites targeting a gap position must pass
    target='fact' explicitly (a gap id alone is ambiguous); migrated
    recorded steps carry the marker.

    data keys:
    - theorem: rewrite rule (omit when rewriting with a fact)
    - sym: 'true' for the symmetric direction
    - loc: goal subterm position, e.g. "0", "1", "0.1" (goal mode only)
    """
    def __init__(self):
        self.sig = ['theorem', 'sym']
        self.limit = None

    def _mode(self, state, id, data):
        target = data.get('target')
        if target is None:
            target = 'goal' if state.get_proof_item(id).rule == 'sorry' else 'fact'
        source = data.get('source')
        if source is None:
            source = 'thm' if data.get('theorem') else 'prev'
        return target, source

    def search(self, state, id, prevs):
        results = _rw_goal_thm.search(state, id, prevs)
        if prevs:
            # Each mode is tried defensively: a mode that does not fit
            # the current facts (e.g. a no-effect check raising
            # InvalidDerivationException) simply contributes nothing.
            for mode_fn, marker in ((_rw_goal_prev, {'source': 'prev'}),
                                    (_rw_fact_thm, {'target': 'fact'}),
                                    (_rw_fact_prev, {'target': 'fact', 'source': 'prev'})):
                try:
                    for r in mode_fn.search(state, id, prevs):
                        r.update(marker)
                        results.append(r)
                except Exception:
                    pass
        return results

    def display_step(self, state, data):
        if not data.get('theorem'):
            return pprint.N("rewrite with fact")
        if 'sym' in data and data['sym'] == 'true':
            return pprint.N(data['theorem'] + " (sym, r)")
        else:
            return pprint.N(data['theorem'] + " (r)")

    def apply(self, state, id, data, prevs):
        target, source = self._mode(state, id, data)
        if target == 'fact':
            # Fact mode: prevs[0] is the fact being rewritten; the
            # remaining facts serve as conditions of the rewrite rule.
            if source == 'prev':
                _rw_fact_prev.apply(state, id, data, prevs)
            else:
                _rw_fact_thm.apply(state, id, data, prevs)
        else:
            if source == 'prev':
                _rw_goal_prev.apply(state, id, data, prevs)
            else:
                _rw_goal_thm.apply(state, id, data, prevs)


@register_method('forward')
class forward(Method):
    """Forward reasoning: derive a new fact line.

    Mode is inferred: with a theorem argument the theorem is applied to
    the selected facts (zero facts allowed); without one, the first
    selected fact (a forall/implies fact) is applied to the others.

    data keys:
    - theorem: theorem to apply (omit for fact-on-facts mode)
    """
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        results = _fwd_step.search(state, id, prevs)
        if prevs:
            for r in _apply_fact.search(state, id, prevs):
                r['source'] = 'fact'
                results.append(r)
        return results

    def display_step(self, state, data):
        if data.get('theorem'):
            return pprint.N(data['theorem'] + " (f)")
        return pprint.N("Apply fact (f)")

    def apply(self, state, id, data, prevs):
        if data.get('theorem'):
            _fwd_step.apply(state, id, data, prevs)
        else:
            _apply_fact.apply(state, id, data, prevs)


@register_method('inst')
class inst(Method):
    """Instantiation.

    Mode is inferred: with selected facts, instantiate a forall fact
    with a term; without, provide a witness for an exists goal.
    Explicit 'target' key overrides inference.

    data keys: s (the term/witness).
    """
    def __init__(self):
        self.sig = ['s']
        self.limit = None

    def search(self, state, id, prevs):
        results = []
        for r in _inst_exists.search(state, id, prevs):
            r['target'] = 'goal'
            results.append(r)
        if prevs:
            for r in _forall_elim.search(state, id, prevs):
                r['target'] = 'fact'
                results.append(r)
        return results

    def display_step(self, state, data):
        if data.get('target') == 'fact':
            return pprint.N("Forall elimination")
        return pprint.N("Instantiate exists goal")

    def apply(self, state, id, data, prevs):
        target = data.get('target') or ('fact' if prevs else 'goal')
        if target == 'fact':
            _forall_elim.apply(state, id, data, prevs)
        else:
            _inst_exists.apply(state, id, data, prevs)


@register_method('assumption')
class assumption(Method):
    """Close a goal whose proposition is one of its own assumptions."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        cur_th = state.get_proof_item(id).th
        if cur_th.prop in cur_th.hyps:
            return [{}]
        return []

    def display_step(self, state, data):
        return pprint.N("assumption")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.assumption())


@register_method('refl')
class refl(Method):
    """Prove an equality goal t = t by reflexivity."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        cur_item = state.get_proof_item(id)
        prop = cur_item.th.prop
        if prop.is_equals() and prop.arg1 == prop.arg:
            return [{}]
        return []

    def display_step(self, state, data):
        return pprint.N("reflexive")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.reflexive())


@register_method('eq_intro')
class eq_intro(Method):
    """Prove an equality goal A = B by proving A --> B and B --> A."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        cur_item = state.get_proof_item(id)
        prop = cur_item.th.prop
        if prop.is_equals():
            return [{}]
        return []

    def display_step(self, state, data):
        return pprint.N("equal_intr")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.equal_intr())


@register_method('trans')
class trans_method(Method):
    """Prove an equality goal s = t by choosing a middle term u:
    the subgoals are s = u and u = t (TRANS_TAC)."""
    def __init__(self):
        self.sig = ['s']
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        cur_item = state.get_proof_item(id)
        prop = cur_item.th.prop
        if prop.is_equals() and prop.arg1 != prop.arg:
            return [{'_needs_params': ['s']}]
        return []

    def display_step(self, state, data):
        return pprint.N("trans via " + data['s'])

    def apply(self, state, id, data, prevs):
        with context.fresh_context(vars=state.get_vars(id)):
            u = parser.parse_term(data['s'])
            for v in u.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('trans: extra variable %s' % v.name)
        state.apply_tactic(id, tactic.trans(), args=u)


@register_method('unfold')
class unfold(Method):
    """Unfold (or fold, with sym=true) a definition."""
    def __init__(self):
        self.sig = ['theorem', 'sym']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        if 'sym' in data and data['sym'] == 'true':
            return pprint.N("fold " + data.get('theorem', '?'))
        return pprint.N("unfold " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("unfold: theorem required")
        sym_b = 'sym' in data and data['sym'] == 'true'
        state.apply_tactic(id, tactic.unfold(sym=sym_b), args=thm_name, prevs=prevs)


"""Registry of normalization macros by type (replaces the former
hardcoded NatType/RealType/IntType dispatch in norm/eval/linarith).
Domains register their normalizer here; the norm method only does the
lookup through the checked apply_macro entry."""
norm_registry = dict()

def register_norm(T, macro_name: str):
    norm_registry[T] = macro_name

from kernel.type import NatType, RealType, IntType
register_norm(NatType, 'nat_norm')
register_norm(RealType, 'real_norm')
register_norm(IntType, 'int_norm')


@register_method('norm')
class norm(Method):
    """Normalize an equality goal using the domain normalizer
    registered for its type."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        try:
            cur_item = state.get_proof_item(id)
            goal_prop = cur_item.th.prop
            if not goal_prop.is_equals():
                return []
            return [{}]
        except Exception:
            return []

    def display_step(self, state, data):
        return pprint.N("norm")

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        goal_prop = cur_item.th.prop
        if goal_prop.is_equals():
            T = goal_prop.lhs.get_type()
        else:
            T = goal_prop.get_type()
        macro_name = norm_registry.get(T)
        if macro_name is None or not theory.has_macro(macro_name):
            raise AssertionError(
                "norm: no normalizer registered for type %s" % str(T))
        state.apply_macro(id, macro_name)


@register_method('simp')
class simp(Method):
    """Simplify the goal by rewriting with all hint_rewrite theorems
    of the current theory, iterating to a fixed point (bounded).

    The whole simplification is committed as a single visible simp
    macro line (the conv chain expands inside the kernel on check).
    Only unconditional rewrite theorems participate (conditional ones
    are left to rewrite with explicit facts). Fails when nothing can
    be simplified (must-change semantics).
    """
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        try:
            cur_item = state.get_proof_item(id)
            if cur_item.th.prop.is_var():
                return []
            return [{}]
        except Exception:
            return []

    def display_step(self, state, data):
        return pprint.N("simp")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.simp(), prevs=prevs)


def register_macro_method(name: str, *, limit=None):
    """Register a method auto-generated from a macro.

    The standard channel exposing a domain macro as an interactive
    method: search is gated by the macro's can_eval (when defined),
    and apply goes through the checked state.apply_macro entry point.
    No hand-written boilerplate is needed per macro.
    """
    class _macro_method(Method):
        def __init__(self):
            self.sig = []
            self.limit = limit

        def search(self, state, id, prevs, data=None):
            if data:
                return [data]
            if len(prevs) != 0:
                return []
            if not theory.has_macro(name):
                return []
            macro = theory.get_macro(name)
            if hasattr(macro, 'can_eval'):
                cur_th = state.get_proof_item(id).th
                if macro.can_eval(cur_th.prop):
                    return [{}]
                return []
            return [{}]

        def display_step(self, state, data):
            return pprint.N(name + ": ") + pprint.KWGreen("(solves)")

        def apply(self, state, id, data, prevs):
            assert len(prevs) == 0, name
            state.apply_macro(id, name)

    _macro_method.__name__ = name + '_method'
    return register_method(name)(_macro_method)



def apply_method(state: ProofState, step):
    """Apply a method to the state. Here data is a dictionary containing
    all necessary information.

    """
    method = get_method(step['method_name'])
    goal_id = ItemID(step['goal_id'])
    fact_ids = [ItemID(fact_id) for fact_id in step['fact_ids']] \
        if 'fact_ids' in step and step['fact_ids'] else []
    assert all(goal_id.can_depend_on(fact_id) for fact_id in fact_ids), \
        "apply_method: illegal dependence."
    return method.apply(state, goal_id, step, fact_ids)

def output_step(state: ProofState, step):
    """Obtain the string explaining the step in the user interface."""
    try:
        method = get_method(step['method_name'])
        res = method.display_step(state, step)
    except Exception as e:
        res = pprint.N(step['method_name'])
    goal = step.get('goal_id', str(step.get('goal', '')))
    res += pprint.N(' on ' + goal)
    facts = step.get('fact_ids') or [str(f) for f in step.get('facts', [])]
    if facts:
        res += pprint.N(' using ' + ','.join(str(f) for f in facts))
    return res

def output_hint(state: ProofState, step):
    method = get_method(step['method_name'])
    res = method.display_step(state, step)
    if '_goal' in step:
        if step['_goal']:
            goals = [printer.print_term(t) for t in step['_goal']]
            res += pprint.KWRed(" goal ") + printer.commas_join(goals)
        else:
            res += pprint.KWGreen(" (solves)")

    if '_fact' in step and len(step['_fact']) > 0:
        facts = [printer.print_term(t) for t in step['_fact']]
        res += pprint.KWGreen(" fact ") + printer.commas_join(facts)

    return res

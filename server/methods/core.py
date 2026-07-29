# Author: Bohua Zhan

from typing import Dict
import copy
import itertools
import traceback

from kernel.type import TyInst
from kernel import term
from kernel.term import Term, Var, Inst
from kernel.thm import Thm, InvalidDerivationException
from kernel import report
from kernel.proof import ProofItem, ItemID, Proof, ProofStateException
from kernel import theory
from kernel.proofterm import ProofTerm
from logic import matcher
from logic import logic
from logic import context
from logic import tactic
from logic.tactic import Tactic
from logic import conv
from logic.macros.core import trivial_macro, apply_theorem_macro, rewrite_fact_macro, rewrite_fact_with_prev_macro, apply_fact_macro
from syntax import parser, printer, pprint
from syntax.settings import settings, global_setting


class ProofState():
    """Represents proof state on the server side."""

    def __init__(self):
        """Empty proof state."""
        self.vars = []
        self.prf = Proof()
        self.rpt = None

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
                    if item.th is not None and item.th.can_prove(concl):
                        return item.id
                prf = prf.items[n].subproof
        except (AttributeError, IndexError):
            raise ProofStateException

    def apply_search(self, id, method: "Method", prevs=None):
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        return method.search(self, id, prevs)
    
    def search_method(self, id, prevs):
        """Perform search for each method."""
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        results = []
        all_methods = get_all_methods()
        for name in all_methods:
            cur_method = all_methods[name]
            if hasattr(cur_method, 'no_order'):
                test_prevs = [prevs]
            else:
                test_prevs = itertools.permutations(prevs)
            for perm_prevs in test_prevs:
                res = cur_method.search(self, id, perm_prevs)
                for r in res:
                    r['method_name'] = name
                    r['goal_id'] = str(id)
                    if prevs:
                        r['fact_ids'] = list(str(id) for id in perm_prevs)
                    with global_setting(unicode=True, highlight=True):
                        r['display'] = output_hint(self, r)
                results.extend(res)

        # If there is an element in results that solves the goal,
        # output only results that solves.
        if any('_goal' in r and len(r['_goal']) == 0 for r in results):
            results = list(filter(lambda r: '_goal' in r and len(r['_goal']) == 0, results))
        return results

    def apply_tactic(self, id, tactic: Tactic, args=None, prevs=None):
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        prevs = [ProofTerm.atom(prev, self.get_proof_item(prev).th) for prev in prevs]
        
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_tactic: id is not a gap"

        pt = tactic.get_proof_term(cur_item.th, args=args, prevs=prevs)
        
        # When the tactic returns an atom, the fact directly proves the goal.
        # Find the fact's proof item and replace the sorry with it.
        if pt.rule == 'atom':
            fact_id = pt.args  # ItemID of the fact
            # Set the sorry line's theorem to match, then replace
            self.set_line(id, 'sorry', th=pt.th)
            fact_item = self.get_proof_item(fact_id)
            if fact_item.th is not None and fact_item.th.can_prove(cur_item.th):
                self.replace_id(id, fact_id)
            return
        
        new_prf = pt.export(prefix=id, subproof=False)

        self.add_line_before(id, len(new_prf.items) - 1)
        for i, item in enumerate(new_prf.items):
            cur_id = item.id
            prf = self.prf.get_parent_proof(cur_id)
            prf.items[cur_id.last()] = item
        self.check_proof(compute_only=True)

        # Test if the goals are already proved:
        for item in new_prf.items:
            if item.rule == 'sorry':
                new_id = self.find_goal(self.get_proof_item(item.id).th, item.id)
                if new_id is not None:
                    self.replace_id(item.id, new_id)

        # Resolve trivial subgoals
        for item in new_prf.items:
            if item.rule == 'sorry':
                if trivial_macro().can_eval(item.th.prop):
                    self.set_line(item.id, 'trivial', args=item.th.prop)

    def parse_steps(self, steps):
        """Parse and apply a list of steps to self.

        Return the output from the list of steps.

        """
        history = []
        for step in steps:
            with global_setting(unicode=True, highlight=True):
                step_output = output_step(self, step)
            history.append({
                'step_output': step_output,
                'goal_id': step['goal_id'],
                'fact_ids': step.get('fact_ids', [])
            })
            try:
                apply_method(self, step)
                self.check_proof(compute_only=True)
            except Exception as e:
                history[-1]['error'] = {
                    'err_type': e.__class__.__name__,
                    'err_str': str(e),
                    'trace': traceback.format_exc()
                }

        return history


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

def register_method(name):
    def decorator(method_cls):
        # Idempotent: skip if already registered (supports reloading theories).
        if name in global_methods:
            return method_cls
        global_methods[name] = method_cls()
        return method_cls
    return decorator


def _loc_to_conv(loc, base_cv):
    """Convert a location string to a conv combinator.
    
    loc format:
    - "0": go to function part of f(x) → fun_conv
    - "1": go to argument part of f(x) → arg_conv
    - "0.1": argument of function → fun_conv(arg_conv(...))
    - "1.0": function of argument → arg_conv(fun_conv(...))
    
    Each digit selects which part of a Comb(f, a) to descend into.
    """
    cv = base_cv
    for digit in reversed(loc.split('.')):
        if digit == '0':
            cv = conv.fun_conv(cv)
        elif digit == '1':
            cv = conv.arg_conv(cv)
        else:
            raise AssertionError("loc: invalid digit '%s', expected 0 or 1" % digit)
    return cv


class Method:
    """Methods represent potential actions on the state."""
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
        self.sig = ['goal']
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        return []

    def display_step(self, state: ProofState, data):
        id = data['goal_id']
        with context.fresh_context(vars=state.get_vars(id)):
            goal = parser.parse_term(data['goal'])
        return pprint.N("have ") + printer.print_term(goal)

    def apply(self, state: ProofState, id, data, prevs):
        cur_item = state.get_proof_item(id)
        hyps = cur_item.th.hyps

        with context.fresh_context(vars=state.get_vars(id)):
            C = parser.parse_term(data['goal'])
            for v in C.get_vars():
                if v.name not in context.ctxt.vars:
                    raise AssertionError('Insert goal: extra variable %s' % v.name)

        state.add_line_before(id, 1)
        state.set_line(id, 'sorry', th=Thm(C, hyps))


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
            pt = tactic.apply_prev().get_proof_term(cur_item.th, args=None, prevs=prevs)
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


@register_method('rewrite_goal_with_prev')
class rewrite_goal_with_prev(Method):
    """Rewrite using previous fact."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        try:
            cur_item = state.get_proof_item(id)
            prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
            pt = tactic.rewrite_goal_with_prev().get_proof_term(cur_item.th, args=None, prevs=prevs)
        except (AssertionError, matcher.MatchException):
            return []
        else:
            return [{"_goal": [gap.prop for gap in pt.gaps]}]        

    def display_step(self, state: ProofState, data):
        return pprint.N("rewrite with fact")

    def apply(self, state: ProofState, id, args, prevs):
        state.apply_tactic(id, tactic.rewrite_goal_with_prev(), prevs=prevs)


@register_method('rewrite_goal')
class rewrite_goal(Method):
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
                pt = tactic.rewrite_goal(sym=sym_b).get_proof_term(cur_item.th, args=th_name, prevs=prevs)
                results.append({"theorem": th_name, "sym": sym, "_goal": [gap.prop for gap in pt.gaps]})
            except (AssertionError, matcher.MatchException) as e:
                pass

        for th_name in theory.thy.get_data("theorems"):
            if 'hint_rewrite' in theory.thy.get_attributes(th_name):
                search_thm(th_name, 'false')
            if 'hint_rewrite_sym' in theory.thy.get_attributes(th_name):
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
            # Position-specific rewriting using conv combinators
            # loc format: "0" = function part, "1" = argument part
            # "0.1" = argument of function, etc.
            thm = theory.thy.get_theorem(data['theorem'])
            base_cv = conv.rewr_conv(thm, sym=sym_b)
            cv = _loc_to_conv(loc, base_cv)
            cv = conv.then_conv(cv, conv.beta_norm_conv())
            state.apply_tactic(id, tactic.rewrite_goal_with_conv(cv), prevs=prevs)
        else:
            # Full goal rewriting (original behavior)
            state.apply_tactic(id, tactic.rewrite_goal(sym=sym_b), args=data['theorem'], prevs=prevs)


@register_method('rewrite_fact')
class rewrite_fact(Method):
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
                pt = rewrite_fact_macro(sym=sym_b).get_proof_term(th_name, prevs)
                results.append({"theorem": th_name, "sym": sym, "_fact": [pt.prop]})
            except (AssertionError, matcher.MatchException, InvalidDerivationException) as e:
                # print(e)
                pass

        for th_name in theory.thy.get_data("theorems"):
            if 'hint_rewrite' in theory.thy.get_attributes(th_name):
                search_thm(th_name, 'false')
            if 'hint_rewrite_sym' in theory.thy.get_attributes(th_name):
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
            pt = rewrite_fact_macro(sym=sym_b).get_proof_term(data['theorem'], prev_pts)
        except InvalidDerivationException as e:
            raise e

        state.add_line_before(id, 1)
        if 'sym' in data and data['sym'] == 'true':
            state.set_line(id, 'rewrite_fact_sym', args=data['theorem'], prevs=prevs)
        else:
            state.set_line(id, 'rewrite_fact', args=data['theorem'], prevs=prevs)

        id2 = id.incr_id(1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)


@register_method('rewrite_fact_with_prev')
class rewrite_fact_with_prev(Method):
    """Rewrite fact using a previous equality."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        prevs = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
        try:
            macro = rewrite_fact_with_prev_macro()
            pt = macro.get_proof_term(args=None, pts=prevs)
            return [{"_fact": [pt.prop]}]
        except (AssertionError, matcher.MatchException):
            return []

    def display_step(self, state: ProofState, data):
        return pprint.N("rewrite fact with fact")

    def apply(self, state: ProofState, id, args, prevs):
        try:
            prev_pts = [ProofTerm.atom(prev, state.get_proof_item(prev).th) for prev in prevs]
            pt = rewrite_fact_with_prev_macro().get_proof_term(None, prev_pts)
        except AssertionError as e:
            raise e

        state.add_line_before(id, 1)
        state.set_line(id, 'rewrite_fact_with_prev', prevs=prevs)

        id2 = id.incr_id(1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)


@register_method('apply_forward_step')
class apply_forward_step(Method):
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
                macro = apply_theorem_macro()
                res_th = macro.eval(th_name, prev_ths)
                results.append({"theorem": th_name, "_fact": [res_th.prop]})
            except theory.ParameterQueryException:
                results.append({"theorem": th_name})
            except (AssertionError, matcher.MatchException):
                pass

        for th_name in theory.thy.get_data("theorems"):
            if 'hint_forward' in theory.thy.get_attributes(th_name):
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

        th = theory.get_theorem(data['theorem'])

        # Check whether to ask for parameters
        As, C = th.prop.strip_implies()
        match_svars = term.get_svars(As[:len(prevs)])
        all_svars = th.prop.get_svars()
        param_svars = [v for v in all_svars if v not in match_svars and 'param_' + v.name not in data]
        if param_svars:
            raise theory.ParameterQueryException(list("param_" + v.name for v in param_svars))

        # First test apply_theorem
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        macro = apply_theorem_macro(with_inst=True)
        res_th = macro.eval((data['theorem'], inst), prev_ths)

        state.add_line_before(id, 1)
        if inst:
            state.set_line(id, 'apply_theorem_for', args=(data['theorem'], inst), prevs=prevs)
        else:
            state.set_line(id, 'apply_theorem', args=data['theorem'], prevs=prevs)

        id2 = id.incr_id(1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)


@register_method('apply_backward_step')
class apply_backward_step(Method):
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
                pt = tactic.rule().get_proof_term(cur_item.th, args=th_name, prevs=prevs)
                results.append({"theorem": th_name, "_goal": [gap.prop for gap in pt.gaps]})
            except theory.ParameterQueryException:
                # In this case, still suggest the result
                results.append({"theorem": th_name})
            except (AssertionError, matcher.MatchException):
                pass

        for th_name in theory.thy.get_data("theorems"):
            if 'hint_backward' in theory.thy.get_attributes(th_name) or \
                ('hint_backward1' in theory.thy.get_attributes(th_name) and len(prevs) >= 1):
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


@register_method('apply_resolve_step')
class apply_resolve_step(Method):
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
                pt = tactic.resolve().get_proof_term(cur_item.th, args=th_name, prevs=prevs)
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


@register_method('introduction')
class introduction(Method):
    """Introducing variables and assumptions."""
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
            raise theory.ParameterQueryException(['names'])

        intros_tac = tactic.intros()
        if 'names' in data and data['names'] != '':
            names = [name.strip() for name in data['names'].split(",")]
        else:
            names = []
        pt = intros_tac.get_proof_term(cur_item.th, args=names)

        cur_item.rule = "subproof"
        cur_item.subproof = pt.export(prefix=id)
        state.check_proof(compute_only=True)

        # Test if the goal is already proved
        for item in cur_item.subproof.items:
            new_id = state.find_goal(state.get_proof_item(item.id).th, item.id)
            if new_id is not None:
                state.replace_id(item.id, new_id)


@register_method('revert_intro')
class revert_intro(Method):
    """Reverse an introduction."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        return []

    def display_step(self, state: ProofState, data):
        return pprint.N("revert intro")

    def apply(self, state: ProofState, id, data, prevs):
        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "revert intro: id is not a gap"

        assert len(prevs) == 1, "revert intro: prevs must have length one"

        pt = state.get_proof_item(prevs[0])
        assert pt.rule == 'assume', "revert_intro: prev is not assume"
        state.set_line(id, 'sorry', th=Thm.implies_intr(pt.th.prop, cur_item.th))
        item = state.get_proof_item(id.incr_id(1))
        state.set_line(id.incr_id(1), item.rule, args=item.args,
                       prevs=[p for p in item.prevs if p != prevs[0]], th=item.th)
        state.remove_line(prevs[0])


@register_method('exists_elim')
class exists_elim(Method):
    """Make use of an exists fact."""
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
        assert len(prevs) == 1, "exists_elim"

        # Parse the list of variable names
        with context.fresh_context(vars=state.get_vars(id)):
            names = [name.strip() for name in data['names'].split(',')]
            for name in names:
                if name in context.ctxt.vars:
                    raise AssertionError("Instantiate exists: duplicate name %s" % name)

        exists_item = state.get_proof_item(prevs[0])
        exists_prop = exists_item.th.prop
        assert exists_prop.is_exists(), "exists_elim"

        vars, body = logic.strip_exists(exists_prop, names)

        # Add one line for each variable, and one line for body of exists
        state.add_line_before(id, len(vars) + 1)
        for i, var in enumerate(vars):
            state.set_line(id.incr_id(i), 'variable', args=(var.name, var.T), prevs=[])
        state.set_line(id.incr_id(len(vars)), 'assume', args=body, prevs=[])

        # Find the intros at the end, append exists fact and new variables
        # and assumptions to prevs.
        new_intros = [prevs[0]] + [id.incr_id(i) for i in range(len(vars)+1)]
        i = len(vars) + 1
        while True:
            try:
                item = state.get_proof_item(id.incr_id(i))
            except ProofStateException:
                raise AssertionError("exists_elim: cannot find intros at the end")
            else:
                if item.rule == 'intros':
                    if item.args is None:
                        item.args = [exists_prop]
                    else:
                        item.args = [exists_prop] + item.args
                    item.prevs = item.prevs[:-1] + new_intros + [item.prevs[-1]]
                    break
                else:
                    state.set_line(id.incr_id(i), item.rule, args=item.args, prevs=item.prevs, \
                                   th=Thm(item.th.prop, item.th.hyps, body))
            i += 1


@register_method('forall_elim')
class forall_elim(Method):
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

        state.add_line_before(id, 1)
        state.set_line(id, 'forall_elim_gen', args=t, prevs=prevs)


@register_method('inst_exists_goal')
class inst_exists_goal(Method):
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


@register_method('induction')
class induction(Method):
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
            if len(vars) == 1:
                results.append({'theorem': name, 'var': vars[0].name})
            elif len(vars) > 1:
                results.append({'theorem': name})
        return results

    def display_step(self, state: ProofState, data):
        if 'var' in data:
            return pprint.N("Induction " + data['theorem'] + " var: " + data['var'])
        else:
            return pprint.N("Induction " + data['theorem'])

    def apply(self, state: ProofState, id, data, prevs):
        # Find variable
        with context.fresh_context(vars=state.get_vars(id)):
            assert data['var'] in context.ctxt.vars, "induction: cannot find variable."
            var = Var(data['var'], context.ctxt.vars[data['var']])

        state.apply_tactic(id, tactic.var_induct(), args=(data['theorem'], var))


@register_method('new_var')
class new_var(Method):
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


@register_method('apply_fact')
class apply_fact(Method):
    """When one of the prevs is an forall/implies fact, apply that fact
    to the remaining prevs.

    """
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state: ProofState, id, prevs):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]

        try:
            macro = apply_fact_macro()
            pt = macro.eval(args=None, prevs=prev_ths)
            return [{"_fact": [pt.prop]}]
        except (AssertionError, matcher.MatchException):
            return []

    def display_step(self, state: ProofState, data):
        return pprint.N("Apply fact (f) %s onto %s" % (data['fact_ids'][0], ", ".join(data['fact_ids'][1:])))

    def apply(self, state: ProofState, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_fact', prevs=prevs)


# ==================== New generic methods ====================

@register_method('call_tactic')
class call_tactic_method(Method):
    """Directly invoke any registered tactic by name.
    Escape hatch when no method works.
    """
    def __init__(self):
        self.sig = ['tactic_name']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("tactic " + data.get('tactic_name', '?'))

    def apply(self, state, id, data, prevs):
        tactic_name = data.get('tactic_name')
        if not tactic_name:
            raise AssertionError("call_tactic: tactic_name required")
        
        if tactic_name == 'rule':
            thm_name = data.get('theorem')
            if not thm_name:
                raise AssertionError("call_tactic rule: theorem required")
            state.apply_tactic(id, tactic.rule(thm_name), prevs=prevs)
        elif tactic_name == 'rewrite_goal':
            thm_name = data.get('theorem')
            sym = data.get('sym', 'false') == 'true'
            if not thm_name:
                raise AssertionError("call_tactic rewrite_goal: theorem required")
            state.apply_tactic(id, tactic.rewrite_goal(thm_name, sym=sym), prevs=prevs)
        elif tactic_name == 'apply_prev':
            state.apply_tactic(id, tactic.apply_prev(), prevs=prevs)
        elif tactic_name == 'intros':
            state.apply_tactic(id, tactic.intros(), prevs=prevs)
        elif tactic_name == 'assumption':
            state.apply_tactic(id, tactic.assumption(), prevs=prevs)
        elif tactic_name == 'resolve':
            thm_name = data.get('theorem')
            if not thm_name:
                raise AssertionError("call_tactic resolve: theorem required")
            state.apply_tactic(id, tactic.resolve(thm_name), prevs=prevs)
        elif tactic_name == 'cases':
            case_expr = data.get('case')
            if not case_expr:
                raise AssertionError("call_tactic cases: case required")
            with context.fresh_context(vars=state.get_vars(id)):
                case_term = parser.parse_term(case_expr)
            state.apply_tactic(id, tactic.cases(case_term), prevs=prevs)
        else:
            raise AssertionError("call_tactic: unknown tactic '%s'" % tactic_name)


@register_method('call_macro')
class call_macro_method(Method):
    """Directly invoke any registered macro by name.
    Escape hatch when no method works.
    """
    def __init__(self):
        self.sig = ['macro_name']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("macro " + data.get('macro_name', '?'))

    def apply(self, state, id, data, prevs):
        macro_name = data.get('macro_name')
        if not macro_name:
            raise AssertionError("call_macro: macro_name required")
        
        if not theory.has_macro(macro_name):
            raise AssertionError("call_macro: macro '%s' not found" % macro_name)
        
        macro_obj = theory.get_macro(macro_name)
        prev_ths = [state.get_proof_item(p).th for p in prevs]
        
        result_th = macro_obj.eval(None, prev_ths)
        state.set_line(id, macro_name, prevs=prevs, th=result_th)


@register_method('simp')
class simp_method(Method):
    """Generic simplifier: rewrite goal using all hint_rewrite theorems."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        try:
            attrs = theory.thy.get_data('attributes')
            rewrite_thms = [n for n, a in attrs.items() if 'hint_rewrite' in a]
            if not rewrite_thms:
                return []
            return [{}]
        except Exception:
            return []

    def display_step(self, state, data):
        return pprint.N("simp")

    def apply(self, state, id, data, prevs):
        attrs = theory.thy.get_data('attributes')
        rewrite_thms = []
        for name, a in attrs.items():
            if 'hint_rewrite' in a:
                try:
                    thm = theory.thy.get_theorem(name)
                    rewrite_thms.append((name, thm))
                except theory.TheoryException:
                    pass
        
        if not rewrite_thms:
            raise AssertionError("simp: no rewrite theorems available")
        
        cur_item = state.get_proof_item(id)
        goal_prop = cur_item.th.prop
        
        # Try each rewrite and build combined conv
        best_cv = conv.all_conv()
        for name, thm in rewrite_thms:
            try:
                cv = conv.rewr_conv(thm)
                cv.get_proof_term(goal_prop)
                best_cv = conv.then_conv(best_cv, conv.top_conv(cv))
            except Exception:
                continue
        
        if isinstance(best_cv, conv.all_conv):
            raise AssertionError("simp: no rewrite applicable to this goal")
        
        state.apply_tactic(id, tactic.rewrite_goal_with_conv(best_cv), prevs=prevs)


@register_method('norm')
class norm_method(Method):
    """Generic normalization: dispatch to domain-specific normalizer
    based on the type of the goal.
    """
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        try:
            cur_item = state.get_proof_item(id)
            goal_prop = cur_item.th.prop
            # Check if goal is an equality
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
        
        # Detect type from the equality's LHS
        if goal_prop.is_equals():
            T = goal_prop.lhs.get_type()
        else:
            T = goal_prop.get_type()
        
        # Dispatch based on type
        from kernel.type import NatType, RealType
        
        if T == NatType:
            if theory.has_macro('nat_norm'):
                state.apply_tactic(id, tactic.MacroTactic('nat_norm'))
                return
        elif T == RealType:
            if theory.has_macro('real_norm'):
                state.apply_tactic(id, tactic.MacroTactic('real_norm'))
                return
        
        raise AssertionError("norm: unsupported type %s or no normalizer available" % str(T))


@register_method('eval')
class eval_method(Method):
    """Generic evaluation: dispatch to domain-specific evaluator
    based on the type of the goal.
    """
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        try:
            cur_item = state.get_proof_item(id)
            goal_prop = cur_item.th.prop
            # Check if goal is an equality with constant expressions
            if not goal_prop.is_equals():
                return []
            return [{}]
        except Exception:
            return []

    def display_step(self, state, data):
        return pprint.N("eval")

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        goal_prop = cur_item.th.prop
        
        if goal_prop.is_equals():
            T = goal_prop.lhs.get_type()
        else:
            T = goal_prop.get_type()
        
        from kernel.type import NatType, RealType, IntType
        
        if T == NatType:
            if theory.has_macro('nat_eval'):
                state.apply_tactic(id, tactic.MacroTactic('nat_eval'))
                return
        elif T == IntType:
            if theory.has_macro('int_eval'):
                state.apply_tactic(id, tactic.MacroTactic('int_eval'))
                return
        elif T == RealType:
            if theory.has_macro('real_eval'):
                state.apply_tactic(id, tactic.MacroTactic('real_eval'))
                return
        
        raise AssertionError("eval: unsupported type %s or no evaluator available" % str(T))


@register_method('sym')
class sym_method(Method):
    """Apply symmetry to an equality goal. If goal is a = b, produces b = a."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        cur_item = state.get_proof_item(id)
        if cur_item.th.prop.is_equals():
            return [{}]
        return []

    def display_step(self, state, data):
        return pprint.N("sym")

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        goal_th = cur_item.th
        assert goal_th.prop.is_equals(), "sym: goal must be an equality"
        a, b = goal_th.prop.args
        new_prop = term.equals(a.get_type())(b, a)
        state.set_line(id, 'sorry', th=Thm(new_prop, goal_th.hyps))


@register_method('reflexive')
class reflexive_method(Method):
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


@register_method('equal_intr')
class equal_intr_method(Method):
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


@register_method('subst')
class subst_method(Method):
    """Substitute using an equality theorem: replace LHS with RHS in goal."""
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("subst " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("subst: theorem required")
        thm = theory.thy.get_theorem(thm_name)
        assert thm.prop.is_equals(), "subst: theorem must be an equality"
        cv = conv.then_conv(conv.top_sweep_conv(conv.rewr_conv(thm)), conv.beta_norm_conv())
        state.apply_tactic(id, tactic.rewrite_goal_with_conv(cv), prevs=prevs)


@register_method('unfold')
class unfold_method(Method):
    """Unfold a definition: replace the defined constant with its body."""
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("unfold " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("unfold: theorem required")
        thm = theory.thy.get_theorem(thm_name)
        cv = conv.then_conv(conv.top_conv(conv.rewr_conv(thm)), conv.beta_norm_conv())
        state.apply_tactic(id, tactic.rewrite_goal_with_conv(cv), prevs=prevs)


@register_method('fold')
class fold_method(Method):
    """Fold a definition: replace the body with the defined constant."""
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("fold " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("fold: theorem required")
        thm = theory.thy.get_theorem(thm_name)
        cv = conv.then_conv(conv.top_conv(conv.rewr_conv(thm, sym=True)), conv.beta_norm_conv())
        state.apply_tactic(id, tactic.rewrite_goal_with_conv(cv), prevs=prevs)


@register_method('thin')
class thin_method(Method):
    """Weakening: remove an assumption from the goal.

    If goal is A1, ..., An |- C, thin(i) removes Ai, giving
    A1, ..., A(i-1), A(i+1), ..., An |- C.

    This works because HOL's proof checker accepts a proof of H |- C
    as also proving H' |- C when H' is a superset of H (hyps subset
    semantics in can_prove). We create a sorry with fewer hypotheses,
    then find_goal locates the original proof which can_prove accepts.
    """
    def __init__(self):
        self.sig = ['index']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("thin " + str(data.get('index', '?')))

    def apply(self, state, id, data, prevs):
        idx = int(data.get('index', 0))
        cur_item = state.get_proof_item(id)
        goal_th = cur_item.th

        if idx < 0 or idx >= len(goal_th.hyps):
            raise AssertionError("thin: index %d out of range (0-%d)" % (idx, len(goal_th.hyps) - 1))

        # Build new theorem with the idx-th hypothesis removed.
        new_hyps = list(goal_th.hyps)
        new_hyps.pop(idx)
        new_th = Thm(goal_th.prop, *new_hyps)

        # Set as sorry, then find an existing proof that can_prove it.
        # can_prove accepts when the existing proof's hyps are a superset,
        # so H |- C can prove H\{A} |- C automatically.
        state.set_line(id, 'sorry', th=new_th)
        proof_id = state.find_goal(new_th, id)
        if proof_id is not None:
            state.replace_id(id, proof_id)


@register_method('insert')
class insert_method(Method):
    """Insert a named theorem as a new line in the proof."""
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("insert " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("insert: theorem required")
        thm = theory.thy.get_theorem(thm_name)
        state.add_line_before(id, 1)
        state.set_line(id, 'theorem', args=thm_name, prevs=[])


@register_method('drule')
class drule_method(Method):
    """Forward reasoning: consume a fact to derive a new fact.

    Given a theorem name and previous facts, applies the theorem in the
    forward direction. The first fact (prevs[0]) is CONSUMED: its proof
    line is replaced with the derived result. Use frule to preserve the
    original fact.
    """
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("drule " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("drule: theorem required")
        if not prevs:
            raise AssertionError("drule: at least one fact required")

        thm = theory.thy.get_theorem(thm_name)
        prev_ths = [state.get_proof_item(p).th for p in prevs]

        # Apply the theorem forward to derive a new fact
        macro_obj = apply_theorem_macro()
        result_th = macro_obj.eval(thm_name, prev_ths)

        # drule consumes the first fact: replace the fact line with the result.
        # This makes the original fact unavailable for later proof steps.
        fact_id = prevs[0]
        state.set_line(fact_id, 'apply_theorem', args=thm_name, prevs=prevs, th=result_th)
        # Point the goal to reference the new result line
        state.replace_id(id, fact_id)


@register_method('frule')
class frule_method(Method):
    """Forward reasoning: keep the fact and derive a new fact.

    Given a theorem name and previous facts, applies the theorem in the
    forward direction. Unlike drule, the original facts are PRESERVED:
    a new line is inserted with the derived result, and the goal is
    updated to reference it.
    """
    def __init__(self):
        self.sig = ['theorem']
        self.limit = None

    def search(self, state, id, prevs):
        return []

    def display_step(self, state, data):
        return pprint.N("frule " + data.get('theorem', '?'))

    def apply(self, state, id, data, prevs):
        thm_name = data.get('theorem')
        if not thm_name:
            raise AssertionError("frule: theorem required")

        thm = theory.thy.get_theorem(thm_name)
        prev_ths = [state.get_proof_item(p).th for p in prevs]

        # Apply the theorem forward to derive a new fact
        macro_obj = apply_theorem_macro()
        result_th = macro_obj.eval(thm_name, prev_ths)

        # frule preserves facts: insert a new line with the derived result.
        # The original fact lines remain unchanged and available.
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_theorem', args=thm_name, prevs=prevs, th=result_th)


@register_method('linarith')
class linarith_method(Method):
    """Generic linear arithmetic: dispatch to nat or real normalizer."""
    def __init__(self):
        self.sig = []
        self.limit = None

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []
        try:
            cur_item = state.get_proof_item(id)
            goal_prop = cur_item.th.prop
            if goal_prop.is_equals() or goal_prop.is_less_eq() or goal_prop.is_less():
                return [{}]
            return []
        except Exception:
            return []

    def display_step(self, state, data):
        return pprint.N("linarith")

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        goal_prop = cur_item.th.prop
        
        if goal_prop.is_equals():
            T = goal_prop.lhs.get_type()
        elif goal_prop.is_less_eq() or goal_prop.is_less():
            T = goal_prop.arg1.get_type()
        else:
            T = goal_prop.get_type()
        
        from kernel.type import NatType, RealType, IntType
        
        # Try nat first, then real, then int
        if T == NatType:
            if theory.has_macro('nat_norm'):
                state.apply_tactic(id, tactic.MacroTactic('nat_norm'))
                return
        elif T == RealType:
            if theory.has_macro('real_norm'):
                state.apply_tactic(id, tactic.MacroTactic('real_norm'))
                return
        elif T == IntType:
            # For integers, try omega or simplex
            if theory.has_macro('int_norm'):
                state.apply_tactic(id, tactic.MacroTactic('int_norm'))
                return
        
        raise AssertionError("linarith: unsupported type %s" % str(T))


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
        method = global_methods[step['method_name']]
        res = method.display_step(state, step)
    except Exception as e:
        res = pprint.N(step['method_name'])
    res += pprint.N(' on ' + step['goal_id'])
    if 'fact_ids' in step and len(step['fact_ids']) > 0:
        res += pprint.N(' using ' + ','.join(step['fact_ids']))
    return res

def output_hint(state: ProofState, step):
    method = global_methods[step['method_name']]
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

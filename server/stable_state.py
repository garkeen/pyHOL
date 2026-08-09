"""Stable-ID proof state adapter.

Wraps the positional-ID ProofState with a stable #[N] ID layer.
The kernel stays unchanged; this module translates stable <-> positional
at the API boundary.

Key mapping: th2sid (Thm value -> stable int). Items are tracked by their
Thm (proposition + hyps), which is stable across goal->fact transitions.
"""

from typing import List, Dict, Optional, Tuple
from copy import copy

from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof, ItemID, ProofStateException
from kernel import theory
from syntax import parser, printer
from syntax.settings import global_setting
from server.methods.core import ProofState, apply_method, get_method_sig, get_method_list_params
from server.methods import core as methods_core
from logic import tactic, context

# Items with these rules carry no new goal/fact content: they only
# reference already-registered lines. They get a positional ItemID for
# display, but no stable ID of their own.
_SKIP_RULES = {'intros', 'close_by'}

# Method direction classification
BACKWARD = {
    'apply_backward_step', 'apply_resolve_step', 'introduction',
    'cases', 'rewrite_goal', 'rewrite_goal_with_prev', 'apply_prev',
    'inst_exists_goal', 'induction', 'reflexive', 'equal_intr',
    'subst', 'unfold', 'fold', 'simp', 'assumption',
    'norm', 'eval', 'linarith', 'z3',
    'vcg',
}
FORWARD = {
    'apply_forward_step', 'rewrite_fact', 'rewrite_fact_with_prev',
    'apply_fact', 'forall_elim', 'drule', 'frule',
}


def _trackable(item):
    return item.th is not None and item.rule not in _SKIP_RULES


def _traverse(prf):
    """Yield all ProofItems depth-first."""
    for item in prf.items:
        yield item
        if item.subproof:
            yield from _traverse(item.subproof)


class StableProofState:
    """Proof state with stable #[N] IDs, wrapping positional ProofState."""

    def __init__(self):
        self.state = ProofState()
        self.th2sid: Dict[Thm, int] = {}
        self.next_sid = 1
        self.rpt = None

    def _ensure_sid(self, th: Thm) -> int:
        if th not in self.th2sid:
            self.th2sid[th] = self.next_sid
            self.next_sid += 1
        return self.th2sid[th]

    def _build_pos2sid(self) -> Dict[str, int]:
        """Build positional-ID -> stable-ID mapping by traversing proof tree."""
        pos2sid = {}
        for item in _traverse(self.state.prf):
            if _trackable(item):
                pos2sid[str(item.id)] = self._ensure_sid(item.th)
        return pos2sid

    def _find_new_items(self, old_ths: set) -> List[Tuple[int, Thm]]:
        """Find items whose th is not in old_ths. Assign stable IDs."""
        new_items = []
        seen = set()
        for item in _traverse(self.state.prf):
            if _trackable(item) and item.th not in old_ths:
                sid = self._ensure_sid(item.th)
                if sid not in seen:
                    seen.add(sid)
                    new_items.append((sid, item.th))
        return new_items

    @classmethod
    def create(cls, prop_str, vars_dict=None) -> 'StableProofState':
        """Create initial state: #0 = full proposition (no implicit splitting)."""
        sps = cls()
        # Set up context variables
        if vars_dict:
            from kernel.type import Type
            for nm, T_val in vars_dict.items():
                if isinstance(T_val, str):
                    T = parser.parse_type(T_val)
                else:
                    T = T_val  # already a Type object
                context.ctxt.vars[nm] = T
                sps.state.vars.append(Var(nm, T))

        prop = parser.parse_term(prop_str) if isinstance(prop_str, str) else prop_str
        sps.state.prf = Proof()
        sps.state.prf.add_item(0, 'sorry', th=Thm(prop, ()))
        sps.state.check_proof(compute_only=True)
        sps.th2sid[Thm(prop, ())] = 0
        return sps

    def replay(self, steps: List[dict]) -> bool:
        """Replay old-format steps (with positional goal_id/fact_ids).

        Used for loading saved proofs that haven't been converted yet.
        Returns True on success.
        """
        for step in steps:
            try:
                old_ths = set(self.th2sid.keys())
                apply_method(self.state, step)
                self.state.check_proof(compute_only=True)
                self._find_new_items(old_ths)
            except Exception:
                return False
        return True

    def replay_new(self, new_steps: list) -> bool:
        """Replay new-format steps (NewStep objects with stable IDs).

        Returns True on success.
        """
        for ns in new_steps:
            if not self.apply_method_new(ns):
                return False
        return True

    def apply_method_new(self, ns) -> bool:
        """Apply a single new-format step (stable IDs).

        ns has: method_name, args (dict), goal (int), facts (list of int), new_ids (list of int)
        Returns True on success.
        """
        # Build pos -> sid map
        pos2sid = self._build_pos2sid()
        sid2pos = {v: k for k, v in pos2sid.items()}

        # Translate stable IDs to positional
        goal = ns.goal
        if goal is None:
            # Forward step without a goal: insert at the first open goal
            goal = self._find_insertion_point(list(ns.facts))
            if goal is None:
                return False
        goal_pos = sid2pos.get(goal)
        if goal_pos is None:
            return False

        fact_pos = []
        for f in ns.facts:
            fp = sid2pos.get(f)
            if fp is None:
                return False
            fact_pos.append(fp)

        # Build step dict for apply_method
        step_dict = {'method_name': ns.method_name, 'goal_id': goal_pos}
        if fact_pos:
            step_dict['fact_ids'] = fact_pos
        step_dict.update(ns.args)

        old_ths = set(self.th2sid.keys())
        try:
            apply_method(self.state, step_dict)
            self.state.check_proof(compute_only=True)
        except Exception:
            return False

        # Assign stable IDs to new items
        new_items = self._find_new_items(old_ths)

        # If new_ids provided, override auto-assigned IDs
        if ns.new_ids and len(ns.new_ids) == len(new_items):
            for (old_sid, th), new_sid in zip(new_items, ns.new_ids):
                # Reassign: move th mapping to the specified ID
                if old_sid != new_sid:
                    self.th2sid[th] = new_sid
                    if new_sid >= self.next_sid:
                        self.next_sid = new_sid + 1

        return True

    def apply_method_dict(self, step: dict) -> bool:
        """Apply a method from a plain dict with stable IDs.

        step keys: method_name, args (dict), goal (int), facts (list[int]),
                   new_ids (list[int], optional, for replay)
        """
        pos2sid = self._build_pos2sid()
        sid2pos = {v: k for k, v in pos2sid.items()}

        goal = step.get('goal')
        if goal is None:
            # Forward step without a goal: insert at the first open goal
            # that can depend on all facts.
            goal = self._find_insertion_point(step.get('facts', []))
            if goal is None:
                return False
        goal_pos = sid2pos.get(goal)
        if goal_pos is None:
            return False

        fact_pos = []
        for f in step.get('facts', []):
            fp = sid2pos.get(f)
            if fp is None:
                return False
            fact_pos.append(fp)

        step_dict = {'method_name': step['method_name'], 'goal_id': goal_pos}
        if fact_pos:
            step_dict['fact_ids'] = fact_pos
        # Copy all extra keys (flat args at top level + nested args dict)
        for k, v in step.items():
            if k not in ('method_name', 'goal', 'facts', 'new_ids', 'new_items', 'args'):
                step_dict[k] = v
        args = step.get('args', {})
        for k, v in args.items():
            step_dict[k] = v

        old_ths = set(self.th2sid.keys())
        try:
            apply_method(self.state, step_dict)
            self.state.check_proof(compute_only=True)
        except Exception:
            return False

        new_items = self._find_new_items(old_ths)

        # Override IDs if new_ids provided
        new_ids = step.get('new_ids', [])
        if new_ids and len(new_ids) == len(new_items):
            for (old_sid, th), new_sid in zip(new_items, new_ids):
                if old_sid != new_sid:
                    self.th2sid[th] = new_sid
                    if new_sid >= self.next_sid:
                        self.next_sid = new_sid + 1
        return True

    def _find_insertion_point(self, fact_sids: list) -> Optional[int]:
        """Find the stable ID of the first sorry after the last fact."""
        pos2sid = self._build_pos2sid()
        sid2pos = {v: k for k, v in pos2sid.items()}

        # Find positional IDs of facts
        fact_positions = []
        for fsid in fact_sids:
            pos = sid2pos.get(fsid)
            if pos is not None:
                fact_positions.append(ItemID(pos))

        if not fact_positions:
            # Find first sorry
            for item in _traverse(self.state.prf):
                if item.rule == 'sorry' and _trackable(item):
                    return self._ensure_sid(item.th)
            return None

        # Find the last fact by tree order, then find next sorry after it
        last_fact = max(fact_positions, key=lambda x: x.id)
        for item in _traverse(self.state.prf):
            if item.rule == 'sorry' and _trackable(item):
                # Check if this sorry can depend on all facts
                try:
                    if all(item.id.can_depend_on(fid) for fid in fact_positions):
                        return self._ensure_sid(item.th)
                except Exception:
                    pass
        return None

    def apply_method_raw(self, step_dict: dict) -> Optional[List[Tuple[int, Thm]]]:
        """Apply a method with positional IDs (for backward compat).

        Returns list of (sid, th) for new items, or None on failure.
        """
        old_ths = set(self.th2sid.keys())
        try:
            apply_method(self.state, step_dict)
            self.state.check_proof(compute_only=True)
        except Exception:
            return None
        return self._find_new_items(old_ths)

    def check_proof(self, *, no_gaps=False):
        self.rpt = None
        return self.state.check_proof(no_gaps=no_gaps)

    @property
    def num_gaps(self):
        if self.state.rpt is None:
            self.state.check_proof(compute_only=True)
        return len(self.state.rpt.gaps)

    def get_open_goals(self) -> List[Tuple[int, Thm]]:
        """Return (sid, th) for all sorry items."""
        goals = []
        for item in _traverse(self.state.prf):
            if item.rule == 'sorry' and _trackable(item):
                sid = self._ensure_sid(item.th)
                goals.append((sid, item.th))
        return goals

    def json_data(self) -> dict:
        """Export proof state with stable IDs for frontend."""
        with global_setting(unicode=True):
            vars = {v.name: printer.print_type(v.T) for v in self.state.vars}
            proof_lines = self._export_proof_lines()

        # Ensure rpt is computed
        if self.state.rpt is None:
            self.state.check_proof(compute_only=True)

        return {
            'vars': vars,
            'proof': proof_lines,
            'num_gaps': len(self.state.rpt.gaps),
            'method_sig': get_method_sig(),
            'method_list_params': get_method_list_params(),
            'open_goals': [{'sid': sid, 'prop': printer.print_term(th.prop)}
                          for sid, th in self.get_open_goals()],
        }

    def _export_proof_lines(self) -> list:
        """Export proof tree as flat list with stable IDs."""
        lines = []
        for item in _traverse(self.state.prf):
            # Kernel auto-solves a leaf goal and records the closure as an
            # 'intros' item whose prevs reference the proving lines. Surface
            # it as an explicit close line (display only).
            if item.rule == 'intros' and item.prevs:
                try:
                    prev_item = self.state.prf.find_item(item.prevs[0])
                    witness = prev_item.th
                except (ProofStateException, AttributeError):
                    witness = None
                if witness is not None:
                    lines.append({
                        'id': str(item.id),
                        'sid': self._ensure_sid(item.th),
                        'rule': 'close_by',
                        'args': '',
                        'prevs': [self._ensure_sid(witness)],
                        'th': printer.print_term(item.th.prop),
                        'is_goal': False,
                        'indent': len(item.id.id),
                    })
                continue

            if not _trackable(item):
                continue
            sid = self._ensure_sid(item.th)
            prev_sids = []
            for prev_id in item.prevs:
                try:
                    prev_item = self.state.prf.find_item(prev_id)
                    if _trackable(prev_item):
                        prev_sids.append(self._ensure_sid(prev_item.th))
                except ProofStateException:
                    pass

            with global_setting(unicode=True):
                th_str = printer.print_term(item.th.prop) if item.th else ''

            lines.append({
                'id': str(item.id),
                'sid': sid,
                'rule': item.rule,
                'args': self._serialize_args(item.args),
                'prevs': prev_sids,
                'th': th_str,
                'is_goal': item.rule == 'sorry',
                'indent': len(item.id.id),
            })
        return lines

    def _translate_search_result(self, r: dict, pos2sid: dict) -> dict:
        """Translate positional IDs in search results to stable IDs.
        Also serialize Term objects to strings for JSON."""
        r = dict(r)  # copy
        # fact_ids (positional) -> facts (stable)
        if 'fact_ids' in r:
            r['facts'] = [pos2sid.get(str(fid), fid) if isinstance(fid, str) else fid
                          for fid in r['fact_ids']]
            del r['fact_ids']
        # goal_id (positional) -> goal (stable)
        if 'goal_id' in r:
            r['goal'] = pos2sid.get(str(r['goal_id']), r['goal_id'])
            del r['goal_id']
        # Serialize Term objects to strings
        from kernel.term import Term
        from kernel.thm import Thm
        with global_setting(unicode=True):
            for k, v in list(r.items()):
                if isinstance(v, Term):
                    r[k] = printer.print_term(v)
                elif isinstance(v, list):
                    r[k] = [printer.print_term(x) if isinstance(x, Term) else x for x in v]
                elif isinstance(v, Thm):
                    r[k] = printer.print_term(v.prop)
        return r

    def _serialize_args(self, args):
        """Serialize args for JSON."""
        if args is None:
            return None
        if isinstance(args, tuple):
            return [str(a) for a in args]
        return str(args)

    def search_backward(self, goal_sid: int, fact_sids: list) -> dict:
        """Backward search: find methods applicable to goal_sid.

        Exact results use the original fact order; fuzzy results cover
        other permutations and subsets (largest first).
        Returns {'results': [...], 'fuzzy': [...]}.
        """
        import itertools
        pos2sid = self._build_pos2sid()
        sid2pos = {v: k for k, v in pos2sid.items()}

        goal_pos = sid2pos.get(goal_sid)
        if goal_pos is None:
            return {'results': [], 'fuzzy': []}

        fact_pos = [sid2pos.get(f) for f in fact_sids]
        if any(f is None for f in fact_pos):
            return {'results': [], 'fuzzy': []}

        goal_id = ItemID(goal_pos)
        prevs = [ItemID(f) for f in fact_pos]

        results, fuzzy = [], []

        def collect(method_name, method_obj, perm_prevs, exact):
            try:
                search_res = method_obj.search(self.state, goal_id, perm_prevs)
            except Exception:
                return
            for r in search_res:
                r['method_name'] = method_name
                r['fact_ids'] = [str(p) for p in perm_prevs]
                try:
                    with global_setting(unicode=True):
                        r['_facts'] = [printer.print_term(self.state.get_proof_item(p).th.prop)
                                       for p in perm_prevs]
                except Exception:
                    r['_facts'] = []
                r['fuzzy'] = not exact
                tr = self._translate_search_result(r, pos2sid)
                (results if exact else fuzzy).append(tr)

        for method_name in methods_core.global_methods:
            method = methods_core.global_methods[method_name]
            if method.limit is not None and not theory.thy.has_theorem(method.limit):
                continue
            collect(method_name, method, prevs, exact=True)
            if hasattr(method, 'no_order'):
                continue
            # Fuzzy: other permutations of all facts, then subsets, largest first
            n = len(prevs)
            for k in range(n, 0, -1):
                for comb in itertools.combinations(prevs, k):
                    for perm in itertools.permutations(comb):
                        if k == n and list(perm) == prevs:
                            continue  # already in exact
                        collect(method_name, method, list(perm), exact=False)
        return {'results': results, 'fuzzy': fuzzy}

    def search_forward(self, fact_sids: list) -> dict:
        """Forward search: find methods applicable to facts (no goal).

        Exact results use the original fact order; fuzzy results cover
        other permutations and subsets (largest first).
        Returns {'results': [...], 'fuzzy': [...]}.
        """
        import itertools
        pos2sid = self._build_pos2sid()
        sid2pos = {v: k for k, v in pos2sid.items()}

        fact_pos = [sid2pos.get(f) for f in fact_sids]
        if any(f is None for f in fact_pos):
            return {'results': [], 'fuzzy': []}

        prevs = [ItemID(f) for f in fact_pos]

        # Find insertion point (first sorry after last fact)
        if not prevs:
            # Find first sorry
            for item in self.state.prf.items:
                if item.rule == 'sorry':
                    prevs = []
                    break
            else:
                return {'results': [], 'fuzzy': []}

        results, fuzzy = [], []

        def collect(method_name, method_obj, perm_prevs, exact):
            try:
                search_res = method_obj.search(self.state, ItemID(0), perm_prevs)
            except Exception:
                return
            for r in search_res:
                r['method_name'] = method_name
                r['fact_ids'] = [str(p) for p in perm_prevs]
                try:
                    with global_setting(unicode=True):
                        r['_facts'] = [printer.print_term(self.state.get_proof_item(p).th.prop)
                                       for p in perm_prevs]
                except Exception:
                    r['_facts'] = []
                r['fuzzy'] = not exact
                tr = self._translate_search_result(r, pos2sid)
                (results if exact else fuzzy).append(tr)

        for method_name in methods_core.global_methods:
            method = methods_core.global_methods[method_name]
            if method_name not in FORWARD:
                continue
            if method.limit is not None and not theory.thy.has_theorem(method.limit):
                continue
            collect(method_name, method, prevs, exact=True)
            if hasattr(method, 'no_order'):
                continue
            # Fuzzy: other permutations of all facts, then subsets, largest first
            n = len(prevs)
            for k in range(n, 0, -1):
                for comb in itertools.combinations(prevs, k):
                    for perm in itertools.permutations(comb):
                        if k == n and list(perm) == prevs:
                            continue  # already in exact
                        collect(method_name, method, list(perm), exact=False)
        return {'results': results, 'fuzzy': fuzzy}
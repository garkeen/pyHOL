"""New-format .pyhol parser and replay with stable #[N] IDs.

Format:
  proof
    ← introduction goal=0
      #[1] A ∨ B ∨ C
      #[2] (A ∨ B) ∨ C
    ← apply_backward_step disjE goal=2 facts=[1]
      #[3] A ⟶ (A ∨ B) ∨ C
    -> apply_forward_step conjD1 goal=0 facts=[3]
      #[4] A
  qed

Replay: stable IDs are mapped to positional IDs for the current kernel.
#[N] propositions are read (for ID assignment) but NOT verified.
Prop texts are kept in new_items for round-trip display/export.
"""

import re
from typing import List, Dict, Optional, Tuple

from kernel.proof import ItemID, ProofStateException
from kernel.thm import Thm
from kernel import theory
from syntax import parser, printer
from syntax.settings import global_setting
from server import server
from server.methods.core import apply_method, ProofState


# ── parsing ──────────────────────────────────────────────────────

class NewStep:
    """One method call + its #[N] annotations."""
    def __init__(self, method_name, args, goal, facts, new_ids, new_items=None):
        self.method_name = method_name
        self.args = args            # dict of arg key -> value
        self.goal = goal            # stable ID (int)
        self.facts = facts          # list of stable IDs (ints)
        self.new_ids = new_ids      # list of stable IDs from #[N] annotations
        self.new_items = new_items if new_items is not None else []  # [(sid, prop)]

    def __repr__(self):
        return 'NewStep(%s goal=%d facts=%s new=%s)' % (
            self.method_name, self.goal, self.facts, self.new_ids)


def parse_proof_body(lines: List[str]) -> List[NewStep]:
    """Parse lines between 'proof' and 'qed' into NewStep list."""
    steps = []
    current_step = None

    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith('--'):
            continue
        if stripped == 'proof' or stripped == 'qed':
            continue

        # #[N] annotation line
        m = re.match(r'^#\[(\d+)\]\s*(.*)$', stripped)
        if m:
            sid = int(m.group(1))
            if current_step is not None:
                current_step.new_ids.append(sid)
                current_step.new_items.append((sid, m.group(2)))
            continue

        # Method call line
        # Direction prefix: ← or -> (optional)
        m = re.match(r'^(?:←\s+|→\s+)?(\S+)\s*(.*)$', stripped)
        if not m:
            continue

        method_name = m.group(1)
        rest = m.group(2)

        # Parse goal=N and facts=[N,...]
        goal = 0
        facts = []
        args = {}

        # Extract goal=N
        m_goal = re.search(r'goal=(\d+)', rest)
        if m_goal:
            goal = int(m_goal.group(1))
            rest = rest[:m_goal.start()] + rest[m_goal.end():]

        # Extract facts=[N,...]
        m_facts = re.search(r'facts=\[([\d,\s]*)\]', rest)
        if m_facts:
            fact_str = m_facts.group(1).strip()
            if fact_str:
                facts = [int(f.strip()) for f in fact_str.split(',')]
            rest = rest[:m_facts.start()] + rest[m_facts.end():]

        # Parse remaining as args
        rest = rest.strip()
        if rest:
            # Simple tokenization: split by spaces, handle key=value
            tokens = _tokenize(rest)
            pos_keys = _get_positional_keys(method_name)
            for i, tok in enumerate(tokens):
                if '=' in tok:
                    k, v = tok.split('=', 1)
                    args[k] = v
                elif i < len(pos_keys):
                    val = tok
                    if val.startswith('"') and val.endswith('"'):
                        val = val[1:-1]
                    args[pos_keys[i]] = val
                else:
                    args['_extra_%d' % i] = tok

        current_step = NewStep(method_name, args, goal, facts, [])
        steps.append(current_step)

    return steps


def _tokenize(s):
    """Simple tokenizer that respects quotes."""
    tokens = []
    current = ''
    in_quote = False
    for ch in s:
        if ch == '"':
            in_quote = not in_quote
            current += ch
        elif ch == ' ' and not in_quote:
            if current.strip():
                tokens.append(current.strip())
            current = ''
        else:
            current += ch
    if current.strip():
        tokens.append(current.strip())
    return tokens


def _get_positional_keys(method_name):
    from syntax.pyhol import _METHOD_POSITIONAL
    return _METHOD_POSITIONAL.get(method_name, [])


# ── replay ───────────────────────────────────────────────────────

_SKIP_RULES = {'intros'}

def _trackable(item):
    return item.th is not None and item.rule not in _SKIP_RULES

def _traverse(prf):
    for item in prf.items:
        yield item
        if item.subproof:
            yield from _traverse(item.subproof)


def replay_proof(thy_name, thm_name, vars_dict, prop_str, steps: List[NewStep]):
    """Replay new-format steps and return (ProofState, ok).

    Maps stable IDs to positional IDs for the current kernel.
    """
    from framework import context

    from kernel.term import Term
    from server.methods.core import ProofState

    with theory.fresh_theory():
        try:
            try:
                context.set_context(thy_name, limit=('thm', thm_name), vars=vars_dict)
            except Exception:
                context.set_context(thy_name, vars=vars_dict)
        except Exception:
            return None, False

        try:
            prop_term = parser.parse_term(prop_str) if isinstance(prop_str, str) else prop_str
        except Exception:
            return None, False

        # Create initial state: just #0 = sorry(full proposition), no splitting
        from kernel.proof import Proof
        from kernel.thm import Thm
        state = ProofState()
        for nm, T in context.ctxt.vars.items():
            state.vars.append(__import__('kernel.term', fromlist=['Var']).Var(nm, T))
        state.prf = Proof()
        state.prf.add_item(0, 'sorry', th=Thm(prop_term, ()))
        state.check_proof(compute_only=True)

        # Stable ID bookkeeping
        th2sid = {}
        next_sid = [1]

        def ensure_sid(th):
            if th not in th2sid:
                th2sid[th] = next_sid[0]
                next_sid[0] += 1
            return th2sid[th]

        # #0 = the full proposition
        th2sid[Thm(prop_term, ())] = 0

        # Replay each step
        for step in steps:
            # Build pos -> sid map
            pos2sid = {}
            for it in _traverse(state.prf):
                if _trackable(it):
                    pos2sid[str(it.id)] = ensure_sid(it.th)

            # Find positional IDs for goal and facts
            # Reverse lookup: sid -> pos
            sid2pos = {v: k for k, v in pos2sid.items()}

            goal_pos_str = sid2pos.get(step.goal)
            if goal_pos_str is None:
                return None, False

            fact_pos_strs = []
            for f in step.facts:
                fps = sid2pos.get(f)
                if fps is None:
                    return None, False
                fact_pos_strs.append(fps)

            # Build the step dict for apply_method
            step_dict = {'method_name': step.method_name, 'goal_id': goal_pos_str}
            if fact_pos_strs:
                step_dict['fact_ids'] = fact_pos_strs
            step_dict.update(step.args)

            try:
                apply_method(state, step_dict)
                state.check_proof(compute_only=True)
            except Exception:
                return None, False

            # Assign stable IDs to new items
            # Use #[N] annotations if available, otherwise auto-assign
            new_items = []
            old_ths = set(th2sid.keys())
            for it in _traverse(state.prf):
                if _trackable(it) and it.th not in old_ths:
                    new_items.append(it)

            # If the step has #[N] annotations, use them
            if step.new_ids and len(step.new_ids) == len(new_items):
                for sid, it in zip(step.new_ids, new_items):
                    th2sid[it.th] = sid
                    if sid >= next_sid[0]:
                        next_sid[0] = sid + 1
            else:
                # Auto-assign
                for it in new_items:
                    ensure_sid(it.th)

        return state, True
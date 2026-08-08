#!/usr/bin/env python3
"""Convert old .pyhol to new explicit #[N] format with direction labels.

Key principles:
- #0 = full proposition (no implicit splitting)
- If prop has implications, insert explicit ← introduction goal=0
- Every #[N] comes from a method call, never implicit
- ← = backward (consumes goal, produces subgoals)
- -> = forward (consumes facts, produces fact)
- fixes keeps its semantics (variables in context, no #[N])
"""

import sys, os, copy, traceback
sys.path.insert(0, os.path.dirname(__file__))

from logic import basic, context
from kernel import theory
from kernel.proof import ItemID
from kernel.thm import Thm
from kernel.term import Term
from syntax import parser, printer
from syntax.pyhol import _quote_if_needed, _norm_arrows, _METHOD_POSITIONAL, _SKIP_KEYS
from syntax.settings import global_setting
from server import server
from server.methods.core import apply_method
from server.monitor import validate_theory

# ── method direction ─────────────────────────────────────────────

BACKWARD = {
    'apply_backward_step', 'apply_resolve_step', 'introduction',
    'cases', 'rewrite_goal', 'rewrite_goal_with_prev', 'apply_prev',
    'inst_exists_goal', 'induction', 'reflexive', 'equal_intr',
    'subst', 'unfold', 'fold', 'simp', 'assumption',
    'norm', 'eval', 'linarith', 'z3',
}
FORWARD = {
    'apply_forward_step', 'rewrite_fact', 'rewrite_fact_with_prev',
    'apply_fact', 'forall_elim', 'drule', 'frule',
}
# Structural: cut, new_var, thin, insert, sym, revert_intro, exists_elim

def _dir_prefix(method_name):
    if method_name in BACKWARD:
        return '← '
    if method_name in FORWARD:
        return '→ '
    return ''

# ── items to skip (internal, no stable ID) ───────────────────────

_SKIP_RULES = {'intros'}

def _trackable(item):
    return item.th is not None and item.rule not in _SKIP_RULES

def _traverse(prf):
    for item in prf.items:
        yield item
        if item.subproof:
            yield from _traverse(item.subproof)

# ── step export ──────────────────────────────────────────────────

def _export_step_new(step, sgoal, sfacts):
    method = step['method_name']
    pos_keys = _METHOD_POSITIONAL.get(method, [])
    positional, named = [], {}
    for k in pos_keys:
        if k in step:
            val = str(step[k])
            if val:
                positional.append(_quote_if_needed(_norm_arrows(val)))
    for k, v in step.items():
        if k in _SKIP_KEYS or k in pos_keys or k == 'fact_ids':
            continue
        named[k] = _norm_arrows(str(v))
    parts = [_dir_prefix(method) + method]
    if positional:
        parts.extend(positional)
    for k in sorted(named):
        parts.append('%s=%s' % (k, _quote_if_needed(named[k])))
    parts.append('goal=%d' % sgoal)
    if sfacts:
        parts.append('facts=[%s]' % ','.join(str(f) for f in sfacts))
    return ' '.join(parts)

# ── core conversion ──────────────────────────────────────────────

def convert_proof(thy_name, item):
    """Returns (lines, ok)."""
    vars = dict(item.vars) if item.vars else {}
    with theory.fresh_theory():
        try:
            try:
                context.set_context(thy_name, limit=('thm', item.name), vars=vars)
            except Exception:
                context.set_context(thy_name, vars=vars)
            state = server.parse_init_state(item.prop)
        except Exception:
            return [], False

        # ── determine initial structure ──
        # parse_init_state creates: assume* , sorry, intros
        # We want: #0 = full prop, then ← introduction goal=0 produces assumptions + subgoal
        prop_term = parser.parse_term(item.prop) if isinstance(item.prop, str) else item.prop
        assums, concl = prop_term.strip_implies()
        n_assum = len(assums)

        # Stable ID tracking
        th2sid = {}
        next_sid = [1]

        def ensure_sid(th):
            if th not in th2sid:
                th2sid[th] = next_sid[0]
                next_sid[0] += 1
            return th2sid[th]

        lines = []

        # #0 = full proposition (implicit, not written)
        # Assign #0 to the intros item's th (= full proposition)
        # and map initial positions
        # parse_init_state: pos 0..n-1 = assume, pos n = sorry, pos n+1 = intros
        goal_pos = n_assum
        sorry_item = state.prf.items[goal_pos]
        intros_item = state.prf.items[goal_pos + 1] if len(state.prf.items) > goal_pos + 1 else None

        # The full proposition th = th of intros item (or sorry if no intros)
        if intros_item and intros_item.th:
            th2sid[intros_item.th] = 0  # #0 = full proposition
        else:
            th2sid[sorry_item.th] = 0

        # If there are implications, output ← introduction goal=0
        if n_assum > 0:
            # Assign stable IDs to assumptions and subgoal
            for i in range(n_assum):
                ensure_sid(state.prf.items[i].th)
            ensure_sid(sorry_item.th)

            # Output the introduction call
            lines.append('  ← introduction goal=0')
            # Output #[N] for each assumption and the subgoal
            for i in range(n_assum):
                with global_setting(unicode=True):
                    lines.append('    #[%d] %s' % (th2sid[state.prf.items[i].th],
                                                   printer.print_term(state.prf.items[i].th.prop)))
            with global_setting(unicode=True):
                lines.append('    #[%d] %s' % (th2sid[sorry_item.th],
                                               printer.print_term(sorry_item.th.prop)))

        # ── replay each step ──
        for step in item.steps:
            gid = ItemID(step['goal_id'])
            fids = step.get('fact_ids', [])
            if isinstance(fids, list):
                fids = [ItemID(f) for f in fids]
            elif fids:
                fids = [ItemID(fids)]
            else:
                fids = []

            # Build pos -> sid map
            pos2sid = {}
            for idx, it in enumerate(state.prf.items):
                if _trackable(it):
                    pos2sid[str(it.id)] = ensure_sid(it.th)
                if it.subproof:
                    for sub_it in _traverse(it.subproof):
                        if _trackable(sub_it):
                            pos2sid[str(sub_it.id)] = ensure_sid(sub_it.th)

            sgoal = pos2sid.get(str(gid))
            sfacts = [pos2sid.get(str(f)) for f in fids]
            if sgoal is None or any(f is None for f in sfacts):
                return [], False

            old_ths = set(th2sid.keys())
            try:
                apply_method(state, step)
                state.check_proof(compute_only=True)
            except Exception:
                return [], False

            # Find new items
            new_items = []
            seen = set()
            for it in _traverse(state.prf):
                if _trackable(it) and it.th not in old_ths:
                    sid = ensure_sid(it.th)
                    if sid not in seen:
                        seen.add(sid)
                        new_items.append((sid, it.th))

            lines.append('  ' + _export_step_new(step, sgoal, sfacts))
            for sid, th in new_items:
                with global_setting(unicode=True):
                    lines.append('    #[%d] %s' % (sid, printer.print_term(th.prop)))

        return lines, True


# ── file-level export ────────────────────────────────────────────

def _export_item_new(item, new_proof=None):
    ty = item.ty
    if ty == 'thm':
        lines = ['theorem %s' % item.name]
        v = getattr(item, 'vars', {})
        if v:
            lines.append('  fixes %s' % ', '.join(
                '%s :: %s' % (n, _norm_arrows(t)) for n, t in v.items()))
        prop = item.prop
        if isinstance(prop, list):
            prop = ' '.join(s.strip() for s in prop if s.strip())
        lines.append('  prop %s' % _norm_arrows(prop))
        attrs = getattr(item, 'attributes', [])
        if attrs:
            lines.append('  [%s]' % ','.join(attrs))
        if new_proof:
            lines.append('proof')
            lines.extend(new_proof)
            lines.append('qed')
        return lines
    from syntax.pyhol import _export_item
    try:
        return _export_item(item.export_json())
    except Exception:
        try:
            return _export_item(item.get_display())
        except Exception:
            return ['# <unexportable: %s>' % ty]


def convert_file(filename, out_dir):
    print('  Converting %s ...' % filename)
    basic.load_theory(filename)
    statuses, errors = validate_theory(filename, force=True)
    cache = basic.theory_cache[filename]
    content = cache['content']

    out_lines = ['theory %s' % filename]
    imports = cache.get('imports', [])
    out_lines.append('imports %s' % ', '.join(imports) if imports else 'imports')
    if cache.get('domains'):
        out_lines.append('domains %s' % ', '.join(cache['domains']))
    if cache.get('description'):
        out_lines.append('description "%s"' % cache['description'])
    out_lines.append('')

    stats = {'VALID': 0, 'DEP_FAILED': 0, 'SKIPPED': 0, 'FAILED_CONV': 0}
    for item in content:
        name = getattr(item, 'name', '')
        ty = item.ty
        if ty == 'thm' and getattr(item, 'steps', None):
            status = statuses.get(name, 'STEP_FAILED')
            if status in ('VALID', 'DEP_FAILED'):
                stats[status] += 1
                proof_lines, ok = convert_proof(filename, item)
                if ok:
                    out_lines.extend(_export_item_new(item, proof_lines))
                else:
                    stats['FAILED_CONV'] += 1
                    out_lines.extend(_export_item_new(item, None))
            else:
                stats['SKIPPED'] += 1
                out_lines.extend(_export_item_new(item, None))
        else:
            out_lines.extend(_export_item_new(item))
        out_lines.append('')

    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, os.path.basename(filename) + '.pyhol')
    with open(out_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(out_lines) + '\n')
    print('    %s' % stats)
    return stats


def main():
    basic.load_metadata()
    files = basic.get_import_order(sorted(basic.theory_cache.keys()))
    for fn in files:
        basic.load_theory_cache(fn)
    out_dir = os.path.join(os.path.dirname(__file__), 'library_new')
    total = {'VALID': 0, 'DEP_FAILED': 0, 'SKIPPED': 0, 'FAILED_CONV': 0}
    for fn in files:
        cache = basic.theory_cache.get(fn)
        if not cache or 'content' not in cache:
            continue
        if not any(it.ty == 'thm' and getattr(it, 'steps', None) for it in cache['content']):
            continue
        try:
            s = convert_file(fn, out_dir)
            for k in total:
                total[k] += s[k]
        except Exception as e:
            print('  ERROR converting %s: %s' % (fn, e))
            traceback.print_exc()
    print('\nTOTAL: %s' % total)


if __name__ == '__main__':
    main()
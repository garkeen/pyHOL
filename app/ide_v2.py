"""New-pipeline API endpoints using stable #[N] IDs.

Routes are prefixed with /api/v2/ to coexist with the old pipeline.
"""

import json, os, traceback, time
from flask import request
from flask.json import jsonify

from app.app import app
from kernel import theory
from kernel.theory import TheoryException
from syntax import parser, printer
from syntax.settings import global_setting
from logic import basic, context
from server.stable_state import StableProofState, BACKWARD, FORWARD


def _load_theory(thy_name, thm_name, vars):
    """Set up theory context for proof operations."""
    if thm_name:
        try:
            context.set_context(thy_name, limit=('thm', thm_name), vars=vars)
            return
        except TheoryException:
            pass
    context.set_context(thy_name, vars=vars)


@app.route('/api/v2/init-saved-proof', methods=['POST'])
def v2_init_saved_proof():
    """Load and replay a saved proof with stable IDs.

    Input:
    * theory_name, thm_name, vars, prop
    * steps: list of step dicts {method_name, args, goal, facts, new_ids}
    * index: replay up to this index

    Returns:
    * state: proof state with stable IDs
    * history: list of step outputs
    """
    data = json.loads(request.get_data().decode('utf-8'))
    start = time.perf_counter()

    with theory.fresh_theory():
        try:
            _load_theory(data['theory_name'], data.get('thm_name'), data.get('vars', {}))
            sps = StableProofState.create(data['prop'], data.get('vars', {}))
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        steps = data.get('steps', [])
        index = data.get('index', len(steps))

        history = []
        for i, step in enumerate(steps[:index]):
            ok = sps.apply_method_dict(step)
            entry = {'method_name': step.get('method_name', ''),
                     'goal': step.get('goal', 0),
                     'facts': step.get('facts', [])}
            if not ok:
                entry['error'] = 'replay failed at step %d' % i
            history.append(entry)

        return jsonify({
            'state': sps.json_data(),
            'history': history,
            'num_gaps': sps.num_gaps,
            'load_time': time.perf_counter() - start,
        })


@app.route('/api/v2/apply-method', methods=['POST'])
def v2_apply_method():
    """Apply a method with stable IDs.

    Input:
    * theory_name, thm_name, vars, prop
    * steps: list of step dicts (replayed up to index)
    * index: current position
    * step: step dict to apply {method_name, args, goal, facts}

    Returns:
    * state: updated proof state
    * new_items: list of {sid, prop} for #[N] annotations
    * Or: query for parameters
    """
    data = json.loads(request.get_data().decode('utf-8'))
    start = time.perf_counter()

    with theory.fresh_theory():
        try:
            _load_theory(data['theory_name'], data.get('thm_name'), data.get('vars', {}))
            sps = StableProofState.create(data['prop'], data.get('vars', {}))
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        steps = data.get('steps', [])
        index = data.get('index', 0)

        # Replay up to index
        for i, step in enumerate(steps[:index]):
            if not sps.apply_method_dict(step):
                return jsonify({'error': 'replay failed at step %d' % i}), 500

        # Apply the new step
        step = data['step']

        # Handle forward methods without goal
        if step.get('goal') is None and step.get('facts'):
            goal_sid = sps._find_insertion_point(step['facts'])
            if goal_sid is not None:
                step['goal'] = goal_sid

        old_ths = set(sps.th2sid.keys())
        ok = sps.apply_method_dict(step)

        if not ok:
            # Check if it's a parameter query
            try:
                # Re-apply to catch the exception
                sps2 = StableProofState.create(data['prop'], data.get('vars', {}))
                for s in steps[:index]:
                    sps2.apply_method_dict(s)
                pos2sid = sps2._build_pos2sid()
                sid2pos = {v: k for k, v in pos2sid.items()}
                step_dict = _build_step_dict(step, sid2pos)
                from server.methods.core import apply_method as core_apply
                core_apply(sps2.state, step_dict)
            except TheoryException as e:
                if hasattr(e, 'params'):
                    return jsonify({'query': e.params, 'query_hints': getattr(e, 'hints', {})})
            except Exception as e:
                if hasattr(e, 'params'):
                    return jsonify({'query': e.params, 'query_hints': getattr(e, 'hints', {})})
            return jsonify({'error': 'method application failed'}), 500

        # Get new items for #[N] annotations
        new_items = sps._find_new_items(old_ths)

        return jsonify({
            'state': sps.json_data(),
            'new_items': [{'sid': sid, 'prop': printer.print_term(th.prop)}
                         for sid, th in new_items],
            'num_gaps': sps.num_gaps,
            'apply_time': time.perf_counter() - start,
        })


@app.route('/api/v2/backward-search', methods=['POST'])
def v2_backward_search():
    """Backward search with stable IDs.

    Input: theory_name, thm_name, vars, prop, steps, index, goal (sid), facts (sids)
    Returns: search results with method_name, theorem, _goal, etc.
    """
    data = json.loads(request.get_data().decode('utf-8'))

    with theory.fresh_theory():
        try:
            _load_theory(data['theory_name'], data.get('thm_name'), data.get('vars', {}))
            sps = StableProofState.create(data['prop'], data.get('vars', {}))
            for step in data.get('steps', [])[:data.get('index', 0)]:
                sps.apply_method_dict(step)
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        goal_sid = data.get('goal')
        fact_sids = data.get('facts', [])
        results = sps.search_backward(goal_sid, fact_sids)
        return jsonify({'results': results, 'ctxt': {}})


@app.route('/api/v2/forward-search', methods=['POST'])
def v2_forward_search():
    """Forward search with stable IDs.

    Input: theory_name, thm_name, vars, prop, steps, index, facts (sids)
    Returns: search results
    """
    data = json.loads(request.get_data().decode('utf-8'))

    with theory.fresh_theory():
        try:
            _load_theory(data['theory_name'], data.get('thm_name'), data.get('vars', {}))
            sps = StableProofState.create(data['prop'], data.get('vars', {}))
            for step in data.get('steps', [])[:data.get('index', 0)]:
                sps.apply_method_dict(step)
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        fact_sids = data.get('facts', [])
        results = sps.search_forward(fact_sids)
        return jsonify({'results': results, 'ctxt': {}})


# ── helpers ──────────────────────────────────────────────────────

def _build_step_dict(step, sid2pos):
    """Convert a stable-ID step dict to positional step dict."""
    goal_pos = sid2pos.get(step.get('goal', 0))
    if goal_pos is None:
        goal_pos = '0'
    step_dict = {'method_name': step['method_name'], 'goal_id': goal_pos}
    facts = step.get('facts', [])
    if facts:
        fact_pos = [sid2pos.get(f, '0') for f in facts]
        step_dict['fact_ids'] = fact_pos
    step_dict.update(step.get('args', {}))
    return step_dict
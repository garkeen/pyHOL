"""New-pipeline API endpoints using stable #[N] IDs.

Routes are prefixed with /api/v2/ (the old positional pipeline is gone).
"""

import json, traceback, time
from flask import request
from flask.json import jsonify

from backend.app import app
from kernel import theory
from kernel.theory import TheoryException
from syntax import printer
from syntax.settings import global_setting
from core import basic
from core import context
from core import verify
from method.stable_state import StableProofState


def _trust_from(data):
    """Computation-oracle trust set for this request.

    The /v2 endpoints are stateless (each one replays from scratch), so
    the session's trust set travels with every request.  Omitted ->
    core.verify.COMPUTATION_ORACLES (the CLI validator's default); an
    explicit list wins; an empty list is strict and rejects every oracle.
    """
    names = data.get('trust')
    if names is None:
        return verify.COMPUTATION_ORACLES
    return frozenset(names)


# Method args whose value carries the meaningful display content
# (theorem name, case expression, ...); shown in the history list.


def _step_display(step: dict) -> str:
    """Human-readable step summary for the history list, e.g.
    'rule conjI', 'cut A & B', 'induct nat_induct n', 'rewrite conj_comm'."""
    name = step.get('method_name', '')
    if not name:
        return ''
    parts = [name]
    for k in ('theorem', 'cut_goal', 'case', 'var', 's'):
        v = step.get(k)
        if v:
            parts.append(str(v))
    if step.get('sym'):
        parts.append('sym')
    if step.get('loc'):
        parts.append('loc=' + str(step['loc']))
    names = step.get('names')
    if names:
        parts.append(str(names))
    return ' '.join(parts)


def _load_theory(thy_name, thm_name, prop, vars):
    """Set up theory context for proof operations.

    Returns the canonical (prop, vars) for StableProofState.create.

    The display format served by load-json-file is NOT valid proof
    input: when the proposition exceeds line_length, its prop field is
    a list of wrapped display lines, so feeding it back to
    init-saved-proof fails with 'Thm expects Term but got list' even
    though the same proof validates fine (validation reads .pyhol
    directly).  Prefer the parsed item from the theory cache whenever
    possible, and only fall back to the client-supplied input.
    """
    if thm_name:
        try:
            cache = basic.load_theory_cache(thy_name)
            item = None
            for it in cache['content']:
                if it.ty == 'thm' and it.name == thm_name and it.error is None:
                    item = it
                    break
            if item is not None:
                vars = dict(item.vars)
                try:
                    context.set_context(thy_name, limit=('thm', thm_name), vars=vars)
                    return item.prop, vars
                except TheoryException:
                    pass
        except TheoryException:
            pass
    context.set_context(thy_name, vars=vars)
    if isinstance(prop, list):
        prop = ' '.join(str(line) for line in prop)
    return prop, vars


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
            prop, vars = _load_theory(data['theory_name'], data.get('thm_name'),
                                      data.get('prop'), data.get('vars', {}))
            sps = StableProofState.create(prop, vars, trust=_trust_from(data))
        except Exception as e:
            # 200 + error payload: the frontend reads response.data.error
            # instead of relying on an axios throw (see FRONTEND_API.md).
            return jsonify({'error': str(e)})

        steps = data.get('steps', [])
        index = data.get('index', len(steps))

        history = []
        for i, step in enumerate(steps[:index]):
            ok = sps.apply_method_dict(step)
            entry = {'method_name': step.get('method_name', ''),
                     'goal': step.get('goal', 0),
                     'facts': step.get('facts', []),
                     'display': _step_display(step)}
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
            prop, vars = _load_theory(data['theory_name'], data.get('thm_name'),
                                      data.get('prop'), data.get('vars', {}))
            sps = StableProofState.create(prop, vars, trust=_trust_from(data))
        except Exception as e:
            return jsonify({'error': str(e)})

        steps = data.get('steps', [])
        index = data.get('index', 0)

        # Replay up to index
        for i, step in enumerate(steps[:index]):
            if not sps.apply_method_dict(step):
                return jsonify({'error': 'replay failed at step %d' % i})

        # Apply the new step
        step = data['step']

        # Handle forward methods without goal
        if step.get('goal') is None and step.get('facts'):
            goal_sid = sps._find_insertion_point(step['facts'])
            if goal_sid is not None:
                step['goal'] = goal_sid

        old_ths = set(sps.th2sid.keys())
        try:
            # strict: surface the underlying exception instead of a
            # terse False, so the frontend gets err_type/err_str (or the
            # parameter query) rather than a generic failure.
            sps.apply_method_dict(step, strict=True)
        except Exception as e:
            if hasattr(e, 'params'):
                return jsonify({'query': e.params,
                                'query_hints': getattr(e, 'hints', {})})
            return jsonify({'error': {
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback.format_exc(),
            }})

        # Get new items for #[N] annotations
        new_items = sps._find_new_items(old_ths)

        with global_setting(unicode=True):
            new_items_out = [{'sid': sid, 'prop': printer.print_term(th.prop)}
                             for sid, th in new_items]

        return jsonify({
            'state': sps.json_data(),
            'new_items': new_items_out,
            'num_gaps': sps.num_gaps,
            'apply_time': time.perf_counter() - start,
        })


@app.route('/api/v2/trust-report', methods=['POST'])
def v2_trust_report():
    """Run a FULL verification of the replayed proof and return its trust
    report (audit §7.2).

    Interactive apply uses verify(compute_only=True), which deliberately
    skips the independent primitive replay -- so its state carries no
    oracle entries.  This endpoint pays for that replay on demand, giving
    the UI the true set of oracles/axioms the proof rests on.

    Input: same as init-saved-proof (theory_name, thm_name, vars, prop,
    steps, index?, trust?).
    Returns: { oracles, axioms, num_gaps, trust } or { error }.
    """
    data = json.loads(request.get_data().decode('utf-8'))

    with theory.fresh_theory():
        try:
            prop, vars = _load_theory(data['theory_name'], data.get('thm_name'),
                                      data.get('prop'), data.get('vars', {}))
            sps = StableProofState.create(prop, vars, trust=_trust_from(data))
        except Exception as e:
            return jsonify({'error': str(e)})

        steps = data.get('steps', [])
        index = data.get('index', len(steps))
        try:
            for step in steps[:index]:
                sps.apply_method_dict(step, strict=True)
            sps.verify()
        except Exception as e:
            return jsonify({'error': {
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback.format_exc(),
            }})

        rpt = sps.state.rpt
        return jsonify({
            'oracles': sorted(rpt.oracles),
            'axioms': sorted(rpt.axioms),
            'num_gaps': len(rpt.gaps),
            'trust': sorted(sps.trust),
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
            prop, vars = _load_theory(data['theory_name'], data.get('thm_name'),
                                      data.get('prop'), data.get('vars', {}))
            sps = StableProofState.create(prop, vars, trust=_trust_from(data))
            for step in data.get('steps', [])[:data.get('index', 0)]:
                sps.apply_method_dict(step)
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        goal_sid = data.get('goal')
        fact_sids = data.get('facts', [])
        res = sps.search_backward(goal_sid, fact_sids)
        return jsonify({'results': res['results'], 'fuzzy': res['fuzzy'], 'ctxt': {}})


@app.route('/api/v2/forward-search', methods=['POST'])
def v2_forward_search():
    """Forward search with stable IDs.

    Input: theory_name, thm_name, vars, prop, steps, index, facts (sids)
    Returns: search results
    """
    data = json.loads(request.get_data().decode('utf-8'))

    with theory.fresh_theory():
        try:
            prop, vars = _load_theory(data['theory_name'], data.get('thm_name'),
                                      data.get('prop'), data.get('vars', {}))
            sps = StableProofState.create(prop, vars, trust=_trust_from(data))
            for step in data.get('steps', [])[:data.get('index', 0)]:
                sps.apply_method_dict(step)
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        fact_sids = data.get('facts', [])
        res = sps.search_forward(fact_sids)
        return jsonify({'results': res['results'], 'fuzzy': res['fuzzy'], 'ctxt': {}})

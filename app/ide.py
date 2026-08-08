# Author: Chaozhu Xiang, Bohua Zhan

import json, os, traceback, time
import copy
from flask import request
from flask.json import jsonify
from pstats import Stats
import cProfile

from kernel import theory
from kernel.theory import TheoryException
from syntax import parser, printer, settings, pprint
from server import server, methods as method
from kernel.proof import ItemID
from logic import basic
from logic import context
from server import monitor
from server import items
from app.app import app
from syntax import pyhol


def _load_theory_for_proof(theory_name, thm_name, vars):
    """Helper to set up theory context for proof operations.
    
    For new theorems not yet saved to disk, thm_name may not exist in the
    theory file. In that case, load the full theory without a limit.
    """
    if thm_name:
        try:
            context.set_context(theory_name, limit=('thm', thm_name), vars=vars)
            return
        except theory.TheoryException:
            pass  # Theorem not in file (new theorem), fall through
    context.set_context(theory_name, vars=vars)
    """Load a saved proof.
    
    Input:
    * theory_name: name of the theory.
    * thm_name: name of the theorem.
    * vars: variable declarations.
    * prop: proposition.
    * steps: list of proof steps.
    * index: current step index.
    * proof: (optional) saved proof lines - use directly if available.

    Returns:
    * state: proof state (proof, num_gaps, method_sig).
    * history: list of step outputs.

    """
    data = json.loads(request.get_data().decode("utf-8"))

    start_time = time.perf_counter()
    
    with theory.fresh_theory():
        try:
            _load_theory_for_proof(data['theory_name'], data['thm_name'], data['vars'])
            state, history = _create_proof_state(data['prop'], data.get('steps', []), data.get('index'))
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        print("Load: %f" % (time.perf_counter() - start_time))

        return jsonify({
            'state': state.json_data(),
            'history': history,
            'num_gaps': len(state.rpt.gaps),
        })


@app.route('/api/find-files', methods=['POST'])
def find_files():
    """Return list of theory files.
    
    Returns:
    * theories: list of theory names.

    """
    basic.load_metadata()

    files = []
    for name, cache in basic.theory_cache.items():
        files.append((cache['order'], name))
    files.sort()

    return jsonify({
        'theories': tuple(name for _, name in files)
    })


@app.route('/api/load-json-file', methods=['POST'])
def load_json_file():
    """Load content of a json file.
    
    Input:
    * filename: name of the file.
    * line_length: maximum length of printed line.

    Returns:
    * content of the file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    filename = data['filename']
    line_length = data.get('line_length')
    profile = data.get('profile', False)

    if profile:
        pr = cProfile.Profile()
        pr.enable()

    cache = basic.load_theory_cache(filename)
    f_data = {
        'name': filename,
        'imports': cache['imports'],
        'domains': cache.get('domains', []),
        'description': cache['description'],
        'content': []
    }
    with theory.fresh_theory():
        basic.load_theory(filename, limit='start')
        for item in cache['content']:
            if item.error is None:
                try:
                    theory.thy.unchecked_extend(item.get_extension())
                except TheoryException:
                    pass
            try:
                with settings.global_setting(line_length=line_length):
                    output_item = item.export_web()
            except Exception:
                try:
                    output_item = item.export_json()
                except Exception:
                    output_item = {
                        'ty': item.ty,
                        'name': item.name or '',
                    }
                    if item.ty in ('thm', 'thm.ax'):
                        output_item['vars'] = dict(item.vars) if isinstance(item.vars, dict) else {}
                        output_item['prop'] = str(item.prop) if item.prop else ''
                        output_item['attributes'] = getattr(item, 'attributes', [])
                output_item['display'] = {'name': item.name or '', 'ty': item.ty}
                output_item['edit'] = {'name': item.name or '', 'ty': item.ty}
            # Remove error field - it's from load_theory_cache parsing, not real errors
            output_item.pop('error', None)
            f_data['content'].append(output_item)

    if profile:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    return jsonify(f_data)


@app.route('/api/save-file', methods=['POST'])
def save_file():
    """Save given data to file.
    
    Input:
    * filename: name of the file.
    * content: content to save.
    
    """
    data = json.loads(request.get_data().decode("utf-8"))
    filename = data['filename']

    s = pyhol.export_pyhol(data['content'])
    with open(basic.user_file(filename), 'w+', encoding='utf-8') as f:
        f.write(s)

    # Invalidate cache for this file
    if filename in basic.theory_cache:
        if 'timestamp' in basic.theory_cache[filename]:
            del basic.theory_cache[filename]['timestamp']

    return jsonify({})


@app.route('/api/check-modify', methods=['POST'])
def check_modify():
    """Check a modified item for validity.
    
    Input:
    * filename: name of the file.
    * limit_ty: type of the limit item.
    * limit_name: name of the limit item.
    * line_length: maximum length of printed line.
    * item: item to be checked.

    Returns:
    * checked item.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    edit_item = data['item']
    line_length = data.get('line_length')

    with theory.fresh_theory():
        if 'limit_ty' in data:
            limit = (data['limit_ty'], data['limit_name'])
        else:
            limit = None
        basic.load_theory(data['filename'], limit=limit)

        item = items.parse_edit(edit_item)
        if item.error is None:
            try:
                theory.thy.unchecked_extend(item.get_extension())
            except TheoryException:
                pass
        with settings.global_setting(line_length=line_length):
            output_item = item.export_web()

    return jsonify({
        'item': output_item
    })
    """Apply a proof method.
    
    Input:
    * theory_name: name of the theory.
    * thm_name: name of the theorem.
    * vars: variable declarations.
    * prop: proposition.
    * steps: list of proof steps.
    * index: current step index.
    * step: step to apply.

    Returns:
    * On success: the updated proof state and history.
    * On failure: query for parameters, or fail outright.

    """
    data = json.loads(request.get_data().decode("utf-8"))

    start_time = time.perf_counter()

    with theory.fresh_theory():
        try:
            _load_theory_for_proof(data['theory_name'], data['thm_name'], data['vars'])
            state, history = _create_proof_state(data['prop'], data.get('steps', [])[:data['index']])
        except Exception as e:
            print("Load failed: %s" % str(e))
            return jsonify({'error': str(e)}), 500

        # If no goal_id, find insertion point in the same context as facts
        if not data['step'].get('goal_id'):
            fact_ids = data['step'].get('fact_ids', [])
            if fact_ids:
                from kernel.proof import ItemID
                fact_id_objs = [ItemID(fid) for fid in fact_ids]
                last_fact = max(fact_id_objs, key=lambda x: x.id)
                prefix = last_fact.id[:-1]
                # Try next items at the same level
                for n in range(last_fact.id[-1] + 1, last_fact.id[-1] + 200):
                    candidate_id = ItemID(prefix + (n,))
                    try:
                        state.get_proof_item(candidate_id)
                        if all(candidate_id.can_depend_on(fid) for fid in fact_id_objs):
                            data['step']['goal_id'] = str(candidate_id)
                            break
                    except Exception:
                        break
                # Fallback: find first sorry that can depend on all facts
                if not data['step'].get('goal_id'):
                    def find_sorry_recursive(prf):
                        for item in prf.items.values():
                            if item.rule == 'sorry':
                                sid = ItemID(str(item.id))
                                if all(sid.can_depend_on(fid) for fid in fact_id_objs):
                                    return str(item.id)
                            if hasattr(item, 'subproof') and item.subproof:
                                result = find_sorry_recursive(item.subproof)
                                if result:
                                    return result
                        return None
                    result = find_sorry_recursive(state.prf)
                    if result:
                        data['step']['goal_id'] = result
            else:
                for item in state.prf.items.values():
                    if item.rule == 'sorry':
                        data['step']['goal_id'] = str(item.id)
                        break
        
        try:
            method.apply_method(state, data['step'])
        except Exception as e:
            if isinstance(e, theory.ParameterQueryException):
                return jsonify({
                    "query": e.params,
                    "query_hints": e.hints
                })
            else:
                return jsonify({
                    "error": {
                        "err_type": e.__class__.__name__,
                        "err_str": str(e),
                        "trace": traceback.format_exc()
                    }
                })

        # Generate step output for display (don't re-apply the step)
        try:
            with settings.global_setting(unicode=True, highlight=True):
                step_output = method.output_step(state, data['step'])
            history.append({
                'step_output': step_output,
                'goal_id': data['step']['goal_id'],
                'fact_ids': data['step'].get('fact_ids', [])
            })
        except Exception:
            pass  # If output generation fails, still return the state

        res = {
            'state': state.json_data(),
            'history': history,
            'step': data['step']
        }
        return jsonify(res)
    """Check the proof for validity.
    
    Input:
    * theory_name: name of the theory.
    * thm_name: name of the theorem.
    * vars: variable declarations.
    * prop: proposition.
    * steps: list of proof steps.

    Returns:
    * num_gaps: number of gaps in the proof.

    """
    data = json.loads(request.get_data().decode("utf-8"))

    with theory.fresh_theory():
        try:
            _load_theory_for_proof(data['theory_name'], data['thm_name'], data['vars'])
            state, _ = _create_proof_state(data['prop'], data.get('steps', []))
        except Exception as e:
            print("Load failed: %s" % str(e))
            return jsonify({'num_gaps': 0})

        state.check_proof()

        return jsonify({
            'num_gaps': len(state.rpt.gaps),
        })


@app.route('/api/remove-file', methods=['PUT'])
def remove_file():
    """Remove file with the given name.
    
    Input:
    * filename: name of the file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    filename = data['filename']
    filepath = basic.user_file(filename)
    if os.path.exists(filepath):
        os.remove(filepath)

    # Invalidate cache
    if filename in basic.theory_cache:
        del basic.theory_cache[filename]

    return jsonify({})


@app.route('/api/find-link', methods=['POST'])
def find_link():
    """Return the location of the link.

    Input:
    * filename: name of the file in which the query originates.
    * ty: type of item.
    * name: name of the item to find.

    Returns:
    * filename: name of the theory file.
    * position: index of the item in the theory.

    """
    data = json.loads(request.get_data().decode("utf-8"))

    res = basic.query_item_index(data['filename'], data['ext_ty'], data['name'])
    if res:
        filename, index = res
        return jsonify({
            'filename': filename,
            'index': index
        })
    else:
        return jsonify({})


# ==================== Validation ====================

@app.route('/api/validate-theory', methods=['POST'])
def validate_theory():
    """Validate all theorems in a theory file.

    Input:
    * filename: name of the theory file.
    * force: (optional) if true, ignore cache and re-validate.

    Returns:
    * statuses: dict of {name: status}.
    * errors: dict of {name: error_message} for failed theorems.
    * valid: number of VALID theorems.
    * axiom: number of AXIOM theorems.
    * unproved: number of UNPROVED theorems.
    * failed: number of STEP_FAILED + DEP_FAILED theorems.
    * total: total number of theorems.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    force = data.get('force', False)
    statuses, errors = monitor.validate_theory(data['filename'], force=force)
    counts = {}
    for s in statuses.values():
        counts[s] = counts.get(s, 0) + 1
    return jsonify({
        'statuses': statuses,
        'errors': errors,
        'valid': counts.get('VALID', 0),
        'axiom': counts.get('AXIOM', 0),
        'unproved': counts.get('UNPROVED', 0),
        'failed': counts.get('STEP_FAILED', 0) + counts.get('DEP_FAILED', 0),
        'total': len(statuses)
    })
    """Forward-only search: given facts, find derivable facts.
    
    No goal_id needed. Searches hint_forward and hint_rewrite (for facts).
    """
    data = json.loads(request.get_data().decode("utf-8"))
    start_time = time.perf_counter()

    with theory.fresh_theory():
        try:
            _load_theory_for_proof(data['theory_name'], data['thm_name'], data['vars'])
            state, history = _create_proof_state(data['prop'], data.get('steps', [])[:data['index']])
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        fact_ids = data['step'].get('fact_ids', [])
        if not fact_ids:
            return jsonify({'results': [], 'ctxt': {}})

        from kernel.proof import ItemID
        prevs = [ItemID(fid) for fid in fact_ids]

        # Forward methods to search
        FORWARD_SEARCH_METHODS = ['apply_forward_step', 'apply_fact', 'rewrite_fact',
                                  'forall_elim', 'exists_elim', 'drule', 'frule']

        results = []
        fuzzy = []
        import itertools

        def collect(method_name, perm_prevs, exact):
            method_obj = method.get_method(method_name)
            try:
                res = method_obj.search(state, None, perm_prevs)
            except Exception:
                return
            for r in res:
                r['method_name'] = method_name
                r['fact_ids'] = [str(p) for p in perm_prevs]
                r['_facts'] = [printer.print_term(state.get_proof_item(p).th.prop) for p in perm_prevs]
                # Print _fact and _thm for display
                if '_fact' in r:
                    r['_fact'] = [printer.print_term(t) if not isinstance(t, str) else t for t in r['_fact']]
                if '_thm' in r:
                    if not isinstance(r['_thm'], str):
                        r['_thm'] = printer.print_term(r['_thm'])
                if exact:
                    r['fuzzy'] = False
                    results.append(r)
                else:
                    r['fuzzy'] = True
                    fuzzy.append(r)

        for method_name in FORWARD_SEARCH_METHODS:
            if not method.has_method(method_name):
                continue
            method_obj = method.get_method(method_name)
            # Exact: original order, all facts
            collect(method_name, prevs, exact=True)
            if hasattr(method_obj, 'no_order'):
                continue
            # Fuzzy: other permutations of all facts, then subsets, largest first
            n = len(prevs)
            for k in range(n, 0, -1):
                for comb in itertools.combinations(prevs, k):
                    for perm in itertools.permutations(comb):
                        if k == n and list(perm) == prevs:
                            continue  # already in exact
                        collect(method_name, list(perm), exact=False)

    return jsonify({'results': results, 'fuzzy': fuzzy, 'ctxt': {}})
    """Backward-only search: given goal (and optional facts), find ways to modify goal.
    
    Every result must modify the goal (decompose, close, or transform).
    """
    data = json.loads(request.get_data().decode("utf-8"))
    start_time = time.perf_counter()

    with theory.fresh_theory():
        try:
            _load_theory_for_proof(data['theory_name'], data['thm_name'], data['vars'])
            state, history = _create_proof_state(data['prop'], data.get('steps', [])[:data['index']])
        except Exception as e:
            return jsonify({'error': str(e)}), 500

        goal_id = data['step'].get('goal_id')
        if not goal_id:
            return jsonify({'results': [], 'ctxt': {}})

        from kernel.proof import ItemID
        goal_id = ItemID(goal_id)
        fact_ids = data['step'].get('fact_ids', [])
        prevs = [ItemID(fid) for fid in fact_ids] if fact_ids else []

        # Backward methods to search
        BACKWARD_SEARCH_METHODS = ['apply_backward_step', 'apply_prev', 'rewrite_goal',
                                   'apply_resolve_step', 'reflexive', 'sym',
                                   'introduction', 'inst_exists_goal', 'simp', 'induction']

        results = []
        fuzzy = []
        import itertools

        def collect(method_name, perm_prevs, exact):
            method_obj = method.get_method(method_name)
            try:
                res = method_obj.search(state, goal_id, perm_prevs)
            except Exception:
                return
            for r in res:
                r['method_name'] = method_name
                r['goal_id'] = str(goal_id)
                if prevs:
                    r['fact_ids'] = [str(p) for p in perm_prevs]
                    r['_facts'] = [printer.print_term(state.get_proof_item(p).th.prop) for p in perm_prevs]
                if '_goal' in r:
                    r['_goal'] = [printer.print_term(t) if not isinstance(t, str) else t for t in r['_goal']]
                if '_thm' in r:
                    if not isinstance(r['_thm'], str):
                        if not isinstance(r['_thm'], str):
                            r['_thm'] = printer.print_term(r['_thm'])
                if exact:
                    r['fuzzy'] = False
                    results.append(r)
                else:
                    r['fuzzy'] = True
                    fuzzy.append(r)

        for method_name in BACKWARD_SEARCH_METHODS:
            if not method.has_method(method_name):
                continue
            method_obj = method.get_method(method_name)
            # Exact: original order, all facts
            collect(method_name, prevs, exact=True)
            if hasattr(method_obj, 'no_order'):
                continue
            # Fuzzy: other permutations of all facts, then subsets, largest first
            n = len(prevs)
            for k in range(n, 0, -1):
                for comb in itertools.combinations(prevs, k):
                    for perm in itertools.permutations(comb):
                        if k == n and list(perm) == prevs:
                            continue  # already in exact
                        collect(method_name, list(perm), exact=False)

        # Goal-centric filtering: if any result closes goal, keep closing + structural
        if any('_goal' in r and len(r['_goal']) == 0 for r in results):
            results = [r for r in results if '_goal' not in r or len(r['_goal']) == 0]

    return jsonify({'results': results, 'fuzzy': fuzzy, 'ctxt': {}})


@app.route('/api/theorem-search', methods=['POST'])
def theorem_search():
    """Search theorems by name pattern within current theory context.
    
    Input:
    * theory_name: name of the theory.
    * thm_name: name of the theorem being proved (for context limit).
    * pattern: search pattern (case-insensitive substring).
    
    Returns:
    * results: list of {name, prop, attrs} for matching theorems.
    """
    data = json.loads(request.get_data().decode("utf-8"))
    pattern = data.get('pattern', '').lower()
    theory_name = data.get('theory_name', '')
    thm_name = data.get('thm_name', '')
    
    results = []
    with theory.fresh_theory():
        try:
            _load_theory_for_proof(theory_name, thm_name, {})
        except Exception:
            return jsonify({'results': []})
        
        for name in theory.thy.get_data("theorems"):
            if pattern and pattern not in name.lower():
                continue
            try:
                th = theory.get_theorem(name)
                attrs = theory.thy.get_attributes(name)
                results.append({
                    'name': name,
                    'prop': str(th.prop),
                    'attrs': list(attrs) if attrs else []
                })
            except Exception:
                pass
    
    return jsonify({'results': results[:30]})

@app.route('/api/theory-status', methods=['GET'])
def theory_status():
    """Return current proof statuses for all theorems."""
    return jsonify(theory.get_all_statuses())

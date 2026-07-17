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
from logic import basic
from logic import context
from server import monitor
from server import items
from app.app import app
from format import pyhol


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


def _create_proof_state(prop, steps, index=None):
    """Helper to create proof state and replay steps.
    
    Returns (state, history) tuple.
    """
    state = server.parse_init_state(prop)
    history = []
    # Only replay steps up to index (if provided)
    replay_steps = steps[:index] if index is not None else steps
    for step in replay_steps:
        history.extend(state.parse_steps([step]))
    return state, history


@app.route('/api/init-saved-proof', methods=['POST'])
def init_saved_proof():
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


@app.route('/api/search-method', methods=['POST'])
def search_method():
    """Search for applicable methods.
    
    Input:
    * theory_name: name of the theory.
    * thm_name: name of the theorem.
    * vars: variable declarations.
    * prop: proposition.
    * steps: list of proof steps.
    * index: current step index.
    * step: current step (goal_id, fact_ids).

    Returns:
    * search_res: list of search results.
    * ctxt: context variables.

    """
    data = json.loads(request.get_data().decode("utf-8"))

    profile = data.get('profile', False)
    if profile:
        pr = cProfile.Profile()
        pr.enable()
    else:
        pr = None

    start_time = time.perf_counter()

    with theory.fresh_theory():
        try:
            _load_theory_for_proof(data['theory_name'], data['thm_name'], data['vars'])
            state, _ = _create_proof_state(data['prop'], data.get('steps', [])[:data['index']])
        except Exception as e:
            print("Load failed: %s" % str(e))
            return jsonify({'search_res': [], 'ctxt': {}})

        print("Load: %f" % (time.perf_counter() - start_time))

        goal_id = data['step']['goal_id']
        fact_ids = data['step']['fact_ids']

        search_res = state.search_method(goal_id, fact_ids)
        with settings.global_setting(unicode=True):
            for res in search_res:
                if '_goal' in res:
                    res['_goal'] = [printer.print_term(t) for t in res['_goal']]
                if '_fact' in res:
                    res['_fact'] = [printer.print_term(t) for t in res['_fact']]

        vars = state.get_vars(goal_id)
        with settings.global_setting(unicode=True, highlight=True):
            print_vars = dict((k, printer.print_type(v)) for k, v in vars.items())
        print("Response:", time.perf_counter() - start_time)

    if pr:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    return jsonify({
        'search_res': search_res,
        'ctxt': print_vars
    })


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


@app.route('/api/apply-method', methods=['POST'])
def apply_method():
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

        try:
            method.apply_method(state, data['step'])
        except Exception as e:
            if isinstance(e, theory.ParameterQueryException):
                return jsonify({
                    "query": e.params
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
            'history': history
        }
        return jsonify(res)


@app.route('/api/check-proof', methods=['POST'])
def check_proof():
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


@app.route('/api/check-theory', methods=['POST'])
def check_theory():
    """Check a theory.
    
    Input:
    * filename: name of the theory file.
    * rewrite: whether to rewrite.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    filename = data['filename']

    with theory.fresh_theory():
        res = monitor.check_theory(filename, rewrite=data['rewrite'])
    return jsonify(res)


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


# ==================== Validation Registry ====================

# In-memory registry: {(theory_name, thm_name): {'status': str, 'gaps': int, 'errors': list}}
validation_registry = {}

# Reverse dependency map: {(theory_name, thm_name): set of (theory_name, thm_name) that depend on it}
reverse_dep_map = {}


def _get_theorems_to_validate(filename):
    """Get list of (theory_name, thm_name, vars, prop, steps) for all theorems in a file and its imports."""
    result = []
    
    # Get import order
    basic.load_metadata()
    depend_list = basic.get_import_order([filename])
    
    for theory_name in depend_list:
        cache = basic.load_theory_cache(theory_name)
        for item in cache['content']:
            if item.ty == 'thm' and item.steps:
                result.append((theory_name, item.name, dict(item.vars) if item.vars else {}, item.prop, item.steps))
    
    return result


def _build_reverse_deps(filename):
    """Build reverse dependency map from steps."""
    global reverse_dep_map
    reverse_dep_map = {}
    
    basic.load_metadata()
    depend_list = basic.get_import_order([filename])
    
    for theory_name in depend_list:
        cache = basic.load_theory_cache(theory_name)
        for item in cache['content']:
            if item.ty == 'thm' and item.steps:
                key = (theory_name, item.name)
                if key not in reverse_dep_map:
                    reverse_dep_map[key] = set()
                
                # Find referenced theorems in steps
                for step in item.steps:
                    if 'theorem' in step:
                        ref_name = step['theorem']
                        # Find which theory this theorem belongs to
                        ref_key = _find_theorem_theory(ref_name, theory_name, depend_list)
                        if ref_key and ref_key != key:
                            if ref_key not in reverse_dep_map:
                                reverse_dep_map[ref_key] = set()
                            reverse_dep_map[ref_key].add(key)


def _find_theorem_theory(thm_name, current_theory, depend_list):
    """Find which theory a theorem belongs to."""
    # Check current theory first
    cache = basic.load_theory_cache(current_theory)
    for item in cache['content']:
        if item.name == thm_name and item.ty in ('thm', 'thm.ax'):
            return (current_theory, thm_name)
    
    # Check dependencies
    for theory_name in depend_list:
        if theory_name == current_theory:
            continue
        cache = basic.load_theory_cache(theory_name)
        for item in cache['content']:
            if item.name == thm_name and item.ty in ('thm', 'thm.ax'):
                return (theory_name, thm_name)
    
    return None


@app.route('/api/validate-theory', methods=['POST'])
def validate_theory():
    """Validate all theorems in a theory file using SSE.
    
    Input:
    * filename: name of the theory file.

    Returns:
    * SSE stream with validation results for each theorem.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    filename = data['filename']

    def generate():
        try:
            with theory.fresh_theory():
                theorems = _get_theorems_to_validate(filename)
                _build_reverse_deps(filename)
            
            total = len(theorems)
            valid = 0
            invalid = 0
            
            for i, (theory_name, thm_name, vars, prop, steps) in enumerate(theorems):
                key = (theory_name, thm_name)
                
                # Check if already validated
                if key in validation_registry:
                    result = validation_registry[key]
                    if result['status'] == 'VALID':
                        valid += 1
                    else:
                        invalid += 1
                    yield f"data: {json.dumps({'name': thm_name, 'status': result['status'], 'gaps': result['gaps'], 'progress': i+1, 'total': total})}\n\n"
                    continue
                
                # Check dependencies first
                dep_failed = False
                for step in steps:
                    if 'theorem' in step:
                        ref_key = _find_theorem_theory(step['theorem'], theory_name, [d[0] for d in theorems])
                        if ref_key and ref_key in validation_registry:
                            if validation_registry[ref_key]['status'] != 'VALID':
                                dep_failed = True
                                failed_dep = ref_key[1]
                                break
                
                if dep_failed:
                    result = {'status': 'DEP_FAILED', 'gaps': 0, 'errors': [], 'failed_dep': failed_dep}
                    validation_registry[key] = result
                    invalid += 1
                    yield f"data: {json.dumps({'name': thm_name, 'status': 'DEP_FAILED', 'failed_dep': failed_dep, 'progress': i+1, 'total': total})}\n\n"
                    continue
                
                # Validate by replaying steps
                try:
                    with theory.fresh_theory():
                        context.set_context(theory_name, limit=('thm', thm_name), vars=vars)
                        state = server.parse_init_state(prop)
                        for step in steps:
                            state.parse_steps([step])
                        state.check_proof(compute_only=True)
                        gaps = len(state.rpt.gaps)
                        
                        if gaps == 0:
                            result = {'status': 'VALID', 'gaps': 0, 'errors': []}
                            valid += 1
                        else:
                            result = {'status': 'STEP_FAILED', 'gaps': gaps, 'errors': []}
                            invalid += 1
                        
                        validation_registry[key] = result
                        yield f"data: {json.dumps({'name': thm_name, 'status': result['status'], 'gaps': result['gaps'], 'progress': i+1, 'total': total})}\n\n"
                except Exception as e:
                    result = {'status': 'STEP_FAILED', 'gaps': 0, 'errors': [str(e)]}
                    validation_registry[key] = result
                    invalid += 1
                    yield f"data: {json.dumps({'name': thm_name, 'status': 'STEP_FAILED', 'errors': [str(e)[:100]], 'progress': i+1, 'total': total})}\n\n"
            
            yield f"data: {json.dumps({'done': True, 'valid': valid, 'invalid': invalid, 'total': total})}\n\n"
        except Exception as e:
            yield f"data: {json.dumps({'error': str(e)})}\n\n"

    return app.response_class(
        generate(),
        mimetype='text/event-stream',
        headers={'Cache-Control': 'no-cache', 'X-Accel-Buffering': 'no'}
    )


@app.route('/api/invalidate', methods=['POST'])
def invalidate():
    """Invalidate validation results for a theorem and its dependents.
    
    Input:
    * theory_name: name of the theory.
    * name: name of the theorem.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    theory_name = data['theory_name']
    thm_name = data['name']
    
    key = (theory_name, thm_name)
    
    # Invalidate self
    validation_registry.pop(key, None)
    
    # Invalidate all dependents (recursively)
    to_invalidate = [key]
    visited = set()
    while to_invalidate:
        current = to_invalidate.pop()
        if current in visited:
            continue
        visited.add(current)
        
        if current in reverse_dep_map:
            for dep_key in reverse_dep_map[current]:
                validation_registry.pop(dep_key, None)
                to_invalidate.append(dep_key)
    
    return jsonify({})

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


def _create_proof_state(prop, steps, index=None):
    """Create proof state and replay steps using stable-ID pipeline."""
    from server.stable_state import StableProofState
    vars_dict = {nm: T for nm, T in context.ctxt.vars.items()}
    sps = StableProofState.create(prop, vars_dict)
    replay = steps[:index] if index is not None else steps
    history = []
    for step in replay:
        ok = sps.apply_method_dict(step)
        entry = {'goal': step.get('goal', 0), 'facts': step.get('facts', [])}
        if not ok:
            entry['error'] = {'err_type': 'ReplayError', 'err_str': 'failed at %s' % step.get('method_name', '?')}
        history.append(entry)
    return sps.state, history


def _fill_step_annotations(item):
    """Replay a theorem's steps and backfill #[N] annotations.

    Steps saved by older versions only stored new_ids (sid) but not the
    proposition text. Replaying assigns the correct sids, so we can
    regenerate [{sid, prop}] entries and export them as #[N] prop lines.

    Mutates item['steps'] in place; silently does nothing if replay fails.
    """
    from server.stable_state import StableProofState
    steps = item.get('steps') or []
    if not steps or all(s.get('new_items') for s in steps):
        return
    try:
        vars_dict = {}
        context.set_context(None, vars=item.get('vars') or {})
        vars_dict = {nm: T for nm, T in context.ctxt.vars.items()}
        sps = StableProofState.create(item.get('prop'), vars_dict)
    except Exception:
        return
    for step in steps:
        old_ths = set(sps.th2sid.keys())
        if not sps.apply_method_dict(step):
            return
        if not step.get('new_items'):
            new_items = sps._find_new_items(old_ths)
            if new_items:
                with settings.global_setting(unicode=True):
                    step['new_items'] = [{'sid': sid, 'prop': printer.print_term(th.prop)}
                                         for sid, th in new_items]


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
        from logic import context as _context
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
            # Backfill #[N] annotations (sid + prop) for steps saved without them
            if item.ty == 'thm' and output_item.get('steps'):
                _fill_step_annotations(output_item)
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

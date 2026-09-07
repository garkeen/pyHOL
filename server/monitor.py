# Author: Bohua Zhan

"""Facility for checking theory files."""

import traceback
import json
import copy
import os
import time
from pstats import Stats
import cProfile

from kernel import theory
from framework import basic
from framework import context
from server import server
from server import methods as method
from framework import logic
from framework import items
from syntax import parser
from solvers import z3wrapper
from syntax.settings import settings, global_setting


def check_proof(item, *, rewrite):
    if item.steps:
        from server.stable_state import StableProofState
        context.set_context(None, vars=item.vars)
        vars_dict = {nm: T for nm, T in context.ctxt.vars.items()}
        sps = StableProofState.create(item.prop, vars_dict)
        for step in item.steps:
            ok = sps.apply_method_dict(step)
            if not ok:
                return {
                    'status': 'Failed',
                    'err_type': 'ReplayError',
                    'err_str': 'failed at %s' % step.get('method_name', '?'),
                    'trace': ''
                }
        if rewrite:
            with global_setting(unicode=True):
                item.proof = sps.state.export_proof()

        try:
            sps.state.check_proof()
        except Exception as e:
            return {
                'status': 'Failed',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback.format_exc()
            }

        return {
            'status': 'OK' if len(sps.state.rpt.gaps) == 0 else 'Partial',
            'num_steps': len(item.steps),
        }
    elif item.proof:
        try:
            context.set_context(None, vars=item.vars)
            state = server.parse_proof(item.proof)
            state.check_proof(no_gaps=True)
        except Exception as e:
            return {
                'status': 'ProofFail',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback.format_exc()
            }
        
        return {
            'status': 'ProofOK'
        }
    else:
        return {
            'status': 'NoSteps'
        }

def check_theory(filename, rewrite=False):
    """Check the theory with the given name."""
    start_time = time.perf_counter()

    data = basic.load_json_data(filename)
    basic.load_theory(filename, limit='start')

    res = []
    stat = {'OK': 0, 'NoSteps': 0, 'Failed': 0, 'Partial': 0,
            'ProofOK': 0, 'ProofFail': 0, 'ParseOK': 0, 'ParseFail': 0, 'EditFail': 0}

    content = []

    for raw_item in data['content']:
        item = items.parse_item(raw_item)
        if item.error:
            e = item.error
            item_res = {
                'ty': item.ty,
                'name': item.name,
                'status': 'ParseFail',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': item.trace
            }
        else:
            exts = item.get_extension()
            old_thy = copy.copy(theory.thy)
            theory.thy.unchecked_extend(exts)
            new_thy = theory.thy

            # Check consistency with edit_item
            with global_setting(unicode=True, highlight=False):
                edit_item = item.get_display()
            theory.thy = old_thy
            item2 = items.parse_edit(edit_item)
            if item.ty == 'thm':
                item2.proof = item.proof
                item2.steps = item.steps
                item2.num_gaps = item.num_gaps
            if item2.error or item != item2:
                item_res = {
                    'ty': item.ty,
                    'name': item.name,
                    'status': 'EditFail'
                }
            elif item.ty == 'thm':
                item_res = check_proof(item, rewrite=rewrite)
                item_res['ty'] = 'thm'
                item_res['name'] = item.name
            else:
                item_res = {
                    'ty': item.ty,
                    'name': item.name,
                    'status': 'ParseOK'
                }
            theory.thy = new_thy

        stat[item_res['status']] += 1
        res.append(item_res)

        if rewrite:
            content.append(item.export_json())

    if rewrite:
        data['content'] = content
        with open(basic.save_user_file(filename), 'w+', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)

    stat['exec_time'] = time.perf_counter() - start_time

    return {
        'data': res,
        'stat': stat
    }


def validate_theory(filename, *, force=False):
    """Validate all theorems in a theory file.

    Uses .json cache: if the .pyhol file has not changed, returns cached
    statuses without re-validating. Otherwise re-validates all theorems
    and writes new cache.

    If force=True, ignores cache and re-validates everything.

    Returns (statuses, errors): statuses is a dict of
    {theorem_name: status} ('VALID', 'STEP_FAILED', 'DEP_FAILED',
    'AXIOM', 'UNPROVED'); errors is a dict of
    {theorem_name: error_message} for every failed theorem.
    """
    # File unchanged, return cached results (unless force)
    if not force and basic.is_cache_valid(filename):
        basic.load_theory(filename)
        return theory.get_all_statuses(), theory.get_all_errors()

    # File changed, re-validate everything
    basic.load_theory(filename)
    content = basic.theory_cache[filename]['content']
    statuses = {}
    errors = {}

    for item in content:
        name = item.name

        if item.ty == 'thm.ax':
            statuses[name] = 'AXIOM'
            theory.thy.set_status(name, 'AXIOM')
            theory.thy.set_error(name, None)
            continue

        if item.ty != 'thm':
            continue

        if not item.steps:
            statuses[name] = 'UNPROVED'
            theory.thy.set_status(name, 'UNPROVED')
            theory.thy.set_error(name, None)
            continue

        # Check if any dependency has failed
        dep_failed = False
        for step in item.steps:
            if 'theorem' in step and step['theorem']:
                dep_status = statuses.get(step['theorem'])
                if dep_status in ('STEP_FAILED', 'DEP_FAILED'):
                    dep_err = errors.get(step['theorem'], '')
                    errors[name] = ('depends on %s which failed%s'
                                    % (step['theorem'],
                                       (': ' + dep_err) if dep_err else ''))
                    dep_failed = True
                    break

        if dep_failed:
            statuses[name] = 'DEP_FAILED'
            theory.thy.set_status(name, 'DEP_FAILED')
            theory.thy.set_error(name, errors[name])
            continue

        # Replay the proof using stable-ID pipeline
        try:
            from server.stable_state import StableProofState
            with theory.fresh_theory():
                context.set_context(filename, limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                sps = StableProofState.create(item.prop,
                    dict(item.vars) if item.vars else {})
                for step in item.steps:
                    if not sps.apply_method_dict(step):
                        raise Exception('replay failed at step: %s' % step.get('method_name', '?'))
                gaps = sps.num_gaps
            statuses[name] = 'VALID' if gaps == 0 else 'STEP_FAILED'
            errors[name] = None if gaps == 0 else 'proof has %d open goal(s)' % gaps
        except Exception as e:
            statuses[name] = 'STEP_FAILED'
            errors[name] = '%s: %s' % (e.__class__.__name__, str(e))

        theory.thy.set_status(name, statuses[name])
        theory.thy.set_error(name, errors[name])

    basic.save_status(filename, statuses)
    return statuses, errors


def _gap_error(state):
    """Extract a readable error message from the remaining proof gaps."""
    try:
        gaps = state.rpt.gaps
        if not gaps:
            return 'proof has unmet goals'
        parts = []
        for g in gaps[:5]:
            txt = str(g)
            # Keep the first line of each gap.
            parts.append(txt.split('\n')[0])
        msg = 'proof has %d open goal(s): %s' % (len(gaps), '; '.join(parts))
        return msg
    except Exception:
        return 'proof has open goals'


if __name__ == "__main__":
    import sys, getopt

    opts, args = getopt.getopt(sys.argv[1:], 'p')

    basic.load_metadata()
    # The z3 macro/method read the injected backend slot; flip it
    # there (the wrapper module global is no longer consulted).
    from framework.macros.z3 import backend as z3_backend
    z3_backend.check_z3 = False

    files = []
    if not args:
        # Load all file names.
        for name, cache in basic.theory_cache['master'].items():
            files.append((cache['order'], name))
        files.sort()
        files = [name for _, name in files]
    else:
        # Load provided names
        files = args

    profile = False
    for opt, arg in opts:
        if opt == '-p':
            profile = True

    if profile:
        pr = cProfile.Profile()
        pr.enable()

    def print_stat(filename, stat):
        return '%17s | %4d | %7d | %6d | %7d | %7d | %9d | %7d | %9d | %8d | %5.2f' % (
            filename, stat['OK'], stat['Partial'], stat['Failed'], stat['NoSteps'], stat['ProofOK'],
            stat['ProofFail'], stat['ParseOK'], stat['ParseFail'], stat['EditFail'], stat['exec_time'])

    print('       File       |  OK  | Partial | Failed | NoSteps | ProofOK | ProofFail | ParseOK | ParseFail | EditFail | Time')
    print('--------------------------------------------------------------------------------------------------------------------')
    total_stat = {
        'OK': 0, 'Partial': 0, 'Failed': 0, 'NoSteps': 0,
        'ProofOK': 0, 'ProofFail': 0, 'ParseOK': 0, 'ParseFail': 0, 'EditFail': 0, 'exec_time': 0.0
    }
    for filename in files:
        res = check_theory(filename)
        print(print_stat(filename, res['stat']))
        for s in total_stat.keys():
            total_stat[s] += res['stat'][s]

    if len(files) > 1:
        print('--------------------------------------------------------------------------------------------------------------------')
        print(print_stat('Total', total_stat))
    else:
        print()
        print(' Item type |           Name           |   Status   ')
        print('---------------------------------------------------')
        for line in res['data']:
            if 'err_type' in line:
                err = " %s: %s" % (line['err_type'], line['err_str'])
            else:
                err = ''
            print("%10s | %24s | %9s%s" % (line['ty'], line['name'], line['status'], err))

    if profile:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats(100)

# Author: Wenfan Zhou, Bohua Zhan

"""API for program verification."""

import json, os
from flask import request
from flask.json import jsonify

from logic import basic
from imperative import imp_compile as imp_compiler
from app.app import app


def _programs_dir():
    """Directory containing .imp files."""
    import os
    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base_dir, 'imperative', 'programs')



@app.route('/api/imp-list', methods=['POST'])
def imp_list():
    """List all .imp program files.

    Returns:
    * files: list of {name, text}.

    """
    programs_dir = _programs_dir()
    files = []
    for fn in sorted(os.listdir(programs_dir)):
        if fn.endswith('.imp'):
            with open(os.path.join(programs_dir, fn), 'r', encoding='utf-8') as f:
                files.append({'name': fn[:-4], 'text': f.read()})
    return jsonify({'files': files})


@app.route('/api/imp-load', methods=['POST'])
def imp_load():
    """Load an .imp file as structured data.

    Returns:
    * theory, imports, programs: [{name, vars, pre, post, body}]

    """
    data = json.loads(request.get_data().decode("utf-8"))
    name = data['name']
    path = os.path.join(_programs_dir(), name + '.imp')
    if not os.path.exists(path):
        return jsonify({'ok': False, 'error': 'File not found: %s.imp' % name})
    try:
        with open(path, 'r', encoding='utf-8') as f:
            text = f.read()
        imp_file = imp_compiler.parse_imp(text)
        programs = []
        for prog in imp_file.programs:
            programs.append({
                'name': prog.name,
                'vars': [[nm, ty] for nm, ty in prog.vars],
                'pre': prog.pre or '',
                'post': prog.post or '',
                'body': prog.body or '',
            })
        return jsonify({
            'ok': True,
            'theory': imp_file.theory or name,
            'imports': imp_file.imports,
            'programs': programs,
        })
    except Exception as e:
        return jsonify({'ok': False, 'error': '%s: %s' % (e.__class__.__name__, str(e))})


def _imp_to_text(theory, imports, programs):
    """Reconstruct .imp text from structured data."""
    lines = ['theory %s' % theory]
    if imports:
        lines.append('imports %s' % ', '.join(imports))
    lines.append('')
    for prog in programs:
        lines.append('program %s' % prog['name'])
        if prog.get('vars'):
            lines.append('  vars: %s' % ', '.join('%s: %s' % (v[0], v[1]) for v in prog['vars']))
        lines.append('  pre: %s' % prog.get('pre', 'true'))
        lines.append('  post: %s' % prog.get('post', 'true'))
        lines.append('  body:')
        for body_line in prog.get('body', '').split('\n'):
            if body_line.strip():
                lines.append('    ' + body_line.strip())
        lines.append('')
    return '\n'.join(lines)


@app.route('/api/imp-compile', methods=['POST'])
def imp_compile():
    """Save (optionally) and compile an .imp program.

    Input:
    * name: name of the program.
    * text: (optional) updated .imp text to save.

    Compiles to library/<name>.pyhol, returns the verification
    conditions (from the kernel vcg) together with their z3 verdict.

    Returns:
    * ok: whether the compilation succeeded.
    * error: error message (if not ok).
    * name, num_vcs, vcs: list of {index, prop, smt} on success.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    name = data['name']

    # Accept either raw text or structured programs.
    if 'programs' in data:
        text = _imp_to_text(data.get('theory', name), data.get('imports', ['hoare']), data['programs'])
    else:
        text = data.get('text')

    path = os.path.join(_programs_dir(), name + '.imp')
    try:
        if text is not None:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)

        # Read existing .pyhol to preserve manual proofs.
        pyhol_path = os.path.join(_programs_dir(), name + '.pyhol')
        existing_pyhol = None
        if os.path.exists(pyhol_path):
            with open(pyhol_path, 'r', encoding='utf-8') as f:
                existing_pyhol = f.read()

        pyhol, num_vcs, vcs = imp_compiler.compile_file(path, existing_pyhol_text=existing_pyhol)

        # Write the translated theorem file.
        with open(pyhol_path, 'w', encoding='utf-8') as f:
            f.write(pyhol)

        # Refresh metadata so that newly written files are visible to
        # load-json-file / validate-theory immediately.
        basic.load_metadata()
    except Exception as e:
        return jsonify({'ok': False, 'error': '%s: %s' % (e.__class__.__name__, str(e))})

    return jsonify({'ok': True, 'name': name, 'num_vcs': num_vcs, 'vcs': vcs})

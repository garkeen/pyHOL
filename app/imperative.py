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
    text = data.get('text')

    path = os.path.join(_programs_dir(), name + '.imp')
    try:
        if text is not None:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)

        pyhol, num_vcs, vcs = imp_compiler.compile_file(path)

        # Write the compiled theorem.
        pyhol_path = os.path.join(_programs_dir(), name + '.pyhol')
        with open(pyhol_path, 'w', encoding='utf-8') as f:
            f.write(pyhol)

        # Refresh metadata so that newly written files are visible to
        # load-json-file / validate-theory immediately.
        basic.load_metadata()
    except Exception as e:
        return jsonify({'ok': False, 'error': '%s: %s' % (e.__class__.__name__, str(e))})

    return jsonify({'ok': True, 'name': name, 'num_vcs': num_vcs, 'vcs': vcs})

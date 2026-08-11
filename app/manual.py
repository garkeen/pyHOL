"""API for serving the markdown manual to the web frontend."""

import json, os
from flask import request
from flask.json import jsonify

from app.app import app


def _manual_dir():
    return os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'manual')


@app.route('/api/manual-list', methods=['POST'])
def manual_list():
    """List all markdown files in the manual directory.

    Returns:
    * files: list of {name, title} in reading order (README first).

    """
    files = []
    for fn in os.listdir(_manual_dir()):
        if fn.endswith('.md'):
            title = fn[:-3]
            files.append({'name': title, 'title': title})
    files.sort(key=lambda f: f['name'])
    files.sort(key=lambda f: f['name'] != 'README')
    return jsonify({'files': files})


@app.route('/api/manual-load', methods=['POST'])
def manual_load():
    """Load the content of a manual markdown file.

    Input:
    * name: file name without the .md extension.

    Returns:
    * name, text: raw markdown text.

    """
    data = json.loads(request.get_data().decode('utf-8'))
    name = data['name']
    path = os.path.join(_manual_dir(), name + '.md')
    if not os.path.exists(path):
        return jsonify({'ok': False, 'error': 'File not found: %s.md' % name})
    with open(path, 'r', encoding='utf-8') as f:
        text = f.read()
    return jsonify({'ok': True, 'name': name, 'text': text})

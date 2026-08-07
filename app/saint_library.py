import os, re, json
from flask import request
from flask.json import jsonify
from SAINT import parser, latex, context
from SAINT.calcfmt import parse_calc_text
from app.app import app

dirname = os.path.dirname(__file__)
EXAMPLES_DIR = os.path.join(dirname, "../SAINT/examples")


@app.route("/api/saint/library", methods=['POST'])
def saint_library():
    """Return library items from base.calc, grouped by section."""
    path = os.path.join(EXAMPLES_DIR, "base.calc")
    with open(path, 'r', encoding='utf-8') as f:
        info = parse_calc_text(f.read())

    sections = []
    cur_section = None
    for item in info.get('content', []):
        if item['type'] == 'header':
            cur_section = {'name': item.get('name', ''), 'level': item.get('level', 1), 'items': []}
            sections.append(cur_section)
        elif item['type'] in ('axiom', 'theorem', 'definition', 'calculation'):
            if cur_section is None:
                cur_section = {'name': '', 'level': 1, 'items': []}
                sections.append(cur_section)
            try:
                e = parser.parse_expr(item['expr'])
                latex_str = latex.convert_expr(e)
            except:
                latex_str = item['expr']
            cur_section['items'].append({
                'type': item['type'], 'expr': item['expr'], 'latex': latex_str,
                'category': item.get('category', ''),
                'conds': item.get('conds', []),
                'attributes': item.get('attributes', []),
                'rule': item.get('rule', ''),
                'const_vars': item.get('const_vars', []),
            })
        elif item['type'] == 'table':
            if cur_section is None:
                cur_section = {'name': '', 'level': 1, 'items': []}
                sections.append(cur_section)
            cur_section['items'].append({
                'type': 'table', 'name': item.get('name', ''),
                'table': dict(item.get('table', {})),
            })
    return jsonify({"sections": sections})


@app.route("/api/saint/library/save", methods=['POST'])
def saint_library_save():
    """Save library items back to base.calc."""
    data = json.loads(request.get_data().decode('utf-8'))
    path = os.path.join(EXAMPLES_DIR, "base.calc")

    lines = ["theory  Base theory", ""]
    for section in data.get('sections', []):
        lines.append('header  "%s"  level = %d' % (section['name'], section.get('level', 1)))
        for item in section.get('items', []):
            t = item['type']
            if t == 'table':
                lines.append('table  %s' % item.get('name', ''))
                for k, v in item.get('table', {}).items():
                    lines.append('  "%s" = "%s"' % (k, v))
                lines.append('endtable')
            else:
                expr = item.get('expr', '')
                parts = ['%s  "%s"' % (t, expr)]
                conds = item.get('conds', [])
                if conds:
                    parts.append('conds = [%s]' % '; '.join(conds))
                attrs = item.get('attributes', [])
                if attrs:
                    parts.append('attributes = [%s]' % '; '.join(attrs))
                cat = item.get('category', '')
                if cat:
                    parts.append('category = %s' % cat)
                rule = item.get('rule', '')
                if rule:
                    parts.append('rule = %s' % rule)
                cv = item.get('const_vars', [])
                if cv:
                    parts.append('const_vars = [%s]' % '; '.join(cv))
                lines.append('  '.join(parts))
        lines.append("")

    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    return jsonify({"status": "ok"})

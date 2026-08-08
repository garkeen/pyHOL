"""Parser and exporter for .pyhol file format.

.pyhol is a human-readable alternative to JSON for storing HOL theories.
It provides lossless bidirectional conversion with the JSON dict format.

Format specification:
    theory <name>
    imports <name1>, <name2>, ...
    description "<text>"

    header "<text>"
    const <name> :: <type> [overloaded]
    datatype <name> [<args>] =\n  | <constr> ...
    type <name> [<args>]
    def <name> :: <type> = <prop> [attrs]
    fun <name> :: <type>\n  | <rule> ...
    inductive <name> :: <type>\n  | <rule_name>: <prop> ...
    axiom <name>\n  fixes ...\n  prop ...\n  [attrs]
    theorem <name>\n  fixes ...\n  prop ...\n  [attrs]\n  proof\n    ...\n  qed
"""

import re


def _norm_arrows(s):
    """Normalize all function arrows to ⇒ (Unicode)."""
    if not isinstance(s, str):
        return s
    return s.replace('=>', '⇒')


# ============================================================
# Exporter: dict → .pyhol
# ============================================================

def export_pyhol(data):
    """Convert a theory dict (JSON-like) to .pyhol text.
    
    Args:
        data: dict with keys 'name', 'imports', 'description', 'content'.
    
    Returns:
        str: .pyhol formatted text.
    """
    lines = []

    # Header
    lines.append('theory %s' % data['name'])
    if data.get('imports'):
        lines.append('imports %s' % ', '.join(data['imports']))
    else:
        lines.append('imports')
    if data.get('domains'):
        lines.append('domains %s' % ', '.join(data['domains']))
    if data.get('description'):
        lines.append('description "%s"' % data['description'])
    lines.append('')

    # Content
    for item in data.get('content', []):
        lines.extend(_export_item(item))
        lines.append('')

    return '\n'.join(lines)


def _export_item(item):
    """Export a single item to .pyhol lines."""
    # Make a copy to avoid modifying the original
    item = dict(item)
    
    # Strip leading/trailing whitespace from name
    if 'name' in item and isinstance(item['name'], str):
        item['name'] = item['name'].strip()
    
    # Normalize prop: join list to string
    if 'prop' in item and isinstance(item['prop'], list):
        item['prop'] = ' '.join(s.strip() for s in item['prop'] if s.strip())
    
    # Normalize all arrows to ⇒
    if 'type' in item and isinstance(item['type'], str):
        item['type'] = _norm_arrows(item['type'])
    if 'prop' in item and isinstance(item['prop'], str):
        item['prop'] = _norm_arrows(item['prop'])
    
    # Normalize arrows in rules
    if 'rules' in item and isinstance(item['rules'], list):
        item['rules'] = [dict(r, prop=_norm_arrows(r['prop'])) if isinstance(r.get('prop'), str) else r for r in item['rules']]
    
    # Normalize arrows in constrs types
    if 'constrs' in item and isinstance(item['constrs'], list):
        item['constrs'] = [dict(c, type=_norm_arrows(c['type'])) if isinstance(c.get('type'), str) else c for c in item['constrs']]
    
    ty = item['ty']

    if ty == 'header':
        return _export_header(item)
    elif ty == 'def.ax':
        return _export_const(item)
    elif ty == 'type.ind':
        return _export_datatype(item)
    elif ty == 'type.ax':
        return _export_type(item)
    elif ty == 'def':
        return _export_def(item)
    elif ty == 'def.ind':
        return _export_fun(item)
    elif ty == 'def.pred':
        return _export_inductive(item)
    elif ty == 'thm.ax':
        return _export_axiom(item)
    elif ty == 'thm':
        return _export_theorem(item)
    else:
        return ['# Unknown item type: %s' % ty]


def _export_header(item):
    name = item.get('name', '')
    # Escape quotes in name
    name = name.replace('"', '\\"')
    depth = item.get('depth', 0)
    if depth:
        return ['header "%s" %d' % (name, depth)]
    return ['header "%s"' % name]


def _export_const(item):
    parts = ['const %s :: %s' % (item['name'], item['type'])]
    if item.get('overloaded'):
        parts.append('overloaded')
    return [' '.join(parts)]


def _export_datatype(item):
    name = item['name']
    args = item.get('args', [])
    constrs = item.get('constrs', [])

    # Header line
    if args:
        header = "datatype %s %s =" % (name, ' '.join("'%s" % a for a in args))
    else:
        header = "datatype %s =" % name

    lines = [header]
    for constr in constrs:
        lines.append('  | %s' % _format_constr(constr))
    return lines


def _format_constr(constr):
    """Format a constructor: name (arg1 :: type1) (arg2 :: type2) :: return_type
    
    If the constructor has no args, just output: name :: type
    If the constructor has args, output: name (arg1 :: type1) ... :: return_type
    """
    name = constr['name']
    args = constr.get('args', [])
    ctype = constr['type']

    if not args:
        # No arguments: zero :: nat
        return '%s :: %s' % (name, ctype)

    # Parse the constructor type to get argument types and return type
    arg_types, ret_type = _split_fun_type(ctype)

    if not arg_types:
        # Can't split type, just output name :: type
        return '%s :: %s' % (name, ctype)

    # Detect arrow style from original type
    use_unicode = '⇒' in ctype

    parts = [name]
    for i, arg in enumerate(args):
        if i < len(arg_types):
            parts.append('(%s :: %s)' % (arg, arg_types[i]))
        else:
            parts.append('(%s)' % arg)
    parts.append(':: %s' % ret_type)
    return ' '.join(parts)


def _split_fun_type(ty):
    """Split 'a => 'b => 'c into (['a', 'b'], 'c').
    
    Handles nested parentheses: ('a => 'b) => 'c => ('d => 'e)
    Handles both '=>' and '⇒' as function type arrows.
    """
    parts = []
    current = ''
    depth = 0
    i = 0
    while i < len(ty):
        ch = ty[i]
        if ch == '(':
            depth += 1
            current += ch
            i += 1
        elif ch == ')':
            depth -= 1
            current += ch
            i += 1
        elif ch == '⇒' and depth == 0:
            if current.strip():
                parts.append(current.strip())
            current = ''
            i += 1
        elif ch == '=' and i + 1 < len(ty) and ty[i+1] == '>' and depth == 0:
            # '=>' arrow
            if current.strip():
                parts.append(current.strip())
            current = ''
            i += 2
        else:
            current += ch
            i += 1

    ret = current.strip()
    if ret:
        parts.append(ret)

    if len(parts) <= 1:
        return [], parts[0] if parts else ty
    return parts[:-1], parts[-1]


def _export_type(item):
    name = item['name']
    args = item.get('args', [])
    if args:
        return ['type %s %s' % (name, ' '.join("'%s" % a for a in args))]
    else:
        return ['type %s' % name]


def _export_def(item):
    attrs = item.get('attributes', [])
    attr_str = ' [%s]' % ','.join(attrs) if attrs else ''
    return ['def %s :: %s = %s%s' % (item['name'], item['type'], item['prop'], attr_str)]


def _export_fun(item):
    name = item['name']
    ty = item['type']
    rules = item.get('rules', [])

    lines = ['fun %s :: %s' % (name, ty)]
    for rule in rules:
        lines.append('  | %s' % rule['prop'])
    return lines


def _export_inductive(item):
    name = item['name']
    ty = item['type']
    rules = item.get('rules', [])

    lines = ['inductive %s :: %s' % (name, ty)]
    for rule in rules:
        lines.append('  | %s: %s' % (rule['name'], rule['prop']))
    return lines


def _export_axiom(item):
    lines = ['axiom %s' % item['name']]

    # fixes
    vars = item.get('vars', {})
    if vars:
        var_parts = ['%s :: %s' % (nm, _norm_arrows(T)) for nm, T in vars.items()]
        lines.append('  fixes %s' % ', '.join(var_parts))

    # prop
    prop = item.get('prop', '')
    if isinstance(prop, list):
        prop = '\n'.join(prop)
    lines.append('  prop %s' % _norm_arrows(prop))

    # attributes
    attrs = item.get('attributes', [])
    if attrs:
        lines.append('  [%s]' % ','.join(attrs))

    return lines


def _export_theorem(item):
    lines = ['theorem %s' % item['name']]

    # fixes
    vars = item.get('vars', {})
    if vars:
        var_parts = ['%s :: %s' % (nm, _norm_arrows(T)) for nm, T in vars.items()]
        lines.append('  fixes %s' % ', '.join(var_parts))

    # prop
    prop = item.get('prop', '')
    if isinstance(prop, list):
        # Multi-line prop (shouldn't happen in core format, but handle gracefully)
        prop = '\n'.join(prop)
    lines.append('  prop %s' % _norm_arrows(prop))

    # attributes
    attrs = item.get('attributes', [])
    if attrs:
        lines.append('  [%s]' % ','.join(attrs))

    # steps (only if non-empty)
    steps = item.get('steps', [])
    if steps:
        lines.append('proof')
        for step in steps:
            lines.append('  %s' % _export_step(step))
        lines.append('qed')

    return lines

# Method -> (positional_keys, remaining_keys are named)
_METHOD_POSITIONAL = {
    'induction': ['var', 'theorem'],
    'rewrite_goal': ['theorem'],
    'rewrite_fact': ['theorem'],
    'apply_backward_step': ['theorem'],
    'apply_forward_step': ['theorem'],
    'apply_resolve_step': ['theorem'],
    'introduction': ['names'],
    'apply_prev': [],
    'rewrite_goal_with_prev': [],
    'rewrite_fact_with_prev': [],
    'apply_fact': [],
    'revert_intro': [],
    'cut': ['cut_goal'],
    'cases': ['case'],
    'forall_elim': ['s'],
    'exists_elim': ['names'],
    'inst_exists_goal': ['s'],
    'thin': [],
    'insert': ['theorem'],
    'drule': ['theorem'],
    'frule': ['theorem'],
    'unfold': ['theorem'],
    'fold': ['theorem'],
    'subst': ['theorem'],
    'new_var': ['name', 'type'],
    'rewrite_goal_with_prev': [],
    'rewrite_fact_with_prev': [],
}

# Keys to skip (goal_id and method_name are handled separately)
_SKIP_KEYS = {'method_name', 'goal_id'}

# Keys that are fact_ids arrays -> format as comma-separated
_FACT_KEYS = {'fact_ids'}


def _export_step(step):
    """Export a step dict to a .pyhol line.

    New format: [<- |-> ] method [positional] [key=value ...] goal=N [facts=[N,...]]
    Old format: goal_id: method [positional] [key=value ...]
    """
    method = step['method_name']

    # New format: goal is an int
    if 'goal' in step and isinstance(step.get('goal'), int):
        from server.stable_state import BACKWARD, FORWARD
        if method in BACKWARD:
            prefix = '← '
        elif method in FORWARD:
            prefix = '→ '
        else:
            prefix = ''
        pos_keys = _METHOD_POSITIONAL.get(method, [])
        positional = []
        for k in pos_keys:
            if k in step:
                val = str(step[k])
                if val:
                    positional.append(_quote_if_needed(val))
        named = {}
        for k, v in step.items():
            if k in _SKIP_KEYS or k in pos_keys or k in ('goal', 'facts', 'new_ids', 'args'):
                continue
            named[k] = str(v)
        parts = [prefix + method]
        if positional:
            parts.extend(positional)
        for k in sorted(named):
            parts.append('%s=%s' % (k, _quote_if_needed(named[k])))
        parts.append('goal=%d' % step['goal'])
        facts = step.get('facts', [])
        if facts:
            parts.append('facts=[%s]' % ','.join(str(f) for f in facts))
        return ' '.join(parts)

    # Old format: goal_id is a string
    goal_id = step.get('goal_id', '0')
    positional, named = _step_to_args(method, step)
    parts = ['%s:' % goal_id, method]
    if positional:
        parts.extend(positional)
    for k, v in sorted(named.items()):
        parts.append('%s=%s' % (k, _quote_if_needed(v)))
    return ' '.join(parts)


def _step_to_args(method, step):
    """Convert a step dict to positional and named args."""
    positional_keys = _METHOD_POSITIONAL.get(method, [])
    positional = []
    named = {}

    # Extract positional args
    for key in positional_keys:
        if key in step:
            positional.append(_quote_if_needed(_norm_arrows(step[key])))

    # Extract fact_ids as positional (prefixed with @)
    if 'fact_ids' in step:
        fact_ids = step['fact_ids']
        if isinstance(fact_ids, list):
            positional.append('@' + ','.join(str(f) for f in fact_ids))
        else:
            positional.append('@' + str(fact_ids))

    # Everything else becomes named
    for key, value in step.items():
        if key in _SKIP_KEYS:
            continue
        if key in positional_keys:
            continue
        if key == 'fact_ids':
            continue
        named[key] = _norm_arrows(str(value))

    return positional, named


def _quote_if_needed(s):
    """Quote a string if it contains spaces, equals signs, newlines, or other special chars."""
    s = str(s)
    if not s:
        return '""'
    # Quote if contains space, =, newline, or parens, and isn't already quoted
    needs_quote = any(c in s for c in (' ', '=', '\n', '(', ')')) and not (s.startswith('"') and s.endswith('"'))
    if needs_quote:
        # Escape newlines and quotes
        s = s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')
        return '"%s"' % s
    return s


# ============================================================
# Parser: .pyhol → dict
# ============================================================

def parse_pyhol(text):
    """Parse .pyhol text to a theory dict (JSON-like).
    
    Args:
        text: str containing .pyhol formatted text.
    
    Returns:
        dict with keys 'name', 'imports', 'description', 'content'.
    """
    lines = text.split('\n')
    result = {
        'name': '',
        'imports': [],
        'domains': [],
        'description': '',
        'content': []
    }

    i = 0
    n = len(lines)

    # Parse header (theory, imports, domains, description)
    while i < n:
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue

        if line.startswith('theory '):
            result['name'] = line[7:].strip()
            i += 1
        elif line == 'imports' or line.startswith('imports '):
            if line == 'imports':
                result['imports'] = []
            else:
                imports_str = line[8:].strip()
                if imports_str:
                    result['imports'] = [s.strip() for s in imports_str.split(',')]
            i += 1
        elif line == 'domains' or line.startswith('domains '):
            # Domain declarations: which Python domain packages to load.
            if line == 'domains':
                result['domains'] = []
            else:
                domains_str = line[8:].strip()
                if domains_str:
                    result['domains'] = [s.strip() for s in domains_str.split(',')]
            i += 1
        elif line.startswith('description '):
            desc = line[12:].strip()
            if desc.startswith('"') and desc.endswith('"'):
                desc = desc[1:-1]
            result['description'] = desc
            i += 1
        else:
            break

    # Parse content items
    while i < n:
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue

        item, i = _parse_item(lines, i)
        if item:
            result['content'].append(item)

    return result


def _parse_item(lines, i):
    """Parse a single item starting at line i.
    
    Returns (item_dict, next_line_index).
    """
    line = lines[i].rstrip()

    if line.startswith('header '):
        return _parse_header(lines, i)
    elif line.startswith('const '):
        return _parse_const(lines, i)
    elif line.startswith('datatype '):
        return _parse_datatype(lines, i)
    elif line.startswith('type '):
        return _parse_type(lines, i)
    elif line.startswith('def '):
        return _parse_def(lines, i)
    elif line.startswith('fun '):
        return _parse_fun(lines, i)
    elif line.startswith('inductive '):
        return _parse_inductive(lines, i)
    elif line.startswith('axiom '):
        return _parse_axiom(lines, i)
    elif line.startswith('theorem '):
        return _parse_theorem(lines, i)
    else:
        # Unknown line, skip
        return None, i + 1


def _parse_header(lines, i):
    line = lines[i].rstrip()
    # header "text" [depth]
    m = re.match(r'^header\s+"(.*?)"\s*(\d+)?$', line)
    if m:
        name = m.group(1).replace('\\"', '"')
        depth = int(m.group(2)) if m.group(2) else 0
    else:
        # Fallback: header text without quotes
        m2 = re.match(r'^header\s+(.+)$', line)
        if m2:
            name = m2.group(1).strip()
            depth = 0
        else:
            name = ''
            depth = 0
    return {'ty': 'header', 'name': name, 'depth': depth}, i + 1


def _parse_const(lines, i):
    line = lines[i].rstrip()
    # const name :: type [overloaded]
    m = re.match(r'^const\s+(\S+)\s+::\s+(.+?)(\s+overloaded)?$', line)
    if not m:
        return None, i + 1
    name = m.group(1)
    ty = _norm_arrows(m.group(2).strip())
    overloaded = bool(m.group(3))
    result = {'ty': 'def.ax', 'name': name, 'type': ty}
    if overloaded:
        result['overloaded'] = True
    return result, i + 1


def _parse_datatype(lines, i):
    line = lines[i].rstrip()
    # datatype name [args] =
    # Parse header
    m = re.match(r'^datatype\s+(\S+)\s*(.*?)\s*=\s*$', line)
    if not m:
        # Try without = on same line (constrs on next lines)
        m = re.match(r'^datatype\s+(\S+)\s*(.*?)\s*=$', line)
    if not m:
        return None, i + 1

    name = m.group(1)
    args_str = m.group(2).strip()
    args = _parse_type_args(args_str)

    constrs = []
    i += 1
    while i < len(lines):
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue
        if not line.startswith('  |'):
            break
        constr_line = line[3:].strip()
        constr = _parse_constr_line(constr_line)
        if constr:
            constrs.append(constr)
        i += 1

    return {'ty': 'type.ind', 'name': name, 'args': args, 'constrs': constrs}, i


def _parse_type_args(args_str):
    """Parse "'a 'b 'c" to ['a', 'b', 'c']."""
    if not args_str:
        return []
    args = []
    for a in args_str.split():
        a = a.strip()
        if a.startswith("'"):
            a = a[1:]
        if a:
            args.append(a)
    return args


def _parse_constr_line(line):
    """Parse a constructor line: name (arg :: type) ... :: return_type"""
    # Split by :: to get name+args and return type
    parts = _split_by_colon_colon(line)
    if len(parts) < 2:
        # No :: found, just a name
        return {'name': line.strip(), 'args': [], 'type': line.strip()}

    left = parts[0].strip()
    ret_type = '::'.join(parts[1:]).strip()

    # Parse left part: name (arg1 :: type1) (arg2 :: type2)
    tokens = _tokenize_constr(left)
    if not tokens:
        return None

    name = tokens[0]
    args = []
    arg_types = []

    i = 1
    while i < len(tokens):
        tok = tokens[i]
        if tok.startswith('(') and tok.endswith(')'):
            # (arg :: type) or (arg)
            inner = tok[1:-1].strip()
            if '::' in inner:
                arg_name, arg_type = inner.split('::', 1)
                args.append(arg_name.strip())
                arg_types.append(arg_type.strip())
            else:
                args.append(inner)
        i += 1

    # Build full type using ⇒ (standard Unicode arrow)
    all_parts = arg_types + [ret_type]
    full_type = ' ⇒ '.join(all_parts) if len(all_parts) > 1 else ret_type

    return {'name': name, 'args': args, 'type': full_type}


def _split_by_colon_colon(s):
    """Split by :: but not inside parentheses."""
    parts = []
    current = ''
    depth = 0
    i = 0
    while i < len(s):
        if s[i] == '(':
            depth += 1
            current += s[i]
        elif s[i] == ')':
            depth -= 1
            current += s[i]
        elif s[i] == ':' and i + 1 < len(s) and s[i+1] == ':' and depth == 0:
            parts.append(current)
            current = ''
            i += 2
            continue
        else:
            current += s[i]
        i += 1
    if current:
        parts.append(current)
    return parts


def _tokenize_constr(s):
    """Tokenize constructor: name (arg :: type) (arg2 :: type2)"""
    tokens = []
    current = ''
    depth = 0
    for ch in s:
        if ch == '(' and depth == 0:
            if current.strip():
                tokens.append(current.strip())
            current = '('
            depth = 1
        elif ch == '(':
            depth += 1
            current += ch
        elif ch == ')' and depth == 1:
            current += ch
            tokens.append(current)
            current = ''
            depth = 0
        elif ch == ')':
            depth -= 1
            current += ch
        elif ch == ' ' and depth == 0:
            if current.strip():
                tokens.append(current.strip())
            current = ''
        else:
            current += ch
    if current.strip():
        tokens.append(current.strip())
    return tokens


def _parse_type(lines, i):
    line = lines[i].rstrip()
    # type name [args]
    m = re.match(r'^type\s+(\S+)\s*(.*?)$', line)
    if not m:
        return None, i + 1
    name = m.group(1)
    args_str = m.group(2).strip()
    args = _parse_type_args(args_str)
    return {'ty': 'type.ax', 'name': name, 'args': args}, i + 1


def _parse_def(lines, i):
    line = lines[i].rstrip()
    # def name :: type = prop [attrs]
    m = re.match(r'^def\s+(\S+)\s+::\s+(.+?)\s*=\s*(.+)$', line)
    if not m:
        return None, i + 1
    name = m.group(1)
    ty = _norm_arrows(m.group(2).strip())
    rest = m.group(3).strip()

    # Parse prop and attributes from rest
    prop, attrs = _parse_prop_and_attrs(rest)
    prop = _norm_arrows(prop)

    result = {'ty': 'def', 'name': name, 'type': ty, 'prop': prop}
    if attrs:
        result['attributes'] = attrs
    return result, i + 1


def _parse_prop_and_attrs(s):
    """Parse "prop [attr1,attr2]" into (prop, attrs_list)."""
    # Check for trailing [attrs]
    m = re.match(r'^(.*?)\s*\[([^\]]+)\]\s*$', s)
    if m:
        prop = m.group(1).strip()
        attrs = [a.strip() for a in m.group(2).split(',')]
        return prop, attrs
    return s.strip(), []


def _parse_fun(lines, i):
    line = lines[i].rstrip()
    # fun name :: type
    m = re.match(r'^fun\s+(\S+)\s+::\s+(.+)$', line)
    if not m:
        return None, i + 1
    name = m.group(1)
    ty = _norm_arrows(m.group(2).strip())

    rules = []
    i += 1
    while i < len(lines):
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue
        if not line.startswith('  |'):
            break
        rule_prop = _norm_arrows(line[3:].strip())
        rules.append({'prop': rule_prop})
        i += 1

    return {'ty': 'def.ind', 'name': name, 'type': ty, 'rules': rules}, i


def _parse_inductive(lines, i):
    line = lines[i].rstrip()
    # inductive name :: type
    m = re.match(r'^inductive\s+(\S+)\s+::\s+(.+)$', line)
    if not m:
        return None, i + 1
    name = m.group(1)
    ty = _norm_arrows(m.group(2).strip())

    rules = []
    i += 1
    while i < len(lines):
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue
        if not line.startswith('  |'):
            break
        rule_line = line[3:].strip()
        # rule_name: prop
        colon_pos = rule_line.find(':')
        if colon_pos > 0:
            rule_name = rule_line[:colon_pos].strip()
            rule_prop = _norm_arrows(rule_line[colon_pos+1:].strip())
            rules.append({'name': rule_name, 'prop': rule_prop})
        i += 1

    return {'ty': 'def.pred', 'name': name, 'type': ty, 'rules': rules}, i


def _parse_axiom(lines, i):
    line = lines[i].rstrip()
    # axiom name
    m = re.match(r'^axiom\s+(\S+)$', line)
    if not m:
        return None, i + 1
    name = m.group(1)

    result = {'ty': 'thm.ax', 'name': name, 'vars': {}, 'prop': ''}
    i += 1
    i = _parse_thm_body(lines, i, result)
    return result, i


def _parse_theorem(lines, i):
    line = lines[i].rstrip()
    # theorem name
    m = re.match(r'^theorem\s+(\S+)$', line)
    if not m:
        return None, i + 1
    name = m.group(1)

    result = {'ty': 'thm', 'name': name, 'vars': {}, 'prop': ''}
    i += 1
    i = _parse_thm_body(lines, i, result)
    
    # Only add steps key if there are actual steps
    if 'steps' in result and not result['steps']:
        del result['steps']
    
    return result, i


def _parse_thm_body(lines, i, result):
    """Parse the body of an axiom or theorem (fixes, prop, attrs, proof)."""
    while i < len(lines):
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue

        if line.startswith('  fixes '):
            # fixes A :: bool, B :: nat
            fixes_str = line[8:].strip()
            for var_decl in fixes_str.split(','):
                var_decl = var_decl.strip()
                if '::' in var_decl:
                    nm, T = var_decl.split('::', 1)
                    result['vars'][nm.strip()] = _norm_arrows(T.strip())
            i += 1
        elif line.startswith('  prop '):
            prop_str = _norm_arrows(line[7:].strip())
            result['prop'] = prop_str
            i += 1
        elif line.startswith('  [') and line.endswith(']'):
            # Attributes line
            attrs_str = line[3:-1].strip()
            if attrs_str:
                result['attributes'] = [a.strip() for a in attrs_str.split(',')]
            i += 1
        elif line.strip() == 'proof':
            # Start of proof block
            i += 1
            steps, i = _parse_proof_block(lines, i)
            result['steps'] = steps
        elif not line.startswith('  '):
            # Not indented, end of this item
            break
        else:
            i += 1

    # Clean up empty vars
    if not result.get('vars'):
        result['vars'] = {}

    return i


def _parse_proof_block(lines, i):
    """Parse a proof block until 'qed'. Supports new #[N] format."""
    steps = []
    current_step = None
    while i < len(lines):
        line = lines[i].rstrip()
        if not line or line.startswith('--'):
            i += 1
            continue
        if line.strip() == 'qed':
            return steps, i + 1
        stripped = line.strip()
        # #[N] annotation line
        m_ann = re.match(r'^#\[(\d+)\]\s*(.*)$', stripped)
        if m_ann and current_step is not None:
            current_step.setdefault('new_ids', []).append(int(m_ann.group(1)))
            i += 1
            continue
        # Method call line (indented)
        if line.startswith('    ') or line.startswith('  '):
            step = _parse_step_line(stripped)
            if step:
                steps.append(step)
                current_step = step
            i += 1
        else:
            break
    return steps, i


def _parse_step_line(line):
    """Parse a new-format step line.

    Format: [← |-> ] method_name [positional_args] [key=value ...] goal=N [facts=[N,...]]
    """
    # Strip direction prefix
    direction = ''
    if line.startswith('← '):
        direction = '←'
        line = line[2:]
    elif line.startswith('→ '):
        direction = '→'
        line = line[2:]
    
    # Tokenize
    tokens = _tokenize_step(line.strip())
    if not tokens:
        return None

    method_name = tokens[0]
    rest_tokens = tokens[1:]

    step = {'method_name': method_name}

    # Extract goal=N and facts=[N,...]
    remaining = []
    for tok in rest_tokens:
        m_goal = re.match(r'^goal=(\d+)$', tok)
        if m_goal:
            step['goal'] = int(m_goal.group(1))
            continue
        m_facts = re.match(r'^facts=\[([\d,\s]*)\]$', tok)
        if m_facts:
            fact_str = m_facts.group(1).strip()
            step['facts'] = [int(f.strip()) for f in fact_str.split(',')] if fact_str else []
            continue
        remaining.append(tok)

    # Parse remaining as positional + named args
    pos_keys = _METHOD_POSITIONAL.get(method_name, [])
    for i, tok in enumerate(remaining):
        if '=' in tok and not tok.startswith('"'):
            k, v = tok.split('=', 1)
            if v.startswith('"') and v.endswith('"'):
                v = v[1:-1]
            step[k] = v
        elif i < len(pos_keys):
            val = tok
            if val.startswith('"') and val.endswith('"'):
                val = val[1:-1]
            step[pos_keys[i]] = val
        else:
            # Extra positional arg
            pass

    return step


def _tokenize_step(s):
    """Tokenize a step line, handling quoted strings.
    
    Handles key="value with spaces" as a single token.
    """
    tokens = []
    current = ''
    in_quote = False
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == '"':
            if in_quote:
                current += ch
                tokens.append(current)
                current = ''
                in_quote = False
            else:
                # Check if this is key="value" pattern
                if current.endswith('='):
                    current += ch
                    in_quote = True
                else:
                    if current.strip():
                        tokens.append(current.strip())
                    current = '"'
                    in_quote = True
        elif ch == ' ' and not in_quote:
            if current.strip():
                tokens.append(current.strip())
            current = ''
        else:
            current += ch
        i += 1
    if current.strip():
        tokens.append(current.strip())
    return tokens


def _apply_step_args(method_name, args, step):
    """Apply parsed args to a step dict based on method."""
    positional_keys = _METHOD_POSITIONAL.get(method_name, [])

    # Separate positional args from named args
    positional = []

    for arg in args:
        if arg.startswith('@'):
            # Fact IDs
            fact_str = arg[1:]
            if fact_str:
                step['fact_ids'] = fact_str.split(',')
            else:
                step['fact_ids'] = []
        elif arg.startswith('"'):
            # Quoted string - always positional (strip quotes, unescape, normalize arrows)
            val = _norm_arrows(arg[1:-1].replace('\\"', '"').replace('\\n', '\n').replace('\\\\', '\\'))
            positional.append(val)
        elif '=' in arg:
            # Named arg: key=value or key="value"
            k, v = arg.split('=', 1)
            if v.startswith('"') and v.endswith('"'):
                v = _norm_arrows(v[1:-1].replace('\\"', '"').replace('\\n', '\n').replace('\\\\', '\\'))
            else:
                v = _norm_arrows(v)
            step[k] = v
        else:
            positional.append(_norm_arrows(arg))

    # Apply positional args
    for i, key in enumerate(positional_keys):
        if i < len(positional):
            step[key] = positional[i]

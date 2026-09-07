"""Clear, categorized errors for Lark-based parsers.

Lark raises opaque exceptions (UnexpectedToken, UnexpectedCharacters,
UnexpectedEOF) whose messages expose internal terminal names such as
`__ANON_13` or `RPAR`.  This module translates them into a readable
`LarkParseError` that tells the user what went wrong (unclosed bracket,
unmatched bracket, undeclared symbol, ...) and where, with a caret
pointing at the offending position.

Used by the HOL term/type parser, the SAINT expression parser, and the
imperative program parser.  See archspec.txt.
"""

import re

from lark import exceptions


class LarkParseError(Exception):
    """A clear, position-aware parse error."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg


# Friendly names for common Lark terminals.
_TERMINAL_NAMES = {
    'CNAME': 'identifier', 'INT': 'number', 'WS': 'whitespace',
    'LPAR': "'('", 'RPAR': "')'", 'LSQB': "'['", 'RSQB': "']'",
    'LBRACE': "'{'", 'RBRACE': "'}'", 'COMMA': "','", 'QUOTE': "'",
    'PERCENT': "'%'", 'MINUS': "'-'", 'PLUS': "'+'", 'STAR': "'*'",
    'SLASH': "'/'", 'IF': "'if'", 'THEN': "'then'", 'ELSE': "'else'",
    '$END': 'end of input', '$START': 'start of input',
}


def _has_unescaped_meta(pat):
    """Whether a Lark terminal pattern contains an unescaped regex
    metacharacter (and is therefore a real regex, not a plain literal)."""
    i = 0
    while i < len(pat):
        ch = pat[i]
        if ch == '\\':
            i += 2
            continue
        if ch in '([{?*+':
            return True
        i += 1
    return False


def _terminal_display(parser, name):
    """Return a human-readable form of a Lark terminal name."""
    if name in _TERMINAL_NAMES:
        return _TERMINAL_NAMES[name]
    for td in parser.terminals:
        if td.name == name:
            p = td.pattern
            if getattr(p, 'type', None) == 'str':
                return "'" + getattr(p, 'value', name) + "'"
            if getattr(p, 'type', None) == 're':
                val = getattr(p, 'value', '')
                if not _has_unescaped_meta(val):
                    return "'" + re.sub(r'\\(.)', r'\1', val) + "'"
            return name
    return name


def translate_lark_error(parser, text, e):
    """Translate a Lark parsing exception into a clear LarkParseError."""
    line = getattr(e, 'line', None)
    col = getattr(e, 'column', None)
    loc = ''
    if line and col:
        loc = ' at line %d, column %d' % (line, col)
    ctx = ''
    try:
        c = e.get_context(text)
        if c:
            ctx = '\n' + c
    except Exception:
        ctx = ''

    if isinstance(e, exceptions.UnexpectedCharacters):
        ch = repr(getattr(e, 'char', ''))
        return LarkParseError(
            "Unrecognized character %s%s.\n"
            "This symbol is not defined in the grammar; check the spelling "
            "or remove it.%s" % (ch, loc, ctx))

    if isinstance(e, exceptions.UnexpectedEOF):
        return LarkParseError(
            "Unexpected end of input%s.\n"
            "This usually means an unclosed parenthesis/bracket or an "
            "incomplete expression.%s" % (loc, ctx))

    if isinstance(e, exceptions.UnexpectedToken):
        tok = getattr(e, 'token', None)
        ttype = getattr(tok, 'type', None)
        tval = getattr(tok, 'value', '')
        if ttype == '$END':
            msg = ("Unexpected end of input%s.\n"
                   "This usually means an unclosed parenthesis/bracket or an "
                   "incomplete expression." % loc)
        elif ttype in ('RPAR', 'RSQB', 'RBRACE'):
            msg = ("Unmatched closing bracket %r%s.\n"
                   "Check for a missing opening bracket earlier in the input."
                   % (tval, loc))
        else:
            msg = "Unexpected token %r%s." % (tval, loc)
        expected = getattr(e, 'expected', None)
        if expected:
            shown = []
            for n in sorted(expected):
                d = _terminal_display(parser, n)
                if d not in shown:
                    shown.append(d)
            msg += "\nExpected one of: %s" % ', '.join(shown)
        return LarkParseError(msg + ctx)

    if isinstance(e, exceptions.MissingToken):
        return LarkParseError("Missing token%s.%s" % (loc, ctx))

    return LarkParseError(str(e) + ctx)
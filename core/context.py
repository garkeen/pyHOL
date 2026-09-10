# Author: Bohua Zhan

import contextlib
from typing import List, Optional, Dict, Union

from kernel.term import Var
from kernel.type import Type
from kernel.theory import Theory
from syntax import parser


class Context:
    """Context keep track of the currently used schematic variables,
    variables, and definitions.
    
    """
    def __init__(self, *, svars: Optional[Dict[str, Union[str, Type]]] = None,
                 vars: Optional[Dict[str, Union[str, Type]]] = None,
                 defs: Optional[Dict[str, Union[str, Type]]] = None):
        # Mapping of schematic variables
        self.svars: Dict[str, Type] = dict()
        if svars is not None:
            for nm, T in svars.items():
                if isinstance(T, str):
                    T = parser.parse_type(T)
                self.svars[nm] = T

        # Mapping of variables
        self.vars: Dict[str, Type] = dict()
        if vars is not None:
            for nm, T in vars.items():
                if isinstance(T, str):
                    T = parser.parse_type(T)
                self.vars[nm] = T

        # Mapping of definitions
        self.defs: Dict[str, Type] = dict()
        if defs is not None:
            for nm, T in defs.items():
                if isinstance(T, str):
                    T = parser.parse_type(T)
                self.defs[nm] = T

    def __eq__(self, other):
        return isinstance(other, Context) and \
            self.vars == other.vars and self.svars == other.svars and self.defs == other.defs

    def __str__(self):
        return 'vars: %s' % str(self.vars)

    def __repr__(self):
        return str(self)

    def get_vars(self) -> List[Var]:
        return [Var(nm, T) for nm, T in self.vars.items()]


"""Global context"""
ctxt = Context()

@contextlib.contextmanager
def fresh_context(*, svars=None, vars=None, defs=None):
    # Record previous context
    global ctxt
    prev_ctxt = ctxt

    # Set fresh context
    ctxt = Context(svars=svars, vars=vars, defs=defs)
    try:
        yield None
    finally:
        # Recover previous context
        ctxt = prev_ctxt

def set_context(thy_name: Optional[str], *, limit=None, svars=None, vars=None, defs=None):
    """Set theory and context (usually for testing).
    
    Parameters
    ==========
    
    thy_name : str or None
        Name of the theory. If None, theory is not changed.

    """
    # Set theory
    if thy_name is not None:
        from core import basic
        basic.load_theory(thy_name, limit=limit)

    # Set context
    global ctxt
    ctxt = Context(svars=svars, vars=vars, defs=defs)


# ---------------------------------------------------------------------------
# Parsing in context.  The parser itself is pure data-in (syntax must not
# read this module's global singleton -- audit §9.5); these wrappers bind
# the current global context to the parser entry points.  Code above
# syntax that relies on the ambient context calls these instead of
# parser.parse_term etc. directly.
# ---------------------------------------------------------------------------

def parse_term(s):
    """Parse a term under the current global context."""
    return parser.parse_term(s, ctxt=ctxt)

def parse_thm(s):
    """Parse a theorem under the current global context."""
    return parser.parse_thm(s, ctxt=ctxt)

def parse_inst(s):
    """Parse a term instantiation under the current global context."""
    return parser.parse_inst(s, ctxt=ctxt)

def parse_named_thm(s):
    """Parse a named theorem under the current global context."""
    return parser.parse_named_thm(s, ctxt=ctxt)

def parse_term_list(s):
    """Parse a list of terms under the current global context."""
    return parser.parse_term_list(s, ctxt=ctxt)


# The kernel's Term(str) constructor delegates to this hook (set by
# syntax.parser).  Rebind it to context-aware parsing so implicit
# Term(...) conversions inside core and above see the current
# global context.  core depends on syntax, so this rebinding
# direction is legal (syntax itself must not import this module).
import kernel.term as _kernel_term
_kernel_term.term_parser = parse_term

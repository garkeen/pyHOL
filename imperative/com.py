# Author: Bohua Zhan

"""Basic data structure for commands.

These are Python-level AST nodes produced by parser2.  The Translator
in imp_compile.py converts them into HOL com terms; VCG itself operates
on HOL terms (imp.py), not on these objects.
"""

from imperative import expr


class Com():
    """Base class for commands.

    Five core constructors (Skip, Assign, Seq, Cond, While) plus
    For, Break, Continue as syntax sugar.  Each subclass stores the
    structural fields accessed by imp_compile.Translator.
    """


class Skip(Com):
    """Skip program."""
    pass

class Assign(Com):
    """Assign program."""
    def __init__(self, v, e):
        if isinstance(v, str):
            v = expr.Var(v)
        assert isinstance(v, expr.Expr) and v.is_ident and isinstance(e, expr.Expr), "Assign"
        self.v = v
        self.e = e

class Seq(Com):
    """Sequence program."""
    def __init__(self, c1, c2):
        assert isinstance(c1, Com) and isinstance(c2, Com), "Seq"
        self.c1 = c1
        self.c2 = c2

class Cond(Com):
    """Conditional program."""
    def __init__(self, b, c1, c2):
        assert isinstance(b, expr.Expr) and isinstance(c1, Com) and isinstance(c2, Com), "Cond"
        self.b = b
        self.c1 = c1
        self.c2 = c2

class While(Com):
    """While program."""
    def __init__(self, b, inv, c):
        assert isinstance(b, expr.Expr) and isinstance(inv, expr.Expr) and isinstance(c, Com), "While"
        self.b = b
        self.inv = inv
        self.c = c

class For(Com):
    """For program: for (init; cond; step) { [inv] body }.

    Desugared by the compiler into a flag variable plus a While.
    """
    def __init__(self, init, cond, step, inv, c):
        assert isinstance(init, Com) and isinstance(cond, expr.Expr)
        assert isinstance(step, Com) and isinstance(inv, expr.Expr) and isinstance(c, Com), "For"
        self.init = init
        self.cond = cond
        self.step = step
        self.inv = inv
        self.c = c

class Break(Com):
    """Break program: exit the innermost loop."""
    pass

class Continue(Com):
    """Continue program: jump to the next loop iteration."""
    pass

class Assert(Com):
    """Assertion checkpoint (desugared by Translator)."""
    def __init__(self, cond):
        assert isinstance(cond, expr.Expr), "Assert"
        self.cond = cond

class Call(Com):
    """Function call (desugared by Translator using callee spec)."""
    def __init__(self, result, fname, args):
        self.result = result
        self.fname = fname
        self.args = list(args)

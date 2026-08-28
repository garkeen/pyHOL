# Author: Bohua Zhan

"""Expressions in the programming language.

Python-level AST nodes produced by parser2.  The Translator in
imp_compile.py converts them into HOL terms; convert_hol (the old
Python-level VCG path) has been removed.
"""

from kernel.type import TFun
from syntax.numeral import IntType
from util import typecheck


class Expr():
    """Base class for expressions."""
    def __init__(self):
        # Whether the expression is an identifier.
        self.is_ident = None

    def subst(self, inst):
        """Substitute using an instantiation."""
        raise NotImplementedError


class Var(Expr):
    """Variables."""
    def __init__(self, name):
        typecheck.checkinstance('Var', name, str)
        self.name = name
        self.is_ident = True

    def __repr__(self):
        return "Var(%s)" % self.name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self


class ArrayElt(Expr):
    """Element of an array."""
    def __init__(self, ident, idx):
        typecheck.checkinstance('ArrayElt', ident, Expr, idx, Expr)
        if not ident.is_ident:
            raise NotImplementedError
        self.ident = ident
        self.idx = idx
        self.is_ident = True

    def __repr__(self):
        return "ArrayElt(%s,%s)" % (repr(self.ident), repr(self.idx))

    def __str__(self):
        return "%s[%s]" % (str(self.ident), str(self.idx))

    def __eq__(self, other):
        return isinstance(other, ArrayElt) and self.ident == other.ident and self.idx == other.idx

    def subst(self, inst):
        return self


class Field(Expr):
    """Field of an identifier. This includes length of an array
    (given by 'length').

    """
    def __init__(self, ident, fieldname):
        typecheck.checkinstance('Field', ident, Expr, fieldname, str)
        if not ident.is_ident:
            raise NotImplementedError
        self.ident = ident
        self.fieldname = fieldname
        self.is_ident = True

    def __repr__(self):
        return "Field(%s,%s)" % (repr(self.ident), self.fieldname)

    def __str__(self):
        return "%s.%s" % (str(self.ident), self.fieldname)

    def __eq__(self, other):
        return isinstance(other, Field) and self.ident == other.ident and self.fieldname == other.fieldname

    def subst(self, inst):
        return self


class Deref(Expr):
    """Dereference: !e reads the value stored at address e."""
    def __init__(self, e):
        typecheck.checkinstance('Deref', e, Expr)
        self.e = e
        self.is_ident = False

    def __repr__(self):
        return "Deref(%s)" % repr(self.e)

    def __str__(self):
        return "!%s" % str(self.e)

    def __eq__(self, other):
        return isinstance(other, Deref) and self.e == other.e

    def subst(self, inst):
        return Deref(self.e.subst(inst))


class Const(Expr):
    """Constant value."""
    def __init__(self, val):
        typecheck.checkinstance('Const', val, (int, bool))
        self.val = val

    def __repr__(self):
        return "Const(%s)" % str(self.val)

    def __str__(self):
        if isinstance(self.val, bool):
            return "true" if self.val else "false"
        else:
            return str(self.val)

    def __eq__(self, other):
        return isinstance(other, Const) and type(self.val) == type(other.val) and self.val == other.val

    def subst(self, inst):
        return self


class Op(Expr):
    """One of pre-specified operators."""
    def __init__(self, op, *args):
        typecheck.checkinstance('Op', op, str, args, [Expr])
        self.op = op

        if len(args) == 1:
            assert op in ["-", "~"]
        else:
            assert len(args) == 2
            assert op in [
                "+", "-", "*",  # arithmetic
                "==", "!=", "<=", "<", ">=", ">",  # comparison
                "&", "|", "-->", "<-->",  # boolean
            ]

        self.args = list(args)

    def __repr__(self):
        return "Op(%s,%s)" % (self.op, ",".join(repr(arg) for arg in self.args))

    def __str__(self):
        if len(self.args) == 1:
            return "%s%s" % (self.op, str(self.args[0]))
        elif len(self.args) == 2:
            arg1 = str(self.args[0])
            arg2 = str(self.args[1])
            if self.op in ('+', '-') and isinstance(self.args[0], Op) and self.args[0].op in ('+', '-'):
                arg1 = '(' + arg1 + ')'
            if self.op == '*' and isinstance(self.args[1], Op) and self.args[1].op in ('+', '-'):
                arg2 = '(' + arg2 + ')'
            return "%s %s %s" % (arg1, self.op, arg2)
        else:
            raise NotImplementedError

    def __eq__(self, other):
        return isinstance(other, Op) and self.op == other.op and self.args == other.args

    def subst(self, inst):
        return Op(self.op, *(arg.subst(inst) for arg in self.args))


class Fun(Expr):
    """Function application."""
    def __init__(self, fname, *args):
        typecheck.checkinstance('Fun', fname, str, args, [Expr])
        self.fname = fname
        self.args = list(args)

    def __repr__(self):
        return "Fun(%s,%s)" % (self.fname, ",".join(repr(arg) for arg in self.args))

    def __str__(self):
        return "%s(%s)" % (self.fname, ",".join(str(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, Fun) and self.fname == other.fname and self.args == other.args

    def subst(self, inst):
        return Fun(self.fname, *(arg.subst(inst) for arg in self.args))


class ITE(Expr):
    """If-then-else expressions."""
    def __init__(self, cond, e1, e2):
        typecheck.checkinstance('ITE', cond, Expr, e1, Expr, e2, Expr)
        self.cond = cond
        self.e1 = e1
        self.e2 = e2

    def __repr__(self):
        return "ITE(%s,%s,%s)" % (repr(self.cond), repr(self.e1), repr(self.e2))

    def __str__(self):
        return "if %s then %s else %s" % (str(self.cond), str(self.e1), str(self.e2))

    def __eq__(self, other):
        return isinstance(other, ITE) and self.cond == other.cond and \
            self.e1 == other.e1 and self.e2 == other.e2

    def subst(self, inst):
        return ITE(self.cond.subst(inst), self.e1.subst(inst), self.e2.subst(inst))


class Forall(Expr):
    """Forall expressions."""
    def __init__(self, var, e):
        typecheck.checkinstance('Forall', var, Var, e, Expr)
        self.var = var
        self.e = e

    def __repr__(self):
        return "Forall(%s,%s)" % (repr(self.var), repr(self.e))

    def __str__(self):
        return "forall %s. %s" % (str(self.var), str(self.e))

    def __eq__(self, other):
        return isinstance(other, Forall) and self.var == other.var and self.e == other.e

    def subst(self, inst):
        if self.var.name in inst:
            raise NotImplementedError

        return Forall(self.var, self.e.subst(inst))


global_fnames = {
    "abs": ("abs", TFun(IntType, IntType)),
    "max": ("max", TFun(IntType, IntType, IntType)),
}

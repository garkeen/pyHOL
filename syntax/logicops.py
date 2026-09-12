# syntax/logicops.py - Sugar for the base logical constants.
#
# The constants true/false/neg/conj/disj/exists are declared in the
# library theory logic_base. The kernel itself knows only the pure
# primitives equals/implies/all. This module provides the Python-side
# constructors and recognition predicates used by the parser, printer,
# and logic automation. The predicates are plain functions taking a
# Term (same idiom as core.logic.is_if / is_xor); nothing here is part
# of the trusted kernel.

from kernel.type import TFun, BoolType
from kernel.term import Term, Var, Const, Lambda, TermException
from util import typecheck

true = Const("true", BoolType)
false = Const("false", BoolType)

neg = Const("neg", TFun(BoolType, BoolType))
conj = Const("conj", TFun(BoolType, BoolType, BoolType))
disj = Const("disj", TFun(BoolType, BoolType, BoolType))


def Not(t):
    """Return negation of boolean term t."""
    typecheck.checkinstance('Not', t, Term)
    return neg(t)

def And(*args):
    """Return the conjunction of the arguments."""
    typecheck.checkinstance('And', args, [Term])
    if not args:
        return true
    res = args[-1]
    for s in reversed(args[:-1]):
        res = conj(s, res)
    return res

def Or(*args):
    """Return the disjunction of the arguments."""
    typecheck.checkinstance('Or', args, [Term])
    if not args:
        return false
    res = args[-1]
    for s in reversed(args[:-1]):
        res = disj(s, res)
    return res

def exists(T):
    return Const("exists", TFun(TFun(T, BoolType), BoolType))

def Exists(*args):
    """Construct the term EX x. body.

    Here x must be a variable and body is a term possibly depending on x.

    """
    typecheck.checkinstance('Exists', args, [Term])
    if len(args) < 1:
        raise TermException("Exists: must provide one term.")
    body = args[-1]
    for x in reversed(args[:-1]):
        if not (x.is_var() or x.is_svar()):
            raise TermException("Exists: x must be a variable. Got %s" % str(x))
        body = exists(x.T)(Lambda(x, body))
    return body


# ============================================================
# Recognition predicates for the base logical constants.
#
# These are plain functions rather than methods installed on Term:
# the constants are library-declared, so the kernel's Term must not
# know them. Callers import the predicates explicitly, which makes the
# dependency a construction-level fact instead of an import-order
# side effect.
# ============================================================

def is_not(t):
    """Whether t is of form ~A."""
    return t.is_comb('neg', 1)

def is_conj(t):
    """Whether t is of the form A & B."""
    return t.is_comb('conj', 2)

def strip_conj(t):
    """Given s1 & ... & sn, return [s1, ..., sn]."""
    res = []
    while is_conj(t):
        res.append(t.arg1)
        t = t.arg
    res.append(t)
    return res

def is_disj(t):
    """Whether t is of the form A | B."""
    return t.is_comb('disj', 2)

def strip_disj(t):
    """Given s1 | ... | sn, return [s1, ..., sn]."""
    res = []
    while is_disj(t):
        res.append(t.arg1)
        t = t.arg
    res.append(t)
    return res

def is_exists(t):
    """Whether t is of the form ?x. P x."""
    return t.is_comb('exists', 1)

def strip_exists(t, *, num=None):
    """Given ?x1 x2 ... xn. body, return ([x1, x2, ..., xn], body)"""
    args = []
    while is_exists(t) and (num is None or num > 0):
        body = t.arg
        v = Var(body.var_name, body.var_T)
        args.append(v)
        t = body.subst_bound(v)
        if num is not None:
            num -= 1
    return args, t

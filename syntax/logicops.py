# syntax/logicops.py - Sugar for the base logical constants.
#
# The constants true/false/neg/conj/disj/exists are declared in the
# library theory logic_base. The kernel itself knows only the pure
# primitives equals/implies/all. This module provides the Python-side
# constructors and recognition methods (installed on Term) used by the
# parser, printer, and logic automation. Importing it installs the
# sugar; nothing here is part of the trusted kernel.

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
# Recognition methods on Term for the base logical constants.
# ============================================================

def _term_is_not(self):
    """Whether self is of form ~A."""
    return self.is_comb('neg', 1)

def _term_is_conj(self):
    """Whether t is of the form A & B."""
    return self.is_comb('conj', 2)

def _term_strip_conj(self):
    """Given s1 & ... & sn, return [s1, ..., sn]."""
    t = self
    res = []
    while t.is_conj():
        res.append(t.arg1)
        t = t.arg
    res.append(t)
    return res

def _term_is_disj(self):
    """Whether t is of the form A | B."""
    return self.is_comb('disj', 2)

def _term_strip_disj(self):
    """Given s1 | ... | sn, return [s1, ..., sn]."""
    t = self
    res = []
    while t.is_disj():
        res.append(t.arg1)
        t = t.arg
    res.append(t)
    return res

def _term_is_exists(self):
    """Whether self is of the form ?x. P x."""
    return self.is_comb('exists', 1)

def _term_strip_exists(self, *, num=None):
    """Given ?x1 x2 ... xn. body, return ([x1, x2, ..., xn], body)"""
    args = []
    t = self
    while t.is_exists() and (num is None or num > 0):
        body = t.arg
        v = Var(body.var_name, body.var_T)
        args.append(v)
        t = body.subst_bound(v)
        if num is not None:
            num -= 1
    return args, t


Term.is_not = _term_is_not
Term.is_conj = _term_is_conj
Term.strip_conj = _term_strip_conj
Term.is_disj = _term_is_disj
Term.strip_disj = _term_strip_disj
Term.is_exists = _term_is_exists
Term.strip_exists = _term_strip_exists

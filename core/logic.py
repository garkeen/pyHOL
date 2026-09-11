# Author: Bohua Zhan

from typing import List, Tuple

from kernel.type import TFun, BoolType
from kernel.term import Term, SVar, Var, Const, Inst, Lambda
from kernel.proofterm import ProofTerm, eval_macro
from core import matcher
from syntax.logicops import true, false, neg, conj, disj, Not, And, Or, \
    exists, Exists  # noqa: F401  (re-export; also installs Term methods)
from util import name
from util import typecheck


"""Utility functions for logic (domain-independent).

The base logical constants true/false/neg/conj/disj/exists are declared
in the library theory logic_base; their Python-side sugar lives in
syntax/logicops.py and is re-exported here for convenience."""

def is_exists1(t):
    """Whether t is of the form ?!x. P x."""
    return t.is_comb('exists1', 1)

def mk_exists1(x, body):
    """Given a variable x and a term P possibly depending on x, return
    the term ?!x. P.

    """
    assert x.is_var(), "mk_exists1"
    exists1_t = Const("exists1", TFun(TFun(x.T, BoolType), BoolType))
    return exists1_t(Lambda(x, body))

def is_the(t):
    """Whether t is of the form THE x. P x."""
    return t.is_comb('The', 1)

def mk_the(x, body):
    """Given a variable x and a term P possibly depending on x, return
    the term THE x. P.

    """
    assert x.is_var(), "mk_the"
    the_t = Const("The", TFun(TFun(x.T, BoolType), x.T))
    return the_t(Lambda(x, body))

def mk_some(x, body):
    """Given a variable x and a term P possibly depending on x, return
    the term SOME x. P.

    """
    assert x.is_var(), "mk_some"
    some_t = Const("Some", TFun(TFun(x.T, BoolType), x.T))
    return some_t(Lambda(x, body))

def if_t(T):
    return Const("IF", TFun(BoolType, T, T, T))

def is_if(t):
    """Whether t is of the form if P then x else y."""
    return t.is_comb("IF", 3)

def mk_if(P, x, y):
    """Obtain the term if P then x else y."""
    return if_t(x.get_type())(P, x, y)

def get_forall_names(t, svar=True):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    return the names x_1, ... x_k.

    """
    def helper(t):
        if t.is_forall():
            return [t.arg.var_name] + helper(t.arg.body)
        else:
            return []
    old_names = []
    if not svar:
        old_names = [v.name for v in t.get_vars()]
    return name.get_variant_names(helper(t), old_names)

def strip_all_implies(t, names, svar=True):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    Return the triple ([v_1, ..., v_k], [A_1, ... A_n], C), where
    v_1, ..., v_k are new variables with the given names, and
    A_1, ..., A_n, C are the body of the input term, with bound variables
    substituted for v_1, ..., v_k.

    """
    if t.is_forall():
        assert len(names) > 0, "strip_all_implies: not enough names input."
        assert isinstance(names[0], str), "strip_all_implies: names must be strings."
        if svar:
            v = SVar(names[0], t.arg.var_T)
        else:
            v = Var(names[0], t.arg.var_T)
        vars, As, C = strip_all_implies(t.arg.subst_bound(v), names[1:], svar=svar)
        return ([v] + vars, As, C)
    else:
        assert len(names) == 0, "strip_all_implies: too many names input."
        As, C = t.strip_implies()
        return ([], As, C)

def strip_exists(t, names):
    """Given a term of the form

    ?x_1 ... x_k. C

    Return the pair ([v_1, ..., v_k], C), where C is the body of the
    input term, with bound variables substituted for v_1, ..., v_k.

    """
    if t.is_exists() and len(names) > 0:
        assert isinstance(names[0], str), "strip_exists: names must be strings."
        v = Var(names[0], t.arg.var_T)
        vars, body = strip_exists(t.arg.subst_bound(v), names[1:])
        return ([v] + vars, body)
    else:
        return ([], t)

def is_xor(t: Term):
    return t.is_comb('xor', 2)

def apply_theorem(th_name: str, *pts: ProofTerm, concl=None, inst=None) -> ProofTerm:
    """Wrapper for apply_theorem and apply_theorem_for macros.

    The function takes optional arguments concl, inst. Matching
    always starts with inst. If conclusion is specified, it is
    matched next. Finally, the assumptions are matched.

    """
    typecheck.checkinstance('apply_theorem', pts, [ProofTerm])
    if concl is None and inst is None:
        # Normal case, can use apply_theorem
        return eval_macro("apply_theorem", th_name, pts)
    else:
        pt = ProofTerm.theorem(th_name)
        if inst is None:
            inst = Inst()
        if concl is not None:
            inst = matcher.first_order_match(pt.concl, concl, inst)
        for i, prev in enumerate(pts):
            inst = matcher.first_order_match(pt.assums[i], prev.prop, inst)
        return eval_macro("apply_theorem_for", (th_name, inst), pts)

def strip_disj(t):
    res = []
    def helper(t):
        if t.is_disj():
            ts = t.strip_disj()
            for sub_t in ts:
                helper(sub_t)
        else:
            res.append(t)
    helper(t)
    return res

def strip_conj(t):
    res = []
    def helper(t):
        if t.is_conj():
            ts = t.strip_conj()
            for sub_t in ts:
                helper(sub_t)
        else:
            res.append(t)
    helper(t)
    return res

# util/nat.py - Natural number utility functions

from kernel.type import TFun, BoolType, NatType
from kernel import term
from kernel.term import Term, Const, Not, Eq, Binary, Nat, Inst
from kernel.thm import Thm
from kernel import theory
from kernel.proofterm import ProofTerm
from logic.logic import apply_theorem
from util import poly


def convert_to_poly(t):
    """Convert natural number expression to polynomial."""
    if t.is_var():
        return poly.singleton(t)
    elif t.is_number():
        return poly.constant(t.dest_number())
    elif t.is_plus():
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif t.is_times():
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    elif t.is_minus():
        t1, t2 = t.args
        p1, p2 = convert_to_poly(t1), convert_to_poly(t2)
        if p1.is_constant() and p2.is_constant():
            n1 = p1.get_constant()
            n2 = p2.get_constant()
            if n1 <= n2:
                return poly.constant(0)
            else:
                return poly.constant(n1 - n2)
        else:
            return poly.singleton(t)
    else:
        return poly.singleton(t)

def is_bit0(t):
    return t.is_comb('bit0', 1)

def is_bit1(t):
    return t.is_comb('bit1', 1)

def nat_eval(t):
    """Evaluate a term with arithmetic operations.
    
    Return a Python integer.
    
    """
    from logic.conv.nat import nat_eval as _nat_eval
    return _nat_eval(t)


def ineq_zero_proof_term(n):
    """Returns the inequality n ~= 0."""
    assert n != 0, "ineq_zero_proof_term: n = 0"
    if n == 1:
        return ProofTerm.theorem("one_nonzero")
    elif n % 2 == 0:
        return apply_theorem("bit0_nonzero", ineq_zero_proof_term(n // 2))
    else:
        return apply_theorem("bit1_nonzero", inst=Inst(m=Binary(n // 2)))

def ineq_one_proof_term(n):
    """Returns the inequality n ~= 1."""
    assert n != 1, "ineq_one_proof_term: n = 1"
    if n == 0:
        return apply_theorem("ineq_sym", ProofTerm.theorem("one_nonzero"))
    elif n % 2 == 0:
        return apply_theorem("bit0_neq_one", inst=Inst(m=Binary(n // 2)))
    else:
        return apply_theorem("bit1_neq_one", ineq_zero_proof_term(n // 2))

def ineq_proof_term(m, n):
    """Returns the inequality m ~= n."""
    assert m != n, "ineq_proof_term: m = n"
    if n == 0:
        return ineq_zero_proof_term(m)
    elif n == 1:
        return ineq_one_proof_term(m)
    elif m == 0:
        return apply_theorem("ineq_sym", ineq_zero_proof_term(n))
    elif m == 1:
        return apply_theorem("ineq_sym", ineq_one_proof_term(n))
    elif m % 2 == 0 and n % 2 == 0:
        return apply_theorem("bit0_neq", ineq_proof_term(m // 2, n // 2))
    elif m % 2 == 1 and n % 2 == 1:
        return apply_theorem("bit1_neq", ineq_proof_term(m // 2, n // 2))
    elif m % 2 == 0 and n % 2 == 1:
        return apply_theorem("bit0_bit1_neq", inst=Inst(m=Binary(m // 2), n=Binary(n // 2)))
    else:
        return apply_theorem("ineq_sym", ineq_proof_term(n, m))

def nat_const_ineq(a, b):
    return ProofTerm("nat_const_ineq", Not(Eq(a, b)), [])

def nat_less_eq(t1, t2):
    return ProofTerm("nat_const_less_eq", t1 <= t2)

def nat_less(t1, t2):
    return ProofTerm("nat_const_less", t1 < t2)

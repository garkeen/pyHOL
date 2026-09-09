# util/integer.py - Integer utility functions

from syntax import numeral
from fractions import Fraction
from kernel.type import TFun, BoolType
from syntax.numeral import NatType, IntType
from kernel.term import Term, Const, Eq, Inst
from syntax.numeral import Binary, Nat, greater_eq, less_eq, greater, less
from kernel.thm import Thm
from kernel import term
from kernel.proofterm import ProofTerm
from theories.nat import util_nat as nat
from core import logic
from core.logic import apply_theorem
from theories import poly


# Basic definitions
zero = Const('zero', IntType)
one = Const('one', IntType)
plus = numeral.plus(IntType)
minus = numeral.minus(IntType)
uminus = numeral.uminus(IntType)
times = numeral.times(IntType)
equals = term.equals(IntType)
less_eq = numeral.less_eq(IntType)
less = numeral.less(IntType)
greater_eq = numeral.greater_eq(IntType)
greater = numeral.greater(IntType)
of_nat = numeral.of_nat(IntType)

int_of_nat = Const("int_of_nat", TFun(NatType, IntType))


def strip_plus(t):
    """Strip top-level additions, returning a list of terms."""
    if t.is_plus():
        return strip_plus(t.arg1) + [t.arg]
    else:
        return [t]

def strip_plus_full(t):
    """Strip all additions including subtraction (a + (-b))."""
    if t.is_plus():
        return strip_plus_full(t.arg1) + strip_plus_full(t.arg)
    elif t.is_minus():
        return strip_plus_full(t.arg1) + [uminus(t.arg)]
    elif t.is_uminus():
        return [uminus(arg) for arg in strip_plus_full(t.arg)]
    else:
        return [t]

def strip_times(t):
    """Strip top-level multiplications, returning a list of terms."""
    if t.is_times():
        return strip_times(t.arg1) + [t.arg]
    else:
        return [t]

def strip_times_full(t):
    """Strip all multiplications."""
    if t.is_times():
        return strip_times_full(t.arg1) + strip_times_full(t.arg)
    else:
        return [t]

def dest_times(t):
    """Destruct a multiplication term into (left, right)."""
    assert t.is_times(), "dest_times"
    return t.arg1, t.arg

def compare_atom(t1, t2):
    """Compare two atoms for polynomial normalization."""
    from kernel.term_ord import fast_compare
    return fast_compare(t1, t2)

def int_eval(t):
    """Evaluate an integer term to a Python int."""
    if t.is_number():
        return t.dest_number()
    elif t.is_plus():
        return int_eval(t.arg1) + int_eval(t.arg)
    elif t.is_minus():
        return int_eval(t.arg1) - int_eval(t.arg)
    elif t.is_times():
        return int_eval(t.arg1) * int_eval(t.arg)
    elif t.is_uminus():
        return -int_eval(t.arg)
    else:
        raise ValueError("int_eval: cannot evaluate %s" % t)

def convert_to_poly(t):
    """Convert integer expression to polynomial."""
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
        return convert_to_poly(t1) - convert_to_poly(t2)
    elif t.is_uminus():
        return -convert_to_poly(t.arg)
    else:
        return poly.singleton(t)

def from_mono(m):
    """Convert a monomial to a term."""
    coeff, body = m
    if body is None:
        return Nat(abs(coeff))
    elif coeff == 1:
        return body
    elif coeff == -1:
        return uminus(body)
    else:
        return times(Nat(abs(coeff)), body)

def from_poly(p):
    """Convert a polynomial to a term."""
    if p.is_constant():
        return Nat(abs(p.get_constant()))
    elif p.is_monomial():
        return from_mono((p.get_coeff(), p.get_body()))
    else:
        monos = p.get_monomials()
        result = from_mono(monos[0])
        for m in monos[1:]:
            coeff, body = m
            if coeff >= 0:
                result = plus(result, from_mono(m))
            else:
                result = minus(result, from_mono((-coeff, body)))
        return result

def compare_monomial(t1, t2):
    """Compare two monomials for normalization."""
    from kernel.term_ord import fast_compare
    return fast_compare(t1, t2)

def collect_int_polynomial_coeff(poly):
    """Collect polynomial coefficients for integer inequality."""
    # Implementation depends on polynomial representation
    pass

def omega_compare_monomial(t1, t2):
    """Compare monomials for omega normalization."""
    from kernel.term_ord import fast_compare
    return fast_compare(t1, t2)

# syntax/numeral.py - Arithmetic and numeral sugar.
#
# All constants referenced here (zero, one, bit0, bit1, of_nat, plus,
# times, less_eq, power, ...) are declared in library theories
# (nat/int/real). Nothing in this module is part of the trusted kernel:
# numerals are syntax-level sugar. Importing this module installs the
# sugar on Term (methods and operator overloads) and provides the
# Python-side constructors used by the parser, printer, and automation
# code.

import math
from fractions import Fraction

from kernel.type import Type, TConst, TFun, BoolType
from kernel.term import Term, Const, Var
from util import typecheck

# Numeral types. The types themselves are declared by library theories:
# nat is a datatype (zero | Suc), int and real are axiomatic types.
NatType = TConst('nat')
IntType = TConst('int')
RealType = TConst('real')


def is_numeral_type(T):
    return T in (NatType, IntType, RealType)


# ============================================================
# Arithmetic constant constructors
# ============================================================

def plus(T):
    return Const('plus', TFun(T, T, T))

def minus(T):
    return Const('minus', TFun(T, T, T))

def uminus(T):
    return Const('uminus', TFun(T, T))

def times(T):
    return Const('times', TFun(T, T, T))

def divides(T):
    return Const('real_divide', TFun(T, T, T))

def of_nat(T):
    return Const('of_nat', TFun(NatType, T))

def of_int(T):
    return Const('of_int', TFun(IntType, T))

def nat_power(T):
    return Const('power', TFun(T, NatType, T))

def int_power(T):
    return Const('power', TFun(T, IntType, T))

def real_power(T):
    return Const('power', TFun(T, RealType, T))

def less_eq(T):
    return Const('less_eq', TFun(T, T, BoolType))

def less(T):
    return Const('less', TFun(T, T, BoolType))

def greater_eq(T):
    return Const('greater_eq', TFun(T, T, BoolType))

def greater(T):
    return Const('greater', TFun(T, T, BoolType))

# Binary bits 0 and 1
nat_zero = Const('zero', NatType)
nat_one = Const('one', NatType)
bit0 = Const("bit0", TFun(NatType, NatType))
bit1 = Const("bit1", TFun(NatType, NatType))


def Binary(n):
    """Convert Python integer n to HOL binary form.

    This function does not apply of_nat.

    """
    typecheck.checkinstance('Binary', n, int)
    if n == 0:
        return nat_zero
    elif n == 1:
        return nat_one
    elif n % 2 == 0:
        return bit0(Binary(n // 2))
    else:
        return bit1(Binary(n // 2))

def Number(T, x):
    """Convert Python number x to HOL term with type T."""
    if x == 0:
        return Const('zero', T)
    if x == 1:
        return Const('one', T)
    if x < 0:
        assert T != NatType, "Number: natural numbers cannot be negative."
        return uminus(T)(Number(T, -x))
    if isinstance(x, Fraction):
        if x.denominator == 1:
            return Number(T, x.numerator)
        else:
            assert T != NatType, "Number: natural numbers cannot be fractions."
            assert T != IntType, "Number: integers cannot be fractions."
            return divides(T)(Number(T, x.numerator), Number(T, x.denominator))

    return of_nat(T)(Binary(x))

def Nat(n):
    """Construct natural number with value n."""
    return Number(NatType, n)


def Eq(s, t):
    """Construct the term s = t.

    Python numbers (int/Fraction) are accepted on either side and
    converted via Number. The kernel's kernel.term.Eq handles terms
    only; this sugar version lives here because numeral conversion is
    syntax-level sugar.

    """
    if isinstance(s, (int, Fraction)):
        assert isinstance(t, Term), "Eq: one of the arguments must be a term."
        s = Number(t.get_type(), s)
    elif isinstance(t, (int, Fraction)):
        t = Number(s.get_type(), t)
    from kernel.term import Eq as kernel_eq
    return kernel_eq(s, t)

def Int(n):
    """Construct integer with value n."""
    return Number(IntType, n)

def Real(r):
    """Construct real number with value r."""
    return Number(RealType, r)

def Sum(T, ts):
    """Compute the sum of a list of terms with type T."""
    ts = list(ts)  # Coerce generators to list
    typecheck.checkinstance('Sum', T, Type, ts, [Term])
    if len(ts) == 0:
        return Const('zero', T)
    res = ts[0]
    for t in ts[1:]:
        res = res + t
    return res

def Prod(T, ts):
    """Compute the product of a list of terms with type T."""
    ts = list(ts)  # Coerce generators to list
    typecheck.checkinstance('Prod', T, Type, ts, [Term])
    if len(ts) == 0:
        return Const('one', T)
    res = ts[0]
    for t in ts[1:]:
        res = res * t
    return res

def IntVars(s):
    """Create a list of variables of int type.

    s is a string containing space-separated names of variables.

    """
    nms = s.split(' ')
    return [Var(nm, IntType) for nm in nms]


# ============================================================
# Term methods: arithmetic recognition and destructors.
# Defined as plain functions, installed on Term below.
# ============================================================

def is_binary(self):
    """Whether self is in standard binary form.

    Note binary form means no of_nat is applied.

    """
    if self.is_const("zero") or self.is_const("one"):
        return True
    elif self.is_comb('bit0', 1) or self.is_comb('bit1', 1):
        return self.arg.is_binary()
    else:
        return False

def dest_binary(self):
    """Convert HOL binary form to Python integer.

    Note binary form means no of_nat is applied.

    """
    if self.is_const("zero"):
        return 0
    elif self.is_const("one"):
        return 1
    elif self.is_comb('bit0', 1):
        return 2 * self.arg.dest_binary()
    elif self.is_comb('bit1', 1):
        return 2 * self.arg.dest_binary() + 1
    else:
        from kernel.term import TermException
        raise TermException('dest_binary: term is not in binary form.')

def is_nat(self):
    return self.get_type() == NatType

def is_int(self):
    return self.get_type() == IntType

def is_real(self):
    return self.get_type() == RealType

def is_zero(self):
    return self.is_const('zero')

def is_one(self):
    return self.is_const('one')

def is_plus(self):
    return self.is_comb('plus', 2)

def is_minus(self):
    return self.is_comb('minus', 2)

def is_uminus(self):
    return self.is_comb('uminus', 1)

def is_times(self):
    return self.is_comb('times', 2)

def is_divides(self):
    return self.is_comb('real_divide', 2)

def is_real_inverse(self):
    return self.is_comb("real_inverse", 1) and self.arg.get_type() == RealType

def is_nat_power(self):
    return self.is_comb('power', 2) and self.arg.get_type() == NatType

def is_real_power(self):
    return self.is_comb('power', 2) and self.arg.get_type() == RealType

def is_nat_number(self):
    """Whether self represents a nonnegative integer (of any type)."""
    return self.is_zero() or self.is_one() or (self.is_comb('of_nat', 1) and self.arg.is_binary())

def is_frac_number(self):
    """Whether self represents a nonnegative fraction (of any type).

    Note we check that the fraction in normal form: the denominator
    is not 1, and the numerator and denominator have gcd 1.

    """
    if self.is_divides():
        if not (self.arg1.is_nat_number() and self.arg.is_nat_number()):
            return False

        m, n = self.arg1.dest_number(), self.arg.dest_number()
        return n != 1 and math.gcd(m, n) == 1
    else:
        return self.is_nat_number()

def is_number(self):
    """Whether self represents a number.

    Note we check that the number is in normal form. If the number
    is nonnegative, it is a natural number or fraction in normal form.
    Otherwise, it is in the form -x where x > 0.

    """
    if self.is_zero():
        return True
    if self.is_one():
        return True

    if self.is_uminus():
        return self.arg.is_frac_number() and not self.arg.is_zero()
    else:
        return self.is_frac_number()

def is_constant(self):
    """Whether self represents a constant.

    Note the constant could be in arbitrary form.
    """
    if self.is_number():
        return True
    elif self.is_uminus():
        return self.arg.is_constant()
    elif self.head.name in ("plus", "minus", "times", "real_divide", "power"):
        return self.arg1.is_constant() and self.arg.is_constant()
    else:
        return False

def dest_number(self):
    """Convert a term to a Python number."""
    if self.is_zero():
        return 0
    if self.is_one():
        return 1

    if self.is_uminus():
        return -self.arg.dest_number()
    if self.is_divides():
        num, denom = self.arg1.dest_number(), self.arg.dest_number()
        if denom == 0:
            return 0  # n / 0 = 0 in the HOL library
        elif denom == 1:
            return num
        else:
            return Fraction(num) / denom

    if not (self.is_comb('of_nat', 1) and self.arg.is_binary()):
        from kernel.term import TermException
        raise TermException('dest_number: term %s is not a number.' % self)
    return self.arg.dest_binary()

def is_less_eq(self):
    return self.is_comb('less_eq', 2)

def is_less(self):
    return self.is_comb('less', 2)

def is_greater_eq(self):
    return self.is_comb('greater_eq', 2)

def is_greater(self):
    return self.is_comb('greater', 2)

def is_compares(self):
    """Whether self is of the form A <(=) B or A >(=) B"""
    return self.is_less() or self.is_less_eq() or self.is_greater() or self.is_greater_eq()


# ============================================================
# Operator overloads: build arithmetic terms using Python syntax.
# ============================================================

def _term_add(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    if not isinstance(other, Term):
        return NotImplemented
    return plus(T)(self, other)

def _term_radd(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return plus(T)(other, self)

def _term_sub(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return minus(T)(self, other)

def _term_rsub(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return minus(T)(other, self)

def _term_mul(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return times(T)(self, other)

def _term_rmul(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return times(T)(other, self)

def _term_truediv(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return divides(T)(self, other)

def _term_rtruediv(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return divides(T)(other, self)

def _term_neg(self):
    T = self.get_type()
    return uminus(T)(self)

def _term_pos(self):
    return self

def _term_pow(self, other):
    T = self.get_type()
    if isinstance(other, int) and other >= 0:
        other = Number(NatType, other)
    elif isinstance(other, (int, Fraction)):
        other = Number(RealType, other)
    if other.get_type() == NatType:
        return nat_power(T)(self, other)
    elif other.get_type() == RealType:
        return real_power(T)(self, other)
    else:
        from kernel.term import TermException
        raise TermException('__pow__: unexpected type for exponent.')

def _term_rpow(self, other):
    if not isinstance(other, Term):
        from kernel.term import TermException
        raise TermException('__rpow__: base must be a HOL term.')
    base_T = other.get_type()
    exponent_T = self.get_type()
    if exponent_T == NatType:
        return nat_power(base_T)(other, self)
    elif exponent_T == RealType:
        return real_power(base_T)(other, self)
    else:
        from kernel.term import TermException
        raise TermException('__rpow__: unexpected type for exponent.')

def _term_le(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return less_eq(T)(self, other)

def _term_lt(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return less(T)(self, other)

def _term_ge(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return greater_eq(T)(self, other)

def _term_gt(self, other):
    T = self.get_type()
    if isinstance(other, (int, Fraction)):
        other = Number(T, other)
    return greater(T)(self, other)


def strip_plus(t):
    """Given t1 + ... + tn, return [t1, ..., tn].

    Plain term-shape helper over the "+" sugar (not a Term method).
    Single definition point shared by the integer domain convs and the
    omega solver core.
    """
    if t.is_plus():
        return strip_plus(t.arg1) + [t.arg]
    else:
        return [t]


# ============================================================
# Install the sugar on Term.
# ============================================================

Term.is_binary = is_binary
Term.dest_binary = dest_binary
Term.is_nat = is_nat
Term.is_int = is_int
Term.is_real = is_real
Term.is_zero = is_zero
Term.is_one = is_one
Term.is_plus = is_plus
Term.is_minus = is_minus
Term.is_uminus = is_uminus
Term.is_times = is_times
Term.is_divides = is_divides
Term.is_real_inverse = is_real_inverse
Term.is_nat_power = is_nat_power
Term.is_real_power = is_real_power
Term.is_nat_number = is_nat_number
Term.is_frac_number = is_frac_number
Term.is_number = is_number
Term.is_constant = is_constant
Term.dest_number = dest_number
Term.is_less_eq = is_less_eq
Term.is_less = is_less
Term.is_greater_eq = is_greater_eq
Term.is_greater = is_greater
Term.is_compares = is_compares

Term.__add__ = _term_add
Term.__radd__ = _term_radd
Term.__sub__ = _term_sub
Term.__rsub__ = _term_rsub
Term.__mul__ = _term_mul
Term.__rmul__ = _term_rmul
Term.__truediv__ = _term_truediv
Term.__rtruediv__ = _term_rtruediv
Term.__neg__ = _term_neg
Term.__pos__ = _term_pos
Term.__pow__ = _term_pow
Term.__rpow__ = _term_rpow
Term.__le__ = _term_le
Term.__lt__ = _term_lt
Term.__ge__ = _term_ge
Term.__gt__ = _term_gt

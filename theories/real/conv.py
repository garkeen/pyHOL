# Author: Bohua Zhan

from syntax import numeral
from fractions import Fraction
import math
from sympy.ntheory.factor_ import factorint

from kernel.type import TFun
from syntax.numeral import RealType
from kernel import term
from kernel.term import Term, Const, Eq
from syntax.numeral import Nat, Real, Sum, Prod
from kernel.proofterm import TacticException, eval_macro
from kernel import term_ord
from theories.nat import util_nat as nat
from theories.integer import util_integer as integer
from syntax.set_tools import setT
from core import auto
from core import matcher
from core.conv import rewr_conv, binop_conv, arg1_conv, arg_conv, try_conv, Conv, ConvException
from kernel.proofterm import refl, ProofTerm
from theories import poly
from syntax.logicops import is_not

# Basic definitions

zero = Const('zero', RealType)
one = Const('one', RealType)
plus = numeral.plus(RealType)
minus = numeral.minus(RealType)
uminus = numeral.uminus(RealType)
times = numeral.times(RealType)
divides = numeral.divides(RealType)
nat_power = numeral.nat_power(RealType)
real_power = numeral.real_power(RealType)
of_nat = numeral.of_nat(RealType)
equals = term.equals(RealType)
less_eq = numeral.less_eq(RealType)
less = numeral.less(RealType)
greater_eq = numeral.greater_eq(RealType)
greater = numeral.greater(RealType)

inverse = Const("real_inverse", TFun(RealType, RealType))
sqrt = Const("sqrt", TFun(RealType, RealType))
pi = Const("pi", RealType)

# Transcendental functions

log = Const("log", TFun(RealType, RealType))
exp = Const("exp", TFun(RealType, RealType))
sin = Const("sin", TFun(RealType, RealType))
cos = Const("cos", TFun(RealType, RealType))
tan = Const("tan", TFun(RealType, RealType))
cot = Const("cot", TFun(RealType, RealType))
sec = Const("sec", TFun(RealType, RealType))
csc = Const("csc", TFun(RealType, RealType))
hol_abs = Const("abs", TFun(RealType, RealType))
atn = Const("atn", TFun(RealType, RealType))

# Intervals

closed_interval = Const("real_closed_interval", TFun(RealType, RealType, setT(RealType)))
open_interval = Const("real_open_interval", TFun(RealType, RealType, setT(RealType)))
lopen_interval = Const("real_lopen_interval", TFun(RealType, RealType, setT(RealType)))
ropen_interval = Const("real_ropen_interval", TFun(RealType, RealType, setT(RealType)))

def real_eval(t):
    """Evaluate t as a constant. Return an integer or rational number.

    Assume t does not contain non-rational constants.

    """
    def rec(t):
        if t.is_number():
            return t.dest_number()
        elif t.is_comb('of_nat', 1):
            return nat.nat_eval(t.arg)
        elif t.is_comb('of_int', 1):
            return integer.int_eval(t.arg)
        elif t.is_plus():
            return rec(t.arg1) + rec(t.arg)
        elif t.is_minus():
            return rec(t.arg1) - rec(t.arg)
        elif t.is_uminus():
            return -rec(t.arg)
        elif t.is_times():
            return rec(t.arg1) * rec(t.arg)
        elif t.is_divides():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_eval: divide by zero')
            elif denom == 1:
                return rec(t.arg1)
            else:
                return Fraction(rec(t.arg1)) / denom
        elif t.is_real_inverse():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_eval: divide by zero')
            else:
                return Fraction(1) / denom
        elif t.is_nat_power():
            return rec(t.arg1) ** nat.nat_eval(t.arg)
        elif t.is_real_power():
            x, p = rec(t.arg1), rec(t.arg)
            if p == 0:
                return 1
            elif x == 0:
                return 0
            elif x == 1:
                return 1
            elif isinstance(p, int):
                if p >= 0:
                    return rec(t.arg1) ** p
                else:
                    return Fraction(1) / (rec(t.arg1) ** (-p))
            else:
                raise ConvException('real_eval: %s' % str(t))
        else:
            raise ConvException('real_eval: %s' % str(t))
    
    res = rec(t)
    if isinstance(res, Fraction) and res.denominator == 1:
        return res.numerator
    else:
        return res

def real_approx_eval(t):
    """Evaluate t to a Python numeral (int or float) value.

    This is an imprecise (but more general) version of real_eval.

    """
    def rec(t):
        if t.is_number():
            return t.dest_number()
        elif t.is_comb('of_nat', 1):
            return nat.nat_eval(t.arg)
        elif t.is_comb('of_int', 1):
            return integer.int_eval(t.arg)
        elif t.is_plus():
            return rec(t.arg1) + rec(t.arg)
        elif t.is_minus():
            return rec(t.arg1) - rec(t.arg)
        elif t.is_uminus():
            return -rec(t.arg)
        elif t.is_times():
            return rec(t.arg1) * rec(t.arg)
        elif t.is_divides():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_approx_eval: divide by zero')
            else:
                return rec(t.arg1) / denom
        elif t.is_real_inverse():
            denom = rec(t.arg)
            if denom == 0:
                raise ConvException('real_approx_eval: divide by zero')
            else:
                return 1 / denom
        elif t.is_nat_power():
            return rec(t.arg1) ** nat.nat_eval(t.arg)
        elif t.is_real_power():
            x, p = rec(t.arg1), rec(t.arg)
            return x ** p
        elif t.is_comb() and t.head == sqrt:
            return math.sqrt(rec(t.arg))
        elif t == pi:
            return math.pi
        elif t.is_comb() and t.head == sin:
            return math.sin(rec(t.arg))
        elif t.is_comb() and t.head == cos:
            return math.cos(rec(t.arg))
        elif t.is_comb() and t.head == tan:
            return math.tan(rec(t.arg))
        elif t.is_comb() and t.head == cot:
            return math.cot(rec(t.arg))
        elif t.is_comb() and t.head == sec:
            return math.sec(rec(t.arg))
        elif t.is_comb() and t.head == csc:
            return math.csc(rec(t.arg))
        elif t.is_comb() and t.head == atn:
            return math.atan(rec(t.arg))
        elif t.is_comb() and t.head == log:
            return math.log(rec(t.arg))
        elif t.is_comb() and t.head == exp:
            return math.exp(rec(t.arg))
        elif t.is_comb() and t.head == hol_abs:
            return abs(rec(t.arg))
        else:
            raise NotImplementedError

    return rec(t)


class real_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, t):
        if t.get_type() != RealType:
            return refl(t)
        try:
            simp_t = Real(real_eval(t))
        except (ConvException, ValueError, NotImplementedError):
            # Terms containing variables cannot be evaluated as constants;
            # skip them (refl is always a sound fallback).
            return refl(t)
        if simp_t == t:
            return refl(t)
        return eval_macro('real_eval', Eq(t, simp_t))


"""Normalization of polynomials.

Each monomial is in the form x, c * x, or c, where c is a numerical
constant (may be rational) and x is a product of atoms.

Each atom is of the form x ^ n (nat_power), x ^ r (real_power), or
simply x (no powers). Powers are combined (e.g. x ^ m * x ^ n = x ^ (m + n))
but not automatically expanded.

"""

def dest_monomial(t):
    """Remove the coefficient part of a monomial t."""
    if t.is_times() and t.arg1.is_number():
        return t.arg
    elif t.is_number():
        return one
    else:
        return t

class to_coeff_form(Conv):
    """Convert c to c * 1, x to 1 * x, and leave c * x unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_times() and t.arg1.is_number():
            return pt
        elif t.is_number():  # c to c * 1
            return pt.on_rhs(rewr_conv('real_mul_rid', sym=True))
        else:  # x to 1 * x
            return pt.on_rhs(rewr_conv('real_mul_lid', sym=True))

class from_coeff_form(Conv):
    """Convert c * 1 to c, 1 * x to x, and leave c * x unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_one():
            return pt.on_rhs(rewr_conv('real_mul_rid'))
        elif t.arg1.is_one():
            return pt.on_rhs(rewr_conv('real_mul_lid'))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv('real_mul_rzero'))
        elif t.arg1.is_zero():
            return pt.on_rhs(rewr_conv('real_mul_lzero'))
        else:
            return pt

class combine_monomial(Conv):
    """Combine (add) two monomials with the same body."""
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            binop_conv(to_coeff_form()),
            rewr_conv('real_add_rdistrib', sym=True),
            arg1_conv(real_eval_conv()),
            from_coeff_form())

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b."""
    def get_proof_term(self, t):
        pt = refl(t)
        return pt.on_rhs(
            rewr_conv('real_add_assoc', sym=True),
            arg_conv(rewr_conv('real_add_comm')),
            rewr_conv('real_add_assoc'))

def atom_less(t1, t2):
    """Compare two atoms, put constants in front."""
    if not t1.has_var() and t2.has_var():
        return True
    elif not t2.has_var() and t1.has_var():
        return False
    else:
        return term_ord.fast_compare(t1, t2) < 0

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + b."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("real_add_lid"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("real_add_rid"))
        elif t.arg1.is_plus():
            # Left side has more than one term. Compare last term with a
            m1, m2 = dest_monomial(t.arg1.arg), dest_monomial(t.arg)
            if m1 == m2:
                pt = pt.on_rhs(rewr_conv('real_add_assoc', sym=True),
                               arg_conv(combine_monomial()))
                if pt.rhs.arg.is_zero():
                    pt = pt.on_rhs(rewr_conv('real_add_rid'))
                return pt
            elif atom_less(m1, m2):
                return pt
            else:
                pt = pt.on_rhs(swap_add_r(), arg1_conv(self))
                if pt.rhs.arg1.is_zero():
                    pt = pt.on_rhs(rewr_conv('real_add_lid'))
                return pt
        else:
            # Left side is an atom. Compare two sides
            m1, m2 = dest_monomial(t.arg1), dest_monomial(t.arg)
            if m1 == m2:
                return pt.on_rhs(combine_monomial())
            elif atom_less(m1, m2):
                return pt
            else:
                return pt.on_rhs(rewr_conv('real_add_comm'))

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_m)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv('real_add_assoc'), arg1_conv(self), norm_add_monomial())
        else:
            return pt.on_rhs(norm_add_monomial())

auto.add_global_autos_norm(plus, norm_add_polynomial())


def dest_atom(t):
    """Remove power part of an atom t."""
    if t.is_comb('exp', 1):
        return exp(one)
    elif t.is_nat_power() and t.arg.is_number():
        return t.arg1
    elif t.is_real_power() and t.arg.is_number():
        return t.arg1
    else:
        return t

class to_exponent_form(Conv):
    """Convert x to x ^ 1, and leave x ^ n or x ^ r unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_comb('exp', 1):
            return pt
        elif t.is_nat_power() and t.arg.is_number():
            return pt
        elif t.is_real_power() and t.arg.is_number():
            return pt
        else:
            return pt.on_rhs(rewr_conv('real_pow_1', sym=True))

class from_exponent_form(Conv):
    """Convert x ^ 1 to x, and leave x ^ n or x ^ r unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_comb('exp', 1):
            return pt
        elif t.is_nat_power() and t.arg.is_one():
            return pt.on_rhs(rewr_conv('real_pow_1'))
        elif t.is_real_power() and t.arg.is_one():
            return pt.on_rhs(rewr_conv('rpow_1'))
        elif t.is_real_power() and t.arg.is_zero():
            return pt.on_rhs(rewr_conv('rpow_0'))
        else:
            return pt

class combine_atom(Conv):
    """Combine (multiply) two atoms with the same body.
    
    This may require conditions on the body, as the combination
    (x ^ p) * (x ^ q) = x ^ (p + q), where p and q are rational
    numbers, requires assuming x >= 0. No condition is required
    for (x ^ m) * (x ^ n) = x ^ (m + n), where m and n are
    natural numbers.

    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t).on_rhs(binop_conv(to_exponent_form()))
        if pt.rhs.arg1.is_comb('exp', 1) and pt.rhs.arg.is_comb('exp', 1):
            # Both sides are exponentials
            return pt.on_rhs(rewr_conv('real_exp_add', sym=True),
                             arg_conv(auto.norm_conv(self.conds)))
        elif pt.rhs.arg1.is_nat_power() and pt.rhs.arg.is_nat_power():
            # Both sides are natural number powers, simply add
            return pt.on_rhs(rewr_conv('real_pow_add', sym=True),
                             arg_conv(nat.nat_conv()))
        else:
            # First check that x > 0 can be proved. If not, just return
            # without change.
            x = pt.rhs.arg1.arg1
            try:
                x_gt_0 = auto.solve(x > 0, self.conds)
            except TacticException:
                return refl(t)

            # Convert both sides to real powers
            if pt.rhs.arg1.is_nat_power():
                pt = pt.on_rhs(arg1_conv(rewr_conv('rpow_pow', sym=True)))
            if pt.rhs.arg.is_nat_power():
                pt = pt.on_rhs(arg_conv(rewr_conv('rpow_pow', sym=True)))
            pt = pt.on_rhs(rewr_conv('rpow_add', sym=True, conds=[x_gt_0]),
                           arg_conv(real_eval_conv()))

            # Simplify back to nat if possible
            if pt.rhs.arg.is_comb('of_nat', 1):
                pt = pt.on_rhs(rewr_conv('rpow_pow'),
                               arg_conv(rewr_conv('nat_of_nat_def', sym=True)))

            return pt.on_rhs(from_exponent_form())

class swap_mult_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b."""
    def get_proof_term(self, t):
        pt = refl(t)
        return pt.on_rhs(
            rewr_conv('real_mult_assoc', sym=True),
            arg_conv(rewr_conv('real_mult_comm')),
            rewr_conv('real_mult_assoc'))

class norm_mult_atom(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * b.
    
    It is possible for a_i or b to be 1 (signifying empty atom) but not
    any other constant number.
    
    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_one():
            return pt.on_rhs(rewr_conv('real_mul_lid'))
        elif t.arg.is_one():
            return pt.on_rhs(rewr_conv('real_mul_rid'))
        elif t.arg1.is_times():
            # Left side has more than one atom. Compare last atom with b
            m1, m2 = dest_atom(t.arg1.arg), dest_atom(t.arg)
            if m1 == m2:
                pt = pt.on_rhs(rewr_conv('real_mult_assoc', sym=True),
                               arg_conv(combine_atom(self.conds)))
                if pt.rhs.arg.is_one():
                    pt = pt.on_rhs(rewr_conv('real_mul_rid'))
                return pt
            elif atom_less(m1, m2):
                return pt
            else:
                pt = pt.on_rhs(swap_mult_r(), arg1_conv(self))
                if pt.rhs.arg1.is_one():
                    pt = pt.on_rhs(rewr_conv('real_mul_lid'))
                return pt
        else:
            # Left side is an atom. Compare two sides
            m1, m2 = dest_atom(t.arg1), dest_atom(t.arg)
            if m1 == m2:
                return pt.on_rhs(combine_atom(self.conds))
            elif atom_less(m1, m2):
                return pt
            else:
                return pt.on_rhs(rewr_conv('real_mult_comm'))

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_m)."""
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_times():
            return pt.on_rhs(rewr_conv('real_mult_assoc'),
                             arg1_conv(self),
                             norm_mult_atom(self.conds))
        else:
            return pt.on_rhs(norm_mult_atom(self.conds))

class norm_mult_monomials(Conv):
    """Normalize (c_1 * m_1) * (c_2 * m_2), where c_1, c_2 are constants,
    and m_1, m_2 are monomials.

    """
    def __init__(self, conds):
        self.conds = conds

    def get_proof_term(self, t):
        pt = refl(t)
        is_l_atom = (dest_monomial(t.arg1) == t.arg1)
        is_r_atom = (dest_monomial(t.arg) == t.arg)
        if is_l_atom and is_r_atom:
            return pt.on_rhs(norm_mult_monomial(self.conds))
        elif is_l_atom and not is_r_atom:
            if t.arg.is_number():
                return pt.on_rhs(
                    rewr_conv('real_mult_comm'),
                    try_conv(rewr_conv('real_mul_rid')),
                    try_conv(rewr_conv('real_mul_lzero')))
            else:
                return pt.on_rhs(
                    arg_conv(rewr_conv('real_mult_comm')),
                    rewr_conv('real_mult_assoc'),
                    rewr_conv('real_mult_comm'),
                    arg_conv(norm_mult_monomial(self.conds)))
        elif not is_l_atom and is_r_atom:
            if t.arg1.is_number():
                return pt.on_rhs(
                    try_conv(rewr_conv('real_mul_rid')),
                    try_conv(rewr_conv('real_mul_lzero')))
            else:
                return pt.on_rhs(
                    rewr_conv('real_mult_assoc', sym=True),
                    arg_conv(norm_mult_monomial(self.conds)))
        else:
            return pt.on_rhs(
                binop_conv(to_coeff_form()),  # (c_1 * m_1) * (c_2 * m_2)
                rewr_conv('real_mult_assoc'),  # (c_1 * m_1 * c_2) * m_2
                arg1_conv(swap_mult_r()),  # (c_1 * c_2 * m_1) * m_2
                arg1_conv(arg1_conv(real_eval_conv())),  # (c_1c_2 * m_1) * m_2
                rewr_conv('real_mult_assoc', sym=True),  # c_1c_2 * (m_1 * m_2)
                arg_conv(norm_mult_monomial(self.conds)),
                from_coeff_form())

def norm_mult(t, pts):
    """Normalization of mult. Assume two sides are in normal form."""
    pt = refl(t)
    if t.arg1.is_plus():
        return pt.on_rhs(rewr_conv('real_add_rdistrib'))
    elif t.arg.is_plus():
        return pt.on_rhs(rewr_conv('real_add_ldistrib'))
    else:
        return pt.on_rhs(norm_mult_monomials(pts))

auto.add_global_autos_norm(times, norm_mult)

def norm_uminus(t, pts):
    """Normalization of uminus."""
    pt = refl(t)
    if t.is_number():
        return pt.on_rhs(real_eval_conv())
    else:
        return pt.on_rhs(rewr_conv('real_poly_neg1'))

auto.add_global_autos_norm(uminus, norm_uminus)

auto.add_global_autos_norm(minus, auto.norm_rules(['real_poly_neg2']))

def norm_divides(t, pts):
    """Normalization of divides."""
    pt = refl(t)
    if t.is_number():
        return pt.on_rhs(real_eval_conv())
    else:
        return pt.on_rhs(rewr_conv('real_divide_def'))

auto.add_global_autos_norm(divides, norm_divides)

auto.add_global_autos_norm(
    inverse,
    auto.norm_rules([
        'rpow_neg_one'
    ]))

auto.add_global_autos_norm(
    of_nat,
    auto.norm_rules([
        'real_of_nat_id',
        'real_of_nat_add',
        'real_of_nat_mul'
    ]))

auto.add_global_autos_norm(nat_power, real_eval_conv())

auto.add_global_autos_norm(
    nat_power,
    auto.norm_rules([
        'real_nat_power_def_1',
        'real_nat_power_def_2',
        'real_pow_1',
        'real_pow_one',
        'real_pow_mul',
        'real_pow_pow',
        'rpow_rpow_nat2',
        'real_exp_n_sym',
    ])
)

class real_nat_power_conv(Conv):
    def get_proof_term(self, t):
        """Unfold powers of 2 and 3, leave other powers unexpanded."""
        a, p = t.args

        # Exponent is 2, apply real_add_ldistrib to avoid folding back.
        if p.is_number() and p.dest_number() == 2 and a.is_plus():
            return refl(t).on_rhs(rewr_conv('real_pow_2'),
                                  rewr_conv('real_add_ldistrib'))
        # Exponent is 3
        elif p.is_number() and p.dest_number() == 3 and a.is_plus():
            return refl(t).on_rhs(rewr_conv('real_pow_3'),
                                  rewr_conv('real_add_ldistrib'))

        return refl(t)

auto.add_global_autos_norm(nat_power, real_nat_power_conv())

auto.add_global_autos_norm(real_power, real_eval_conv())

auto.add_global_autos_norm(
    real_power,
    auto.norm_rules([
        'rpow_0',
        'rpow_1',
        'rpow_rpow',
        'rpow_rpow_nat1',
        'rpow_mul',
        'rpow_base_divide',
        'rpow_exp',
        'rpow_abs',
    ])
)

class real_power_conv(Conv):
    def get_proof_term(self, t):
        a, p = t.args

        # Exponent is an integer: apply rpow_pow
        if p.is_number() and p.is_comb('of_nat', 1) and p.arg.is_binary():
            return refl(t).on_rhs(arg_conv(rewr_conv('real_of_nat_id', sym=True)),
                                  rewr_conv('rpow_pow'))

        if not (a.is_number() and p.is_number()):
            raise ConvException

        a, p = a.dest_number(), p.dest_number()
        if a <= 0:
            raise ConvException

        # Case 1: base is a composite number
        factors = factorint(a)
        keys = list(factors.keys())
        if len(keys) > 1 or (len(keys) == 1 and keys[0] != a):
            b1 = list(factors.keys())[0]
            b2 = a // b1
            eq_th = refl(Real(b1) * b2).on_rhs(real_eval_conv())
            pt = refl(t).on_rhs(arg1_conv(rewr_conv(eq_th, sym=True)))
            pt = pt.on_rhs(rewr_conv('rpow_mul'))
            return pt

        # Case 2: exponent is not between 0 and 1
        if isinstance(p, Fraction) and p.numerator // p.denominator != 0:
            div, mod = divmod(p.numerator, p.denominator)
            eq_th = refl(Real(div) + Real(mod) / p.denominator).on_rhs(real_eval_conv())
            pt = refl(t).on_rhs(arg_conv(rewr_conv(eq_th, sym=True)))
            a_gt_0 = auto.auto_solve(Real(a) > 0)
            pt = pt.on_rhs(rewr_conv('rpow_add', conds=[a_gt_0]))
            return pt

        return refl(t)

auto.add_global_autos_norm(real_power, real_power_conv())

auto.add_global_autos_norm(
    sqrt,
    auto.norm_rules([
        'rpow_sqrt'
    ]))

def convert_to_poly(t):
    """Convert a term t to polynomial normal form."""
    if t.is_var():
        return poly.singleton(t)
    elif t.is_number():
        return poly.constant(t.dest_number())
    elif t.is_comb('of_nat', 1):
        return nat.convert_to_poly(t.arg)
    elif t.is_plus():
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif t.is_minus():
        t1, t2 = t.args
        return convert_to_poly(t1) - convert_to_poly(t2)
    elif t.is_uminus():
        return -convert_to_poly(t.arg)
    elif t.is_times():
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    elif t.is_divides():
        num, denom = t.args
        p_denom = convert_to_poly(denom)
        if p_denom.is_nonzero_constant():
            return convert_to_poly(num).scale(Fraction(1, p_denom.get_constant()))
        else:
            return poly.singleton(t)
    elif t.is_nat_power():
        power = nat.convert_to_poly(t.arg)
        if power.is_constant():
            return convert_to_poly(t.arg1) ** power.get_constant()
        else:
            return poly.singleton(t)
    elif t.is_real_power():
        base = convert_to_poly(t.arg1)
        power = convert_to_poly(t.arg)
        if base.is_constant() and power.is_constant():
            return poly.constant(Fraction(base.get_constant()) ** Fraction(power.get_constant()))
        else:
            return poly.singleton(t)
    else:
        return poly.singleton(t)

def from_mono(m):
    """Convert a monomial to a term."""
    assert isinstance(m, poly.Monomial), "from_mono: input is not a monomial"
    factors = []
    for base, power in m.factors:
        assert isinstance(base, Term), "from_mono: base is not a Term"
        baseT = base.get_type()
        if baseT != RealType:
            base = Const('of_nat', TFun(baseT, RealType))(base)
        if power == 1:
            factors.append(base)
        else:
            factors.append(nat_power(base, Nat(power)))
    if m.coeff != 1:
        factors = [Real(m.coeff)] + factors
    return Prod(RealType, factors)

def from_poly(p):
    """Convert a polynomial to a term t."""
    return Sum(RealType, list(from_mono(m) for m in p.monomials))


class real_norm_conv(Conv):
    """Conversion for real_norm."""
    def get_proof_term(self, t):
        t2 = from_poly(convert_to_poly(t))
        if t2 == t:
            return refl(t)
        else:
            return eval_macro('real_norm', Eq(t, t2))


def is_real_ineq(tm):
    """Check if tm is an real inequality."""
    return (tm.is_less() or tm.is_less_eq() or tm.is_greater() or tm.is_greater_eq()) and tm.arg1.get_type() == RealType

class norm_real_ineq_conv(Conv):
    """
    Given an linear real arithmetic inequation, normalize it to canonical form.
    There are four possible input inequality forms:
    1) a < b <==> a - b < 0
    2) a > b <==> a - b > 0
    3) a ≤ b <==> a - b ≤ 0
    4) a ≥ b <==> a - b ≥ 0
    """
    def get_proof_term(self, tm):
        if not is_real_ineq(tm):
            raise ConvException("Invalid term: %s" % str(tm))

        pt = refl(tm)
        
        if tm.is_less():
            return pt.on_rhs(rewr_conv("real_le_sub"))

        elif tm.is_greater():
            return pt.on_rhs(rewr_conv("real_gt_sub"))
        
        elif tm.is_less_eq():
            return pt.on_rhs(rewr_conv("real_leq_sub"))
        
        elif tm.is_greater_eq():
            return pt.on_rhs(rewr_conv("real_geq_sub"))

class norm_neg_real_ineq_conv(Conv):
    """
    Give a negative linear real arithmetic inequation, normalize it to canonical form:
    There are four possible input inequality form:
    1) Not(a < b) <==> a ≥ b
    2) Not(a ≤ b) <==> a > b
    3) Not(a > b) <==> a ≤ b
    4) Not(a ≥ b) <==> a < b
    """
    def get_proof_term(self, tm):
        if not is_not(tm) or not is_real_ineq(tm.arg):
            raise ConvException("Invalid term: %s" % str(tm))
        pt = refl(tm)
        if tm.arg.is_less():
            return pt.on_rhs(rewr_conv("real_neg_lt"))
        elif tm.arg.is_greater():
            return pt.on_rhs(rewr_conv("real_not_gt"))            
        elif tm.arg.is_less_eq():
            return pt.on_rhs(rewr_conv("real_not_leq")) 
        else:
            return pt.on_rhs(rewr_conv("real_not_geq")) 


class real_const_eq_conv(Conv):
    def get_proof_term(self, t):
        return eval_macro('real_const_eq', t)

class real_norm_comparison(Conv):
    """Given an real comparison(including equation and inequation), move all term to
    left-hand side, and guarantee the left-most term' coefficient is positive.
    """
    def get_proof_term(self, t):
        if not t.is_equals() and not t.is_compares() or t.arg1.get_type() != RealType:
            return refl(t)
        pt = refl(t)
        if t.is_equals():
            pt1 = pt.on_rhs(rewr_conv('real_sub_0', sym=True), auto.norm_conv())
        elif t.is_greater_eq():
            pt1 = pt.on_rhs(rewr_conv('real_geq_sub'), auto.norm_conv())
        elif t.is_greater():
            pt1 = pt.on_rhs(rewr_conv('real_gt_sub'), auto.norm_conv())
        elif t.is_less_eq():
            pt1 = pt.on_rhs(rewr_conv('real_leq_sub'), auto.norm_conv())
        elif t.is_less():
            pt1 = pt.on_rhs(rewr_conv('real_le_sub'), auto.norm_conv())
        else:
            raise ConvException(str(t))

        summands = integer.strip_plus(pt1.rhs.arg1)
        first = summands[0]
        if first.is_var():
            return pt1
        elif first.is_number() and real_eval(first) > 0:
            return pt1
        elif first.is_times() and real_eval(first.arg1) > 0:
            return pt1

        lhs = pt1.rhs
        if lhs.is_equals():
            return pt1.on_rhs(rewr_conv('real_eq_neg2', sym=True), auto.norm_conv())
        elif lhs.is_greater_eq():
            return pt1.on_rhs(rewr_conv('real_geq_leq'), auto.norm_conv())
        elif lhs.is_greater():
            return pt1.on_rhs(rewr_conv('real_gt_le'), auto.norm_conv())
        elif lhs.is_less_eq():
            return pt1.on_rhs(rewr_conv('real_leq_geq'), auto.norm_conv())
        elif lhs.is_less():
            return pt1.on_rhs(rewr_conv('real_le_gt'), auto.norm_conv())

class real_simplex_form(Conv):
    """Convert an inequality to simplex form: 
    c_1 * x_1 + ... + c_n * x_n ⋈ d 
    """
    def get_proof_term(self, t):
        if not is_real_ineq(t):
            return refl(t)

        pt_refl = refl(t).on_rhs(real_norm_comparison())
        left_expr = pt_refl.rhs.arg1
        summands = integer.strip_plus(left_expr)
        first = summands[0]

        if not left_expr.is_plus() or not first.is_constant():
            return pt_refl
        first_value = real_eval(first)
        if pt_refl.rhs.is_greater_eq():
            pt_th = ProofTerm.theorem("real_sub_both_sides_geq")
        elif pt_refl.rhs.is_greater():
            pt_th = ProofTerm.theorem("real_sub_both_sides_gt")
        elif pt_refl.rhs.is_less_eq():
            pt_th = ProofTerm.theorem("real_sub_both_sides_leq")
        elif pt_refl.rhs.is_less():
            pt_th = ProofTerm.theorem("real_sub_both_sides_le")
        else:
            raise NotImplementedError(str(t))

        inst = matcher.first_order_match(pt_th.lhs, pt_refl.rhs, inst=matcher.Inst(c=first))
        return pt_refl.transitive(pt_th.substitution(inst=inst)).on_rhs(auto.norm_conv())
class replace_conv(Conv):
    def __init__(self, pt):
        self.pt = pt

    def get_proof_term(self, t):
        if t == self.pt.prop.lhs:
            return self.pt
        else:
            raise ConvException

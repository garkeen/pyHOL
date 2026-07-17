# logic/conv/nat.py - Nat Conv classes
# Extracted from data/nat.py

from kernel.type import TFun, BoolType, NatType
from kernel import term
from kernel.term import Term, Const, Not, Eq, Binary, Nat, Inst
from kernel.thm import Thm
from kernel import theory
from kernel import term_ord
from logic.conv.core import Conv, ConvException, all_conv, rewr_conv, \
    then_conv, arg_conv, arg1_conv, binop_conv
from kernel.proofterm import ProofTerm, refl


# Basic definitions
zero = term.nat_zero
one = term.nat_one
plus = term.plus(NatType)
minus = term.minus(NatType)
times = term.times(NatType)
Suc = Const("Suc", TFun(NatType, NatType))


def is_bit0(t):
    return t.is_comb('bit0', 1)

def is_bit1(t):
    return t.is_comb('bit1', 1)


class Suc_conv(Conv):
    """Computes Suc of a binary number."""
    def eval(self, t):
        return Thm(Eq(t, Binary(t.arg.dest_binary() + 1)))

    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_zero():
            return pt.on_rhs(rewr_conv("nat_one_def", sym=True))
        elif t.arg.is_one():
            return pt.on_rhs(rewr_conv("one_Suc"))
        elif is_bit0(t.arg):
            return pt.on_rhs(rewr_conv("bit0_Suc"))
        else:
            return pt.on_rhs(rewr_conv("bit1_Suc"), arg_conv(self))

class add_conv(Conv):
    """Computes the sum of two binary numbers."""
    def eval(self, t):
        return Thm(Eq(t, Binary(t.arg1.dest_binary() + t.arg.dest_binary())))

    def get_proof_term(self, t):
        if not (t.is_plus() and t.arg1.is_binary() and t.arg.is_binary()):
            raise ConvException("add_conv")
        pt = refl(t)
        n1, n2 = t.arg1, t.arg  # two summands
        if n1.is_zero():
            return pt.on_rhs(rewr_conv("nat_plus_def_1"))
        elif n2.is_zero():
            return pt.on_rhs(rewr_conv("add_0_right"))
        elif n1.is_one():
            return pt.on_rhs(rewr_conv("add_1_left"), Suc_conv())
        elif n2.is_one():
            return pt.on_rhs(rewr_conv("add_1_right"), Suc_conv())
        elif is_bit0(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit0_bit0_add"), arg_conv(self))
        elif is_bit0(n1) and is_bit1(n2):
            return pt.on_rhs(rewr_conv("bit0_bit1_add"), arg_conv(self))
        elif is_bit1(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit1_bit0_add"), arg_conv(self))
        else:
            return pt.on_rhs(rewr_conv("bit1_bit1_add"),
                             arg_conv(arg_conv(self)), arg_conv(Suc_conv()))

class mult_conv(Conv):
    """Computes the product of two binary numbers."""
    def eval(self, t):
        return Thm(Eq(t, Binary(t.arg1.dest_binary() * t.arg.dest_binary())))

    def get_proof_term(self, t):
        n1, n2 = t.arg1, t.arg  # two summands
        pt = refl(t)
        if n1.is_zero():
            return pt.on_rhs(rewr_conv("nat_times_def_1"))
        elif n2.is_zero():
            return pt.on_rhs(rewr_conv("mult_0_right"))
        elif n1.is_one():
            return pt.on_rhs(rewr_conv("mult_1_left"))
        elif n2.is_one():
            return pt.on_rhs(rewr_conv("mult_1_right"))
        elif is_bit0(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit0_bit0_mult"), arg_conv(arg_conv(self)))
        elif is_bit0(n1) and is_bit1(n2):
            return pt.on_rhs(rewr_conv("bit0_bit1_mult"), arg_conv(self))
        elif is_bit1(n1) and is_bit0(n2):
            return pt.on_rhs(rewr_conv("bit1_bit0_mult"), arg_conv(self))
        else:
            return pt.on_rhs(rewr_conv("bit1_bit1_mult"),
                             arg_conv(arg1_conv(add_conv())),
                             arg_conv(arg_conv(arg_conv(self))),
                             arg_conv(add_conv()))

class rewr_of_nat_conv(Conv):
    """Remove or apply of_nat."""
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_zero() or t.is_one():
            return pt
        else:
            return pt.on_rhs(rewr_conv("nat_of_nat_def", sym=self.sym))

def nat_eval(t):
    """Evaluate a term with arithmetic operations.
    
    Return a Python integer.
    
    """
    if t.is_number():
        return t.dest_number()
    elif t.is_comb('Suc', 1):
        return nat_eval(t.arg) + 1
    elif t.is_plus():
        return nat_eval(t.arg1) + nat_eval(t.arg)
    elif t.is_minus():
        m, n = nat_eval(t.arg1), nat_eval(t.arg)
        return 0 if m <= n else m - n
    elif t.is_times():
        return nat_eval(t.arg1) * nat_eval(t.arg)
    else:
        raise ConvException('nat_eval: %s' % str(t))

class nat_conv(Conv):
    """Simplify all arithmetic operations."""
    def eval(self, t):
        return Thm(Eq(t, Nat(nat_eval(t))))

    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_number():
            return pt
        elif t.is_comb('Suc', 1):
            return pt.on_rhs(arg_conv(self),
                             arg_conv(rewr_of_nat_conv()),
                             Suc_conv(),
                             rewr_of_nat_conv(sym=True))
        elif t.is_plus():
            return pt.on_rhs(binop_conv(self),
                             binop_conv(rewr_of_nat_conv()),
                             add_conv(),
                             rewr_of_nat_conv(sym=True))
        elif t.is_times():
            return pt.on_rhs(binop_conv(self),
                             binop_conv(rewr_of_nat_conv()),
                             mult_conv(),
                             rewr_of_nat_conv(sym=True))
        else:
            raise ConvException("nat_conv")

class nat_eval_conv(Conv):
    """Simplify all arithmetic operations."""
    def get_proof_term(self, t):
        simp_t = Nat(nat_eval(t))
        if simp_t == t:
            return refl(t)
        return ProofTerm('nat_eval', Eq(t, simp_t))


# Normalization on the semiring.

# First level normalization: AC rules for addition only.

def compare_atom(t1: Term, t2: Term) -> bool:
    """Compare two atoms for AC-ordering.
    
    Numbers are ordered last, otherwise use fast_compare in term_ord.
    
    """
    if t1.is_number() and t2.is_number():
        return 0
    elif t1.is_number():
        return 1
    elif t2.is_number():
        return -1
    else:
        return term_ord.fast_compare(t1, t2)

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b, or if the left argument
    is an atom, rewrite a + b to b + a.

    """
    def get_proof_term(self, t: Term) -> ProofTerm:
        pt = refl(t)
        if t.arg1.is_plus():
            return pt.on_rhs(rewr_conv("add_assoc"),
                             arg_conv(rewr_conv("add_comm")),
                             rewr_conv("add_assoc", sym=True))
        else:
            return pt.on_rhs(rewr_conv("add_comm"))

class norm_add_atom_1(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, t: Term) -> ProofTerm:
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("nat_plus_def_1"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("add_0_right"))
        elif t.arg1.is_plus():
            if compare_atom(t.arg1.arg, t.arg) > 0:
                return pt.on_rhs(swap_add_r(), arg1_conv(norm_add_atom_1()))
            else:
                return pt
        else:
            if compare_atom(t.arg1, t.arg) > 0:
                return pt.on_rhs(rewr_conv("add_comm"))
            else:
                return pt

class norm_add_1(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv("add_assoc", sym=True),
                             arg1_conv(norm_add_1()),
                             norm_add_atom_1())
        else:
            return pt.on_rhs(norm_add_atom_1())

# Second level normalization.

class swap_times_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b, or if the left argument
    is an atom, rewrite a * b to b * a.

    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_times():
            return pt.on_rhs(rewr_conv("mult_assoc"),
                             arg_conv(rewr_conv("mult_comm")),
                             rewr_conv("mult_assoc", sym=True))
        else:
            return pt.on_rhs(rewr_conv("mult_comm"))

def has_binary_thms():
    return theory.thy.has_theorem('bit1_bit1_mult')

class norm_mult_atom(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * a."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("nat_times_def_1"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("mult_0_right"))
        elif t.arg1.is_one():
            return pt.on_rhs(rewr_conv("mult_1_left"))
        elif t.arg.is_one():
            return pt.on_rhs(rewr_conv("mult_1_right"))
        elif t.arg1.is_times():
            cp = compare_atom(t.arg1.arg, t.arg)
            if cp > 0:
                return pt.on_rhs(swap_times_r(), arg1_conv(norm_mult_atom()))
            elif cp == 0:
                if t.arg.is_number() and has_binary_thms():
                    return pt.on_rhs(rewr_conv("mult_assoc"), arg_conv(nat_conv()))
                else:
                    return pt
            else:
                return pt
        else:
            cp = compare_atom(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(rewr_conv("mult_comm"))
            elif cp == 0:
                if t.arg.is_number() and has_binary_thms():
                    return pt.on_rhs(nat_conv())
                else:
                    return pt
            else:
                return pt

class norm_mult_monomial(Conv):
    """Normalize expression of the form (a_1 * ... * a_n) * (b_1 * ... * b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_times():
            return pt.on_rhs(rewr_conv("mult_assoc", sym=True),
                             arg1_conv(norm_mult_monomial()),
                             norm_mult_atom())
        else:
            return pt.on_rhs(norm_mult_atom())

def dest_monomial(t):
    """Remove coefficient part of a monomial t."""
    if t.is_times() and t.arg.is_number():
        return t.arg1
    elif t.is_number():
        return one
    else:
        return t

def compare_monomial(t1, t2):
    """Compare two monomials by their body."""
    if has_binary_thms():
        return term_ord.fast_compare(dest_monomial(t1), dest_monomial(t2))
    else:
        return term_ord.fast_compare(t1, t2)

class to_coeff_form(Conv):
    """Convert a to a * 1, n to 1 * n, and leave a * n unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_times() and t.arg.is_number():
            return pt
        elif t.is_number():
            return pt.on_rhs(rewr_conv("mult_1_left", sym=True))
        else:
            return pt.on_rhs(rewr_conv("mult_1_right", sym=True))

class from_coeff_form(Conv):
    """Convert a * 1 to a, 1 * n to n, and leave a * n unchanged."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_one():
            return pt.on_rhs(rewr_conv("mult_1_right"))
        elif t.arg1.is_one():
            return pt.on_rhs(rewr_conv("mult_1_left"))
        else:
            return pt

class combine_monomial(Conv):
    """Combine two monomials with the same body."""
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            binop_conv(to_coeff_form()),
            rewr_conv("distrib_l", sym=True),
            arg_conv(nat_conv()),
            from_coeff_form())

class norm_add_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + a."""
    def get_proof_term(self, t: Term) -> ProofTerm:
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("nat_plus_def_1"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("add_0_right"))
        elif t.arg1.is_plus():
            cp = compare_monomial(t.arg1.arg, t.arg)
            if cp > 0:
                return pt.on_rhs(swap_add_r(), arg1_conv(norm_add_monomial()))
            elif cp == 0 and has_binary_thms():
                return pt.on_rhs(rewr_conv("add_assoc"), arg_conv(combine_monomial()))
            else:
                return pt
        else:
            cp = compare_monomial(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(rewr_conv("add_comm"))
            elif cp == 0 and has_binary_thms():
                return pt.on_rhs(combine_monomial())
            else:
                return pt

class norm_add_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) + (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv("add_assoc", sym=True),
                             arg1_conv(norm_add_polynomial()),
                             norm_add_monomial())
        else:
            return pt.on_rhs(norm_add_monomial())

class norm_mult_poly_monomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * b."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_plus():
            return pt.on_rhs(rewr_conv("distrib_r"),
                             arg1_conv(norm_mult_poly_monomial()),
                             arg_conv(norm_mult_monomial()),
                             norm_add_polynomial())
        else:
            return pt.on_rhs(norm_mult_monomial())

class norm_mult_polynomial(Conv):
    """Normalize expression of the form (a_1 + ... + a_n) * (b_1 + ... + b_n)."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_plus():
            return pt.on_rhs(rewr_conv("distrib_l"),
                             arg1_conv(norm_mult_polynomial()),
                             arg_conv(norm_mult_poly_monomial()),
                             norm_add_polynomial())
        else:
            return pt.on_rhs(norm_mult_poly_monomial())

class norm_full(Conv):
    """Normalize expressions on natural numbers involving plus and times."""
    def get_proof_term(self, t):
        pt = refl(t)
        if theory.thy.has_theorem('mult_comm'):
            # Full conversion, with or without binary numbers
            if t.is_number():
                return pt
            elif t.is_comb('Suc', 1):
                return pt.on_rhs(rewr_conv("add_1_right", sym=True), norm_full())
            elif t.is_plus():
                return pt.on_rhs(binop_conv(norm_full()), norm_add_polynomial())
            elif t.is_times():
                return pt.on_rhs(binop_conv(norm_full()), norm_mult_polynomial())
            else:
                return pt
        elif theory.thy.has_theorem('add_assoc'):
            # Conversion using only AC rules for addition
            if t.is_number():
                return pt
            elif t.is_comb('Suc', 1):
                return pt.on_rhs(rewr_conv("add_1_right", sym=True), norm_full())
            elif t.is_plus():
                return pt.on_rhs(binop_conv(norm_full()), norm_add_1())
            else:
                return pt
        else:
            return pt

class nat_eq_conv(Conv):
    """Simplify equality a = b to either True or False."""
    def get_proof_term(self, t):
        if not t.is_equals():
            return refl(t)

        a, b = t.args
        if not (a.is_number() and b.is_number()):
            return refl(t)

        if a == b:
            return refl(a).on_prop(rewr_conv("eq_true"))
        else:
            from data.nat import nat_const_ineq
            return nat_const_ineq(a, b).on_prop(rewr_conv("eq_false"))

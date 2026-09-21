"""
Tseitin encoding from formulae in pyHOL to CNF.
"""

from kernel.type import BoolType
from kernel.term import Term, Var, Implies, Eq
from syntax.logicops import And, Or, Not, is_not, is_conj, strip_conj, is_disj, strip_disj
from kernel.thm import Thm
from kernel import term_ord
from kernel.proofterm import ProofTerm
from core.logic import apply_theorem
from core.conv import rewr_conv, every_conv, top_conv


def is_logical(t):
    return t.is_implies() or t.is_equals() or is_conj(t) or is_disj(t) or is_not(t)

def logic_subterms(t):
    """Returns the list of logical subterms for a term t."""
    def rec(t):
        if not is_logical(t):
            return [t]
        elif is_not(t):
            return rec(t.arg) + [t]
        else:
            return rec(t.arg1) + rec(t.arg) + [t]

    return term_ord.sorted_terms(rec(t))

def encode(t, norm_conj):
    """Given a propositional formula t, compute its Tseitin encoding.

    The theorem is structured as follows:

    Each of the assumptions, except the last, is an equality, where
    the right side is either an atom or a logical operation between
    atoms. We call these assumptions As.

    The last assumption is the original formula. We call it F.

    The conclusion is in CNF. Each clause except the last is an
    expansion of one of As. The last clause is obtained by performing
    substitutions of As on F.

    norm_conj is the conjunction-normalization Conv (theories.logic.
    logic.conj_norm).  It is injected by the caller (audit §8 task E:
    solvers do not import theories; domain glue lives at the call
    site, like the z3 backend injection).

    """
    # Mapping from subterms to newly introduced variables
    subterm_dict = dict()
    for i, subt in enumerate(logic_subterms(t)):
        subterm_dict[subt] = Var('x' + str(i+1), BoolType)

    # Collect list of equations
    eqs = []
    for subt in subterm_dict:
        r = subterm_dict[subt]
        if not is_logical(subt):
            eqs.append(Eq(r, subt))
        elif is_not(subt):
            r1 = subterm_dict[subt.arg]
            eqs.append(Eq(r, Not(r1)))
        else:
            r1 = subterm_dict[subt.arg1]
            r2 = subterm_dict[subt.arg]
            eqs.append(Eq(r, subt.head(r1, r2)))

    # Form the proof term
    eq_pts = [ProofTerm.assume(eq) for eq in eqs]
    encode_pt = ProofTerm.assume(t)
    for eq_pt in eq_pts:
        encode_pt = encode_pt.on_prop(top_conv(rewr_conv(eq_pt, sym=True)))
    for eq_pt in eq_pts:
        if is_logical(eq_pt.rhs):
            encode_pt = apply_theorem('conjI', eq_pt, encode_pt)
    
    # Rewrite using Tseitin rules
    encode_thms = ['encode_conj', 'encode_disj', 'encode_imp', 'encode_eq', 'encode_not']

    for th in encode_thms:
        encode_pt = encode_pt.on_prop(top_conv(rewr_conv(th)))
    
    # Normalize the conjuncts
    return encode_pt.on_prop(norm_conj())

def convert_cnf(t):
    """Convert a term to CNF form (as a list of lists of literals)."""
    def convert_literal(lit):
        if is_not(lit):
            return (lit.arg.name, False)
        else:
            return (lit.name, True)
        
    def convert_clause(clause):
        return [convert_literal(lit) for lit in strip_disj(clause)]

    return [convert_clause(clause) for clause in strip_conj(t)]

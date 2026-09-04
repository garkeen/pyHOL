# domains/integer/macro.py - Integer macros.
# Importing this module registers int_norm (polynomial normalization
# for integer equalities), mirroring nat_norm in domains/nat/macro.py.

from kernel.term import Term
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm
from syntax.numeral import IntType
from domains.integer.conv import int_norm_conv


@register_macro('int_norm')
class int_norm_macro(Macro):
    """Attempt to prove goal by normalization."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'int_mul_1_l'

    def eval(self, goal, pts):
        assert len(pts) == 0, "int_norm_macro"
        assert self.can_eval(goal), "int_norm_macro: normalization is not equal."
        return Thm(goal)

    def can_eval(self, goal):
        assert isinstance(goal, Term), "int_norm_macro"
        if not (goal.is_equals() and goal.lhs.get_type() == IntType):
            return False

        t1, t2 = goal.args
        pt1 = int_norm_conv().get_proof_term(t1)
        pt2 = int_norm_conv().get_proof_term(t2)
        return pt1.prop.rhs == pt2.prop.rhs

    def get_proof_term(self, goal, pts):
        assert len(pts) == 0, "int_norm_macro"
        assert goal.is_equals(), "int_norm_macro: goal is not an equality."

        t1, t2 = goal.args
        pt1 = int_norm_conv().get_proof_term(t1)
        pt2 = int_norm_conv().get_proof_term(t2)
        assert pt1.prop.rhs == pt2.prop.rhs, "int_norm_macro: normalization is not equal."
        return pt1.transitive(pt2.symmetric())

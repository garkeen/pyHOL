# framework/macros/z3.py - Z3 Macro class (domain-independent)
# Extracted from prover/z3wrapper.py

from kernel.term import Term, Implies
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm
from prover.z3wrapper import z3_loaded, check_z3, solve


@register_macro('z3')
class Z3Macro(Macro):
    """Macro invoking SMT solver Z3."""
    def __init__(self):
        self.level = 0  # No expand implemented for Z3.
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if z3_loaded:
            assms = [prev.prop for prev in prevs]
            if check_z3:
                assert solve(Implies(*(assms + [args]))), "Z3: not solved."
        else:
            print("Warning: Z3 is not installed")

        return Thm(args, *(th.hyps for th in prevs))

    def expand(self, prefix, args, prevs):
        raise NotImplementedError


def apply_z3(t):
    return ProofTerm('z3', args=t)

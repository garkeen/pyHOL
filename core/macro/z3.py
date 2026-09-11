# core/macro/z3.py - Z3 Macro class (domain-independent)
# Extracted from solvers/z3wrapper.py
#
# By-name injection (audit §6 supplement): this macro lives in the
# oracle slot of the macro layer and must not module-import solver
# code.  The solver backend (z3_loaded / check_z3 / solve) is injected
# by solvers/z3wrapper.py when it is loaded; until then the macro
# evaluates as an unchecked oracle that only prints a warning -- the
# same behavior as z3-not-installed.

from kernel.term import Term, Implies
from kernel.thm import oracle_thm
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import eval_macro


class Z3Backend:
    """Injection slot for the z3 solver backend.

    By default the backend is absent: the macro is an unchecked
    oracle.  solvers/z3wrapper.py calls inject() on load, binding
    z3_loaded / check_z3 / solve to the real solver.
    """

    def __init__(self):
        self.z3_loaded = False
        self.check_z3 = False
        self.solve = None

    def inject(self, z3_loaded, check_z3, solve):
        self.z3_loaded = z3_loaded
        self.check_z3 = check_z3
        self.solve = solve


backend = Z3Backend()


@register_macro('z3')
class Z3Macro(Macro):
    """Macro invoking SMT solver Z3."""
    def __init__(self):
        self.level = 0  # No expand implemented for Z3.
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if backend.z3_loaded:
            assms = [prev.prop for prev in prevs]
            if backend.check_z3:
                assert backend.solve(Implies(*(assms + [args]))), "Z3: not solved."
        else:
            print("Warning: Z3 is not installed")

        return oracle_thm(self.name, args, *(th.hyps for th in prevs))

    def expand(self, prefix, args, prevs):
        raise NotImplementedError


def apply_z3(t):
    return eval_macro('z3', args=t)

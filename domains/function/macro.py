# logic/macros/function.py - Function update macros

from kernel.term import Term
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm
from domains.function.conv import fun_upd_eval_conv


@register_macro('fun_upd_eval')
class fun_upd_eval_macro(Macro):
    """Macro using fun_upd_eval_conv."""

    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'fun_upd_twist'

    def get_proof_term(self, args, pts):
        assert len(pts) == 0, "fun_upd_eval_macro"
        assert args.is_equals(), "fun_upd_eval_macro: goal is not an equality"

        t1, t2 = args.arg1, args.arg
        pt = fun_upd_eval_conv().get_proof_term(t1)
        assert pt.prop.arg == t2, "fun_upd_eval_macro: incorrect rhs"

        return pt

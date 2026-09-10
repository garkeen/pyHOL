# theories/nat/interval.py - Interval conversions
# Domain-dependent: hardcodes nat.pyhol theorem names (natseg_emptyI, natseg_lrec)

from kernel.type import TFun
from syntax.numeral import NatType
from kernel.term import Const
from kernel.proofterm import refl
from core.conv import Conv, rewr_conv, arg_conv, arg1_conv


def setT(T):
    """Construct set type for given element type."""
    from kernel.type import TConst
    return TConst("set", T)


def mk_interval(m, n):
    return Const("nat_interval", TFun(NatType, NatType, setT(NatType)))(m, n)


def is_interval(t):
    return t.is_comb('nat_interval', 2)

class numseg_conv(Conv):
    """Evaluate {m..n} to a concrete set. Here m and n are specific
    numerals.
    
    """
    def get_proof_term(self, t):
        from theories.nat import util_nat as nat
        from theories.nat.macro import nat_const_less_macro, nat_const_less_eq_macro
        assert is_interval(t), "numseg_conv"
        mt, nt = t.args
        m, n = mt.dest_number(), nt.dest_number()
        pt = refl(t)
        if n < m:
            less_goal = nat.less(nt, mt)
            less_pt = nat_const_less_macro().get_proof_term(less_goal, [])
            return pt.on_rhs(rewr_conv("natseg_emptyI", conds=[less_pt]))
        else:
            le_goal = nat.less_eq(mt, nt)
            le_pt = nat_const_less_eq_macro().get_proof_term(le_goal, [])
            return pt.on_rhs(rewr_conv("natseg_lrec", conds=[le_pt]),
                             arg_conv(arg1_conv(nat.nat_conv())),
                             arg_conv(self))

# theories/expr/util_expr.py - Expression type constants
# Domain-dependent: constants of expr.pyhol (aexp, N, V, Plus, Times, avalI)

from kernel.type import TConst, TFun, BoolType
from syntax.numeral import NatType
from kernel.term import Const

aexpT = TConst("aexp")

N = Const("N", TFun(NatType, aexpT))
V = Const("V", TFun(NatType, aexpT))
Plus = Const("Plus", TFun(aexpT, aexpT, aexpT))
Times = Const("Times", TFun(aexpT, aexpT, aexpT))

avalI = Const("avalI", TFun(TFun(NatType, NatType), aexpT, NatType, BoolType))

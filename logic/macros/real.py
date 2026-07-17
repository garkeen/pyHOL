# logic/macros/real.py - Real macros interface
# Re-exports macros from data.real for the new folder structure

from data.real import (
    # Macro classes
    real_eval_macro,
    real_norm_macro,
    RealEqMacro,
    RealCompareMacro,
    real_const_ineq_macro,
    RealCompEq,
    relax_strict_simplex_macro,
)

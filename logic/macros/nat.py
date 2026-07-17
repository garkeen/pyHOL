# logic/macros/nat.py - Nat macros interface
# Re-exports macros from data.nat for the new folder structure

from data.nat import (
    # Macro classes
    nat_eval_macro,
    nat_norm_macro,
    nat_const_ineq_macro,
    nat_const_less_eq_macro,
    nat_const_less_macro,
    # Conv classes used by macros
    nat_eval_conv,
    norm_full,
    # Utility functions
    nat_eval,
    ineq_proof_term,
    nat_const_ineq,
)

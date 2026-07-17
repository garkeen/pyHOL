# logic/macros/__init__.py - Unified macro registration interface
# Imports from both core macros and domain-specific macros

# Core macros (from logic.logic)
from logic.macros.core import (
    beta_norm_macro, intros_macro, apply_theorem_macro,
    apply_induct_macro, apply_fact_macro, rewrite_goal_macro,
    rewrite_fact_macro, rewrite_goal_with_prev_macro,
    rewrite_fact_with_prev_macro, forall_elim_gen_macro,
    trivial_macro, resolve_theorem_macro,
    imp_conj_macro, imp_disj_macro, resolution_macro
)

# Domain macros are loaded on demand by logic/basic.py:
# - logic.macros.nat (nat_eval, nat_norm, etc.)
# - logic.macros.integer (int_eval, int_eq, etc.)
# - logic.macros.real (real_eval, real_norm, etc.)
# - logic.macros.expr (prove_avalI)
# - logic.macros.function (fun_upd_eval)
# - logic.macros.z3 (z3)

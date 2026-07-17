# logic/macros/core.py - Core macros (imported from logic.logic)
# This module re-exports the core macros for the new folder structure

from logic.logic import (
    # Core macros
    beta_norm_macro, intros_macro, apply_theorem_macro,
    apply_induct_macro, apply_fact_macro, rewrite_goal_macro,
    rewrite_fact_macro, rewrite_goal_with_prev_macro,
    rewrite_fact_with_prev_macro, forall_elim_gen_macro,
    trivial_macro, resolve_theorem_macro,
    # Logic macros
    imp_conj_macro, imp_disj_macro, resolution_macro,
    # Utility functions used by macros
    apply_theorem, conj_thms,
    get_forall_names, strip_all_implies, strip_exists,
    strip_conj, strip_disj,
    imp_conj_iff, imp_disj_iff,
    # Conv classes
    norm_bool_expr, norm_conj_assoc_clauses, norm_conj_assoc,
    disj_norm, conj_norm,
    # Utility proof functions
    resolution,
)

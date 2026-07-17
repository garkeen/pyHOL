# logic/macros/core.py - Core macros (imported from logic.logic)
# This module re-exports the core macros for the new folder structure

from logic.logic import (
    beta_norm_macro, intros_macro, apply_theorem_macro,
    apply_induct_macro, apply_fact_macro, rewrite_goal_macro,
    rewrite_fact_macro, rewrite_goal_with_prev_macro,
    rewrite_fact_with_prev_macro, forall_elim_gen_macro,
    trivial_macro, resolve_theorem_macro,
    imp_conj_macro, imp_disj_macro, resolution_macro
)

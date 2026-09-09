# core/macro/ - Macro layer: expansion mechanism + concrete macros.
#
# Single home for the macro category (audit §2/§5.7: directory name =
# category name; the former core/macros/ sister directory held the same
# category and is merged in here):
#   simp.py       simp_sweep (iterated rewrite sweep behind simp/auto)
#   registry.py   Macro base registry + domain-independent macros
#                 (intros, apply_theorem, beta_norm, auto_close, ...)
#   z3.py         Z3 oracle macro (by-name injection slot)
#
# simp_sweep moved here in rewrite step 2 (ARCHITECTURE_AUDIT.md §8): it
# is macro expansion machinery, not a tactic, and its old home in
# tactic.py forced tactic.py to import core.auto, forming a
# tactic<->auto import cycle.

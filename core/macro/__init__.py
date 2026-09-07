# framework/macro/ - Macro-layer mechanisms.
#
# Expansion procedures shared between macros. simp_sweep (the iterated
# rewrite sweep behind the simp tactic, simp macro and auto macro)
# moved here in rewrite step 2 (ARCHITECTURE_AUDIT.md §8): it is macro
# expansion machinery, not a tactic, and its old home in
# framework/tactic.py forced tactic.py to import core.auto,
# forming a tactic<->auto import cycle.

# domains/logic/__init__.py
# Propositional logic domain automation, bound to library/logic.pyhol:
# activated by basic.py when the .pyhol declares `domains logic`.
# Importing this package registers the domain macros (imp_conj, imp_disj,
# resolution).  The conv/logic submodules are libraries imported directly
# by their consumers (importing them here would create import cycles).
# Note: the generic automation engine (auto) is domain-independent and
# lives in framework/auto.py.

from theories.logic import macro   # noqa: F401  (registers imp_conj, imp_disj, resolution)

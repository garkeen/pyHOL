# domains/nat/__init__.py
# Importing this package registers nat-specific conv, macro, and method.
# Triggered by basic.py when the 'nat' domain is declared in a .pyhol file,
# or by server/methods/__init__.py for eager loading.

# Import order matters: conv first (no domain deps), then macro (uses conv),
# then method (uses macro). util_nat is imported on demand.
from domains.nat import conv  # noqa: F401  (defines nat_eval_conv etc.)
from domains.nat import macro  # noqa: F401  (registers nat_eval, nat_norm, etc.)
from domains.nat import method  # noqa: F401  (registers nat_norm, nat_const_ineq methods)

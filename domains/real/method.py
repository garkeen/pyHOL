# domains/real/method.py - Real methods.
# The real_norm method is auto-generated from the real_norm macro
# (defined in domains/real/macro.py) via register_macro_method: the
# checked apply_macro entry point. This module performs the
# registration; importing it (via domains.real) wires the method up.

from framework.method import register_macro_method
from domains.real import conv  # noqa: F401  (normalization convs used by auto)
from domains.real import macro  # noqa: F401  (registers the real macros)

register_macro_method('real_norm', limit='real_neg_0')

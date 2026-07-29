# logic/macros/integer.py - Re-export shim.
# Integer macros are registered in domains/integer/conv.py (integer puts conv and macro in the same file).
# This shim re-exports them for backward compatibility.
from domains.integer.conv import *  # noqa: F401,F403

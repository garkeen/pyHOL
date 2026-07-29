# logic/macros/nat.py - Re-export shim for backward compatibility.
# The real implementation has moved to domains/nat/macro.py.
# This file exists so existing `from logic.macros.nat import ...` still works.
# Once all imports are updated to use domains.nat.macro, this shim can be removed.

from domains.nat.macro import *  # noqa: F401,F403

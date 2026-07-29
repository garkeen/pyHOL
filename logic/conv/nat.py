# logic/conv/nat.py - Re-export shim for backward compatibility.
# The real implementation has moved to domains/nat/conv.py.
# This file exists so existing `from logic.conv.nat import ...` still works.
# Once all imports are updated to use domains.nat.conv, this shim can be removed.

from domains.nat.conv import *  # noqa: F401,F403

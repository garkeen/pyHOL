# util/nat.py - Re-export shim for backward compatibility.
# The real implementation has moved to domains/nat/util_nat.py.
# This file exists so existing `from util import nat` / `from util.nat import ...` still works.
# Once all imports are updated to use domains.nat.util_nat, this shim can be removed.

from domains.nat.util_nat import *  # noqa: F401,F403

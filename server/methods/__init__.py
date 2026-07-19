# server/methods - Unified method registration interface
# Provides ProofState, Method base class, and all registered methods

from server.methods.core import (
    ProofState, Method, global_methods,
    register_method, get_method, has_method, get_method_sig,
    apply_method, output_step, output_hint
)

# Import domain-specific methods to register them
try:
    import server.methods.nat
except Exception:
    pass
try:
    import server.methods.real
except Exception:
    pass
try:
    import server.methods.z3
except Exception:
    pass
try:
    import server.methods.expr
except Exception:
    pass

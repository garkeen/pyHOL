# server/methods - Unified method registration interface
# Provides ProofState, Method base class, and all registered methods

from server.methods.core import (
    ProofState, Method, global_methods,
    register_method, get_method, has_method, get_method_sig,
    apply_method, output_step, output_hint
)

# Import domain-specific method modules (triggers registration)
# These are thin wrappers around data/ implementations

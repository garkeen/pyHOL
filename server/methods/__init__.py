# server/methods - Unified method registration interface
# Provides ProofState, Method base class, and all registered methods

from server.methods.core import (
    ProofState, Method, global_methods,
    register_method, get_method, has_method, get_method_sig,
    apply_method, output_step, output_hint
)

# Import domain packages to register their methods.
# Domains live in the top-level domains/ package. Importing them triggers
# @register_method / @register_macro decorators.
# basic.py also re-imports them when a .pyhol declares `domains <name>`,
# but importing here ensures methods are registered even before any
# theory is loaded (e.g. for IDE method listing).
# Decorators are idempotent, so double-registration is a no-op.

for _domain in ('nat', 'real', 'function', 'expr'):
    try:
        __import__(f'domains.{_domain}')
    except Exception as e:
        import sys
        print(f"Warning: failed to load domain '{_domain}': {e}", file=sys.stderr)

# z3 method is not a domain - it's a generic oracle wrapper.
try:
    import server.methods.z3
except Exception as e:
    import sys
    print(f"Warning: failed to load server.methods.z3: {e}", file=sys.stderr)

# Register domain-specific methods
import imperative.imp  # noqa: F401 (registers vcg method)

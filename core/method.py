# framework/method.py - Method registry (the core registration API).
#
# The Method base class, the global method store, and the registration
# channels (register_method, register_macro_method, register_norm) live
# here, below the application layer: domains and imperative register
# into this registry directly, and the method layer (server/methods) is
# a reader -- it contributes its own interactive methods through the
# same checked API and serves the registry to the frontend.
#
# Rewrite step 4 (ARCHITECTURE_AUDIT.md §8): domains/*/method.py must
# not import method.*; this registry is the contract between the layers.

from typing import Dict

from kernel import theory
from syntax import pprint


"""Global store for methods."""
global_methods: Dict[str, "Method"] = dict()

def has_method(name: str) -> bool:
    """Return whether the method with the given name exists and can be
    used in the current location of the theory.

    """
    if name in global_methods:
        method = global_methods[name]
        return method.limit is None or theory.thy.has_theorem(method.limit)
    else:
        return False

def get_method(name: str) -> "Method":
    """Return method with the given name."""
    assert has_method(name), "get_method: %s is not available" % name
    return global_methods[name]

def get_all_methods() -> Dict[str, "Method"]:
    """Return a dictionary mapping method names to methods."""
    res = dict()
    for name in global_methods:
        if has_method(name):
            res[name] = global_methods[name]
    return res

def get_method_sig():
    sig = dict()
    for name in global_methods:
        if has_method(name):
            sig[name] = global_methods[name].sig
    return sig

def get_method_list_params():
    """Return per-method list of params that are comma-separated lists.

    These are rendered as +/- dynamic fields in the frontend query dialog.
    Any Method subclass can declare ``list_params = {'names'}`` to opt in.
    """
    res = dict()
    for name in global_methods:
        if has_method(name):
            m = global_methods[name]
            lp = list(getattr(m, 'list_params', set()))
            if lp:
                res[name] = lp
    return res

def register_method(name):
    def decorator(method_cls):
        # Idempotent: skip if already registered (supports reloading theories).
        if name in global_methods:
            return method_cls
        global_methods[name] = method_cls()
        return method_cls
    return decorator


class Method:
    """Methods represent potential actions on the state."""
    list_params = set()  # param names that are comma-separated lists (rendered as +/- fields)
    def search(self, state, id, prevs):
        """Search for parameters on which the method can be applied
        given the current proof state.

        """
        pass

    def display_step(self, state, data):
        """Display the current step in pretty-printed form."""
        pass

    def apply(self, state, id, args, prevs):
        """Apply the method on the current state using the given
        parameters. Return new proof state if successful.

        """
        pass


def register_macro_method(name: str, *, limit=None):
    """Register a method auto-generated from a macro.

    The standard channel exposing a domain macro as an interactive
    method: search is gated by the macro's can_eval (when defined),
    and apply goes through the checked state.apply_macro entry point.
    No hand-written boilerplate is needed per macro.
    """
    class _macro_method(Method):
        def __init__(self):
            self.sig = []
            self.limit = limit

        def search(self, state, id, prevs, data=None):
            if data:
                return [data]
            if len(prevs) != 0:
                return []
            if not theory.has_macro(name):
                return []
            macro = theory.get_macro(name)
            if hasattr(macro, 'can_eval'):
                cur_th = state.get_proof_item(id).th
                if macro.can_eval(cur_th.prop):
                    return [{}]
                return []
            return [{}]

        def display_step(self, state, data):
            return pprint.N(name + ": ") + pprint.KWGreen("(solves)")

        def apply(self, state, id, data, prevs):
            assert len(prevs) == 0, name
            state.apply_macro(id, name)

    _macro_method.__name__ = name + '_method'
    return register_method(name)(_macro_method)


"""Registry mapping types to their normalization macros (read by the
norm method; numeric types are wired to the domain normalizers here)."""
norm_registry = dict()

def register_norm(T, macro_name: str):
    norm_registry[T] = macro_name


from syntax.numeral import NatType, RealType, IntType  # noqa: E402
register_norm(NatType, 'nat_norm')
register_norm(RealType, 'real_norm')
register_norm(IntType, 'int_norm')

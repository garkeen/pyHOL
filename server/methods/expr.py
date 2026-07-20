# server/methods/expr.py - Expression evaluation method

from server.methods.core import Method, register_method
from logic.tactic import MacroTactic
from logic.macros.expr import prove_avalI_macro
from syntax import pprint


@register_method('prove_avalI')
class prove_avalI_method(Method):
    """Apply prove_avalI macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'avalI_times'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if prove_avalI_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("prove_avalI: ") + pprint.KWGreen("(solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "prove_avalI_method"
        state.apply_tactic(id, MacroTactic('prove_avalI'))

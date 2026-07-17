# server/methods/nat.py - Nat Method classes
# Extracted from data/nat.py

from server.methods.core import Method, register_method
from logic.tactic import MacroTactic
from logic.macros.nat import nat_norm_macro, nat_const_ineq_macro
from syntax import pprint


@register_method('nat_norm')
class nat_norm_method(Method):
    """Apply nat_norm macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'nat_nat_power_def_1'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if nat_norm_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("nat_norm: ") + pprint.KWGreen("(solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_norm_method"
        state.apply_tactic(id, MacroTactic('nat_norm'))


@register_method('nat_const_ineq')
class nat_const_ineq_method(Method):
    """Apply nat_const_ineq macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'bit1_neq_one'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if nat_const_ineq_macro().can_eval(cur_th.prop):
            return [{}]
        else:
            return []

    def display_step(self, state, data):
        return pprint.N("nat_const_ineq: ") + pprint.KWGreen("(solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "nat_const_ineq_method"
        state.apply_tactic(id, MacroTactic('nat_const_ineq'))

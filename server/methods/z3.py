# server/methods/z3.py - Z3 Method class
# Extracted from solvers/z3wrapper.py

from framework.method import Method, register_method
from framework.macros.z3 import backend as z3_backend
from kernel.term import Implies
from syntax import pprint


@register_method('z3')
class Z3Method(Method):
    """Method invoking SMT solver Z3."""
    def __init__(self):
        self.sig = []
        self.limit = None
        self.no_order = True

    def search(self, state, id, prevs, data=None):
        return []

    def display_step(self, state, data):
        return pprint.N("Apply Z3")

    def apply(self, state, id, data, prevs):
        assert z3_backend.z3_loaded, "Z3 method: not installed"
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        assms = [prev.prop for prev in prev_ths]

        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"
        goal = cur_item.th.prop

        if z3_backend.check_z3:
            assert z3_backend.solve(Implies(*(assms + [goal]))), "Z3 method: not solved"
        state.set_line(id, 'z3', args=goal, prevs=prevs)

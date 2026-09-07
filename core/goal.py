# core/goal.py - The goal concept: statement of an open target.

"""Single definition point of the goal concept (audit \u00a77.3).

A Goal is the statement of an open target: a proposition under
hypotheses.  Tactics open subgoals by minting a Goal, and the sorry
node eats the goal.  Goal is the only place outside the kernel where
the statement of a hole may be minted (through kernel.thm.Thm.sorry);
raw Thm construction elsewhere is banned by the private-constructor
lint rule.
"""

from kernel.thm import Thm
from kernel.proofterm import ProofTerm


class Goal:
    """The statement of an open goal: prop under hyps.

    Hyps flatten exactly like Thm: each entry may be a Term or a tuple
    of Terms.
    """
    def __init__(self, prop, *hyps):
        self.prop = prop
        self.hyps = hyps

    @property
    def th(self) -> Thm:
        """The statement of this goal, minted as an anonymous hole."""
        return Thm.sorry(self.prop, *self.hyps)

    def sorry(self) -> ProofTerm:
        """Open this goal as a sorry node."""
        return ProofTerm.sorry(self.th)

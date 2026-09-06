# kernel/replay.py - Pure primitive replay with assumption rules.
#
# Step 0 of the rewrite plan (ARCHITECTURE_AUDIT.md §8): the kernel-side
# half of verify. It knows ONLY:
#
#   * the 15 primitive derivation rules,
#   * theorem / variable lines,
#   * the assumption rules (sorry lines, axiom-bearing theorem lines),
#
# and nothing else. In particular it does NOT know macros: macro lines
# must be expanded to primitive streams before replay (kernel/bootstrap.py
# provides the kernel-only expander slot; the full macro registry stays
# in kernel.theory.global_macros as the kernel extension slot).
#
# The rule set is closed: any other rule name raises ReplayException.
# replay is a pure function -- it does not write back into the proof,
# does not cache subproofs, and returns the assumption list explicitly:
#
#   replay(prf) -> (Thm, holes)
#   holes = [(rule, label, Thm)]  with rule in {'sorry', 'axiom'}
#
# A theorem line's axiom status is read from the theory's thm_status
# table (maintained by the validation pipeline; 'AXIOM' marks entries
# accepted by the axiom assumption rule). Theorems without an AXIOM
# status are trusted theory content, as in check_proof.

from kernel.thm import Thm, primitive_deriv
from kernel.proof import Proof
from kernel.term import Var
from kernel import theory


class ReplayException(Exception):
    """Raised when a proof cannot be replayed with primitives only."""

    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg


def is_axiom(name: str) -> bool:
    """Whether the theorem with the given name entered the theory via
    the axiom assumption rule (as recorded in thm_status)."""
    status = theory.thy.data.get("thm_status", {})
    return status.get(name) == "AXIOM"


def _replay(prf: Proof):
    """Core replay loop. Returns (final Thm, holes, id-tuple -> Thm map)."""
    assert isinstance(prf, Proof), "replay"

    ths = {}  # id tuple -> Thm, theorems derived so far
    holes = []  # list of (rule, label, Thm)
    res_th = None

    for item in prf.items:
        rule, args, prevs = item.rule, item.args, item.prevs
        key = item.id.id

        if rule == "":
            # Empty line
            continue

        if rule == "sorry":
            # Assumption rule: anonymous open gap.
            if item.th is None:
                raise ReplayException("sorry must have explicit statement")
            ths[key] = item.th
            holes.append(("sorry", None, item.th))
            res_th = item.th
            continue

        if rule == "theorem":
            # A theorem line is either a real proof (replayable, no new
            # assumption) or an axiom (assumption rule, recorded).
            try:
                th = theory.thy.get_theorem(args)
            except theory.TheoryException:
                raise ReplayException("theorem not found: %s" % args)
            ths[key] = th
            if is_axiom(args):
                holes.append(("axiom", args, th))
            res_th = th
            continue

        if rule == "variable":
            # Variable declaration. Pure data, no derivation.
            nm, T = args
            th = Thm.mk_VAR(Var(nm, T))
            ths[key] = th
            res_th = th
            continue

        if rule == "subproof":
            raise ReplayException(
                "subproof lines must be flattened before replay")

        if rule in primitive_deriv:
            # One of the 15 primitives.
            prev_ths = []
            for prev in prevs:
                prev_th = ths.get(prev.id)
                if prev_th is None:
                    raise ReplayException(
                        "id %s cannot depend on %s (not yet derived)"
                        % (item.id, prev))
                prev_ths.append(prev_th)
            try:
                th = (primitive_deriv[rule][0](*prev_ths) if args is None
                      else primitive_deriv[rule][0](args, *prev_ths))
            except Exception as e:
                raise ReplayException(
                    "primitive %s failed: %s" % (rule, e))
            ths[key] = th
            res_th = th
            continue

        raise ReplayException(
            "rule not replayable with primitives: %s "
            "(expand macros first)" % rule)

    if res_th is None:
        raise ReplayException("empty proof")

    return res_th, holes, ths


def replay(prf: Proof):
    """Re-derive the theorem of the given proof using primitives only.

    Returns the pair (final theorem, holes), where holes lists every
    assumption rule used:

      ("sorry", None, th)    -- an open gap in the proof,
      ("axiom", name, th)    -- a theorem line accepted by the axiom rule.

    The proof is not modified. Unknown rules raise ReplayException:
    macro lines must be expanded before replay.

    """
    res_th, holes, _ = _replay(prf)
    return res_th, holes


def replay_full(prf: Proof):
    """Like replay, additionally returning the map from id tuple to
    derived theorem for every line. Used by the bootstrap expander to
    annotate appended lines."""
    return _replay(prf)

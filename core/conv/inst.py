# framework/conv/inst.py - Primitive theorem instantiation for convs.
#
# Step 1 of the rewrite plan (ARCHITECTURE_AUDIT.md §8): convs must not
# emit macro nodes (audit iron law: conv 不得出现宏名). A conv's output
# expands to primitives on export, and an apply_theorem line inside it
# would make the exported proof depend on the macro registry.
#
# inst_theorem performs the same derivation as the apply_theorem macro
# but links the result purely with primitives:
#
#   theorem + subst_type + substitution + implies_elim (+ forall_intr
#   for undetermined schematic variables, beta_norm for non-first-order
#   patterns)
#
# so convs can apply theorems without polluting exported proofs with
# macro lines. The macro layer (tactics, macros) keeps using
# core.logic.apply_theorem -- macro-to-macro emission is the
# sanctioned path.

from kernel.term import Inst
from kernel import theory
from kernel.proofterm import ProofTerm
from core import matcher
from core.conv.core import beta_norm_conv


def inst_theorem(th_name, *pts, inst=None):
    """Apply theorem th_name to the given facts, linked by primitives
    only.

    Matches the theorem's assumptions against the facts (starting from
    the optional inst), substitutes, discharges the assumptions with
    implies_elim, and forall_intr's any remaining schematic variables.
    Every emitted node is a primitive or theorem line.

    """
    th = theory.get_theorem(th_name)
    As, C = th.prop.strip_implies()
    assert len(pts) <= len(As), "inst_theorem: too many prevs"

    if inst is None:
        inst = Inst()

    svars = th.prop.get_svars()
    for v in svars:
        if v.name in inst:
            v.T.match_incr(inst[v.name].get_type(), inst.tyinst)

    pats = As[:len(pts)]
    ts = [pt.prop for pt in pts]
    inst = matcher.first_order_match_list(pats, ts, inst)

    for stvar in th.prop.get_stvars():
        assert stvar.name in inst.tyinst, \
            "inst_theorem: unmatched type variable %s" % stvar

    pt = ProofTerm.theorem(th_name)
    pt = pt.subst_type(inst.tyinst).substitution(inst)

    # Non-first-order theorems need beta normalization after
    # substitution.
    if not matcher.is_fo_pattern(th.prop):
        pt = pt.on_prop(beta_norm_conv())

    pt = pt.implies_elim(*pts)

    remain_svars = [t.subst_type(inst.tyinst)
                    for t in svars if t.name not in inst]
    for v in reversed(remain_svars):
        pt = pt.forall_intr(v)

    return pt

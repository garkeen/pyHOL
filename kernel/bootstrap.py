# kernel/bootstrap.py - Kernel-only bootstrap macros and expander.
#
# Step 0 of the rewrite plan (ARCHITECTURE_AUDIT.md §8 step 0): the
# proof machinery needed to prove theorems with kernel+syntax alone.
#
#   * bootstrap_macros: registry of macros whose get_proof_term builds
#     ProofTerm trees with PRIMITIVES ONLY -- no conv, no matcher, no
#     framework imports. They live beside kernel.theory.global_macros
#     as a separate registry: the framework's richer macros (intros
#     with apply_theorem, rewrite_*, simp, ...) remain in
#     kernel.theory.global_macros, the kernel extension slot.
#   * expand_macro_proof(prf, name, args, prevs, prev_ids): expand a
#     macro line of a proof into a pure primitive stream appended to
#     the proof, verified by kernel.replay.
#
# The bootstrap macros implement the semantic core of their framework
# counterparts (framework/macros/core.py intros / trivial) restricted to
# pure primitives, so kernel+syntax can prove non-trivial theorems
# end-to-end without the core.

from kernel.thm import Thm
from kernel.term import Term, Implies
from kernel.proof import Proof, ItemID, ProofItem
from kernel.proofterm import ProofTerm
from kernel.macro import Macro
from kernel import replay


class intros_macro(Macro):
    """Introduce assumptions: from a proof of C under assumptions
    A_1, ..., A_n (each prev proved the corresponding A_i), derive
    |- A_1 --> ... --> A_n --> C.

    get_proof_term expects prevs = [pt_A1, ..., pt_An, pt_C], mirroring
    the framework intros macro's variable/assume/continuation order
    restricted to the assume case.

    """

    def __init__(self):
        self.level = None  # always expanded: pure primitives
        self.sig = None
        self.limit = None

    def get_proof_term(self, args, pts):
        assert len(pts) >= 1, "bootstrap intros_macro"
        pt = pts[-1]
        for prev in reversed(pts[:-1]):
            # Each prev proves an assumption A_i.
            assert prev.th.hyps == (prev.th.prop,), \
                ("bootstrap intros_macro: prev must be a bare assumption, "
                 "got %s" % prev.th)
            pt = pt.implies_intr(prev.th.prop)
        return pt

    def expand(self, prefix, args, prevs):
        pts = tuple(ProofTerm.atom(prev_id, th)
                    for prev_id, th in prevs)
        return self.get_proof_term(args, pts).export(prefix)


class trivial_macro(Macro):
    """Prove A_1 --> ... --> A_n --> B when B agrees with some A_i,
    using assume + implies_intr only."""

    def __init__(self):
        self.level = None
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts):
        prop = args
        As, C = prop.strip_implies()
        assert C in As, "bootstrap trivial_macro: %s not among assumptions" % C
        pt = ProofTerm.assume(C)
        for A in reversed(As):
            pt = pt.implies_intr(A)
        return pt

    def expand(self, prefix, args, prevs):
        assert not prevs, "bootstrap trivial_macro takes no prevs"
        return self.get_proof_term(args, []).export(prefix)


"""Registry of kernel-only bootstrap macros. Separate from
kernel.theory.global_macros (the kernel extension slot filled by the
framework and domain packages)."""
bootstrap_macros = {
    "intros": intros_macro(),
    "trivial": trivial_macro(),
}


def get_bootstrap_macro(name):
    if name not in bootstrap_macros:
        return None
    return bootstrap_macros[name]


def expand_macro_proof(prf: Proof, name: str, args, prevs, prev_ids):
    """Expand the macro line (name, args, prevs) against the given
    proof, appending the expanded primitive lines to prf.

    prevs -- theorems of the macro's input facts;
    prev_ids -- their ItemIDs in prf (the appended lines may depend on
        them via atom references).

    Returns the modified proof, or None if the macro is not a bootstrap
    macro. The appended lines are verified immediately by pure
    primitive replay of the whole proof.

    """
    macro = get_bootstrap_macro(name)
    if macro is None:
        return None

    pts = tuple(ProofTerm.atom(prev_id, th)
                for prev_id, th in zip(prev_ids, prevs))
    pt = macro.get_proof_term(args, pts)

    # export appends flat ids starting at len(prf.items); subproof=False
    # requires a nonempty prefix id.
    prefix = ItemID(len(prf.items) if prf.items else 0)
    expanded = pt.export(prefix=prefix, prf=prf, subproof=False)
    # Verify by pure primitive replay of the whole stream and record
    # the derived theorem on the new last line.
    th, holes = replay.replay(expanded)
    expanded.items[-1].th = th
    return expanded

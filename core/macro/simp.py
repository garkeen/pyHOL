# framework/macro/simp.py - The simp macro's expansion mechanism.
#
# simp_sweep applies all hint_rewrite theorems of the current theory,
# round by round, to a fixed point. It is shared by the simp tactic
# (pre-check), the simp macro (kernel expansion) and the auto macro
# (fixpoint loop). Moved here from tactic/steps.py in rewrite
# step 2 (ARCHITECTURE_AUDIT.md §8): the tactic layer imports it from
# this module (downward), and tactic/steps.py no longer imports
# core.auto -- the tactic<->auto import cycle is dissolved.
#
# The lazy `from core import auto` below is the same-layer
# auto<->simp mutual recursion (solve, simplify, retry); both modules
# land in core/ at the step-9 rename.

from kernel import theory
from core.conv import then_conv, top_conv, rewr_conv, beta_norm_conv


def simp_sweep(C, *, max_rounds=100, pts=None):
    """Iterated rewrite sweep: apply all unconditional hint_rewrite
    theorems of the current theory to C, round by round, until a fixed
    point (bounded). Returns (cv_acc, current) where cv_acc converts C
    to current, or (None, C) when nothing can be simplified.

    Shared between the simp tactic (pre-check) and the simp macro
    (kernel expansion).

    With pts given, conditional hint_rewrite theorems are also tried:
    each premise is discharged by auto.solve against pts. Without pts
    only unconditional rewrites participate (simp method behavior).
    """
    from core import auto
    uncond_names = []
    cond_thms = []
    attrs = theory.thy.get_data('attributes')
    for nm, a in attrs.items():
        if 'hint_rewrite' not in a:
            continue
        try:
            th = theory.thy.get_theorem(nm)
        except theory.TheoryException:
            continue
        As, concl = th.prop.strip_implies()
        if not concl.is_equals():
            continue
        if len(As) == 0:
            uncond_names.append(nm)
        elif pts is not None:
            cond_thms.append((nm, As))

    def round_step(current):
        round_cv = None
        for nm in uncond_names:
            try:
                top_conv(rewr_conv(nm)).get_proof_term(current)
            except Exception:
                continue
            cv_i = top_conv(rewr_conv(nm))
            round_cv = cv_i if round_cv is None else then_conv(round_cv, cv_i)
        if pts is not None:
            for nm, As in cond_thms:
                try:
                    cond_pts = [auto.solve(A, pts) for A in As]
                except Exception:
                    continue
                try:
                    top_conv(rewr_conv(nm, conds=cond_pts)).get_proof_term(current)
                except Exception:
                    continue
                cv_i = top_conv(rewr_conv(nm, conds=cond_pts))
                round_cv = cv_i if round_cv is None else then_conv(round_cv, cv_i)
        return round_cv

    cv_acc = None
    current = C
    for _ in range(max_rounds):
        round_cv = round_step(current)
        if round_cv is None:
            break
        round_cv = then_conv(round_cv, beta_norm_conv())
        new_prop = round_cv.eval(current).prop.rhs
        cv_acc = round_cv if cv_acc is None else then_conv(cv_acc, round_cv)
        if new_prop == current:
            break
        current = new_prop

    return cv_acc, current

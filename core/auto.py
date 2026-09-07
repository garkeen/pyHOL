# framework/auto.py - Generic proof automation (domain-independent)
#
# A head-term -> proof-procedure dispatch engine shared by all domains:
# nat/real/... register their normalization and solving procedures into
# global_autos / global_autos_norm.  The connective decomposition in
# solve() only uses logic_base axioms (conjI, conjD1, disjE, ...), which
# are always available, so this module belongs to the core.

from kernel import term
from kernel.term import Term, Var
from kernel.macro import Macro
from kernel import theory
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, TacticException
from core import logic
from core.logic import apply_theorem
from core import matcher
from core.conv import Conv, ConvException, refl, eta_conv, top_conv
from util import name


"""Setup for generic automation.

Generic automation is organized as a mapping from head terms
to proof procedures. Each proof procedure takes as arguments the
current theory, a term (the goal), and a list of conditions
(as proof terms), and either returns a proof term or fails.

"""
# Turn on / off debugging information
debug_auto = False

# Mapping from head terms to the corresponding automatic procedure.
global_autos = dict()

# Mapping from negation of head terms to the corresponding automatic
# procedure.
global_autos_neg = dict()

# Mapping from head term to the normalization / simplification
# procedure
global_autos_norm = dict()


def add_global_autos(head, f):
    if head not in global_autos:
        global_autos[head] = [f]
    else:
        global_autos[head].append(f)

def add_global_autos_neg(head, f):
    if head not in global_autos_neg:
        global_autos_neg[head] = [f]
    else:
        global_autos_neg[head].append(f)

def add_global_autos_norm(head, f):
    if head not in global_autos_norm:
        global_autos_norm[head] = [f]
    else:
        global_autos_norm[head].append(f)


solve_record = dict()

def solve(goal, pts=None, depth=0):
    """The main automation function.

    If the function succeeds, it should return a proof term whose
    proposition is the goal.

    depth guards recursive backchaining in solve_hints.

    """
    if debug_auto:
        print("Solve:", goal, [str(pt.prop) for pt in pts])

    if pts is None:
        pts = []
    elif isinstance(pts, tuple):
        pts = list(pts)

    # First handle the case where goal matches one of the conditions.
    for pt in pts:
        if goal == pt.prop:
            return pt

    # Next, consider the situation where one of the assumptions is
    # a conjunction or a disjunction.
    for i, pt in enumerate(pts):
        if pt.prop.is_conj():
            pt1 = apply_theorem('conjD1', pt)
            pt2 = apply_theorem('conjD2', pt)
            return solve(goal, [pt1, pt2] + pts[:i] + pts[i+1:], depth=depth)

        if pt.prop.is_disj():
            a1, a2 = pt.prop.args
            assume_pt1 = ProofTerm.assume(a1)
            assume_pt2 = ProofTerm.assume(a2)
            pt1 = solve(goal, [assume_pt1] + pts[:i] + pts[i+1:], depth=depth)
            pt1 = pt1.implies_intr(a1)
            pt2 = solve(goal, [assume_pt2] + pts[:i] + pts[i+1:], depth=depth)
            pt2 = pt2.implies_intr(a2)
            return apply_theorem('disjE', pt, pt1, pt2)

    # Handle various logical connectives.
    if goal.is_conj():
        a1, a2 = goal.args
        pt1 = solve(a1, pts, depth=depth)
        pt2 = solve(a2, pts, depth=depth)
        return apply_theorem('conjI', pt1, pt2)

    if goal.is_disj():
        a1, a2 = goal.args
        try:
            pt1 = solve(a1, pts, depth=depth)
            return apply_theorem('disjI1', pt1, concl=goal)
        except TacticException:
            pt2 = solve(a2, pts, depth=depth)
            return apply_theorem('disjI2', pt2, concl=goal)

    if goal.is_implies():
        a1, a2 = goal.args
        assume_pt = ProofTerm.assume(a1)
        return solve(a2, [assume_pt] + pts, depth=depth).implies_intr(a1)

    if goal.is_forall():
        var_names = [v.name for v in term.get_vars([goal] + [pt.prop for pt in pts])]
        nm = name.get_variant_name(goal.arg.var_name, var_names)
        v = Var(nm, goal.arg.var_T)
        t = goal.arg.subst_bound(v)
        return solve(t, pts, depth=depth).forall_intr(v)

    # Normalize goal
    eq_pt = norm(goal, pts)
    goal = eq_pt.rhs

    if goal.is_conj():
        pt = solve(goal, pts, depth=depth)
        return eq_pt.symmetric().equal_elim(pt)

    res_pt = None

    if not pts and goal in solve_record:
        res_pt = solve_record[goal]

    # Call registered functions
    elif goal.is_not() and goal.arg.head in global_autos_neg:
        for f in global_autos_neg[goal.arg.head]:
            try:
                res_pt = f(goal, pts)
                break
            except TacticException:
                pass

    elif goal.head in global_autos:
        for f in global_autos[goal.head]:
            try:
                res_pt = f(goal, pts)
                break
            except TacticException:
                pass

    if res_pt is not None:
        if not pts:
            solve_record[goal] = res_pt
        return eq_pt.symmetric().equal_elim(res_pt)
    else:
        return solve_hints(eq_pt.rhs, pts, depth=depth)


def solve_hints(goal, pts, depth=0, max_depth=6):
    """Backchain over hint_backward theorems and assumption implications.

    Tries each hint_backward candidate whose conclusion matches goal,
    recursively solving its premises. Falls back to modus ponens on
    assumption implications. Raises TacticException on failure.
    """
    if depth > max_depth:
        raise TacticException('Cannot solve %s' % goal)

    from core import search

    for th_name in search.candidates_for(goal, category='hint_backward'):
        if not theory.thy.has_theorem(th_name):
            continue
        th = theory.get_theorem(th_name)
        try:
            inst = matcher.first_order_match(th.concl, goal)
        except matcher.MatchException:
            continue
        As, _ = th.prop.subst_norm(inst).strip_implies()
        try:
            sub_pts = [solve(A, pts, depth=depth + 1) for A in As]
        except TacticException:
            continue
        try:
            return apply_theorem(th_name, *sub_pts, concl=goal)
        except (TacticException, matcher.MatchException, AssertionError):
            continue

    for pt in pts:
        if not pt.prop.is_implies():
            continue
        A0, B0 = pt.prop.arg1, pt.prop.arg
        try:
            inst = matcher.first_order_match(B0, goal)
        except matcher.MatchException:
            continue
        try:
            sub = solve(A0.subst_norm(inst), pts, depth=depth + 1)
        except TacticException:
            continue
        return pt.substitution(inst).implies_elim(sub)

    raise TacticException('Cannot solve %s' % goal)


def solve_rules(th_names):
    """Return a solve function that tries to apply each of the theorems
    in th_names.

    """ 
    def solve_fun(goal, pts, depth=0):
        for th_name in th_names:
            if theory.thy.has_theorem(th_name):
                th = theory.get_theorem(th_name)
            else:
                continue
            try:
                inst = matcher.first_order_match(th.concl, goal)
            except matcher.MatchException:
                continue

            As, _ = th.prop.subst_norm(inst).strip_implies()
            try:
                pts = [solve(A, pts, depth=depth + 1) for A in As]
            except TacticException:
                continue

            return apply_theorem(th_name, *pts, concl=goal)

        # Not solved
        raise TacticException

    return solve_fun


norm_record = dict()

def norm(t, pts=None):
    """The main normalization function.
    
    The function should always succeed. It returns an equality whose left
    side is t. If no normalization is available, it returns t = t.

    """
    if debug_auto:
        print("Norm:", t, [str(pt.prop) for pt in pts])

    # Do not normalize variables and abstractions
    if t.is_var() or t.is_abs():
        return refl(t)

    # No further work for numbers
    if t.is_number():
        return refl(t)

    # Record
    if not pts and t in norm_record:
        return norm_record[t]

    eq_pt = refl(t.head)

    # First normalize each argument
    for arg in t.args:
        eq_pt = eq_pt.combination(norm(arg, pts))

    # Next, apply each normalization rule
    if t.head in global_autos_norm:
        ori_rhs = eq_pt.rhs
        for f in global_autos_norm[t.head]:
            try:
                if isinstance(f, Conv):
                    eq_pt = eq_pt.on_rhs(f)
                else:
                    eq_pt = eq_pt.transitive(f(eq_pt.rhs, pts))
            except ConvException:
                continue

            if eq_pt.rhs.head != t.head:
                # Head changed, should try something else
                break

        if eq_pt.rhs == ori_rhs:
            # Unchanged, normalization stops here
            res_pt = eq_pt
        else:
            # Head changed, continue apply norm
            eq_pt2 = norm(eq_pt.rhs, pts)
            if eq_pt2.lhs != eq_pt.rhs:
                eq_pt2 = eq_pt2.on_lhs(top_conv(eta_conv()))
            res_pt = eq_pt.transitive(eq_pt2)
    else:
        # No normalization rule available for this head
        res_pt = eq_pt

    if not pts:
        norm_record[t] = res_pt
    return res_pt

def norm_rules(th_names):
    """Return a normalization function that tries to apply each of the
    rewriting rules.

    """
    def norm_fun(t, pts):
        for th_name in th_names:
            if theory.thy.has_theorem(th_name):
                th = theory.get_theorem(th_name)
            else:
                continue

            try:
                inst = matcher.first_order_match(th.concl.lhs, t)
            except matcher.MatchException:
                continue

            As, C = th.prop.subst_norm(inst).strip_implies()
            try:
                pts = [solve(A, pts) for A in As]
            except TacticException:
                continue

            return apply_theorem(th_name, *pts, concl=C)

        # No rewriting available
        return refl(t)

    return norm_fun


@register_macro('auto')
class auto_macro(Macro):
    """Macro applying auto.solve, interleaved with simplification.

    Fixpoint loop (bounded): try solve on the current goal; on
    failure simplify one round with simp_sweep and retry. The
    simplification chain is composed back to the original goal,
    so the whole macro stays a single level-1 line.
    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, pts, max_rounds=10):
        from core.macro.simp import simp_sweep
        cur = args
        chain = None
        for _ in range(max_rounds):
            if cur.is_equals():
                eq1 = norm(cur.lhs, pts)
                eq2 = norm(cur.rhs, pts)
                if eq1.rhs == eq2.rhs:
                    close = eq1.transitive(eq2.symmetric())
                    return close if chain is None else chain.transitive(close)
            try:
                close = solve(cur, pts)
            except TacticException:
                close = None
            if close is not None:
                if chain is None:
                    return close
                return chain.symmetric().equal_elim(close)
            cv_acc, new_cur = simp_sweep(cur, pts=pts)
            if cv_acc is None or new_cur == cur:
                break
            step = refl(cur).transitive(cv_acc.get_proof_term(cur))
            chain = step if chain is None else chain.transitive(step)
            cur = new_cur
        # Final attempt for an honest error message.
        if cur.is_equals():
            eq1 = norm(cur.lhs, pts)
            eq2 = norm(cur.rhs, pts)
            if eq1.rhs == eq2.rhs:
                close = eq1.transitive(eq2.symmetric())
                return close if chain is None else chain.transitive(close)
        close = solve(cur, pts)
        if chain is None:
            return close
        return chain.symmetric().equal_elim(close)


def auto_solve(t, pts=None):
    return ProofTerm('auto', args=t, prevs=pts)

class norm_conv(Conv):
    """Convert a term to its normal form under the registered
    normalization procedures (dispatches to norm).

    Replaces the deleted auto_conv: returns the derivation built by
    norm directly instead of wrapping it in an 'auto' macro node, so
    the exported proof contains the actual rewrite chain. Conditional
    rewriting premises are passed explicitly via conds.

    """
    def __init__(self, conds=None):
        if conds is None:
            conds = []
        self.conds = conds

    def get_proof_term(self, t):
        return norm(t, self.conds)


"""Managing cache records."""
def cache_stats():
    return "Norm: %d\nSolve: %d" % (len(norm_record), len(solve_record))

def clear_cache():
    global norm_record, solve_record
    norm_record = dict()
    solve_record = dict()

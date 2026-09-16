"""Recursion-relation inference: the measure matrix, as Isabelle does it.

`lexicographic_order.ML` is where Isabelle's `fun` decides which relation
its equations descend through.  It does not look at patterns: each
recursive call is a *row*, each candidate measure function on the tupled
argument is a *column*, and a cell says what the call does at that measure
-- strictly decreases (`<`), does not increase (`<=`), or nothing that can
be shown.  A column is usable when every cell of it is one of the two and
at least one is strict.  The relation is then the right-nested chain

    m_1 <*mlex*> (m_2 <*mlex*> ... <*mlex*> (%x y. false))

over the columns the search kept; its well-foundedness is `wf_mlex`
peeled once per measure down to `wf_false`, and each call is discharged by
walking its row (`mlex_leq` where the call only does not increase,
`mlex_less` where it strictly decreases).

This module is that inference on terms.  It decides which measures to use
and, for every cell, *how* it is proved -- the rewrite sequence for the two
sides plus the arithmetic lemmas at the end -- so the emitter can write the
steps out with literal IDs.  No running prover is consulted: the cells are
decided by reducing both sides with the destructors, the datatypes' size
equations and `1 + t = Suc t`, then comparing the normal forms.

Isabelle's search takes the first usable column and never looks back; a
decision procedure can afford to backtrack, so `infer` searches all
orders and returns None when no chain of the candidate measures works.
"""
from kernel.type import TFun, TConst

NatType = TConst('nat')
from kernel.term import Var, Const, Lambda, Abs

# The arithmetic rules the reduction uses, and the lemmas a comparison
# cites.  All of them are `nat`'s.
ARITH = ['add_1_left', 'add_1_right']


class Cell:
    """What one call does at one measure, with the proof it needs.

    `prop` is the cell as the goal has it (`m call < m lhs` or `m call <=
    m lhs`, the measure applied but not yet reduced); `steps` is what the
    emitted proof writes before the closing `rule`, in order; `kind` is
    `'lt'` or `'le'`.
    """

    def __init__(self, prop, kind, steps):
        self.prop = prop
        self.kind = kind
        self.steps = steps

    def __repr__(self):
        return 'Cell(%s, %s)' % (self.kind, self.prop)


class Measure:
    """A candidate measure on the tupled argument of a definition.

    `kind` is what the measure is made of at that position: `'nat'` is the
    identity (a natural-number argument carries its own order), `'size'` is
    the datatype's generated size function.  A position whose type has
    neither -- a function type, a type variable, a datatype without a size
    family -- contributes no column at all.
    """

    def __init__(self, pos, arg_types, kind, size_name=None):
        self.pos = pos
        self.arg_types = arg_types
        self.kind = kind
        self.size_name = size_name

    def __repr__(self):
        return 'Measure(%d, %s)' % (self.pos, self.kind)

    def term(self, p):
        """The measure as a lambda over the tuple term p."""
        from core import fungen
        proj = fungen.projection(p, self.arg_types, self.pos)
        if self.kind == 'nat':
            body = proj
        else:
            T = self.arg_types[self.pos]
            body = Const(self.size_name, TFun(T, NatType))(proj)
        return Lambda(p, body)

    def applied(self, tup):
        """`m tup`, with the beta redex reduced away."""
        return self.term(Var('p', tup.get_type()))(tup).beta_norm()


def candidate_measures(arg_types, size_of):
    """The measures a definition's argument types admit.

    `size_of` maps a type to its size function's name or None, which is
    the datatype layer's business.  Every position is offered, not just
    the one the patterns are on: which column carries the descent is what
    the search decides.
    """
    res = []
    for pos, T in enumerate(arg_types):
        if T == NatType:
            res.append(Measure(pos, arg_types, 'nat'))
        elif size_of(T) is not None:
            res.append(Measure(pos, arg_types, 'size', size_of(T)))
    return res


# ---------------------------------------------------------------------------
# Reduction: destructors, size equations, and the two `1 + t` forms.
# ---------------------------------------------------------------------------

def _size_body(size_name, T, cname, recs):
    """`1 + size r_1 + ... + size r_n` for the recursive arguments."""
    parts = [Const(size_name, TFun(r.get_type(), NatType))(r) for r in recs]
    res = Const('one', NatType)
    for p in parts:
        res = Const('plus', TFun(NatType, NatType, NatType))(res, p)
    return res


def _redex_kind(t, dmap, sizes):
    """(replacement, rule) for the top-most redex of t, or (t, None)."""
    h, args = t.strip_comb()
    if not h.is_const():
        return t, None
    if h.name in dmap and len(args) == 1:
        inner, iargs = args[0].strip_comb()
        cname, j, rule = dmap[h.name]
        if inner.is_const() and inner.name == cname and len(iargs) > j:
            return iargs[j], rule
    if h.name in sizes and len(args) == 1:
        inner, iargs = args[0].strip_comb()
        if inner.is_const() and inner.name in sizes[h.name]:
            rule, recs = sizes[h.name][inner.name]
            T = args[0].get_type()
            return _size_body(h.name, T, inner.name, recs), rule
    if h.name == 'plus' and len(args) == 2:
        if args[0] == Const('one', NatType):
            return Const('Suc', TFun(NatType, NatType))(args[1]), 'add_1_left'
        if args[1] == Const('one', NatType):
            return Const('Suc', TFun(NatType, NatType))(args[0]), 'add_1_right'
    return t, None


def _sweep(t, dmap, sizes):
    """A top-down sweep like the method layer's: (term, rule).

    The rule is tried at a node and, where it fires, that path is not
    descended into -- which is exactly what one `rewrite` step does -- so
    the rule this returns is the first one that fires anywhere, and `t` is
    the term after clearing every top-most redex of it.
    """
    fired = [None]

    def rec(x):
        y, rule = _redex_kind(x, dmap, sizes)
        if rule is not None:
            fired[0] = rule
            return y
        if x.is_comb():
            f, a = rec(x.fun), rec(x.arg)
            return x if (f is x.fun and a is x.arg) else f(a)
        if x.is_abs():
            body = rec(x.body)
            return x if body is x.body else Abs(x.var_name, x.var_T, body)
        return x

    return rec(t), fired[0]


def reduce(t, dmap, sizes=None):
    """(normal form of t, the rules one `rewrite` step each runs through)."""
    sizes = sizes or {}
    steps = []
    while True:
        t2, rule = _sweep(t, dmap, sizes)
        if rule is None:
            return t, steps
        steps.append(rule)
        t = t2


def _merge(steps_a, steps_b):
    """The steps that reduce both sides at once, in order.

    A `rewrite` step clears the rule's top-most redexes wherever they are,
    so one side needing the rule twice and the other once means the goal
    needs it twice: the merged list takes the larger count of each rule,
    in the order the rules first appear.
    """
    order = []
    for s in list(steps_a) + list(steps_b):
        if s not in order:
            order.append(s)
    res = []
    for s in order:
        res.extend([s] * max(steps_a.count(s), steps_b.count(s)))
    return res


def _suc_spine(t, n):
    """`Suc^n t`, or None when t is not that many successors deep."""
    for _ in range(n):
        h, args = t.strip_comb()
        if h.is_const() and h.name == 'Suc' and len(args) == 1:
            t = args[0]
        else:
            return None
    return t


def compare(left, right):
    """`('lt' | 'le' | None, the lemmas that close the comparison)`.

    Both sides are nat terms in normal form.  Decidable: the same term
    (`<=`), the right side one successor above the left (`<`), or the left
    side as a summand of the right (`<=`, and `<` when the right side is
    that sum's successor).
    """
    if left == right:
        return 'le', ['lesseq_refl']
    inner = _suc_spine(right, 1)
    if inner is not None:
        if inner == left:
            return 'lt', ['less_Suc_lesseq', 'lesseq_refl']
        h2, args2 = inner.strip_comb()
        if (h2.is_const() and h2.name == 'plus' and len(args2) == 2
                and args2[0] == left):
            return 'lt', ['less_Suc_lesseq', 'le_add']
    h, args = right.strip_comb()
    if h.is_const() and h.name == 'plus' and len(args) == 2 and args[0] == left:
        return 'le', ['le_add']
    return None, []


def cell(measure, call, lhs, dmap, sizes=None):
    """The cell of one call at one measure, or None when unusable."""
    from core import fungen
    left0, right0 = measure.applied(call), measure.applied(lhs)
    left, steps_l = reduce(left0, dmap, sizes)
    right, steps_r = reduce(right0, dmap, sizes)
    kind, close = compare(left, right)
    if kind is None:
        return None
    prop = '%s %s %s' % (fungen._prints(left0),
                         '<' if kind == 'lt' else '<=',
                         fungen._prints(right0))
    return Cell(prop, kind, _merge(steps_l, steps_r) + close)


# ---------------------------------------------------------------------------
# The search.
# ---------------------------------------------------------------------------

def infer(measures, calls, dmap, sizes=None):
    """The measures to build the relation from, most significant first.

    `calls` is a list of `(call tuple, the equation's own tuple)` pairs --
    one per recursive call in the whole definition.  Every call has to end
    up strictly decreasing at some column; a usable column lets the calls
    that are strict there stop and the rest recurse on the columns after
    it.  Returns None when no order of the candidate measures works, which
    is the honest answer: this definition's recursion is not expressible
    with the measures in hand.
    """
    if not calls:
        return []
    return _search(measures, list(calls), dmap, sizes or {})


def _search(measures, calls, dmap, sizes):
    if not calls:
        return []
    for measure in measures:
        cells = [cell(measure, call, lhs, dmap, sizes) for call, lhs in calls]
        if any(c is None for c in cells):
            continue
        if not any(c.kind == 'lt' for c in cells):
            continue
        rest = [c for c, cl in zip(calls, cells) if cl.kind == 'le']
        sub = _search([m for m in measures if m is not measure], rest, dmap,
                      sizes)
        if sub is not None:
            return [measure] + sub
    return None

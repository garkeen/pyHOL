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
and, for every cell, *how* it is proved -- the rewrite sequence that
normalizes both sides plus the last steps that close the comparison -- so
the emitter can write the steps out with literal IDs.  No running prover
is consulted: the cells are decided by reducing both sides with the
destructors, the datatypes' size equations and the arithmetic rules below,
then comparing the normal forms.

The normal form of a side is a `Suc`-spine over a right-nested sum of
atoms:

    Suc^k (a_1 + (a_2 + ... + a_n))

where an atom is anything the rules cannot take apart (a variable, a
`size` of a variable, a destructor application).  Two sides are compared
by reading those forms: the strict case needs one more `Suc` on the right
(`less_Suc_lesseq` turns it into the weak one), a common `Suc` on both
sides is stripped (`le_suc`), a surplus `Suc` on the right is absorbed
(`le_suc_right`), and then the left side's atoms have to be a
sub-multiset of the right side's, consumed from the left: an atom the
left side does not start with is added to both sides (`le_add_left_mono`),
one it does is consumed (`le_add_front`), and an atom equal to the whole
current left side closes by `le_add`.  Every one of those steps is a
lemma of `nat`, so the emitted proof is a sequence of ordinary steps with
no automation in it.

Isabelle's search takes the first usable column and never looks back; a
decision procedure can afford to backtrack, so `infer` searches all
orders and returns None when no chain of the candidate measures works.
"""
from kernel.type import TFun, TConst, BoolType

NatType = TConst('nat')
from kernel.term import Var, Const, Lambda, Abs

# The arithmetic rules the normalization runs, in one `rewrite` step each:
# `1 + x` and `x + 1` are `Suc`, a `Suc` summand moves out of the sum, and
# sums are right-associated.  Together they are terminating and put every
# side into the normal form described above.
ARITH = ['add_1_left', 'add_1_right', 'add_Suc_left', 'add_Suc_right',
         'add_assoc']

# The lemmas a finished comparison is closed with.  They are the nat
# comparisons the normalization leaves behind:
#   less_Suc_lesseq  m < Suc n <--> m <= n
#   le_suc           Suc m <= Suc n <--> m <= n
#   lesseq_refl      n <= n
#   lesseq_zero      0 <= n
#   le_add           m <= m + n
#   le_suc_right     m <= n --> m <= Suc n
#   le_add_front     m <= n --> p + m <= p + n
#   le_add_left_mono m <= n --> m <= p + n
CLOSING_LEMMAS = ['less_Suc_lesseq', 'le_suc', 'lesseq_refl', 'lesseq_zero',
                  'le_add', 'le_suc_right', 'le_add_front',
                  'le_add_left_mono']


def _suc(t):
    return Const('Suc', TFun(NatType, NatType))(t)


def _plus(a, b):
    return Const('plus', TFun(NatType, NatType, NatType))(a, b)


def _sucs(t, n):
    for _ in range(n):
        t = _suc(t)
    return t


def _is_suc(t):
    h, args = t.strip_comb()
    return h.is_const() and h.name == 'Suc' and len(args) == 1


def _is_plus(t):
    h, args = t.strip_comb()
    return h.is_const() and h.name == 'plus' and len(args) == 2


class Closing:
    """The last steps of a comparison proof, as a tree.

    The goal is already in normal form, so what is left is the comparison
    of the two atom sums.  A node is either `('rule', thm)` -- a theorem
    without premises closes the goal -- or `('cut', thm, prop, sub)`: the
    sub-comparison `prop` is stated and proved by `sub`, and the goal is
    then closed by `thm`, whose only premise is that sub-comparison.
    """

    def __init__(self, kind, theorem, prop=None, sub=None):
        self.kind = kind
        self.theorem = theorem
        self.prop = prop
        self.sub = sub

    def __repr__(self):
        return 'Closing(%s, %s)' % (self.kind, self.theorem)


class Cell:
    """What one call does at one measure, with the proof it needs.

    `prop` is the cell as the rule that uses it states it -- `m call < m
    pat` or `m call <= m pat`, with the measure applied to the tuples and
    *not* reduced: that is the form `mlex_less` / `mlex_leq` matches, and
    the matcher does not see through a beta redex, so the application has
    to be written the way the relation writes it.  `beta` says whether
    that proposition still carries a redex (it does whenever the measure
    is a lambda), `steps` are the rewrites that normalize it, and
    `closing` finishes it.
    """

    def __init__(self, prop, kind, beta, steps, closing):
        self.prop = prop
        self.kind = kind
        self.beta = beta
        self.steps = steps
        self.closing = closing

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

    def __init__(self, pos, arg_types, kind, size_name=None, def_name=None):
        self.pos = pos
        self.arg_types = arg_types
        self.kind = kind
        self.size_name = size_name
        # The constant the emitter defines for this measure.  A measure is
        # a *named* function, not a lambda written into the relation: the
        # rules that use it (`mlex_less`, `mlex_leq`) state their premises
        # as `f x`, and the matcher is first-order -- it does not beta
        # reduce -- so `f` has to be a constant whose application a
        # `rewrite <f>_def` step unfolds.  With a lambda the premise would
        # be an unreduced redex no fact could match, and the only way to
        # reduce it (`beta`) creates a number of items that cannot be
        # counted statically.
        self.def_name = def_name

    def __repr__(self):
        return 'Measure(%d, %s)' % (self.pos, self.kind)

    def is_named(self):
        return self.def_name is not None

    def as_const(self, Tup):
        """The measure as the function constant the relation uses."""
        return Const(self.def_name, TFun(Tup, NatType))

    def body(self, p):
        """The measure as a function of the tuple term p."""
        from core import fungen
        proj = fungen.projection(p, self.arg_types, self.pos)
        if self.kind == 'nat':
            return proj
        T = self.arg_types[self.pos]
        return Const(self.size_name, TFun(T, NatType))(proj)

    def term(self, p):
        """The measure as a lambda over the tuple term p."""
        return Lambda(p, self.body(p))

    def applied(self, tup):
        """`m tup`, ready to be reduced (`is_named` avoids the redex)."""
        if self.def_name is not None:
            return Const(self.def_name, TFun(tup.get_type(), NatType))(tup)
        return self.term(Var('p', tup.get_type()))(tup).beta_norm()

    def tables(self):
        """The measure's own reduction rule: name -> body, for `_redex_kind`.

        The defining equation is `m p = <body>` with `p` free, so a
        `rewrite m_def` substitutes the tuple into the body directly --
        that is what makes the cell's first step one item, statically
        countable, instead of a beta normalization of unknown length.
        """
        if self.def_name is None:
            return {}
        return {self.def_name: self.body}


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
# Normalization: destructors, size equations, and the arithmetic rules.
# ---------------------------------------------------------------------------

def _size_body(size_name, T, args, positions):
    """`1 + size r_1 + ... + size r_n` for the recursive arguments."""
    parts = [Const(size_name, TFun(T, NatType))(args[j]) for j in positions]
    res = Const('one', NatType)
    for p in parts:
        res = Const('plus', TFun(NatType, NatType, NatType))(res, p)
    return res


def _arith_redex(t):
    """(replacement, rule) for the top-most arithmetic redex of t."""
    if not _is_plus(t):
        return None
    x, y = t.strip_comb()[1]
    one = Const('one', NatType)
    if x == one:
        return _suc(y), 'add_1_left'
    if y == one:
        return _suc(x), 'add_1_right'
    if _is_suc(x):
        return _suc(_plus(x.arg, y)), 'add_Suc_left'
    if _is_suc(y):
        return _suc(_plus(x, y.arg)), 'add_Suc_right'
    if _is_plus(x):
        x1, x2 = x.strip_comb()[1]
        return _plus(x1, _plus(x2, y)), 'add_assoc'
    return None


def _redex_kind(t, dmap, sizes, mdefs):
    """(replacement, rule) for the top-most redex of t, or (t, None)."""
    h, args = t.strip_comb()
    if not h.is_const():
        return t, None
    if h.name in mdefs and len(args) == 1:
        return mdefs[h.name](args[0]), '%s_def' % h.name
    if h.name in dmap and len(args) == 1:
        inner, iargs = args[0].strip_comb()
        cname, j, rule = dmap[h.name]
        if inner.is_const() and inner.name == cname and len(iargs) > j:
            return iargs[j], rule
    if h.name in sizes and len(args) == 1:
        inner, iargs = args[0].strip_comb()
        if inner.is_const() and inner.name in sizes[h.name]:
            rule, positions = sizes[h.name][inner.name]
            T = args[0].get_type()
            return _size_body(h.name, T, iargs, positions), rule
    if h.name == 'plus':
        res = _arith_redex(t)
        if res is not None:
            return res
    return t, None


def _sweep(t, dmap, sizes, mdefs):
    """A top-down sweep like the method layer's: (term, rule).

    The rule is tried at a node and, where it fires, that path is not
    descended into -- which is exactly what one `rewrite` step does -- so
    the rule this returns is the first one that fires anywhere, and `t` is
    the term after clearing every top-most redex of it.
    """
    fired = [None]

    def rec(x):
        y, rule = _redex_kind(x, dmap, sizes, mdefs)
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


def reduce(t, dmap, sizes=None, mdefs=None):
    """(normal form of t, the rules one `rewrite` step each runs through)."""
    sizes, mdefs = sizes or {}, mdefs or {}
    steps = []
    while True:
        t2, rule = _sweep(t, dmap, sizes, mdefs)
        if rule is None:
            return t, steps
        steps.append(rule)
        t = t2


# ---------------------------------------------------------------------------
# Reading the normal form, and proving the comparison it leaves.
# ---------------------------------------------------------------------------

def _spine(t):
    """(number of `Suc`s, the term under them) for a normal form."""
    k = 0
    while _is_suc(t):
        k += 1
        t = t.arg
    return k, t


def _atoms(t):
    """The atoms of a right-nested sum, in order."""
    res = []
    while _is_plus(t):
        x, t = t.strip_comb()[1]
        res.append(x)
    res.append(t)
    return res


def _sum(atoms):
    """The right-nested sum of the given atoms."""
    res = atoms[-1]
    for a in reversed(atoms[:-1]):
        res = _plus(a, res)
    return res


def _prove_le(left, right, sucs=0):
    """The closing of `left <= Suc^sucs right`, or None when unprovable.

    Both sides are normal forms (`_spine` plus a sum of atoms).  The right
    side's atoms are walked from the left: an atom the left side does not
    start with is surplus and gets added to both sides, one the left side
    does start with is consumed from both, and when the left side is down
    to a single atom equal to the next one the surplus right tail is
    absorbed by `le_add` in one step.
    """
    if sucs > 0:
        sub = _prove_le(left, right, sucs - 1)
        if sub is None:
            return None
        return Closing('cut', 'le_suc_right',
                       _le_prop(left, _sucs(right, sucs - 1)), sub)
    if left == Const('zero', NatType):
        return Closing('rule', 'lesseq_zero')
    if left == right:
        return Closing('rule', 'lesseq_refl')
    latoms, ratoms = _atoms(left), _atoms(right)
    if len(ratoms) < 2:
        # The right side is a single atom: nothing left to absorb, and
        # the two sides are not equal, so this comparison is not provable.
        return None
    head, rest = ratoms[0], _sum(ratoms[1:])
    if latoms[0] != head:
        sub = _prove_le(left, rest)
        if sub is None:
            return None
        return Closing('cut', 'le_add_left_mono', _le_prop(left, rest), sub)
    if len(latoms) == 1:
        return Closing('rule', 'le_add')
    ltail = _sum(latoms[1:])
    sub = _prove_le(ltail, rest)
    if sub is None:
        return None
    return Closing('cut', 'le_add_front', _le_prop(ltail, rest), sub)


def _le_prop(left, right):
    """`left <= right`, printed for a `cut`."""
    from core import fungen
    return '%s <= %s' % (fungen._prints(left), fungen._prints(right))


def _comparison(kind, left, right, dmap, sizes, mdefs):
    """(steps, closing) proving `left < right` or `left <= right`, or None.

    The steps are what the goal needs after its beta reduction; the
    closing finishes what is left of it.
    """
    goal = Const(kind, TFun(NatType, NatType, BoolType))(left, right)
    norm, steps = reduce(goal, dmap, sizes, mdefs)
    args = norm.strip_comb()[1]
    k1, lsum = _spine(args[0])
    k2, rsum = _spine(args[1])
    if kind == 'less':
        # One strict comparison: exactly one `Suc` more on the right
        # makes it strict, and `less_Suc_lesseq` turns that into the weak
        # comparison the rest of the walk is about.
        if k2 <= k1:
            return None
        steps = steps + ['less_Suc_lesseq']
        k2 -= 1
    if k1 > k2:
        return None
    steps = steps + ['le_suc'] * k1
    closing = _prove_le(lsum, rsum, k2 - k1)
    if closing is None:
        return None
    return steps, closing


def measure_text(measure, p):
    """The measure the way the relation writes it.

    A named measure is written as its constant -- there the application
    the rules state is a plain constant application, which the matcher
    can compare with a fact.  An unnamed one is written as a lambda, which
    is only usable where the goal keeps the redex (a test of the
    inference, not the emitter's output).
    """
    from core import fungen
    if measure.def_name is not None:
        return measure.def_name
    Tup = fungen._printt(p.get_type())
    return '(%%%s::%s. %s)' % (p.name, Tup, fungen._prints(measure.body(p)))


def _app_text(measure, p, tup):
    """The measure applied to one tuple, as the rule states it."""
    from core import fungen
    return '(%s) (%s)' % (measure_text(measure, p), fungen._prints(tup))


def cell(measure, call, lhs, dmap, sizes=None, mdefs=None):
    """The cell of one call at one measure, or None when unusable.

    `call` and `lhs` are the tupled arguments of the recursive call and of
    the equation's left hand side.  The measure is applied to them the way
    the relation applies it -- as a lambda application, unreduced -- since
    that is the proposition `mlex_less` / `mlex_leq` states as their
    premise.
    """
    p = Var('p', call.get_type())
    left0, right0 = measure.applied(call), measure.applied(lhs)
    for kind, sym in (('less', '<'), ('lesseq', '<=')):
        res = _comparison(kind, left0, right0, dmap, sizes,
                          dict(mdefs or {}, **measure.tables()))
        if res is None:
            continue
        steps, closing = res
        prop = '%s %s %s' % (_app_text(measure, p, call), sym,
                             _app_text(measure, p, lhs))
        return Cell(prop, 'lt' if kind == 'less' else 'le',
                    not measure.is_named(), steps, closing)
    return None


# ---------------------------------------------------------------------------
# The search.
# ---------------------------------------------------------------------------

def infer(measures, calls, dmap, sizes=None, mdefs=None):
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
    return _search(measures, list(calls), dmap, sizes or {}, mdefs or {})


def _search(measures, calls, dmap, sizes, mdefs):
    if not calls:
        return []
    for measure in measures:
        cells = [cell(measure, call, lhs, dmap, sizes, mdefs)
                 for call, lhs in calls]
        if any(c is None for c in cells):
            continue
        if not any(c.kind == 'lt' for c in cells):
            continue
        rest = [c for c, cl in zip(calls, cells) if cl.kind == 'le']
        sub = _search([m for m in measures if m is not measure], rest, dmap,
                      sizes, mdefs)
        if sub is not None:
            return [measure] + sub
    return None


def row(order, call, lhs, dmap, sizes=None, mdefs=None):
    """The columns one call walks, up to and including the strict one.

    A call is discharged at the first column where it strictly decreases
    (`mlex_less` needs nothing else), so the columns after it are not part
    of its proof.  Every call of an order `infer` accepted has one.
    """
    res = []
    for measure in order:
        c = cell(measure, call, lhs, dmap, sizes, mdefs)
        if c is None:
            return None
        res.append((measure, c))
        if c.kind == 'lt':
            return res
    return None

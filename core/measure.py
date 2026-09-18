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
atoms whose order is canonical:

    Suc^k (a_1 + (a_2 + ... + a_n))

where an atom is anything the rules cannot take apart (a variable, a
`size` of a variable, a destructor application, a product of such, a
subtraction that is not `0`), and the atoms are sorted by the kernel's
term order.  Sorting is what makes the normal form canonical: `size a +
size b` and `size b + size a` are the same term, so the comparison below
sees one form rather than two.  Two sides are compared
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
from kernel import term_ord

# The arithmetic rules the normalization runs, in one `rewrite` step each.
# They are the polynomial normal form's rules, run as a terminating
# rewrite system rather than through a conversion:
#   * `Suc` and the literals: `1 + x` and `x + 1` are `Suc`, a `Suc`
#     summand moves out of the sum, sums right-associate, and a numeral
#     (`of_nat (bit0 1)` is how `2` is written) comes apart into that
#     same spine, so ground arithmetic folds;
#   * the AC order: a sum's atoms are sorted by swapping an inverted
#     adjacent pair, which is a bubble sort -- one `add_left_comm` per
#     swap, and `add_comm` where the two are both atoms;
#   * products: a sum factor distributes, a literal factor turns into a
#     sum (`Suc m * n`, `x * Suc y`), factors right-associate and sort
#     the way sum atoms do.  A product of atoms nothing takes apart
#     stays an atom, and the comparison then treats it as one;
#   * subtraction: `n - 0` is `n`, `n - Suc m` is `Pre (n - m)`, `Pre`
#     takes a matching `Suc` off both ends, and the two that cannot be
#     taken apart -- `0 - n`, `n - n` -- are `0`.  What is left is a
#     `Pre`-headed or variable-headed subtraction, an atom like any
#     other: this normalizes subtraction, it does not compare it.
#
# The order *is* the priority order: when several rules match one node,
# the first one here names the step.  It is the order the rules have to
# be tried in to reach the normal form (a `Suc` summand comes out before
# the sum is reassociated, a sum factor distributes before the product
# is reassociated), not an arbitrary list.
ARITH = ['add_1_left', 'add_1_right', 'add_Suc_left', 'add_Suc_right',
         'add_assoc', 'add_left_comm', 'add_comm',
         'nat_of_nat_def', 'nat_one_def', 'bit0_def', 'bit1_def',
         'nat_times_def_1', 'mult_0_right', 'mult_1_left', 'mult_1_right',
         'nat_times_def_2', 'mult_Suc_right', 'distrib_r', 'distrib_l',
         'mult_assoc', 'mult_left_comm', 'mult_comm',
         'nat_minus_l0', 'nat_minus_def_1', 'nat_minus_def_2',
         'nat_minus_refl', 'nat_minus_presuc']

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


def _times(a, b):
    return Const('times', TFun(NatType, NatType, NatType))(a, b)


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
    the datatype's generated size function, and `'given'` is a measure the
    user wrote.  A position whose type has neither -- a function type, a
    type variable, a datatype without a size family -- contributes no
    column at all.

    A given measure carries the term itself (`given`); everything else
    about it is the same, so a measure the user wrote and one the search
    picked are the same object from here on.
    """

    def __init__(self, pos, arg_types, kind, size_name=None, def_name=None,
                 given=None):
        self.pos = pos
        self.arg_types = arg_types
        self.kind = kind
        self.size_name = size_name
        self.given = given
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
        if self.given is not None:
            # A lambda's body directly, so that the emitted definition
            # `m p = <body>` substitutes the tuple into it in one rewrite,
            # and so that the comparison sees the very term the goal gets
            # rather than a beta-reduced variant of it.
            return (self.given.subst_bound(p) if self.given.is_abs()
                    else self.given(p))
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
        """The measure's own reduction rule: name -> body, for `_rewrite`.

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


def _is_times(t):
    h, args = t.strip_comb()
    return h.is_const() and h.name == 'times' and len(args) == 2


def _minus(a, b):
    return Const('minus', TFun(NatType, NatType, NatType))(a, b)


def _is_minus(t):
    h, args = t.strip_comb()
    return h.is_const() and h.name == 'minus' and len(args) == 2


def _pre(t):
    return Const('Pre', TFun(NatType, NatType))(t)


def _atom_gt(a, b):
    """Whether atom `a` sorts after `b` -- the AC order.

    The comparison is the kernel's term order, so it is total and does
    not depend on the goal: a swap always moves a strictly smaller atom
    left, which is what makes the sorting rewrites terminate.
    """
    return term_ord.fast_compare(a, b) > 0


# The rules a step has to be emitted *positionally* (`loc=`), one rewrite
# per step.  They are the commutativity laws: a step named for a rule
# applies that rule at every node of the goal that matches its left side
# (`top_sweep_conv`), and `x + y = y + x` matches *every* sum, so a
# global step would scramble all of them rather than swap the one pair
# the engine planned.  Everything else is directed -- its left side only
# matches where the rewrite is wanted, and applying it everywhere is what
# one step should do.
POSITIONAL = {'add_comm', 'add_left_comm', 'mult_comm', 'mult_left_comm'}

# The rules that take a literal apart, so that a numeral is never an
# atom: `2` is written `of_nat (bit0 1)`, and these turn it into
# `Suc (Suc 0)`, where the `Suc` rules take over.  Two things follow from
# it, both of them the point of the rules: ground arithmetic folds (`2 +
# 3` is one spine), and a literal coefficient distributes (`2 * n` is
# `n + n`, through `mult_Suc_right`), so a multiplicative measure is
# compared additively.
NUMERAL = {'of_nat': 'nat_of_nat_def', 'one': 'nat_one_def',
           'bit0': 'bit0_def', 'bit1': 'bit1_def'}


def _numeral_rewrite(t, name):
    """The replacement for the numeral constant `name` at t, or None.

    None for a constant of this name at *another* type: the rules are
    nat's own (`nat_of_nat_def` is what `of_nat` is at nat, and `one` is
    an overloaded constant), so the type has to be checked before the
    rule is named.
    """
    if t.get_type() != NatType:
        return None
    if name == 'one':
        return _suc(Const('zero', NatType))
    args = t.strip_comb()[1]
    if len(args) != 1:
        return None
    if name == 'of_nat':
        return args[0] if args[0].get_type() == NatType else None
    if name == 'bit0':
        return _plus(args[0], args[0])
    if name == 'bit1':
        return _plus(_plus(args[0], args[0]), Const('one', NatType))
    return None


def _plus_rewrite(rule, x, y):
    """The replacement of `x + y` under one sum rule, or None."""
    one = Const('one', NatType)
    if rule == 'add_1_left':
        return _suc(y) if x == one else None
    if rule == 'add_1_right':
        return _suc(x) if y == one else None
    if rule == 'add_Suc_left':
        return _suc(_plus(x.arg, y)) if _is_suc(x) else None
    if rule == 'add_Suc_right':
        return _suc(_plus(x, y.arg)) if _is_suc(y) else None
    if rule == 'add_assoc':
        if _is_plus(x):
            x1, x2 = x.strip_comb()[1]
            return _plus(x1, _plus(x2, y))
        return None
    if rule == 'add_left_comm':
        if _is_plus(y):
            head, rest = y.strip_comb()[1]
            return _plus(head, _plus(x, rest))
        return None
    if rule == 'add_comm':
        return _plus(y, x)
    return None


def _times_rewrite(rule, x, y):
    """The replacement of `x * y` under one product rule, or None."""
    zero, one = Const('zero', NatType), Const('one', NatType)
    if rule == 'nat_times_def_1':
        return zero if x == zero else None
    if rule == 'mult_0_right':
        return zero if y == zero else None
    if rule == 'mult_1_left':
        return y if x == one else None
    if rule == 'mult_1_right':
        return x if y == one else None
    if rule == 'nat_times_def_2':
        return _plus(y, _times(x.arg, y)) if _is_suc(x) else None
    if rule == 'mult_Suc_right':
        return _plus(x, _times(x, y.arg)) if _is_suc(y) else None
    if rule == 'distrib_r':
        if _is_plus(x):
            x1, x2 = x.strip_comb()[1]
            return _plus(_times(x1, y), _times(x2, y))
        return None
    if rule == 'distrib_l':
        if _is_plus(y):
            y1, y2 = y.strip_comb()[1]
            return _plus(_times(x, y1), _times(x, y2))
        return None
    if rule == 'mult_assoc':
        if _is_times(x):
            x1, x2 = x.strip_comb()[1]
            return _times(x1, _times(x2, y))
        return None
    if rule == 'mult_left_comm':
        if _is_times(y):
            head, rest = y.strip_comb()[1]
            return _times(head, _times(x, rest))
        return None
    if rule == 'mult_comm':
        return _times(y, x)
    return None


def _minus_rewrite(rule, x, y):
    """The replacement of `x - y` under one subtraction rule, or None.

    Subtraction is defined by recursion on its *second* argument, so the
    rules peel a `Suc` off it (`n - Suc m` is `Pre (n - m)`, and `Pre` is
    nat's own destructor) and take the two matching ends off when the
    first argument runs out.  A literal is peeled the same way, once the
    numeral rules have made it a spine.
    """
    zero = Const('zero', NatType)
    if rule == 'nat_minus_l0':
        return zero if x == zero else None
    if rule == 'nat_minus_def_1':
        return x if y == zero else None
    if rule == 'nat_minus_def_2':
        return _pre(_minus(x, y.arg)) if _is_suc(y) else None
    if rule == 'nat_minus_refl':
        return zero if x == y else None
    return None


def _swap_redex(t, rule):
    """Whether the positional swap `rule` should be emitted at t.

    A commutativity rule's left side matches any term of its shape, so
    the direction cannot come from the rule: the swap is taken exactly
    when it moves a *smaller* atom leftward.  That is one pass of a
    bubble sort over the flattened sum (product), which is what makes
    the sorting terminate and end in the canonical order.
    """
    x, y = t.strip_comb()[1]
    if rule in ('add_left_comm', 'mult_left_comm'):
        head, _ = y.strip_comb()[1]
        return _atom_gt(x, head)
    return _atom_gt(x, y)


def _rewrite(t, rule, dmap, sizes, mdefs):
    """The term after rewriting t at its root with `rule`, or None.

    One function per theorem's left side: this is what decides whether
    the theorem matches here, which is *not* the same as the priority
    order below -- the order only names the step, while a step applies
    its rule wherever that rule matches (and a positional one where the
    engine says).
    """
    h, args = t.strip_comb()
    name = h.name
    if len(args) == 1 and name in mdefs and rule == '%s_def' % name:
        return mdefs[name](args[0])
    if len(args) == 1 and name in dmap:
        cname, j, r = dmap[name]
        inner, iargs = args[0].strip_comb()
        if r == rule and inner.is_const() and inner.name == cname \
                and len(iargs) > j:
            return iargs[j]
    if len(args) == 1 and name in sizes:
        inner, iargs = args[0].strip_comb()
        if inner.is_const() and inner.name in sizes[name]:
            r, positions = sizes[name][inner.name]
            if r == rule:
                return _size_body(name, args[0].get_type(), iargs, positions)
    if NUMERAL.get(name) == rule:
        return _numeral_rewrite(t, name)
    if rule in _PLUS_RULES and len(args) == 2 and _is_plus(t):
        return _plus_rewrite(rule, args[0], args[1])
    if rule in _TIMES_RULES and len(args) == 2 and _is_times(t):
        return _times_rewrite(rule, args[0], args[1])
    if rule in _MINUS_RULES and len(args) == 2 and _is_minus(t):
        return _minus_rewrite(rule, args[0], args[1])
    if rule == 'nat_minus_presuc' and name == 'Pre' and len(args) == 1 \
            and _is_minus(args[0]):
        a, b = args[0].strip_comb()[1]
        if _is_suc(a):
            return _minus(a.arg, b)
    return None


_PLUS_RULES = frozenset(['add_1_left', 'add_1_right', 'add_Suc_left',
                         'add_Suc_right', 'add_assoc', 'add_left_comm',
                         'add_comm'])
_TIMES_RULES = frozenset(['nat_times_def_1', 'mult_0_right', 'mult_1_left',
                          'mult_1_right', 'nat_times_def_2', 'mult_Suc_right',
                          'distrib_r', 'distrib_l', 'mult_assoc',
                          'mult_left_comm', 'mult_comm'])
_MINUS_RULES = frozenset(['nat_minus_l0', 'nat_minus_def_1',
                          'nat_minus_def_2', 'nat_minus_refl'])


def _rules(dmap, sizes, mdefs):
    """The rule names in priority order: the definition's own rules (the
    measures, the destructors, the size functions) first, then `ARITH`,
    whose order is this order."""
    res = ['%s_def' % n for n in mdefs]
    res += [r for _, _, r in dmap.values()]
    res += [r for table in sizes.values() for r, _ in table.values()]
    return res + list(ARITH)


def _rule_at(x, rules, dmap, sizes, mdefs):
    """The rule that fires at this node, or None."""
    for rule in rules:
        if _rewrite(x, rule, dmap, sizes, mdefs) is not None:
            if rule in POSITIONAL and not _swap_redex(x, rule):
                continue
            return rule
    return None


def _next_redex(t, dmap, sizes, mdefs):
    """(rule, path) for the rewrite the next step performs.

    The step is the first node of the top-down sweep where a rule fires,
    and `path` is how to reach that node from the root -- `loc_conv`'s
    0/1 digits.  A node under a binder has no path `loc` can name, so a
    swap there is not taken; the comparison that needed it is then
    reported as unprovable, which is the honest answer rather than a
    step the replay would refuse.
    """
    rules = _rules(dmap, sizes, mdefs)

    def rec(x, path, binder):
        rule = _rule_at(x, rules, dmap, sizes, mdefs)
        if rule is not None and not (rule in POSITIONAL and binder):
            return rule, path
        if x.is_comb():
            return rec(x.fun, path + ('0',), binder) \
                or rec(x.arg, path + ('1',), binder)
        if x.is_abs():
            return rec(x.body, path, True)
        return None

    return rec(t, (), False) or (None, None)


def _apply_global(t, rule, dmap, sizes, mdefs):
    """The term after one global `rewrite <rule>` step: the rule at every
    top-most node where it matches, and nowhere else."""
    def rec(x):
        y = _rewrite(x, rule, dmap, sizes, mdefs)
        if y is not None:
            return y
        if x.is_comb():
            f, a = rec(x.fun), rec(x.arg)
            return x if (f is x.fun and a is x.arg) else f(a)
        if x.is_abs():
            body = rec(x.body)
            return x if body is x.body else Abs(x.var_name, x.var_T, body)
        return x

    return rec(t)


def _apply_at(t, path, rule, dmap, sizes, mdefs):
    """The term after rewriting the single node at `path`."""
    if not path:
        y = _rewrite(t, rule, dmap, sizes, mdefs)
        assert y is not None, \
            'measure: the planned positional rewrite does not apply'
        return y
    if path[0] == '0':
        return _apply_at(t.fun, path[1:], rule, dmap, sizes, mdefs)(t.arg)
    return t.fun(_apply_at(t.arg, path[1:], rule, dmap, sizes, mdefs))


def _step_text(rule, path):
    """The step's text: the rule, and where it is for a positional one."""
    if rule in POSITIONAL:
        assert path, 'measure: a swap at the root of the goal'
        return '%s loc=%s' % (rule, '.'.join(path))
    return rule


def _known_rules(dmap, sizes, mdefs):
    """Every rule name the normalization is allowed to emit.

    The arithmetic rules are the declared list, and the rest come from
    the definition at hand: the measure's own equation, the datatype's
    destructors, and its size functions.  `reduce` checks each step
    against this set, because a rule the emitter writes but the file
    cannot see is a broken item rather than a failed expansion.
    """
    res = set(ARITH)
    for _, _, rule in dmap.values():
        res.add(rule)
    for table in sizes.values():
        for rule, _ in table.values():
            res.add(rule)
    res.update('%s_def' % name for name in mdefs)
    return res


def reduce(t, dmap, sizes=None, mdefs=None):
    """(normal form of t, the steps one `rewrite` each runs through).

    A step is the text of a `rewrite` step in the emitted proof: the
    rule's name, plus the position when the rule has to be applied in
    one place only.  The caller writes it out as it stands -- the
    sequence is the term's own normalization, modelled step for step, so
    the replay does exactly what this loop did.
    """
    sizes, mdefs = sizes or {}, mdefs or {}
    known = _known_rules(dmap, sizes, mdefs)
    steps = []
    while True:
        rule, path = _next_redex(t, dmap, sizes, mdefs)
        if rule is None:
            return t, steps
        assert rule in known, (
            'measure.reduce: the normalization fired %s, which is not a '
            'rule the emitter declares (add it to ARITH if it is an '
            'arithmetic rule)' % rule)
        steps.append(_step_text(rule, path))
        if rule in POSITIONAL:
            t = _apply_at(t, path, rule, dmap, sizes, mdefs)
        else:
            t = _apply_global(t, rule, dmap, sizes, mdefs)


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


def _prove_le(left, right, sucs=0, props=True):
    """The closing of `left <= Suc^sucs right`, or None when unprovable.

    Both sides are normal forms (`_spine` plus a sum of atoms).  The right
    side's atoms are walked from the left: an atom the left side does not
    start with is surplus and gets added to both sides, one the left side
    does start with is consumed from both, and when the left side is down
    to a single atom equal to the next one the surplus right tail is
    absorbed by `le_add` in one step.

    `props` says whether a `cut` node carries its sub-comparison as text.
    A caller that applies the tree backwards (`rule` per node, which makes
    the sub-comparison a subgoal) never writes it out, and computing it
    means *printing* terms, which needs their constants registered in the
    theory.  A datatype's size function is not registered while its own
    family is still being generated, so that caller passes props=False.
    """
    if sucs > 0:
        sub = _prove_le(left, right, sucs - 1, props)
        if sub is None:
            return None
        prop = _le_prop(left, _sucs(right, sucs - 1)) if props else None
        return Closing('cut', 'le_suc_right', prop, sub)
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
        sub = _prove_le(left, rest, 0, props)
        if sub is None:
            return None
        prop = _le_prop(left, rest) if props else None
        return Closing('cut', 'le_add_left_mono', prop, sub)
    if len(latoms) == 1:
        return Closing('rule', 'le_add')
    ltail = _sum(latoms[1:])
    sub = _prove_le(ltail, rest, 0, props)
    if sub is None:
        return None
    prop = _le_prop(ltail, rest) if props else None
    return Closing('cut', 'le_add_front', prop, sub)


def _le_prop(left, right):
    """`left <= right`, printed for a `cut`."""
    from core import fungen
    return '%s <= %s' % (fungen._prints(left), fungen._prints(right))


def _comparison(kind, left, right, dmap, sizes, mdefs, props=True):
    """(steps, closing) proving `left < right` or `left <= right`, or None.

    The steps are what the goal needs after its beta reduction; the
    closing finishes what is left of it.  `props` is passed on to
    `_prove_le`; a caller that applies the closing backwards has no use
    for the `cut` nodes' text and passes False to avoid printing terms
    whose constants are not registered yet.
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
    closing = _prove_le(lsum, rsum, k2 - k1, props)
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

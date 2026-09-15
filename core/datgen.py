"""Datatype layer: the recursion relation and its well-foundedness.

A structural `fun` recursion needs a well-founded relation on the datatype
it descends through.  For a datatype `T` with constructors `C i (x_1 ..
x_k)` this module generates, from the constructor list alone,

    theorem  T_wf_subterm
      prop   wf (%a::T. %b::T. <disjunction over the (i, j) with T at j>)

one disjunct per (constructor, recursive argument position) pair.  A
disjunct says `b` is a `C i` whose j-th argument is `a`:

    ?x_1 .. ?x_{j-1} ?x_{j+1} .. ?x_k. b = C i (...)   with a at position j

The witness components pinned by the equation are eliminated: the j-th
component *is* `a`, so it is not quantified, and a constructor whose only
argument is the recursive one gives a disjunct with no quantifier at all.
That reproduces the two hand-written lemmas this module generalises --
`nat`'s `b = Suc a` (Suc's one argument is the recursive one) and
`list`'s `?z. b = z # a` (cons's other argument stays as the witness).
They were proved from `<ty>_induct` the same way, so the scheme covers
any datatype that has one; driving it from the constructor list is what
lets the `fun` generator drop its per-datatype table.

Two shapes are forced by the method layer, and they are the reason the
emitted text looks the way it does:

* `|` parses right associative (`syntax/parser.py`: `disj: conj ("|")
  disj`), so the disjunction is built right nested; the printed text then
  re-parses to the very term it was printed from (checked below, and the
  item is dropped rather than emitted when it does not hold).  `disjE`
  takes off the *leftmost* disjunct, so the branches are discharged left
  to right.
* `elim` matches the exists rule through a lambda and does not see
  through a nested exists, and `strip_exists` wants one name per bound
  variable.  A disjunct therefore binds exactly the free positions, and
  the names handed to `elim` are the ones allocated here.

Every name the proof introduces is allocated fresh and used once in the
whole proof (`_Names`).  This is not cosmetic: `StableProofState` dedups
items by `Thm` identity, and a variable line's `Thm` is
`Thm.mk_VAR(name, T)` with no hypotheses (`kernel/proofterm.py`), so a
name introduced a second time silently reuses the first stable ID and
every later ID shifts by one.  With names used once, the number of items
a step creates is a function of the template alone -- which is what lets
the emitter write literal `goal=`/`facts=` IDs, computed rather than
tried out.

The items are generated at load time from the `type.ind` block, in
`core/basic.py`, next to the `fun` expansion hook.  A file that states
`<ty>_wf_subterm` itself keeps its own: the theorem is a proof, not an
axiom, so it cannot go through `datatype_axioms`' `mk_axiom` channel, and
the statement a file wrote is the one the rest of that file was verified
against.  Such a file gets nothing generated for that datatype.
"""

import os

from kernel.term import Var, Const, Eq, Lambda
from kernel.type import TConst, TFun, TVar, BoolType
from kernel import theory
from syntax.logicops import Or, Exists
from syntax.settings import global_setting
from syntax import printer

from core import fungen


def constr_args(constr):
    """(argument types, argument names) of a constructor.

    The names are empty when the constructor comes from the theory's
    registry rather than from a datatype block: they are only needed to
    name the proof's variables, which the generated lemma does from the
    block.
    """
    argT, _ = constr['type'].strip_type()
    return list(argT), list(constr.get('args', []))


def subterm_pairs(T, constrs):
    """The (constructor index, argument position) pairs typed `T`."""
    res = []
    for i, constr in enumerate(constrs):
        argT, _ = constr_args(constr)
        for j, T2 in enumerate(argT):
            if T2 == T:
                res.append((i, j))
    return res


def _disjunct(T, constrs, pair):
    """One disjunct, as a term: `?w. b = C i (... a ...)`.

    The constructor's non-recursive arguments travel as *one* witness --
    the tuple of their types, or a single variable when there is only one
    of them -- because `elim` takes exactly one bound variable: an exists
    with two binders reaches the goal as a forall chain (`(EX x. EX y. Q)
    --> C` is read as `ALL x y. Q --> C`), which `elim` cannot take apart.
    With no non-recursive argument there is no witness and no quantifier
    at all, which is exactly the `b = Suc a` shape.
    """
    i, j = pair
    constr = constrs[i]
    argT, _ = constr_args(constr)
    freeT = [argT[t] for t in range(len(argT)) if t != j]
    if freeT:
        w = Var('w', fungen.tupled_type(freeT))
        parts = iter(fungen.projection(w, freeT, k) for k in range(len(freeT)))
    else:
        w, parts = None, iter(())
    args = [Var('a', T) if t == j else next(parts) for t in range(len(argT))]
    body = Eq(Var('b', T), Const(constr['name'], constr['type'])(*args))
    return Exists(w, body) if w is not None else body


def relation_body(T, constrs, pairs):
    """The disjunction over the (constructor, position) pairs, right nested."""
    body = None
    for pair in reversed(pairs):
        d = _disjunct(T, constrs, pair)
        body = d if body is None else Or(d, body)
    return body


def relation_term(T, constrs, pairs):
    """`%a::T. %b::T. <disjunction>`, as a term."""
    T_a = Var('a', T)
    T_b = Var('b', T)
    return Lambda(T_a, Lambda(T_b, relation_body(T, constrs, pairs)))


def relation_text(T, constrs, pairs):
    """The relation as the text an item states it with."""
    with global_setting(unicode=True):
        return printer.print_term(relation_term(T, constrs, pairs))


def _require_roundtrip(T, constrs, pairs):
    """Refuse a relation whose printed form does not come back.

    The item is text, so the statement the proof is about is the printed
    form read back by the parser.  A printer that drops parentheses the
    parser needs (`A | B | C` nesting the other way, say) would leave the
    file proving a different proposition than the one derived here, so the
    two are compared and the item is dropped instead of emitted.
    """
    from core import context
    text = relation_text(T, constrs, pairs)
    try:
        back = context.parse_term(text)
    except Exception as error:
        raise fungen.FunGenError('the relation does not parse back: %s (%s)'
                                 % (text, error))
    if back != relation_term(T, constrs, pairs):
        raise fungen.FunGenError('the relation reads back as %s'
                                 % printer.print_term(back))


class _Names:
    """Names introduced by the proof, each used once.

    See the module docstring: a name introduced twice shares a stable ID
    with its first occurrence and the step creates one item less, so
    allocation here is what keeps the emitted IDs computable.
    """

    def __init__(self):
        self.used = set(['a', 'b'])

    def alloc(self, base):
        nm = base
        k = 1
        while nm in self.used:
            nm = '%s_%d' % (base, k)
            k += 1
        self.used.add(nm)
        return nm


class _Proof:
    """Emit a proof block, tracking the stable-ID counter.

    Each step is told how many items it creates -- decided below from the
    template, never by running anything -- and its IDs are written out as
    literal `goal=`/`facts=` numbers.
    """

    def __init__(self):
        self.lines = []
        self.n = 1

    def step(self, text, new=1):
        """Append a step; return the ID it created, or None if it closed."""
        self.lines.append('  ' + text)
        if not new:
            return None
        i = self.n
        self.n += new
        return i

    def ids(self, text, new):
        """Append a step creating `new` items; return all their IDs."""
        self.lines.append('  ' + text)
        res = list(range(self.n, self.n + new))
        self.n += new
        return res

    def text(self):
        return self.lines


def _conjunct_steps(k, n):
    """Forward lemmas selecting conjunct `k` of `n` conjuncts."""
    if n == 1:
        return []
    if k == 0:
        return ['conjD1']
    if k == n - 1:
        return ['conjD2'] * k
    return ['conjD2'] * k + ['conjD1']


def _neq_name(name, constrs, i, k):
    """The distinctness axiom for `C i` vs `C k`.

    `datatype_axioms` names it after the constructor that comes first in
    the declaration, so the fact at hand (`C k ... = C i ...`) matches it
    directly when `k < i` and has to be flipped when `k > i`.
    """
    lo, hi = (i, k) if i < k else (k, i)
    return '%s_%s_%s_neq' % (name, constrs[lo]['name'], constrs[hi]['name'])


def _case(prover, namer, name, T, constrs, k, pair, fact, g):
    """Discharge one disjunct.

    `fact` is the disjunct (the hypothesis of the current subgoal), `g`
    its goal.  A witness is taken apart first; the disjunct then reads
    `C k (...) = C i (...)`, which is either refuted by distinctness or
    reduced by injectivity.
    """
    i, j = pair
    Ci = constrs[i]
    argT, _ = constr_args(Ci)
    freeT = [argT[t] for t in range(len(argT)) if t != j]
    free = [t for t in range(len(argT)) if t != j]
    if freeT:
        w = namer.alloc('w')
        ids = prover.ids('\u2192 elim "%s" goal=%d facts=[%d]' % (w, g, fact), 3)
        eq, g = ids[1], ids[2]
    else:
        eq = fact

    if i != k:
        if k > i:
            # The axiom is stated for the pair in declaration order, which
            # is the reverse of the fact's sides here.
            eq = prover.step('\u2192 rewrite target=fact eq_sym_eq sym=false '
                             'goal=%d facts=[%d]' % (g, eq))
        prover.step('\u2190 resolve %s goal=%d facts=[%d]'
                    % (_neq_name(name, constrs, i, k), g, eq))
        return

    # Same constructor: injectivity turns the constructor equation into the
    # argument equations; the j-th of them is the pattern's recursive
    # argument equalling the relation's first component.
    cj = prover.step('\u2192 forward %s_%s_inject goal=%d facts=[%d]'
                     % (name, Ci['name'], g, eq))
    for lemma in _conjunct_steps(j, len(argT)):
        cj = prover.step('\u2192 forward %s goal=%d facts=[%d]' % (lemma, g, cj))
    flipped = prover.step('\u2192 rewrite target=fact eq_sym_eq sym=false '
                          'goal=%d facts=[%d]' % (g, cj))
    # Rewriting the goal with `y = w_j` turns it into the induction
    # hypothesis of the recursive argument, which is one of this subgoal's
    # assumptions: the step closes the subgoal and creates no item.  A goal
    # rewrite with a fact has no symmetric form to pass
    # (`rewrite_with_prev_impl` has no `sym` signature), hence the flip.
    prover.step('\u2190 rewrite goal=%d facts=[%d]' % (g, flipped), new=0)


def _disjuncts(prover, namer, name, T, constrs, pairs, k, hyp, g):
    """Split the relation hypothesis and discharge every disjunct."""
    rest = list(pairs)
    disj = hyp
    while len(rest) > 1:
        first, others = prover.ids('\u2190 rule disjE goal=%d facts=[%d]'
                                   % (g, disj), 2)
        f0, g0 = prover.ids('\u2190 intro goal=%d' % first, 2)
        _case(prover, namer, name, T, constrs, k, rest[0], f0, g0)
        rest.pop(0)
        disj, g = prover.ids('\u2190 intro goal=%d' % others, 2)
    _case(prover, namer, name, T, constrs, k, rest[0], disj, g)


def wf_subterm_lines(name, args, constrs):
    """The `<ty>_wf_subterm` item, generated from the constructors."""
    T = TConst(name, *[TVar(a) for a in args])
    pairs = subterm_pairs(T, constrs)
    _require_roundtrip(T, constrs, pairs)
    prover = _Proof()
    namer = _Names()
    P = namer.alloc('P')
    x = namer.alloc('x')

    # wf_def leaves `!P. (!x. (!y. R y x --> P y) --> P x) --> !x. P x`.
    g = prover.step('\u2190 rewrite wf_def goal=0')
    ids = prover.ids('\u2190 intro %s goal=%d' % (P, g), 3)
    hyp_H, g = ids[1], ids[2]
    g = prover.ids('\u2190 intro %s goal=%d' % (x, g), 2)[1]
    branches = prover.ids('\u2190 rule %s_induct goal=%d' % (name, g),
                          len(constrs))

    for k, constr in enumerate(constrs):
        g = branches[k]
        argT, argnames = constr_args(constr)
        names = [namer.alloc(nm) for nm in argnames]
        recs = [t for t, Ty in enumerate(argT) if Ty == T]
        if names:
            ids = prover.ids('\u2190 intro "%s" goal=%d' % (', '.join(names), g),
                             len(names) + len(recs) + 1)
            g = ids[-1]
        pat = Const(constr['name'], constr['type'])(
            *[Var(nm, Ty) for nm, Ty in zip(names, argT)])
        h = prover.step('\u2192 inst "%s" goal=%d facts=[%d]'
                        % (fungen._arg_text(pat), g, hyp_H))
        g = prover.step('\u2190 apply_prev goal=%d facts=[%d]' % (g, h))
        y = namer.alloc('y')
        hyp, g = prover.ids('\u2190 intro %s goal=%d' % (y, g), 3)[1:]
        _disjuncts(prover, namer, name, T, constrs, pairs, k, hyp, g)

    return ['theorem %s_wf_subterm' % name,
            '  prop wf (%s)' % relation_text(T, constrs, pairs),
            'proof'] + prover.text() + ['qed']


def _parsed_constrs(data):
    """The datatype's constructors, with their types parsed."""
    from syntax import parser
    return [{'name': constr['name'],
             'type': parser.parse_type(constr['type']),
             'args': list(constr['args'])}
            for constr in data['constrs']]


def _wf_in_scope():
    """The lemma is stated with `wf` and proved from these."""
    for th_name in ('wf_def', 'wf_induct', 'disjE', 'eq_sym_eq',
                    'conjD1', 'conjD2'):
        try:
            theory.get_theorem(th_name)
        except Exception:
            return False
    return True


def expand_item(data, content):
    """The items the datatype block expands into, or None.

    None means nothing can be generated here -- no recursion position, the
    machinery not in scope, or the file stating the lemma itself -- and the
    block is left exactly as written.  Set HOLPY_DATGEN_DEBUG to see the
    underlying exception instead of the silent fallback.
    """
    try:
        return _expand(data, content)
    except fungen.FunGenError:
        return None
    except Exception:
        if os.environ.get('HOLPY_DATGEN_DEBUG'):
            raise
        return None


def _expand(data, content):
    name = data['name']
    if any(item.get('name') == '%s_wf_subterm' % name for item in content):
        # The file wrote the lemma itself (nat and list predate this
        # module).  Its statement is the one the rest of the file was
        # verified against, so it wins and nothing is generated.
        return None
    if not _wf_in_scope():
        return None
    constrs = _parsed_constrs(data)
    T = TConst(name, *[TVar(a) for a in data['args']])
    pairs = subterm_pairs(T, constrs)
    if not pairs:
        # No constructor takes the datatype itself: no recursion position,
        # so there is nothing to descend through.
        return None
    return [fungen._entry(wf_subterm_lines(name, data['args'], constrs))]

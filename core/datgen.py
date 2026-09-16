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

    def reserve(self, names):
        """Mark names as taken (they are written into the item verbatim)."""
        self.used.update(names)

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


# ---------------------------------------------------------------------------
# Destructor family.
#
# A `fun` body is built over the tupled argument, so the pattern's variables
# have to be recovered from that tuple: `f (x # xs)` needs `hd p` and
# `tl p`.  Those destructors are what the emitter's projection rules rewrite
# against the literal pattern (`hd_def_1`, `Pre_def_2`), and they are the
# reason a definition over a datatype outside nat and list cannot be
# emitted at all.
#
# For every (constructor, argument) position whose destructor the library
# does not already name, this module generates
#
#   def      T_C_n t = (THE v. <other args as one witness>. t = C (... v ...))
#   theorem  T_C_n_rule  fixes x_1 .. x_k  prop  T_C_n (C x_1 .. x_k) = x_n
#
# The definition is total (no default value is needed for the other
# constructors, unlike a `fun` with one equation per constructor), and the
# rule is `the_equality`: existence is the pattern itself, uniqueness is
# the datatype's injectivity.  `THE` rather than `SOME`: `the_equality`
# states exactly the two obligations, so the rule needs no separate
# uniqueness argument.
# ---------------------------------------------------------------------------

# The destructors the library already has, under its own names -- nat's
# `Pre` (the argument of Suc), list's `hd`/`tl`, prod's `fst`/`snd`.  They
# are API: library proofs cite them, so the generator leaves those
# positions alone and everything else is generated as `T_C_n`.
_LIB_DESTRUCTORS = {
    ('nat', 'Suc', 0): ('Pre', 'Pre_def_2'),
    ('list', 'cons', 0): ('hd', 'hd_def_1'),
    ('list', 'cons', 1): ('tl', 'tl_def_1'),
    ('prod', 'Pair', 0): ('fst', 'fst_def_1'),
    ('prod', 'Pair', 1): ('snd', 'snd_def_1'),
}


def destructor_names(tyname, constr_name, j):
    """(destructor constant, its rule theorem) for argument j."""
    key = (tyname, constr_name, j)
    if key in _LIB_DESTRUCTORS:
        return _LIB_DESTRUCTORS[key]
    return generated_destructor_names(tyname, constr_name, j)


def generated_destructor_names(tyname, constr_name, j):
    """The generated destructor of argument j, whatever the library names.

    Every position has one of these, including the five the library names
    itself (`Pre`, `hd`/`tl`, `fst`/`snd`, `the`).  Those names are API and
    stay what other definitions use, but the definition of that very
    function cannot be written with its own rule -- while `tl` is being
    emitted, `tl_def_1` does not exist yet -- so it is written with the
    generated destructor of the same position, which is defined by THE and
    does not mention the function at all.
    """
    nm = '%s_%s_%d' % (tyname, constr_name, j + 1)
    return nm, '%s_rule' % nm


def _destructor_term(dname, T, Aj, t):
    """`<d> t`, the destructor applied to a term."""
    return Const(dname, TFun(T, Aj))(t)


def _destructor_body(T, constr, j, var, lhs=None, wname='w', witness=None):
    """`<other args as one witness> <lhs> = C (... var ...)`, as a term.

    `lhs` defaults to the def's own variable `t`; the rule passes the
    constructor pattern instead, so that the same construction gives the
    predicate `the_equality` is applied to.  Both binders are named by the
    caller when the body carries the pattern: a constructor argument can
    be called `v` or `w` (`varType`'s `Para (v, x)`), and a binder that
    captures it would change the term -- or, when the types differ, make
    the abstraction ill-typed.  `witness` substitutes a term for the
    witness, giving the instance `inst` produces.
    """
    argT, _ = constr_args(constr)
    others = [t for t in range(len(argT)) if t != j]
    if others:
        otherT = [argT[t] for t in others]
        if witness is None:
            w = Var(wname, fungen.tupled_type(otherT))
            parts = iter(fungen.projection(w, otherT, k)
                         for k in range(len(otherT)))
        else:
            w = None
            parts = iter(fungen.projection(witness, otherT, k)
                         for k in range(len(otherT)))
    else:
        w, parts = None, iter(())
    args = [var if t == j else next(parts) for t in range(len(argT))]
    body = Eq(Var('t', T) if lhs is None else lhs,
              Const(constr['name'], constr['type'])(*args))
    return Exists(w, body) if w is not None else body


def _the(ty, body):
    """`THE x :: ty. body` as a term."""
    return Const('The', TFun(TFun(ty, BoolType), ty))(
        Lambda(Var('v', ty), body))


def destructor_lines(T, tyname, constrs, i, j, generated=False):
    """The `<ty>_<C>_<n>` definition, as item lines."""
    constr = constrs[i]
    argT, _ = constr_args(constr)
    Aj = argT[j]
    dname, _ = (generated_destructor_names(tyname, constr['name'], j)
                if generated else destructor_names(tyname, constr['name'], j))
    with global_setting(unicode=True):
        body = printer.print_term(
            _the(Aj, _destructor_body(T, constr, j, Var('v', Aj))))
    return ['def %s :: %s = %s t = %s'
            % (dname, fungen._printt(TFun(T, Aj)), dname, body)]


def destructor_rule_lines(T, tyname, constrs, i, j, generated=False):
    """The `<ty>_<C>_<n>_rule` theorem, generated from the constructors."""
    constr = constrs[i]
    argT, argnames = constr_args(constr)
    dname, rule = (generated_destructor_names(tyname, constr['name'], j)
                   if generated else destructor_names(tyname, constr['name'],
                                                      j))
    vars_ = [Var(nm, Ty) for nm, Ty in zip(argnames, argT)]
    prover = _Proof()
    namer = _Names()
    namer.reserve(argnames)
    pat = Const(constr['name'], constr['type'])(*vars_)
    bv = namer.alloc('v')
    wname = namer.alloc('w')

    g = prover.step('\u2190 unfold %s_def goal=0' % dname)
    # The instantiation is passed explicitly: the axiom's `P (THE x. P x)`
    # pattern is higher order, and matching it against the goal's body
    # needs the abstraction named.
    lam = Lambda(Var(bv, argT[j]),
                 _destructor_body(T, constr, j, Var(bv, argT[j]), lhs=pat,
                                  wname=wname))
    prem = prover.ids('\u2190 rule the_equality param_P="%s" goal=%d'
                      % (fungen._prints(lam), g), 2)

    # Existence: the pattern's own arguments witness the other positions;
    # with no other argument the instance is the pattern itself.  A tuple
    # witness leaves projections behind, which the projection rules reduce
    # (`_reduce_used` gives exactly the rules the instance needs, in
    # order); the last one closes the goal, since the instance is
    # `pattern = pattern`.  That closing step is decided here, from the
    # reduced term -- it is one of the two places the emitted counter
    # depends on the method layer closing on its own.
    others = [t for t in range(len(argT)) if t != j]
    if others:
        witness = fungen.tupled_arg([vars_[t] for t in others])
        g = prover.step('\u2192 inst "%s" goal=%d' % (fungen._arg_text(witness),
                                                      prem[0]))
        instance = _destructor_body(T, constr, j, vars_[j], lhs=pat,
                                    witness=witness)
        reduced, rules = fungen._reduce_used(
            instance, fungen._destructor_map(fungen.tupled_type(
                [argT[t] for t in others])))
        for n, lemma in enumerate(rules):
            if n == len(rules) - 1 and reduced.is_reflexive():
                prover.step('\u2190 rewrite %s goal=%d' % (lemma, g), new=0)
            else:
                g = prover.step('\u2190 rewrite %s goal=%d' % (lemma, g))
        if not rules:
            prover.step('\u2190 rule eq_refl goal=%d' % g, new=0)
    else:
        prover.step('\u2190 rule eq_refl goal=%d' % prem[0], new=0)

    # Uniqueness: an equation between two applications of the same
    # constructor gives the argument equations; the j-th is `x_j = y`.
    # Only a constructor with another argument has an exists to take apart.
    ids = prover.ids('\u2190 intro %s goal=%d' % (namer.alloc('y'), prem[1]), 3)
    hyp, g = ids[1], ids[2]
    if others:
        ids = prover.ids('\u2192 elim "%s" goal=%d facts=[%d]' % (wname, g, hyp), 3)
        eq, g = ids[1], ids[2]
    else:
        eq = hyp
    cj = prover.step('\u2192 forward %s_%s_inject goal=%d facts=[%d]'
                     % (tyname, constr['name'], g, eq))
    for lemma in _conjunct_steps(j, len(argT)):
        cj = prover.step('\u2192 forward %s goal=%d facts=[%d]' % (lemma, g, cj))
    # The j-th argument equation flipped is `y = x_j`, which *is* the
    # uniqueness goal (`v = x_j` with `v` named `y`), so this step closes
    # the subgoal; there is nothing left to discharge afterwards.
    prover.step('\u2192 rewrite target=fact eq_sym_eq sym=false '
                'goal=%d facts=[%d]' % (g, cj), new=1)

    return ['theorem %s' % rule,
            '  fixes %s' % ', '.join('%s :: %s' % (v.name, fungen._printt(v.T))
                                     for v in vars_),
            # The pattern is an application, so it needs parentheses: a
            # bare `d C x y` reads as `((d C) x) y`.
            '  prop %s %s = %s' % (dname, fungen._arg_text(pat), vars_[j].name),
            'proof'] + prover.text() + ['qed']


def _printable_application(constr, vars_):
    """Whether `C x_1 .. x_k` can be written down in this theory.

    A constructor can share its name with another constant of the same
    arity (`state`'s `Pair` against prod's): the printed application is
    then ambiguous, and the printer's type inference refuses it.  Such a
    position gets no destructor -- a definition that needs it keeps
    failing with the honest destructor message -- instead of an item that
    cannot be written.
    """
    try:
        fungen._prints(Const(constr['name'], constr['type'])(*vars_))
    except Exception:
        return False
    return True


def _destructor_items(T, name, constrs):
    """Every destructor the library does not already name.

    A position whose items cannot be built is left out rather than
    failing the whole datatype block: the destructors are independent of
    each other and of the relation, and the definition that needs the
    missing one reports it.  Set HOLPY_DATGEN_DEBUG to see the exception.
    """
    res = []
    for i, constr in enumerate(constrs):
        argT, argnames = constr_args(constr)
        vars_ = [Var(nm, Ty) for nm, Ty in zip(argnames, argT)]
        for j in range(len(argT)):
            # The library's own destructors are API and stay what other
            # definitions use, but their positions get the generated one
            # as well: the definition of that very function is written
            # with it (see `generated_destructor_names`).
            lib = (name, constr['name'], j) in _LIB_DESTRUCTORS
            try:
                res.append(fungen._entry(
                    destructor_lines(T, name, constrs, i, j, generated=lib)))
                res.append(fungen._entry(
                    destructor_rule_lines(T, name, constrs, i, j,
                                          generated=lib)))
            except Exception as error:
                if os.environ.get('HOLPY_DATGEN_DEBUG'):
                    print('datgen: %s %s %d skipped: %s: %s'
                          % (name, constr['name'], j + 1,
                             error.__class__.__name__, error))
                    continue
                continue
    return res


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


def size_fun_lines(name, args, constrs, rec_pos):
    """The `<ty>_size` definition, as `fun` item lines.

    One equation per constructor, in declaration order: 1 for the
    constructor plus the size of its recursive argument.  A source
    definition on purpose -- the equations are then derived from the
    relation's well-foundedness like any other `fun`, instead of being
    asserted, and the destructor family the emitter needs is part of the
    same block.  A constructor with no argument of the datatype's own
    (`Some`, `Pair`) contributes the constant 1.
    """
    T = TConst(name, *[TVar(a) for a in args])
    sz = '%s_size' % name
    lines = ['fun %s :: %s ⇒ nat' % (sz, fungen._printt(T))]
    for constr, pos in zip(constrs, rec_pos):
        argT, argnames = constr_args(constr)
        pat = Const(constr['name'], constr['type'])(
            *[Var(nm, Ty) for nm, Ty in zip(argnames, argT)])
        rhs = '1' if pos is None else '1 + %s %s' % (sz, argnames[pos])
        lines.append('  | %s %s = %s'
                     % (sz, fungen._arg_text(pat) if argnames
                        else fungen._prints(pat), rhs))
    return lines


# The theorems `<ty>_size_less`'s proof cites (see `size_less_lines`).
# A caller that generates the size family at the earliest point it can --
# so the file's own definitions can use it as a measure -- has to wait for
# these to be in scope, which in the file that defines them (nat) is later
# than the datatype and even than the comparison itself.
SIZE_LESS_DEPS = ['add_1_left', 'less_Suc_lesseq', 'lesseq_refl']


def size_less_lines(name, args, recursive, rec_pos, suffix=''):
    """`<ty>_size` strictly decreases from a constructor argument.

    The one fact a size is for: the recursive argument of the pattern is
    smaller than the pattern.  With the generated equation that is
    `size x < 1 + size x`, i.e. `size x < Suc (size x)`, i.e. `size x <=
    size x`.
    """
    T = TConst(name, *[TVar(a) for a in args])
    argT, argnames = constr_args(recursive)
    vars_ = [Var(nm, Ty) for nm, Ty in zip(argnames, argT)]
    pat = Const(recursive['name'], recursive['type'])(*vars_)
    prover = _Proof()
    sz = '%s_size' % name
    g = prover.step('← rewrite %s_def_%d goal=0'
                    % (sz, size_equation_index(recursive)))
    g = prover.step('← rewrite add_1_left goal=%d' % g)
    g = prover.step('← rewrite less_Suc_lesseq goal=%d' % g)
    prover.step('← rule lesseq_refl goal=%d' % g, new=0)
    return ['theorem %s_size_less%s' % (name, suffix),
            '  fixes %s' % ', '.join('%s :: %s' % (v.name, fungen._printt(v.T))
                                     for v in vars_),
            '  prop %s %s < %s %s' % (sz, argnames[rec_pos], sz,
                                      fungen._arg_text(pat)),
            'proof'] + prover.text() + ['qed']


def size_equation_index(constr):
    """The position of a constructor's size equation, counting from one.

    The equations are emitted in declaration order and every constructor
    gets one, so the index is the constructor's own place in that list.
    """
    return constr['index'] + 1


def expand_size(data):
    """The datatype's size family, or None.

    Every datatype whose constructors each take at most one argument of the
    datatype itself gets a size: the equations are derived by the emitter,
    and the one fact a size is for -- a recursive argument is smaller than
    the pattern it came from -- comes with it.  A constructor with two
    recursive arguments is left out on purpose: its equation's obligation
    is one disjunct of the subterm relation, which is exactly the case the
    measure engine is for.
    """
    name = data['name']
    constrs = _parsed_constrs(data)
    if not constrs:
        return None
    T = TConst(name, *[TVar(a) for a in data['args']])
    rec_pos = []
    for k, c in enumerate(constrs):
        c['index'] = k
        argT, _ = constr_args(c)
        positions = [j for j, Ty in enumerate(argT) if Ty == T]
        if len(positions) > 1:
            return None
        rec_pos.append(positions[0] if positions else None)
    item = fungen._entry(size_fun_lines(name, data['args'], constrs, rec_pos))
    derived = fungen.expand_item(item)
    if derived is None:
        return None
    recursive = [(c, p) for c, p in zip(constrs, rec_pos) if p is not None]
    for k, (c, p) in enumerate(recursive):
        suffix = '' if len(recursive) == 1 else '_%d' % (k + 1)
        derived.append(fungen._entry(
            size_less_lines(name, data['args'], c, p, suffix)))
    return derived


def _expand(data, content):
    name = data['name']
    constrs = _parsed_constrs(data)
    T = TConst(name, *[TVar(a) for a in data['args']])
    items = []
    if (_wf_in_scope()
            and not any(item.get('name') == '%s_wf_subterm' % name
                        for item in content)):
        # The file wrote the lemma itself (nat and list predate this
        # module).  Its statement is the one the rest of the file was
        # verified against, so it wins and nothing is generated.
        pairs = subterm_pairs(T, constrs)
        if pairs:
            # No constructor takes the datatype itself: no recursion
            # position, so there is nothing to descend through.
            items.append(fungen._entry(
                wf_subterm_lines(name, data['args'], constrs)))
    # The destructor family does not depend on the relation: a definition
    # that only pattern-matches needs the destructors too.
    items.extend(_destructor_items(T, name, constrs))
    return items or None

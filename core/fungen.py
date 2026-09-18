"""Expansion of a `fun` definition (phase 4).

A `fun` definition is no longer axiomatized: it expands into a group of
ordinary items whose equations are *derived* from well-foundedness.  The
first half of this file is the term-level transformation; the second half
emits the items.

Nothing about the emitted proofs is guessed: each template knows how
many items every one of its steps creates, and the few steps whose goal
closes early (`rule` on a proposition that is its own conclusion,
`if_P` / `if_not_P`, the last projection rewrite of a decrease obligation
that resolves to an identity) are decided in code from the step and the
terms involved.  So the literal IDs written into the item are exactly the
ones the replay assigns, with no step ever replayed to find out.

For `fun f :: T1 => ... => Tn => Tr` with equations over the tupled
argument p : Tup it produces

  * `<c>_H`, the body functional: branches are the equations' right
    hands, every source variable written as a projection of p, every
    recursive call `f a1 .. an` replaced by `g (a1 .. an)`;
  * `<c>_rel`, the recursion relation on the tupled argument -- the
    recursion-position component's well-founded relation, lifted through
    the projection.  It is a lambda, so unfolding it never leaves a beta
    redex in a goal (the rewriter cannot see through one);
  * `<c>_in`, the SOME-fixpoint over `wfrec_H <c>_rel <c>_H`, and the
    curried user-facing constant defined through it.

`<c>` is the *overloaded* name of the constant (`nat_plus` for `plus`),
so generated items cannot collide between instances and the derived
equations carry exactly the names the current axiomatization gives them
(`nat_plus_def_1`), `[hint_rewrite]` included.

Everything outside this increment raises FunGenError instead of being
guessed at; the caller then keeps the old mechanism, so a file never
breaks because of the expansion:

  * at most two arguments, at most two equations;
  * exactly one argument may carry constructor patterns, the nullary
    constructor's equation must come first and must not be recursive;
  * one recursive call per equation;
  * a binder in an equation's right hand is not traversed;
  * the destructors for pattern variables are `Pre` (nat) and `hd`/`tl`
    (list); another datatype needs a well-founded subterm lemma plus its
    constructor-argument destructors.
"""
import os
import re
import itertools

from kernel.type import TFun, TConst, BoolType
from kernel.term import Lambda, Var, Const, Eq, Abs, Implies, Forall
from syntax import printer
from syntax.logicops import Exists, Or, is_exists, Not, is_not
from syntax.settings import global_setting
from core import measure

NatType = TConst('nat')


class FunGenError(Exception):
    """Raised when a definition is outside the current increment."""


# ---------------------------------------------------------------------------
# Transformation layer: type and term shapes over the tupled argument.
# ---------------------------------------------------------------------------

def prod_type(arg_types):
    """Nested product of the given types, matching tupled_arg."""
    if len(arg_types) == 2:
        return TConst('prod', arg_types[0], arg_types[1])
    return TConst('prod', arg_types[0], prod_type(arg_types[1:]))


def tupled_type(arg_types):
    """Type of the tupled argument (single argument of the fixpoint)."""
    if len(arg_types) == 1:
        return arg_types[0]
    return prod_type(arg_types)


def tupled_arg(args):
    """The tuple term for the given argument terms."""
    if len(args) == 1:
        return args[0]
    T = prod_type([a.get_type() for a in args])
    T1, T2 = args[0].get_type(), tupled_type([a.get_type() for a in args[1:]])
    return Const('Pair', TFun(T1, TFun(T2, T)))(args[0], tupled_arg(args[1:]))


def projection(p, arg_types, i):
    """Projection of component i, mirroring tupled_arg's nesting."""
    if len(arg_types) == 1:
        return p
    T1, T2 = arg_types[0], tupled_type(arg_types[1:])
    Tup = prod_type(arg_types)
    if i == 0:
        return Const('fst', TFun(Tup, T1))(p)
    return projection(Const('snd', TFun(Tup, T2))(p), arg_types[1:], i - 1)


def _constr_names(T):
    from kernel import theory
    if not T.is_tconst():
        return None
    constrs = theory.thy.get_datatype_constrs(T.name)
    if constrs is None:
        return None
    return {c.name for c in constrs}


def recursion_positions(arg_types, eq_lhs_args):
    """The arguments carrying constructor patterns, in order.

    A definition may match on more than one argument: `lexnat`'s third
    equation keeps the first and decreases the second, which is what makes
    the descent lexicographic rather than a single measure.  Every
    equation has to carry a constructor pattern at every one of these
    positions: a plain variable there would be a pattern overlapping the
    others', and `_complete_equations` has already subtracted those apart
    by the time the emission sees the set.
    """
    positions = set()
    for args in eq_lhs_args:
        for i, a in enumerate(args):
            h, _ = a.strip_comb()
            if h.is_const():
                constrs = _constr_names(arg_types[i])
                if constrs and h.name in constrs:
                    positions.add(i)
    return tuple(sorted(positions))


def recursion_position(arg_types, eq_lhs_args):
    """Index of the argument carrying constructor patterns, or None."""
    positions = recursion_positions(arg_types, eq_lhs_args)
    if not positions:
        return None
    if len(positions) != 1:
        raise FunGenError(
            "constructor patterns on arguments %s; exactly one argument "
            "may carry them" % ", ".join(str(i + 1) for i in positions))
    return positions[0]


def destructor(constr_name, j, t):
    """The j-th argument of a constructor pattern, as a term in t."""
    T = t.get_type()
    if constr_name == 'Suc' and j == 0:
        return Const('Pre', TFun(NatType, NatType))(t)
    if constr_name == 'cons' and T.is_tconst() and T.name == 'list':
        elem = T.args[0]
        if j == 0:
            return Const('hd', TFun(T, elem))(t)
        if j == 1:
            return Const('tl', TFun(T, T))(t)
    raise FunGenError(
        "no destructor for argument %d of constructor %s; this datatype "
        "needs its constructor-argument destructors first"
        % (j + 1, constr_name))


def _subst(t, env):
    """Replace the variables named in env throughout t.

    Patterns and right hand sides carry no binder that could capture a
    bound name (a right hand side that does is refused by `replace`), so a
    plain traversal is enough here.
    """
    if t.is_comb():
        h, args = t.strip_comb()
        # The head is substituted too: a recursive call's arguments can have
        # a *variable* in head position (`foldl f (f z x) xs`, where `f` is
        # a pattern variable applied), and leaving it behind names a
        # variable the branch has since renamed away.  For the constructor
        # patterns this is a no-op -- their heads are constants.
        return _subst(h, env)(*[_subst(a, env) for a in args])
    if t.is_var() and t.name in env:
        return env[t.name]
    return t


def _pattern_leaves(pat):
    """The variables of a (possibly nested) constructor pattern, in order."""
    h, args = pat.strip_comb()
    if not h.is_const():
        raise FunGenError('the pattern %s is not a constructor pattern'
                          % _prints(pat))
    leaves = []
    for a in args:
        if a.is_var():
            leaves.append(a)
        elif a.is_const() and not a.strip_comb()[1]:
            continue              # a nullary constructor inside the pattern
        else:
            leaves.extend(_pattern_leaves(a))
    return leaves


def _leaf_tuple(leaves):
    """The tuple term over the pattern's variables."""
    return tupled_arg(leaves)


def _bind_pattern(pat, t, env):
    """Bind every variable of a pattern to its destructor path from t.

    Nested patterns are followed down: the variable under `x # y # xs` is
    `tl` applied to the pattern's tail, and a nested constructor's own
    arguments are reached through the destructors of that constructor.
    """
    h, args = pat.strip_comb()
    if not h.is_const():
        raise FunGenError('the pattern %s is not a constructor pattern'
                          % _prints(pat))
    for j, a in enumerate(args):
        sub = destructor(h.name, j, t)
        if a.is_var():
            env[a.name] = sub
        elif a.is_const() and not a.strip_comb()[1]:
            continue
        else:
            _bind_pattern(a, sub, env)


def _pattern_positions(lhs_args, positions):
    """The positions where *this* equation's pattern is a constructor.

    A definition that matches on several arguments need not match on all
    of them in every equation: `lexnat 0 n = n` constrains only the first
    argument.  A plain variable at such a position is the general pattern,
    and the equations after it are refuted at some other position (see
    `_expand`), so its test is simply absent.
    """
    res = []
    for i in positions:
        a = lhs_args[i]
        h, _ = a.strip_comb()
        constrs = _constr_names(a.get_type())
        if h.is_const() and constrs and h.name in constrs:
            res.append(i)
    return res


def _as_positions(positions):
    """The recursion positions as a tuple (a single index is accepted)."""
    return (positions,) if isinstance(positions, int) else tuple(positions)


def _pos_tag(tag, k, npos):
    """The witness tag of position k of the equation numbered `tag`.

    One position keeps the equation's own number, so the emitted text of
    the definitions that match on a single argument does not change; with
    several, the witnesses of one equation have to differ from each other
    (a variable line is keyed by name and type alone).
    """
    return tag if npos == 1 else tag * npos + k


def _cond_of(pat, proj, tag):
    """The test that `proj` matches `pat`.

    A pattern with no variable of its own is an equality.  Otherwise the
    variables are bound by one existential over their tuple, so the test
    is exactly as strong as the pattern and can be discharged (or refuted)
    with a single `elim`.  Refuting it is what needs the positions next to
    it to differ in their constructor (`_condition_negation`), which
    `_complete_equations` has already arranged where it could.

    The witness is named after the equation the pattern belongs to: the
    stable-ID layer keys a variable line by its name and type alone, so
    two `elim`s of the same witness name in one proof would share an ID
    (and the second one would create nothing).
    """
    leaves = _pattern_leaves(pat)
    if not leaves:
        return Eq(proj, pat)
    types = [a.get_type() for a in leaves]
    w = Var('_w%d' % (tag + 1), tupled_type(types))
    env = dict((a.name, projection(w, types, k))
               for k, a in enumerate(leaves))
    return Exists(w, Eq(proj, _subst(pat, env)))


def plain_env(lhs_args, p=None):
    """Term for each source variable, all of them projections."""
    arg_types = [a.get_type() for a in lhs_args]
    if p is None:
        p = Var('p', tupled_type(arg_types))
    env = {}
    for i, a in enumerate(lhs_args):
        if not a.is_var():
            raise FunGenError(
                "argument %s is not a plain variable" %
                printer.print_term(a))
        env[a.name] = projection(p, arg_types, i)
    return env


def variable_env(lhs_args, positions, p=None):
    """Term for each source variable in terms of the tuple term p.

    Plain arguments become projections; the pattern variables at the
    recursion positions become destructor applications, following a nested
    pattern down to its leaves.  Passing the literal tuple of an equation
    gives the body in exactly the shape the goal has after the
    corresponding rewrites.
    """
    positions = _as_positions(positions)
    arg_types = [a.get_type() for a in lhs_args]
    if p is None:
        p = Var('p', tupled_type(arg_types))
    env = {}
    patterned = _pattern_positions(lhs_args, positions)
    for i, a in enumerate(lhs_args):
        if i in patterned:
            continue
        if not a.is_var():
            raise FunGenError(
                "argument %d is not a plain variable; only arguments %s may "
                "carry patterns" % (i + 1,
                                    ", ".join(str(k + 1) for k in positions)))
        env[a.name] = projection(p, arg_types, i)
    for i in patterned:
        _bind_pattern(lhs_args[i], projection(p, arg_types, i), env)
    return env


def replace(t, f_const, n, env, g):
    """Substitute source variables; replace `f a1 .. an` by `g (a1 .. an)`.

    A binder in the right hand is refused.  Substituting under it is easy
    (drop the bound name from the environment), and the sweep of `rewrite`
    does descend into binder bodies (`top_sweep_conv`, core/conv/core.py:
    it stops only where a rule fired), so the reason is *not* the method
    layer.  With the substitution in place the equation proof still ends
    with an open goal, which needs re-diagnosing: the likely cause is the
    same one as the three-argument case -- the emitted projection rewrites
    are computed for the equation's body, while the goal carries the
    destructors under the binder as well.
    """
    if t.is_comb():
        h, args = t.strip_comb()
        if h == f_const and len(args) == n:
            return g(tupled_arg([replace(a, f_const, n, env, g) for a in args]))
        return replace(t.fun, f_const, n, env, g)(
            replace(t.arg, f_const, n, env, g))
    if t.is_abs():
        # A binder is entered: the source variables are substituted under
        # it except the name it binds, which shadows them (`sorted`'s
        # `%y. y Mem set xs --> x <= y` mentions the bound `y` and the
        # pattern's `xs`).  The substituted terms are projections and
        # destructors over the tuple variable, so they cannot be captured.
        inner = dict((k, v) for k, v in env.items() if k != t.var_name)
        return Abs(t.var_name, t.var_T,
                   replace(t.body, f_const, n, inner, g))
    if t.is_var() and t.name in env:
        return env[t.name]
    return t


def branch_condition(lhs_args, positions, p, tag):
    """Condition testing the recursion arguments against the pattern.

    A nullary constructor is tested by equality; a constructor with
    arguments by an existential over its pattern variables, since those
    are not in scope in the condition.  With more than one position the
    tests are combined into a conjunction -- the branch is taken when the
    tuple matches the equation's pattern in every position at once -- and
    with one it is left bare, so the emitted text of the definitions that
    match on a single argument does not change.
    """
    arg_types = [a.get_type() for a in lhs_args]
    positions = _pattern_positions(lhs_args, _as_positions(positions))
    tests = [_cond_of(lhs_args[i], projection(p, arg_types, i),
                      _pos_tag(tag, k, len(positions)))
             for k, i in enumerate(positions)]
    if len(tests) == 1:
        return tests[0]
    res = tests[0]
    for t in tests[1:]:
        res = Const('conj', TFun(BoolType, TFun(BoolType, BoolType)))(res)(t)
    return res


# --- symbolic computation of the projection/destructor rewrites -------------

def _reduce_step(t, dmap):
    """One destructor/projection reduction on a literal constructor.

    `dmap` is `_destructor_maps`'s map from a destructor constant to the
    constructor and position it takes apart, so this works for every
    datatype that has destructors -- not just the three whose names the
    library fixed by hand.
    """
    if not t.is_comb():
        return t
    h, args = t.strip_comb()
    if not (h.is_const() and len(args) == 1 and h.name in dmap):
        return t
    inner, iargs = args[0].strip_comb()
    if not inner.is_const():
        return t
    cname, j, _ = dmap[h.name]
    if inner.name == cname and len(iargs) > j:
        return iargs[j]
    return t


def _sweep_rules(t, dmap):
    """(term, rules): the rules a sweep could take, and the term it leaves.

    `rewrite` in goal mode goes through `top_sweep_conv` (core/conv/
    core.py): the rule is tried at a node and, *where it fires*, that path
    is not descended into; function, argument and binder body are entered
    only where nothing fired.  So one step rewrites the top-most redexes of
    one rule, and a redex nested under another is left for a later step --
    which is why the emitted sequence is one rule per step and the same
    rule can appear twice in a row when the projections are nested
    (`snd (snd p)`, as three-argument definitions have).
    """
    rules = []

    def rec(x):
        y = _reduce_step(x, dmap)
        if y is not x:
            rules.append(dmap[x.strip_comb()[0].name][2])
            return y
        if x.is_comb():
            f, a = rec(x.fun), rec(x.arg)
            return x if (f is x.fun and a is x.arg) else f(a)
        if x.is_abs():
            body = rec(x.body)
            return x if body is x.body else Abs(x.var_name, x.var_T, body)
        return x

    return rec(t), _dedupe(rules)


def _sweep_with(t, rule, dmap):
    """The term after one `rewrite <rule>` step."""

    def rec(x):
        if dmap.get(x.strip_comb()[0].name, (None, None, None))[2] == rule                 if x.is_comb() else False:
            y = _reduce_step(x, dmap)
            if y is not x:
                return y
        if x.is_comb():
            f, a = rec(x.fun), rec(x.arg)
            return x if (f is x.fun and a is x.arg) else f(a)
        if x.is_abs():
            body = rec(x.body)
            return x if body is x.body else Abs(x.var_name, x.var_T, body)
        return x

    return rec(t)


def _reduce_used(t, dmap):
    """(fully reduced term, the rewrite steps the goal needs, in order).

    One rule per step, each chosen from a fresh sweep: a step is a whole
    sweep, so it clears every top-most redex of its rule -- including the
    ones the previous step uncovered.  Choosing the next rule without
    re-sweeping would emit a step with nothing to rewrite, which
    `rewrite` refuses.
    """
    steps = []
    while True:
        t2, rules = _sweep_rules(t, dmap)
        if not rules:
            return t, steps
        steps.append(rules[0])
        t = _sweep_with(t, rules[0], dmap)





def _reduce(t, dmap):
    """The fully reduced form of t."""
    return _reduce_used(t, dmap)[0]





def _dedupe(names):
    res = []
    for n in names:
        if n not in res:
            res.append(n)
    return res


# ---------------------------------------------------------------------------
# Relation, for the recursion-position type.
#
# Every datatype has one: `<ty>_wf_subterm`, stated on the bare component
# relation, generated from the constructor list by `core/datgen.py` when the
# block is loaded.  nat and list state the same lemma in their own file --
# they predate that module -- and nothing distinguishes them here: the
# generator rebuilds the relation from the registered constructors, which is
# the construction the lemma was generated from, and uses the lemma itself
# only as the well-foundedness fact the emitted `wf` obligation is
# discharged with (`_rel_wf_entry`).  A file that states some other relation
# for its datatype shows up as a failing `rule <ty>_wf_subterm` when the
# item is replayed -- a failed item, never a silent mismatch.
#
# The relation lives on the component the equations pattern-match on and is
# lifted to the tupled argument through the projection, so the lift is
# exactly `wf_measure_gen`.
#
# The destructor side is data-driven too: `destructor` and the projection
# rules come from `_destructor_maps`, which the datatype layer's naming
# feeds (`core/datgen.py`), so a constructor argument is taken apart the
# same way for every datatype.  Fixed by hand are only the library's own
# names for nat, list and prod -- `Pre`, `hd`, `tl`, `fst`, `snd` -- which
# library proofs cite.
# ---------------------------------------------------------------------------

def _type_inst(pat, T, tyinst):
    """Extend tyinst so that the type `pat` becomes `T`; False if it cannot."""
    if pat.is_tvar():
        if pat.name in tyinst:
            return tyinst[pat.name] == T
        tyinst[pat.name] = T
        return True
    if (pat.is_tconst() and T.is_tconst() and pat.name == T.name
            and len(pat.args) == len(T.args)):
        return all(_type_inst(p, t, tyinst)
                   for p, t in zip(pat.args, T.args))
    return False


def _inst_type(ty, tyinst):
    """Replace the type variables of `ty` by their instances.

    `Type.subst` only instantiates *schematic* variables (kernel/type.py),
    and the registered constructors carry rigid ones; replacing a variable
    by a compound type (`'a := 'a list`, as recursion through `'a list
    list` needs) is not something a rigid variable can hold anyway, so the
    tree is rebuilt here.
    """
    if ty.is_tvar() or ty.is_stvar():
        return tyinst.get(ty.name, ty)
    if ty.is_tconst():
        return TConst(ty.name, *[_inst_type(a, tyinst) for a in ty.args])
    return ty


def _registered_constrs(T):
    """The datatype's constructors, instantiated at T's type arguments.

    The registry holds them at the datatype's own type variables
    (`cons : 'a => 'a list => 'a list`).  The recursion position can carry
    type arguments of its own -- `concat : 'a list list => 'a list`
    descends through `'a list list`, whose constructor argument is
    `'a list` -- so the constructor's result type is matched against T to
    get the instantiation, and the relation and its witness types come out
    at the right instance.
    """
    from kernel import theory
    constrs = theory.thy.get_datatype_constrs(T.name)
    if not constrs:
        return None
    res = []
    for c in constrs:
        cT = c.get_type()
        _, resT = cT.strip_type()
        tyinst = {}
        if not _type_inst(resT, T, tyinst):
            return None
        res.append({'name': c.name, 'type': _inst_type(cT, tyinst)})
    return res


# ---------------------------------------------------------------------------
# Pattern subtraction: the equation set, made pairwise disjoint.
#
# Isabelle turns a `fun`'s equations into a constructor-disjoint set before
# anything else looks at them (Function/pattern_split.ML, `split_all_equations`
# through `pattern_subtract_many`): every equation is rewritten into the splits
# of its own pattern that the equations *before* it do not already cover.  Two
# patterns that differ at some constructor are already disjoint and pass
# through untouched, so a set that is disjoint to begin with comes out
# identical -- which is what lets this run on every definition.
#
# Two things it buys.  A user may write overlapping equations, the specific one
# first: the later equation then means "the equations before it did not match",
# which is Isabelle's sequential reading of `fun` and also the reading the
# branch chain emits (`_expand` used to refuse these outright).  And a
# definition with a *hole* -- an input no equation covers -- is completed by
# subtracting the equations from a catchall `f v1 ... vn = undefined`: what
# survives is exactly the missing patterns, so `dbl 0` with
# `dbl (Suc (Suc n))` leaves `dbl (Suc 0) = undefined` behind and the coverage
# and induction rules become statable.  Isabelle reports the missing patterns
# as a warning; here they are visible in the emitted equation itself.
# ---------------------------------------------------------------------------

def _fresh_var(used):
    """A variable name no equation of the set mentions yet."""
    k = 1
    while 'v%d' % k in used:
        k += 1
    used.add('v%d' % k)
    return 'v%d' % k


def _pattern_splits(t, t2, used):
    """The substitutions of pattern `t` under which it differs from `t2`.

    Each entry is a map from a variable of `t` to the term it takes there.
    `[]` says `t2` covers `t` completely and nothing is left; `[{}]` says the
    two cannot match the same input and nothing has to change; an entry that
    leaves some variables unmentioned narrows `t` at *one* argument only, so
    the entries are a union and not a product -- that is what
    `pattern_split.ML`'s `flat (map2 ...)` amounts to, and it is the right
    reading: `f v1 v2` differs from `f (Suc x) y` exactly when `v1` is not a
    `Suc`, whatever `v2` is.

    The three cases are that function's `pattern_subtract_subst`: a variable
    of `t2` covers everything below it; a variable of `t` is split by its
    type's constructors, one split per constructor; and two constructor
    applications with different heads cannot overlap, while equal heads
    subtract their arguments pairwise.
    """
    if t2.is_var():
        return []
    if t.is_var():
        res = []
        for constr in _registered_constrs(t.T) or []:
            arg_types, _ = constr['type'].strip_type()
            args = [Var(_fresh_var(used), T) for T in arg_types]
            term = Const(constr['name'], constr['type'])(*args)
            for sub in _pattern_splits(term, t2, used):
                env = {t.name: term}
                env.update(sub)
                res.append(env)
        return res
    h, args = t.strip_comb()
    h2, args2 = t2.strip_comb()
    if h == h2 and len(args) == len(args2):
        res = []
        for a, a2 in zip(args, args2):
            res.extend(_pattern_splits(a, a2, used))
        return res
    return [{}]


def _subtract_pattern(eq, other, used):
    """`eq`'s equations once `other`'s pattern is taken out of it.

    An empty list says `other` covers `eq` completely -- the equation states
    nothing about inputs the earlier one does not already decide.
    """
    h, args = eq.lhs.strip_comb()
    out = []
    for a, b in zip(args, _eq_args(other)):
        for env in _pattern_splits(a, b, used):
            piece = Eq(h(*[_subst(x, env) for x in args]),
                       _subst(eq.rhs, env))
            if piece not in out:
                out.append(piece)
    return out


def _chain_separable(arg_types, eqs):
    """Whether the branch chain can rule these equations out of one another.

    A branch refutes an earlier equation's test at a position both equations
    constrain, and `_pattern_neq` gets there from the two patterns' own
    constructors -- peeling one level with a constructor's injectivity when
    they share it.  Two patterns that agree at every such position, or that
    meet a *variable* where the other carries a constructor, cannot be told
    apart at all, and then the emission would fail.
    """
    lhs = [_eq_args(eq) for eq in eqs]
    positions = recursion_positions(arg_types, lhs)
    for i in range(len(eqs)):
        here = _pattern_positions(lhs[i], positions)
        for j in range(i):
            for pos in _pattern_positions(lhs[j], positions):
                if pos in here and _patterns_differ(lhs[j][pos], lhs[i][pos]):
                    break
            else:
                return False
    return True


def _complete_equations(name, arg_types, res_type, eqs, texts):
    """The equations made disjoint, with the holes filled by `undefined`.

    Returns `(eqs, texts, missing)`.  `texts` stays aligned with the equations:
    one that came through untouched keeps the source's own text, and one the
    subtraction narrowed -- or the catchall contributed -- has none, so the
    caller prints it from the term.  `missing` holds the equations the catchall
    kept, the inputs the definition leaves undefined, and is empty exactly when
    the definition's own equations are exhaustive.

    The catchall is appended and never subtracted *from*: it is last, and an
    equation is only narrowed by the equations before it, so the user's
    equations keep their region and the catchall keeps what they do not cover.
    """
    used = set()
    for eq in eqs:
        for v in eq.get_vars():
            used.add(v.name)
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    vs = [Var(_fresh_var(used), T) for T in arg_types]
    catchall = Eq(f_const(*vs), Const('undefined', res_type))
    seq = list(eqs) + [catchall]
    out, out_text, missing = [], [], []
    for k, eq in enumerate(seq):
        pieces = [eq]
        for prev in seq[:k]:
            pieces = [p for piece in pieces
                      for p in _subtract_pattern(piece, prev, used)]
        if k < len(eqs):
            if not pieces:
                raise FunGenError(
                    'fun %s: equation %d is covered by the equations before '
                    'it; it decides no input they do not already decide'
                    % (name, k + 1))
            out.extend(pieces)
            out_text.extend([texts[k]] if pieces == [eq] else [None] * len(pieces))
        else:
            # The catchall's survivors join the set -- they are the equations
            # the definition is proved through -- and are reported as well:
            # they are the inputs the user's equations never mentioned.
            out.extend(pieces)
            out_text.extend([None] * len(pieces))
            missing.extend(pieces)
    if missing and not _chain_separable(arg_types, out):
        # The missing pattern differs from the equation next to it only
        # *inside* a constructor, so the branch chain cannot rule one out of
        # the other and the emission would fail -- and a definition whose
        # emission fails falls back to axioms, losing the equations and the
        # relation it already had.  The fill is dropped instead: the
        # definition keeps everything it had, and only the coverage and
        # induction rules are missing.
        return list(eqs), list(texts), []
    return out, out_text, missing


def _relation(T):
    """The datatype's subterm relation, built from its constructors."""
    from core import datgen
    constrs = _registered_constrs(T)
    if constrs is None:
        raise FunGenError(
            'no well-founded relation is known for recursion on %s: the '
            'datatype is not registered' % printer.print_type(T))
    pairs = datgen.subterm_pairs(T, constrs)
    if not pairs:
        raise FunGenError(
            'recursion on %s: no constructor takes the datatype itself'
            % printer.print_type(T))
    return datgen.relation_term(T, constrs, pairs)


# ---------------------------------------------------------------------------
# Measures: the general path (Isabelle's lexicographic_order).
#
# `fun`'s first relation prover is the measure matrix: candidate measure
# functions on the tupled argument, a cell per (recursive call, measure)
# saying what the call does there, and a right-nested `mlex_prod` chain
# over the columns the search kept.  `core/measure.py` decides all of it
# and hands back the cells with their proofs.  The datatype's own subterm
# relation above is what is left when no measure applies -- most
# importantly for the size function itself, whose only measure would be
# the very constant being defined.
# ---------------------------------------------------------------------------

def _size_name(T):
    """The datatype's generated size function, or None."""
    from kernel import theory
    if not T.is_tconst():
        return None
    name = '%s_size' % T.name
    return name if theory.thy.has_term_sig(name) else None


def _size_rule(sz, T, k):
    """The size function's equation for the k-th constructor, or None."""
    from kernel import theory
    names = ['%s_def_%d' % (sz, k)]
    try:
        names.append('%s_def_%d'
                     % (theory.thy.get_overload_const_name(sz, TFun(T, NatType)),
                        k))
    except Exception:
        pass
    for name in names:
        try:
            theory.get_theorem(name)
            return name
        except Exception:
            continue
    return None


def _size_family(T, def_names):
    """(size function, its parameters' types, its family) for an instance.

    The size of a datatype instance is `<ty>_size`, when the datatype layer
    generated one and it is not the definition being expanded (a size's own
    measure would be the constant being defined).  The family is read from
    the datatype's *declaration* -- its constructors at the datatype's own
    type variables -- because that is what datgen wrote the equations from;
    `param_types` is the same description read at this instance, so the k-th
    measure the size takes has type `TFun(param_types[k], nat)`.

    None when the type is not a datatype, has no generated family, or one of
    the family's equations is missing from the theory: an equation the
    normalization cannot find is a rewrite step the emitted proof could not
    take.
    """
    from kernel import theory
    if not T.is_tconst():
        return None
    sz = _size_name(T)
    if sz is None or sz in def_names:
        return None
    declared = theory.thy.get_datatype_constrs(T.name)
    if not declared:
        return None
    params = [a.name for a in declared[0].get_type().strip_type()[1].args]
    constrs = [{'name': c.name, 'type': c.get_type()} for c in declared]
    used, spec = measure.size_spec(T.name, params, constrs)
    table = {}
    for k, c in enumerate(constrs):
        rule = _size_rule(sz, T, k + 1)
        if rule is None:
            return None
        table[c['name']] = (rule, spec[c['name']])
    return sz, [T.args[params.index(a)] for a in used], (len(used), table)


def _param_measure(T, sizes, def_names):
    """The measure a size of T takes for a parameter of this type, or None.

    Deterministic and *named*: `id` for the natural numbers, `zero_measure`
    for a type variable (nothing measures it, and leaving its contribution
    out still counts the container's own constructors), and a datatype's
    own size otherwise -- with its parameters filled in the same way, so
    `seq_size zero_measure` and `list_size tri_size` come out of the same
    recursion.  A parameter measure is a term, never a lambda: the size's
    equation applies it (`f x`), and a lambda there would be a beta redex
    in the goal the engine compares (`core/measure.py`).

    None when a parameter of the size has no measure at all, in which case
    the size itself is not offered.
    """
    if T == NatType:
        return Const('id', TFun(NatType, NatType))
    if T.is_tvar():
        return Const('zero_measure', TFun(T, NatType))
    fam = _size_family(T, def_names)
    if fam is None:
        return None
    sz, ptypes, (arity, table) = fam
    sizes[sz] = (arity, table)
    mterms = []
    for Ty in ptypes:
        sub = _param_measure(Ty, sizes, def_names)
        if sub is None:
            return None
        mterms.append(sub)
    size_T = TFun(*(list(m.get_type() for m in mterms) + [T, NatType]))
    return Const(sz, size_T)(*mterms) if mterms else Const(sz, TFun(T, NatType))


def _measure_registry(cname, arg_types, def_names):
    """(the sizes in scope, the candidate measures).

    This is Isabelle's `measure_function` set (`measure_functions.ML`)
    resolved into terms: a position is measured by the identity when it is
    a natural number, and by the datatype's size -- with a measure per type
    parameter, `seq_size zero_measure` or `list_size tri_size` -- when it
    is a datatype instance.  A position whose type has neither contributes
    no column.

    Every candidate is named by the argument position it measures, before
    the search runs: the name has to be known while the cells are built
    (`<c>_m2` is what the relation and the obligations both write), and
    naming by position keeps it the same whether the search keeps the
    measure or not.
    """
    sizes, measures = {}, []
    for pos, T in enumerate(arg_types):
        if T == NatType:
            m = measure.Measure(pos, arg_types, 'nat')
        else:
            if not T.is_tconst():
                continue
            fam = _size_family(T, def_names)
            if fam is None:
                continue
            sz, ptypes, (arity, table) = fam
            sizes[sz] = (arity, table)
            mterms = []
            for Ty in ptypes:
                sub = _param_measure(Ty, sizes, def_names)
                if sub is None:
                    mterms = None
                    break
                mterms.append(sub)
            if mterms is None:
                continue
            m = measure.Measure(pos, arg_types, 'size', size_name=sz,
                                mterms=mterms)
        m.def_name = '%s_m%d' % (cname, pos + 1)
        measures.append(m)
    return sizes, measures


def _measure_defs(cname, arg_types, order):
    """The measure constants' definitions, as `def` item lines.

    The relation and the obligations both write a measure as a constant
    (`<c>_m1`) and never as a lambda: the rules that consume the cells
    (`mlex_less`, `mlex_leq`) state their premises as `f x`, the matcher
    is first-order and does not beta reduce, so `f` has to be a constant
    whose application one `rewrite <c>_m1_def` unfolds.  The defining
    equation is written with the tuple variable free, so that rewrite
    substitutes the tuple into the body in one step.
    """
    Tup = tupled_type(arg_types)
    p = Var('p', Tup)
    return ['def %s :: %s ⇒ nat = %s p = %s'
            % (m.def_name, _printt(Tup), m.def_name, _prints(m.body(p)))
            for m in (order or [])]


def _measure_chain_text(arg_types, order, start=0):
    """The relation chain from column `start` on, as text.

    The chain ends at the empty relation, which is what makes it well
    founded without any further work (`wf_false`): the measures before
    the last are compared by `mlex_prod` and the calls that reach the
    end have all strictly decreased by then.  The text is the one the
    relation definition and the obligation proofs both use, so the terms
    they parse are the same term.
    """
    Tup = _printt(tupled_type(arg_types))
    p = Var('p', tupled_type(arg_types))
    body = '(%%x::%s. %%y::%s. false)' % (Tup, Tup)
    for m in reversed(order[start:]):
        body = 'mlex_prod %s (%s)' % (measure.measure_text(m, p), body)
    return body


def _typed_lambda(text, arg_types, ascribe=False):
    """A clause's lambda, with its binders typed from the definition.

    The clause is written as a bare lambda (`"%m n. m + n"`); the parser
    cannot type an unbound lambda on its own, and the types are exactly
    the definition's own arguments, so they are written into the binders
    here.  A binder the user typed keeps its ascription, and a clause that
    is not a plain lambda prefix (`"my_measure"`, say) is left as written
    -- then its type has to stand on its own, which `fun_clauses` checks.
    """
    m = re.match(r'\s*%([^.%]*)\.(.*)$', text, re.S)
    if not m:
        return text
    names = m.group(1).split()
    if ascribe:
        # One binder per tuple: the clause is the relation the machinery
        # uses, over the tupled arguments.
        types = [arg_types[0]] * len(names)
    else:
        types = list(arg_types)
    if len(names) != len(types):
        return text
    # One `%` per binder: the parser reads a type after a binder only when
    # the binder starts a lambda of its own (`%x::nat. %y::nat. ...`).
    parts = [('%' + nm) if '::' in nm else ('%%%s::%s' % (nm, _printt(T)))
             for nm, T in zip(names, types)]
    return '%s. %s' % ('. '.join(parts), m.group(2))


def _tupled_measure(t, arg_types):
    """A measure written over the arguments, as a function of the tuple.

    `"%m n. m + n"` becomes `%p. m + n` with `m`, `n` the projections of
    `p` -- the shape every measure in the emitter has, so a measure the
    user wrote and one the search picked take the same path from here on.
    """
    p = Var('p', tupled_type(arg_types))
    app = t
    for i in range(len(arg_types)):
        app = app(projection(p, arg_types, i))
    return Lambda(p, app.beta_norm())


def _measure_tables(sizes, measures):
    """(size tables, reduction rules) for a set of measures.

    `sizes` is what `_measure_registry` collected -- the families of every
    size the candidates mention, the composed measures' parameters
    included -- and the reduction table is what `measure.cell` unfolds the
    measures and their parameter measures with.
    """
    mdefs = {}
    for m in measures:
        mdefs.update(m.tables())
    return sizes, mdefs


def _given_measures(arg_types, cname, given):
    """The measures a definition was given, as the search's own objects.

    A given measure is a measure like any other from here on: it becomes
    the same named constant (`<c>_m1`), its columns are built by the same
    `cell`, and the chain, the `wf` obligation and the decrease
    obligations are the same code.  Nothing downstream knows where a
    measure came from.
    """
    return [measure.Measure(0, arg_types, 'given',
                            def_name='%s_m%d' % (cname, k + 1), given=m)
            for k, m in enumerate(given)]


def fun_clauses(data, eqs, name, ty):
    """The relation or measures a `fun` was given, parsed and checked.

    Returns `(measures, relation, wf lemma, descent lemmas)`.  The
    measures and the relation are terms of the *tupled* argument -- the
    same shape the inferred measures have, so that they need no
    conversion -- and `wf`/`descent` name theorems of the file.

    The rules about which clause goes with which are stated here, in one
    place, and they are about what can be *proved* rather than about what
    looks tidy:

    * a relation is a term the emitter knows nothing about, so `wf` (the
      theorem proving `wf R`) and `descent` (the theorems proving each
      call's `R call pat`) are both required -- there is nothing
      automatic left to fall back on;
    * a measure chain says its own obligation, in terms of the constants
      the emitter generates for it, so no lemma written in the file can
      state it: `wf`/`descent` with measures is an error rather than a
      clause that would be silently ignored.
    """
    from core import context
    from core import items
    try:
        texts = dict((key, items._clause_values(data.get(key) or []))
                     for key in ('measure', 'relation', 'wf', 'descent'))
    except items.ItemException as error:
        raise FunGenError('fun %s: %s' % (name, error))
    if len(texts['relation']) > 1:
        raise FunGenError('fun %s: one relation, %d given'
                          % (name, len(texts['relation'])))
    if len(texts['wf']) > 1:
        raise FunGenError('fun %s: one `wf` lemma, %d given'
                          % (name, len(texts['wf'])))
    arity = len(_eq_args(eqs[0]))
    arg_types, _ = _strip_type(ty, arity)
    Tup = tupled_type(arg_types)
    curried = TFun(*(list(arg_types) + [NatType]))
    tupled_rel = TFun(Tup, TFun(Tup, BoolType))
    # A clause's type is known here and nowhere else, so it is put into the
    # text rather than asked of the user again: the binders are the
    # definition's own, and `_typed_lambda` ascribes them.  A *measure* is
    # written over the arguments (`"%m n. m + n"`), because who proves its
    # obligations is the emitter, and the arguments are what the user
    # reads; a *relation* is written over the two tupled arguments
    # (`"%p q. fst p < fst q"`), because its obligations are matched
    # against lemmas the user writes, and those have to be the very terms
    # the emitter states.
    with context.fresh_context(defs={name: ty}):
        measures = [_tupled_measure(
            context.parse_term(_typed_lambda(text, arg_types)), arg_types)
            for text in texts['measure']]
        relation = (context.parse_term(_typed_lambda(
            texts['relation'][0], [Tup, Tup], ascribe=True))
            if texts['relation'] else None)
    if measures and relation is not None:
        raise FunGenError('fun %s: a relation or measures, not both' % name)
    if relation is not None:
        if not texts['wf']:
            raise FunGenError(
                'fun %s: a relation needs the theorem proving `wf R`; give '
                '`wf "<lemma>"`, or use `measure` for the automatic path'
                % name)
        if not texts['descent']:
            raise FunGenError(
                'fun %s: a relation needs the lemmas that discharge the '
                'calls\' obligations; give `descent "<lemma>", ...`, or use '
                '`measure`' % name)
    elif texts['wf'] or texts['descent']:
        raise FunGenError(
            'fun %s: `wf`/`descent` discharge the obligations of a relation; '
            'a measure chain states its own, in terms of the measure '
            'constants the emitter generates for it, which no lemma of this '
            'file can name' % name)
    arity = len(_eq_args(eqs[0]))
    arg_types, _ = _strip_type(ty, arity)
    Tup = tupled_type(arg_types)

    def _ascribed(t, T, what):
        """The term at type `T`, instantiating what it left open.

        The clause is parsed with the type ascribed, so this is a check:
        a term that cannot have the type is reported as such rather than
        as a comparison that failed for a reason further on.
        """
        from kernel.type import TyInst, TypeMatchException
        inst = TyInst()
        try:
            t.get_type().match_incr(T, inst)
        except TypeMatchException:
            raise FunGenError(
                'fun %s: the %s %s has type %s; it has to be %s'
                % (name, what, _prints(t), _printt(t.get_type()), _printt(T)))
        return t.subst_type(inst)

    measures = [_ascribed(m, TFun(Tup, NatType), 'measure') for m in measures]
    if relation is not None:
        relation = _ascribed(relation, TFun(Tup, TFun(Tup, BoolType)),
                             'relation')
    return (measures, relation,
            texts['wf'][0] if texts['wf'] else None, texts['descent'])


def _measure_order(arg_types, def_names, cname, eqs, calls, dmap):
    """The measures the definition descends through, or None.

    None means the measure search found no order: the caller then keeps
    the datatype's subterm relation, which is the relation rule that
    applies to definitions the measures cannot express (the size
    function's own recursion above all).  Also returns the size tables
    and the measure constants' defining equations, which are what the
    cells are proved with.

    Every candidate is named by the argument position it measures, before
    the search runs: the name has to be known while the cells are built
    (`<c>_m2` is what the relation and the obligations both write), and
    naming by position keeps it the same whether the search keeps the
    measure or not.
    """
    sizes, measures = _measure_registry(cname, arg_types, def_names)
    _, mdefs = _measure_tables(sizes, measures)
    rows = [(tupled_arg(c), _tuple_of(eqs[i]))
            for i, cs in enumerate(calls) for c in cs]
    return measure.infer(measures, rows, dmap, sizes, mdefs), sizes, mdefs


def _subterm(T):
    """(relation on the component, its well-foundedness lemma).

    The lemma is looked for rather than assumed: a datatype block states it
    at load time, and a definition whose imports do not carry that block
    cannot discharge the obligation.
    """
    from kernel import theory
    if not T.is_tconst():
        raise FunGenError(
            'no well-founded relation is known for recursion on %s'
            % printer.print_type(T))
    lemma = '%s_wf_subterm' % T.name
    try:
        theory.get_theorem(lemma)
    except Exception:
        raise FunGenError(
            '%s is not in scope, so recursion on %s has no well-founded '
            'relation to descend through' % (lemma, printer.print_type(T)))
    return '(%s)' % _prints(_relation(T)), lemma


# ---------------------------------------------------------------------------
# Emission helpers.
# ---------------------------------------------------------------------------

def _prints(t):
    with global_setting(unicode=True):
        return printer.print_term(t)


def _printt(T):
    """A type written into emitted text, refusing one that does not come back.

    The printer drops parentheses the parser needs: `('a × 'b) list`
    prints as `'a × 'b list`, which means `'a × ('b list)`.  An item
    whose type text means something else poisons the rest of the file --
    the constant it defines never registers, and every later item that
    mentions it fails with it -- so the definition keeps its axioms
    instead.
    """
    from syntax import parser
    with global_setting(unicode=True):
        text = printer.print_type(T)
    try:
        back = parser.parse_type(text)
    except Exception:
        back = None
    if back != T:
        raise FunGenError('the type %s does not survive printing as %s'
                          % (_printt_plain(T), text))
    return text


def _printt_plain(T):
    with global_setting(unicode=True):
        return printer.print_type(T)


def _arg_text(t):
    """A term used as an argument: applications need parentheses."""
    text = _prints(t)
    return "(%s)" % text if t.is_comb() else text


def _strip_type(ty, n):
    """`([a_1, ..., a_n], b)` for a type `a_1 => ... => a_n => b`.

    `Type.strip_type` always takes every arrow, which is not the arity of a
    definition whose result is a type abbreviation.
    """
    domains = []
    for _ in range(n):
        if not ty.is_fun():
            raise FunGenError(
                'the declared type %s has fewer than %d arguments'
                % (_printt_plain(ty), n))
        domains.append(ty.domain_type())
        ty = ty.range_type()
    return domains, ty


def _eq_args(eq):
    return eq.lhs.strip_comb()[1]


def _tuple_of(eq):
    return tupled_arg(_eq_args(eq))


def _pattern_vars(eq, r):
    """Bound variables of the pattern at the recursion position."""
    _, args = _eq_args(eq)[r].strip_comb()
    return [a.name for a in args if a.is_var()]


def _constr_name(lhs_args, r):
    head, _ = lhs_args[r].strip_comb()
    return head.name


def _distinct_neq(tyname, c1, c2):
    """Name and statement of the distinctness axiom for two constructors."""
    from kernel import theory
    for th_name in ("%s_%s_%s_neq" % (tyname, c1, c2),
                    "%s_%s_%s_neq" % (tyname, c2, c1)):
        try:
            return th_name, theory.get_theorem(th_name)
        except Exception:
            continue
    return None, None


def _entry(lines):
    """Parse an emitted entry back with the ordinary item parser."""
    from syntax import pyhol
    item, _ = pyhol._parse_item(lines, 0)
    return item


def _calls(t, f_const, n):
    """Recursive calls in t, as argument lists."""
    res = []
    if t.is_comb():
        h, args = t.strip_comb()
        if h == f_const and len(args) == n:
            res.append(args)
            return res
        res.extend(_calls(t.fun, f_const, n))
        res.extend(_calls(t.arg, f_const, n))
    return res


def _typenames(vars_):
    return ", ".join("%s :: %s" % (v.name, _printt(v.T)) for v in vars_)


def _vars_dict(eq):
    """The `fixes` variables as the parser's {name: printed type} map."""
    return {v.name: _printt(v.T) for v in eq.get_vars()}


# ---------------------------------------------------------------------------
# Item emission.
# ---------------------------------------------------------------------------

class _Proof:
    """Emit a proof block, tracking the stable-ID counter.

    Every step of the templates below creates exactly one item, except
    the ones that close their goal.  Which those are is decided here, in
    code, from the step itself and from the terms involved -- a `rule`
    whose conclusion is the goal, `if_P` / `if_not_P`, `unfold` of a
    definition inside its own cut, and the last projection rewrite when
    the obligation resolves to an identity.  Those pass new=0.

    `g` is the ID of the goal the next step rewrites; a step that creates
    an item returns its ID, and the caller keeps the parent's ID when the
    step closes instead.
    """

    def __init__(self):
        self.lines = []
        self.n = 1
        self.g = 0

    def step(self, text, new=1):
        """Append a step; return the ID it created, or None if it closed."""
        self.lines.append('  ' + text)
        if not new:
            return None
        i = self.n
        self.n += new
        self.g = i
        return i

    def text(self):
        return self.lines

    def ids(self, text, new):
        """Append a step creating `new` items; return all their IDs."""
        self.lines.append('  ' + text)
        res = list(range(self.n, self.n + new))
        self.n += new
        return res


class _Names:
    """Unique names for the items one emitted proof introduces.

    A variable line's theorem is `Thm.mk_VAR(name, type)` and carries no
    hypothesis, so two lines with the same name and type are the same
    stable id: the second `intro`/`elim` of a name would create nothing and
    every literal ID after it would be off by one.  Every template that
    introduces a name allocates it here.
    """

    def __init__(self):
        self.used = {}

    def alloc(self, base):
        self.used[base] = self.used.get(base, 0) + 1
        return '%s%d' % (base, self.used[base])


def _typenames(vars_):
    return ", ".join("%s :: %s" % (v.name, _printt(v.T)) for v in vars_)


def _vars_dict(eq):
    """The `fixes` variables as the parser's {name: printed type} map."""
    return {v.name: _printt(v.T) for v in eq.get_vars()}


def _rel_ty_text(arg_types):
    """Printed type of the relation constant."""
    Tup = tupled_type(arg_types)
    return _printt(TFun(Tup, TFun(Tup, BoolType)))


def _rel_wf_prop(cname, arg_types):
    """The wf obligation, with the relation ascribed.

    The ascription supplies the definition's type variables: a bare
    `wf <c>_rel` leaves the parser with nothing to instantiate a
    polymorphic relation from, and `forward` cannot instantiate a
    polymorphic theorem either, so the fact is cut and then ruled.
    """
    return 'wf (%s_rel::%s)' % (cname, _rel_ty_text(arg_types))


def _in_def_prop(cname, arg_types, res_type):
    """The fixpoint equation with the constant ascribed, for its cut."""
    in_ty = _printt(TFun(tupled_type(arg_types), res_type))
    return ('(%s_in::%s) = (SOME g. !z. g z = wfrec_H %s_rel %s_H g z)'
            % (cname, in_ty, cname, cname))


def _kept_whole(body_prop):
    """A definition's right-hand side, in a form the item parser keeps whole.

    A `def` item is one line, and the item parser reads a trailing
    `[...]` group as that item's attribute list.  A body ending in a
    list literal (`... @ [hd p]`) would lose it to the attributes and be
    left truncated at the `@`; the parentheses make the line end on `)`.
    """
    return '(%s)' % body_prop if body_prop.endswith(']') else body_prop


def _def_entries(name, cname, arg_types, res_type, body_prop, rel_prop):
    """The definitional entries: H, rel, in, and the curried constant."""
    Tup = tupled_type(arg_types)
    n = len(arg_types)
    h_ty = _printt(TFun(TFun(Tup, res_type), TFun(Tup, res_type)))
    in_ty = _printt(TFun(Tup, res_type))
    f_ty = _printt(TFun(*(list(arg_types) + [res_type])))
    res = ['def %s_H :: %s = %s_H g p = %s'
           % (cname, h_ty, cname, _kept_whole(body_prop)),
           'def %s_rel :: %s = %s_rel = (%s)' % (cname, _rel_ty_text(arg_types),
                                                 cname, rel_prop),
           'def %s_in :: %s = %s_in = (SOME g. !z. g z = wfrec_H %s_rel %s_H '
           'g z)' % (cname, in_ty, cname, cname, cname)]
    xs = [Var('x%d' % (i + 1), arg_types[i]) for i in range(n)]
    res.append('def %s :: %s = %s %s = %s_in %s' % (
        name, f_ty, name, " ".join(x.name for x in xs), cname,
        _arg_text(tupled_arg(xs))))
    return res


def _lemma_states(lemma, prop):
    """Whether the named theorem states the proposition (or matches it).

    A theorem item's `fixes` become schematic variables
    (`nat_size ?n < nat_size (Suc ?n)`), and those are exactly the points
    `rule` instantiates at replay time, so the question is asked with the
    matcher the replay will use.
    """
    from core import matcher
    from kernel import theory
    return matcher.can_first_order_match(theory.get_theorem(lemma).prop, prop)


def _check_lemma(lemma, prop, what, name):
    """The named theorem that states `prop`, or an error.

    Asking the question here turns a wrong lemma into a report naming it
    instead of an item that fails its replay.
    """
    from kernel import theory
    try:
        th = theory.get_theorem(lemma)
    except Exception:
        raise FunGenError(
            'fun %s: the %s lemma %s is not in the theory yet; it has to be '
            'stated before the definition' % (name, what, lemma))
    if not _lemma_states(lemma, prop):
        raise FunGenError(
            'fun %s: the %s lemma %s states %s, which is not the obligation '
            '%s' % (name, what, lemma, _prints(th.prop), _prints(prop)))
    return lemma


def _unfold_is_the_equality(arg_types, r, tcall, p, eq_tuple):
    """Whether unfolding the relation gives the branch's own equality.

    The subterm relation over a single-argument definition is `q = C p`,
    so `rewrite <c>_rel_def` turns the goal `<c>_rel <call> p` into
    exactly the equation the branch already obtained from `elim` -- and a
    rewrite whose result is a theorem already in the table lays out no new
    line.  With more than one argument the relation is stated over the
    projections (`fst q = Suc (fst p)`), which is a different theorem from
    the equality between the tuples, so the unfold does create one.
    Comparing the two terms says which, instead of leaving the count to
    whatever the table happens to hold.
    """
    T = arg_types[r]
    call = _proj_term(arg_types, r, tcall)
    unfolded = _relation(T)(call)(_proj_term(arg_types, r, p)).beta_norm()
    return unfolded == Eq(p, eq_tuple)


def _given_obligation(prover, arg_types, r, relation, tcall, tup, descent, g,
                      name, i, used, lines=False):
    """One call's decrease obligation, discharged from the user's lemmas.

    The proposition is the relation applied to the call and to the
    equation's own pattern -- the same shape the measure path states, with
    the relation the user wrote -- and the lemma is the one of `descent`
    that states it.  Which lemma serves which call is decided by the
    *statement*, so the user does not have to list them in call order; a
    call no lemma covers is an error naming the obligation, and a lemma no
    call uses is an error naming the lemma.

    Returns the stable ID of the fact that closes the goal, which is the cut
    itself where the lemma closes its goal in place (`_def_entry`'s goals
    carry no hypotheses) and the item the lemma lays out where it does not
    (an induction branch, as in `_emit_closing`).  `lines` says which.
    """
    call = _proj_term(arg_types, r, tcall)
    pat = _proj_term(arg_types, r, tup)
    prop = relation(call)(pat).beta_norm()
    c = prover.step('cut "%s" goal=%d' % (_prints(prop), g))
    for lemma in descent:
        if _lemma_states(lemma, prop):
            used.add(lemma)
            if lines:
                return prover.step('← rule %s goal=%d' % (lemma, c))
            prover.step('← rule %s goal=%d' % (lemma, c), new=0)
            return c
    raise FunGenError(
        'fun %s: equation %d: no `descent` lemma states the obligation %s'
        % (name, i + 1, _prints(prop)))


def _rel_wf_entry(cname, arg_types, r, order=None, relation=None,
                  wf_lemma=None):
    """The `wf` obligation: the relation is well-founded.

    With a measure order the relation is the `mlex_prod` chain, so its
    well-foundedness is `wf_mlex` once per column -- each use takes the
    tail's well-foundedness as its premise, which is why the chain's
    obligations are cut from the tail backwards and closed on the way
    back -- down to `wf_false`, the empty relation at the end.  The
    chain's tail `wf` obligations are the ones `wf_mlex` states, so they
    are stated here with the same text the chain is written with.

    With a relation the user wrote, the obligation is `wf R` and the proof
    is the user's own: unfolding the relation's definition leaves exactly
    that, and `wf_lemma` is the theorem that states it.

    Without either the relation is the datatype's subterm relation lifted
    through the projection.  The relation def is a lambda, so `rewrite`
    unfolds it in the unapplied goal `wf <c>_rel` without a beta redex;
    the lift is `wf_measure_gen`, instantiated explicitly because its
    pattern `?R (?m x) (?m y)` does not match a projection application on
    its own.

    The empty relation of a definition without recursive calls is the one
    case that needs no lift: `wf_false` is its well-foundedness directly.
    """
    prop = _rel_wf_prop(cname, arg_types)
    prover = _Proof()
    g = prover.step('← rewrite %s_rel_def goal=0' % cname)
    if relation is not None:
        wf_prop = Const('wf', TFun(TFun(tupled_type(arg_types),
                                        TFun(tupled_type(arg_types),
                                             BoolType)), BoolType))(relation)
        _check_lemma(wf_lemma, wf_prop, 'wf', cname)
        prover.step('← rule %s goal=%d' % (wf_lemma, g), new=0)
        return ['theorem %s_rel_wf' % cname, '  prop %s' % prop,
                'proof'] + prover.text() + ['qed']
    if order is not None:
        if not order:
            prover.step('← rule wf_false goal=%d' % g, new=0)
            return ['theorem %s_rel_wf' % cname, '  prop %s' % prop,
                    'proof'] + prover.text() + ['qed']
        # The tails are cut from the inside out and closed the same way: a
        # step can only cite lines that precede it, so the tail's `wf` fact
        # has to be created before the step that uses it.
        cuts = []
        for j in range(len(order), 0, -1):
            chain = _measure_chain_text(arg_types, order, j)
            cuts.append(prover.step('cut "wf (%s)" goal=%d' % (chain, g)))
        prover.step('← rule wf_false goal=%d' % cuts[0], new=0)
        for j in range(len(order) - 1):
            prover.step('← rule wf_mlex goal=%d facts=[%d]'
                        % (cuts[j + 1], cuts[j]), new=0)
        prover.step('← rule wf_mlex goal=%d facts=[%d]' % (g, cuts[-1]),
                    new=0)
        return ['theorem %s_rel_wf' % cname, '  prop %s' % prop,
                'proof'] + prover.text() + ['qed']
    T = arg_types[r]
    Rr, lemma = _subterm(T)
    if len(arg_types) > 1:
        m_ty = _printt(TFun(tupled_type(arg_types), T))
        # A lambda has to be ascribed as a whole: `(λp. fst (snd p)::T)`
        # attaches the type to the body.  With one or two arguments the
        # projection is a constant and the short form is kept, so the
        # emitted text of existing definitions does not change.
        # The printed lambda ascribes its own binder, and the result type
        # follows from the body, so it needs no outer ascription -- which
        # the parser would not take after the closing parenthesis anyway.
        if len(arg_types) <= 2:
            m_text = '(%s::%s)' % (_prints(_proj_const(arg_types, r)), m_ty)
        else:
            m_text = '(%s)' % _prints(_proj_const(arg_types, r))
        g = prover.step('← rule wf_measure_gen param_R="%s" param_m="%s" '
                        'goal=%d' % (Rr, m_text, g))
    prover.step('← rule %s goal=%d' % (lemma, g), new=0)
    return ['theorem %s_rel_wf' % cname, '  prop %s' % prop,
            'proof'] + prover.text() + ['qed']


def _neq_sides(th):
    """The two constructor applications a distinctness axiom compares."""
    prop = th.prop
    if not is_not(prop):
        raise FunGenError('the distinctness axiom is not a negation')
    body = prop.arg
    return body.lhs, body.rhs


def _exists_var(t):
    """The variable an existential binds."""
    return t.arg.var_name


def _subst_svars(t, env):
    """Replace the schematic variables of a theorem's statement.

    A schematic variable is an `SVar`, not a `Var`, so the ordinary
    substitution does not see it; the axioms' statements are what needs
    instantiating here.
    """
    if t.is_comb():
        h, args = t.strip_comb()
        return h(*[_subst_svars(a, env) for a in args])
    if t.is_svar() and t.name in env:
        return env[t.name]
    return t


def _conj_of(tests):
    """The right-nested conjunction of the given tests."""
    res = tests[-1]
    for t in reversed(tests[:-1]):
        res = Const('conj', TFun(BoolType, TFun(BoolType, BoolType)))(t)(res)
    return res


def _patterns_differ(t1, t2):
    """Whether two constructor patterns can be told apart by their constructors.

    `C a` and `D b` differ when the constructors do; `C a` and `C b` when one
    of their argument pairs does.  A variable takes any value, so a pattern
    that is one cannot be refuted this way -- which is also the shape a hole
    is left alone for rather than filled (`_chain_separable`).
    """
    if t1.is_var() or t2.is_var():
        return False
    h1, a1 = t1.strip_comb()
    h2, a2 = t2.strip_comb()
    if not (h1.is_const() and h2.is_const()):
        return False
    if h1.name != h2.name or len(a1) != len(a2):
        return True
    return any(_patterns_differ(x, y) for x, y in zip(a1, a2))


def _distinct_fact(prover, T, t1, t2, g):
    """A fact that `t1 = t2` fails, for two *different* constructors of `T`.

    The datatype's distinctness axiom is instantiated with the two terms'
    own arguments -- a schematic variable prints as `?n` and its `param_`
    argument is spelled without the question mark, so the two are built
    apart, and the value is quoted because it can be a compound term -- and
    flipped with `ineq_sym` when the axiom reads the other way round.
    """
    h1, a1 = t1.strip_comb()
    h2, a2 = t2.strip_comb()
    th_name, th = _distinct_neq(T.name, h2.name, h1.name)
    if th is None:
        raise FunGenError(
            'no distinctness axiom for the constructors %s and %s of %s; '
            'without one the branch of %s cannot be ruled out'
            % (h2.name, h1.name, _printt(T), h1.name))
    left, right = _neq_sides(th)
    lc, l_args = left.strip_comb()
    rc, r_args = right.strip_comb()
    if lc.name == h1.name:
        pairs = list(zip(l_args, a1)) + list(zip(r_args, a2))
        flipped = False
    else:
        pairs = list(zip(l_args, a2)) + list(zip(r_args, a1))
        flipped = True
    params = ' '.join('param_%s="%s"' % (v.name.lstrip('?'), _arg_text(t))
                      for v, t in pairs)
    fact = prover.step(u'\u2192 forward %s %s goal=%d' % (th_name, params, g))
    if flipped:
        fact = prover.step(
            u'\u2192 forward ineq_sym param_x="%s" param_y="%s" goal=%d '
            u'facts=[%d]' % (_arg_text(t2), _arg_text(t1), g, fact))
    return fact


def _refute_equality(prover, T, t1, t2, hyp, g):
    """Close goal `g` from `hyp`, the equality of the patterns `t1` and `t2`.

    `g` is a `false` goal and the equality is one that cannot hold.  Different
    constructors at the top make it the distinctness axiom's negation, which
    `negE_gen` closes with the hypothesis.  The *same* constructor means the
    difference is in an argument, so the equality is peeled with that
    constructor's injectivity (`<ty>_<C>_inject` turns `C a = C b` into the
    conjunction of the argument equalities) and the argument that differs is
    refuted in turn.

    Peeling is what rules out a sibling whose pattern differs one level down --
    `dbl (Suc 0)` against `dbl (Suc (Suc n))`, the shape a hole in a datatype as
    shallow as `nat` always leaves.  Isabelle gets there through
    `pat_completeness`'s general case analysis; here it is this recursion, so a
    pair it cannot peel is refused rather than emitted.
    """
    h1, a1 = t1.strip_comb()
    h2, a2 = t2.strip_comb()
    if h1.name != h2.name:
        neq = _distinct_fact(prover, T, t1, t2, g)
        # `negE_gen` closes the goal and leaves one item behind (the goal with
        # the rewritten hypothesis), so the counter moves on even though
        # nothing is left to prove.
        prover.step(u'\u2190 rule negE_gen goal=%d facts=[%d,%d]'
                    % (g, neq, hyp))
        return
    k = next(i for i, (x, y) in enumerate(zip(a1, a2))
             if _patterns_differ(x, y))
    cur = prover.step(u'\u2192 forward %s_%s_inject goal=%d facts=[%d]'
                      % (T.name, h1.name, g, hyp))
    # The k-th conjunct of a right-nested conjunction: `conjD2` walks past
    # the ones before it, and `conjD1` takes it out of the pair it heads --
    # except when it is the last one, where the walk has landed on it.
    for _ in range(k):
        cur = prover.step(u'\u2192 forward conjD2 goal=%d facts=[%d]'
                          % (g, cur))
    if k < len(a1) - 1:
        cur = prover.step(u'\u2192 forward conjD1 goal=%d facts=[%d]'
                          % (g, cur))
    arg_types, _ = h1.get_type().strip_type()
    _refute_equality(prover, arg_types[k], a1[k], a2[k], cur, g)


def _pattern_neq(prover, T, t1, t2, g):
    """A fact that the two patterns `t1` and `t2` are different, in goal `g`.

    Different constructors are the distinctness axiom as it stands: the axiom
    instance *is* the negation, and stating it as a goal of its own first would
    make the step that derives it coincide with that goal -- items are keyed on
    the proposition, so the second one would create nothing and every ID after
    it would be off by one.  Peeling needs a goal of its own (`negI` turns the
    negation into `t1 = t2 ==> false`, `intro` takes the equality as the
    hypothesis, and `_refute_equality` closes it), which is what the `cut`
    below is for.
    """
    if not _patterns_differ(t1, t2):
        raise FunGenError(
            'the patterns %s and %s cannot be told apart: one of them is a '
            'variable where the other carries a constructor, so no branch '
            'rules the other out' % (_prints(t1), _prints(t2)))
    h1, _ = t1.strip_comb()
    h2, _ = t2.strip_comb()
    if h1.name != h2.name:
        return _distinct_fact(prover, T, t1, t2, g)
    c = prover.step(u'cut "%s" goal=%d' % (_prints(Not(Eq(t1, t2))), g))
    c1 = prover.step(u'\u2190 rule negI goal=%d' % c)
    hyp, g2 = prover.ids(u'\u2190 intro goal=%d' % c1, 2)
    _refute_equality(prover, T, t1, t2, hyp, g2)
    return c


def _refute_test(prover, arg_types, pos, eqs, i, j, test, g):
    """A fact that equation j's test at position `pos` fails in branch i.

    The test is refuted from the two patterns' own constructors
    (`_pattern_neq` and `_refute_equality`): this branch's pattern on one side,
    the witness the test binds on the other.  When the test is an equality the
    refutation *is* its negation and is handed out as such; otherwise the
    witness is taken apart first (`elim`) and the equality it leaves behind is
    refuted directly -- that equality is already the one to refute, so nothing
    restates it.

    The fact is a fact of the goal `g` it is handed into, which is what lets
    the caller either rewrite the branch condition with it (one position) or
    use it inside the cut that builds the conjunction's negation (several).
    """
    T = arg_types[pos]
    pat_i = _eq_args(eqs[i])[pos]
    pat_j = _eq_args(eqs[j])[pos]
    # The instantiation of equation j's pattern: its own leaves take the
    # values the test's witness projects to, so a *nested* pattern
    # (`Suc (Suc n)`) is rebuilt whole and not cut down to its top
    # constructor's arguments.
    if not is_exists(test):
        env = {}
    else:
        leaves = _pattern_leaves(pat_j)
        types = [a.get_type() for a in leaves]
        w = Var(_exists_var(test), tupled_type(types))
        w_args = [projection(w, types, k) for k in range(len(types))]
        env = {a.name: t for a, t in zip(leaves, w_args)}
    cj_inst = _subst(pat_j, env)
    if not is_exists(test):
        return _pattern_neq(prover, T, pat_i, cj_inst, g)
    c = prover.step(u'cut "%s" goal=%d' % (_prints(Not(test)), g))
    c1 = prover.step(u'\u2190 rule negI goal=%d' % c)
    ids = prover.ids(u'\u2190 intro goal=%d' % c1, 2)
    eq, g2 = ids[0], ids[1]
    ids = prover.ids(u'\u2192 elim "%s" goal=%d facts=[%d]'
                     % (_exists_var(test), g2, eq), 3)
    # The test's own body is `pat_i = pat_j` with the witness free -- the
    # branch's projection is already written as its own pattern -- so `elim`
    # leaves exactly the equality to refute, and `negE_gen` closes the goal
    # with it (the counter moves on even though nothing is left to prove).
    eq, g2 = ids[1], ids[2]
    _refute_equality(prover, T, pat_i, cj_inst, eq, g2)
    return c


def _condition_negation(prover, names, arg_types, positions, eqs, i, j, g,
                        conds):
    """A fact that equation j's test fails in branch i.

    The two equations' patterns are compared position by position and the
    first position where their constructors differ is the one refuted --
    the position has to be one *both* equations constrain, since a general
    pattern there is not refuted by anything.  If equation j constrains a
    single position its test *is* that refutation and the fact goes
    straight to `if_not_P`.  Otherwise its test is the conjunction of its
    positions, and refuting one conjunct has to become the negation of the
    whole conjunction: `negI` makes the goal `C ==> false`, `intro` takes C
    as a hypothesis, `conjD` takes the refuted conjunct out of it, and
    `negE_gen` closes with the two.
    """
    here = _pattern_positions(_eq_args(eqs[i]), positions)
    poses_j = _pattern_positions(_eq_args(eqs[j]), positions)
    k = None
    for kk, pos in enumerate(poses_j):
        if pos in here and _patterns_differ(_eq_args(eqs[j])[pos],
                                            _eq_args(eqs[i])[pos]):
            k = kk
            break
    if k is None:
        raise FunGenError(
            'the equations %d and %d of this definition do not differ at '
            'any position they both constrain' % (j + 1, i + 1))
    if len(conds) == 1:
        return _refute_test(prover, arg_types, poses_j[0], eqs, i, j,
                            conds[0], g)
    conj = _conj_of(conds)
    c = prover.step(u'cut "%s" goal=%d' % (_prints(Not(conj)), g))
    c1 = prover.step(u'\u2190 rule negI goal=%d' % c)
    ids = prover.ids(u'\u2190 intro goal=%d' % c1, 2)
    hyp, g2 = ids[0], ids[1]
    fact = _refute_test(prover, arg_types, poses_j[k], eqs, i, j, conds[k],
                        g2)
    cur = hyp
    for _ in range(k):
        cur = prover.step(u'\u2192 forward conjD2 goal=%d facts=[%d]'
                          % (g2, cur))
    # The k-th conjunct of a right-nested conjunction: `conjD2` walks
    # past the ones before it, and `conjD1` takes it out of the pair
    # it heads -- except when it is the last one, where the walk has
    # already landed on it.
    if k < len(conds) - 1:
        cur = prover.step(u'→ forward conjD1 goal=%d facts=[%d]'
                          % (g2, cur))
    prover.step(u'\u2190 rule negE_gen goal=%d facts=[%d,%d]'
                % (g2, fact, cur))
    return c


def _test_fact(prover, arg_types, pos, eqs, i, cond, g, dmap, cut=True):
    """Cut one test and prove it from the pattern it came from.

    The test is the pattern against itself: an equality when the pattern
    has no variable, and an existential over the variables otherwise,
    which `inst` turns into that equality with the witness tuple of the
    pattern's own variables.  The reduce closes it exactly when its last
    rewrite leaves an identity.

    Returns the cut's id and, when the test is an existential, the
    instance's proposition and the id `inst` left behind.  That instance
    can be the very proposition the branch's decrease obligation states --
    a pattern whose only variable is the recursive argument (`TriS t`)
    has the instance `C t = C t`, which is its obligation too -- and the
    caller then lets the one item serve both (see `_def_entry`).
    """
    # `cut=False` is a conjunct of a branch test: `conjI` has already left
    # that test as a goal of its own, and cutting it again would state a
    # proposition the goal already has (so the cut would create nothing and
    # the ids after it would be off).
    c = prover.step(u'cut "%s" goal=%d' % (_prints(cond), g)) if cut else g
    if not is_exists(cond):
        prover.step(u'\u2190 rule eq_refl goal=%d' % c, new=0)
        return c, None
    pat = _eq_args(eqs[i])[pos]
    leaves = _pattern_leaves(pat)
    wit = _leaf_tuple(leaves)
    # The witness can be a tuple, so it is quoted: the step parser reads
    # one token for the argument otherwise, and `(Pair a b)` is two.
    c2 = prover.step(u'\u2190 inst "%s" goal=%d' % (_arg_text(wit), c))
    body = cond.arg(wit).beta_norm()
    reduced = _reduce(body, dmap)
    rules = _reduce_used(body, dmap)[1]
    for k, rule in enumerate(rules):
        if k == len(rules) - 1 and reduced.is_reflexive():
            prover.step(u'\u2190 rewrite %s goal=%d' % (rule, c2), new=0)
        else:
            c2 = prover.step(u'\u2190 rewrite %s goal=%d' % (rule, c2))
    if not rules or not reduced.is_reflexive():
        prover.step(u'\u2190 rule eq_refl goal=%d' % c2, new=0)
    return c, (_prints(body), c2)


def _refute_one(prover, arg_types, positions, eqs, i, j, k, test, g):
    """A fact that equation j's test at its k-th position fails in branch i."""
    poses_j = _pattern_positions(_eq_args(eqs[j]), positions)
    return _refute_test(prover, arg_types, poses_j[k], eqs, i, j, test, g)


def _single_test_fact(prover, arg_types, positions, eqs, i, j, k, g, dmap):
    """Cut equation j's test at its k-th position and prove it holds.

    Only the cut's id is returned: the instance a test leaves behind is
    what the *single*-position `_condition_fact` hands on, and a chain with
    several positions never reaches the decrease obligation's own shape
    that way (the guard that reads it only fires with one position).
    """
    poses_j = _pattern_positions(_eq_args(eqs[j]), positions)
    cond = _cond_of(_eq_args(eqs[j])[poses_j[k]],
                    projection(_tuple_of(eqs[i]), arg_types, poses_j[k]),
                    _pos_tag(j, k, len(poses_j)))
    return _test_fact(prover, arg_types, poses_j[k], eqs, j,
                      _reduce(cond, dmap), g, dmap)[0]


def _same_constructor(eqs, positions, i, j, pos):
    """Whether both equations constrain `pos` with the same constructor."""
    return (pos in _pattern_positions(_eq_args(eqs[i]), positions)
            and _constr_name(_eq_args(eqs[j]), pos)
            == _constr_name(_eq_args(eqs[i]), pos))


def _multi_navigation(prover, names, arg_types, positions, eqs, i, g, dmap,
                      conds, last_closes=False):
    """Walk the nested chain to reach equation i's branch.

    Every test of every earlier equation is visited in chain order: one
    whose constructors differ from this branch's is refuted (`if_not_P`),
    one that agrees is *taken* (`if_P` with the pattern's own witness --
    both equations match there, and the chain asks them in order).  Then
    this equation's own tests are taken, which is what its body needs.
    """
    steps = []
    for j in range(i):
        poses_j = _pattern_positions(_eq_args(eqs[j]), positions)
        for k in range(len(poses_j)):
            pos = poses_j[k]
            if _same_constructor(eqs, positions, i, j, pos):
                steps.append((u'take', j, k))
            else:
                steps.append((u'refute', j, k))
    own = (_pattern_positions(_eq_args(eqs[i]), positions)
           if i < len(eqs) - 1 else [])
    for k in range(len(own)):
        steps.append((u'take', i, k))
    for n, (what, j, k) in enumerate(steps):
        last = (n == len(steps) - 1)
        if what == u'take':
            c = _single_test_fact(prover, arg_types, positions, eqs, i, j, k, g,
                                  dmap)
            g = prover.step(u'\u2190 rewrite if_P goal=%d facts=[%d]' % (g, c),
                            new=0 if (last and last_closes) else 1) or g
        else:
            neg = _refute_one(prover, arg_types, positions, eqs, i, j, k,
                              conds[i][j][k], g)
            g = prover.step(u'\u2190 rewrite if_not_P goal=%d facts=[%d]'
                            % (g, neg),
                            new=0 if (last and last_closes) else 1) or g
    return g


def _condition_fact(prover, arg_types, positions, eqs, i, conds, g, dmap):
    """Cut the branch's own tests and prove them from the pattern.

    With one position there is a single test and the cut *is* the fact
    `if_P` wants.  With several the branch's condition is the conjunction
    of the tests, so it is cut once and proved conjunct by conjunct
    (`conjI` states the two halves; the goals it leaves are the tests
    themselves, each proved the way a single one is).

    Returns what `_test_fact` returns: the cut's id and the instance the
    single test left behind, which a decrease obligation of the same
    branch may be.  A conjunction of several tests is its own instance.
    """
    poses = _pattern_positions(_eq_args(eqs[i]), positions)
    if len(poses) == 1:
        return _test_fact(prover, arg_types, poses[0], eqs, i, conds[0],
                          g, dmap)
    conj = _conj_of(conds)
    c = prover.step(u'cut "%s" goal=%d' % (_prints(conj), g))
    _prove_conj(prover, arg_types, positions, eqs, i, conds, c, dmap)
    return c, None


def _prove_conj(prover, arg_types, positions, eqs, i, conds, g, dmap):
    """Prove a right-nested conjunction of tests, left to right.

    Conjunct k is the test of position k of the equation's own constraining
    positions, which is the order `branch_condition` builds them in.
    """
    poses = _pattern_positions(_eq_args(eqs[i]), positions)
    if len(conds) == 1:
        _test_fact(prover, arg_types, poses[0], eqs, i, conds[0], g, dmap,
                   cut=False)
        return
    ids = prover.ids(u'\u2190 rule conjI goal=%d' % g, 2)
    _test_fact(prover, arg_types, poses[0], eqs, i, conds[0], ids[0], dmap,
               cut=False)
    _prove_conj(prover, arg_types, positions, eqs, i, conds[1:], ids[1], dmap)


def _proj_term(arg_types, r, t):
    """Projection of component r, as a term (identity for one argument)."""
    return projection(t, arg_types, r) if len(arg_types) > 1 else t


def _proj_const(arg_types, r):
    """The projection as a plain function, for `wf_measure_gen`'s map.

    Two arguments is the emitter's limit.  The relation side is
    arity-generic (the `wf` obligations of three-argument definitions
    replay VALID), but the equation proofs are not.  Measured on
    `foldr_def_1` with the guard off, the goal after the emitted sweeps is

        if [] = [] then z
        else f (hd []) (cut foldr_in foldr_rel ... (Pair f (Pair z (tl [])))) = z

    -- the condition is reduced, but the else branch carries `hd []` and
    `tl []`, which nothing reduces (`hd`/`tl` are the library's partial
    destructors: one equation each, none for `nil`), and the emitted
    sequence asks for one `fst_def_1` more than the goal still offers.  So
    the remaining work is to make `_sweep_once` match the tactic exactly --
    including the `beta_norm_conv` that follows every sweep
    (`tactic/steps.py:264`) -- and to settle what the sequence does with
    the parts of the branch that `if_P`/`if_not_P` is about to discard.
    """
    if len(arg_types) <= 2:
        return Const('fst' if r == 0 else 'snd',
                     TFun(tupled_type(arg_types), arg_types[r]))
    p = Var('p', tupled_type(arg_types))
    return Lambda(p, _proj_term(arg_types, r, p))


def _has_theorem(name):
    """Whether a theorem is in the theory yet (generated names may not be)."""
    from kernel import theory
    try:
        theory.get_theorem(name)
        return True
    except Exception:
        return False


def _destructor_map(T):
    """{destructor constant: (constructor, position, rule theorem)} for T.

    Built from the constructors the theory registered plus the naming the
    datatype layer uses (`core/datgen.py`): the library's own destructors
    for nat, list and prod, and the generated `T_C_n` for everything else.
    A position whose rule theorem is not in the theory contributes
    nothing, so the emitter reports the missing destructor at the
    constructor that needs it instead of citing a name that is not there.
    """
    from core import datgen
    from kernel import theory
    res = {}
    constrs = _registered_constrs(T)
    if constrs is None:
        return res
    for constr in constrs:
        argT = datgen.constr_args(constr)[0]
        for j in range(len(argT)):
            dname, rule = datgen.destructor_names(T.name, constr['name'], j)
            if not _has_theorem(rule):
                # The library names this position with the function being
                # defined (`tl`, `Pre`, `fst`): while that function is
                # emitted its rule is not in the theory yet, and the body
                # is written with the generated destructor instead.
                dname, rule = datgen.generated_destructor_names(
                    T.name, constr['name'], j)
                if not _has_theorem(rule):
                    continue
            res[dname] = (constr['name'], j, rule)
    return res


def _destructor_maps(arg_types, positions, lhs=None):
    """The destructor map for a definition's arguments.

    Both ends are needed: every recursion position's own destructors
    (`Pre`, `hd`, ...) and the tuple's (`fst`, `snd`), since the emitted
    bodies mention both.

    A pattern with several variables (`Plus a1 a2`) is a third end: its
    branch test is an existential over the tuple of those variables, and
    `_test_fact` takes that witness apart with the product's projectors.
    Whether the argument tuple is a product does not decide it -- `fun
    <ty>_size :: aexp ⇒ nat` matches `Plus a1 a2` with one argument -- so
    the patterns are read when `lhs` is given.
    """
    positions = _as_positions(positions)
    res = {}
    for r in positions:
        res.update(_destructor_map(arg_types[r]))
    if len(arg_types) > 1:
        res.update(_destructor_map(tupled_type(arg_types)))
    for args in lhs or []:
        for r in positions:
            try:
                leaves = _pattern_leaves(args[r])
            except FunGenError:
                continue          # the pattern is a variable: no tuple
            if len(leaves) > 1:
                res.update(_destructor_map(
                    tupled_type([v.T for v in leaves])))
                break
    return res


def destructor(constr_name, j, t):
    """The j-th argument of a constructor pattern, as a term in t."""
    from core import datgen
    from kernel import theory
    T = t.get_type()
    dname, rule = datgen.destructor_names(T.name, constr_name, j)
    if not _has_theorem(rule):
        # Same case as in `_destructor_map`: the library's name for this
        # position is the function being defined, whose rule does not
        # exist yet; the generated destructor does.
        dname, rule = datgen.generated_destructor_names(T.name, constr_name, j)
    try:
        theory.get_theorem(rule)
    except Exception:
        raise FunGenError(
            "no destructor for argument %d of constructor %s on %s; the "
            "datatype layer generates one per constructor argument "
            "(core/datgen.py) unless the constructor cannot be written "
            "unambiguously in the theory"
            % (j + 1, constr_name, printer.print_type(T)))
    argT = None
    for constr in (_registered_constrs(T) or []):
        if constr['name'] == constr_name:
            argT = datgen.constr_args(constr)[0]
    if argT is None:
        raise FunGenError('constructor %s is not registered for %s'
                          % (constr_name, printer.print_type(T)))
    return Const(dname, TFun(T, argT[j]))(t)


def _decrease_prop(arg_types, r, tcall, t):
    """The decrease obligation, in the shape the goal's condition has.

    The relation is applied to the projection terms without reducing them:
    that is exactly the form the goal's relation condition takes, and the
    projection rules are applied inside the obligation's own proof.
    Unfolding the relation inside the goal instead would leave a beta redex
    the later rewrites cannot see through.
    """
    T = arg_types[r]
    call = _proj_term(arg_types, r, tcall)
    pat = _proj_term(arg_types, r, t)
    return _prints(_relation(T)(call)(pat).beta_norm())


def _branch_body(name, arg_types, res_type, eq, positions, tup):
    """One equation's right hand side as the body functional writes it."""
    g = Var('g', TFun(tupled_type(arg_types), res_type))
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    return replace(eq.rhs, f_const, len(arg_types),
                   variable_env(_eq_args(eq), positions, tup), g)


def _decrease_witness(T, constrs, pairs, pattern, call, dmap):
    """The pattern's own terms for the disjunct's witness, as one tuple.

    The disjunct binds one witness for the constructor's non-recursive
    arguments; the pattern's terms at those positions are that witness,
    reduced, because the goal has them reduced by then and a reduced
    witness adds no redex the emitted sequence would have to clear.  A
    disjunct with no such argument -- `Suc`'s only argument is the
    recursive one -- has no witness, so there is nothing to instantiate.
    """
    head, args = pattern.strip_comb()
    if not head.is_const():
        return None
    want = _reduce(call, dmap)
    for i, j in pairs:
        if constrs[i]['name'] != head.name or j >= len(args):
            continue
        if args[j] == want or _reduce(args[j], dmap) == want:
            free = [a for k, a in enumerate(args) if k != j]
            if not free:
                return None
            return tupled_arg([_reduce(a, dmap) for a in free])
    return None


def _exists_body(t):
    """The body of `?x. t`, or None when `t` is not an existential.

    `Exists` is the constant applied to a lambda, and the disjunct's
    witness is that lambda's variable: giving a witness means substituting
    into the body, which is what `inst` does at replay time.
    """
    if not t.is_comb():
        return None
    h, args = t.strip_comb()
    if h.is_const() and h.name == 'exists' and len(args) == 1:
        return args[0]
    return None


def _disjunct_index(constrs, pairs, pattern, call, dmap):
    """Which disjunct of the subterm relation holds for this call.

    The relation is the disjunction over the datatype's recursive
    constructor arguments, and a call sits at exactly one of them: the
    pattern's own constructor, with the call at one of its recursive
    positions.  The index is read off the pattern -- the same match
    `_decrease_witness` makes, so the two agree on which disjunct this is
    -- and it is what the `disjI` chain walks to.  Nothing is tried.
    """
    head, args = pattern.strip_comb()
    if not head.is_const():
        return None
    want = _reduce(call, dmap)
    for k, (i, j) in enumerate(pairs):
        if constrs[i]['name'] != head.name or j >= len(args):
            continue
        if args[j] == want or _reduce(args[j], dmap) == want:
            return k
    return None


def _disjunct_chain(n, k):
    """The introductions that reach the k-th disjunct of an n-way chain.

    The relation's disjunction is right-nested, so every disjunct but the
    last is `disjI2` once per level it is nested under and `disjI1` on
    itself.  The last one is `disjI2` all the way down and has no
    `disjI1` of its own: emitting one there asks the goal to split a
    disjunct that is already the whole goal.
    """
    if k == n - 1:
        return ['rule disjI2'] * k
    return ['rule disjI2'] * k + ['rule disjI1']


def _disjunct_instance(T, constrs, pairs, k, call, pat, witness):
    """The k-th disjunct as the goal carries it once the witness is given.

    This is the proposition `inst` leaves behind, built here so that the
    steps after it are computed from the very term the goal has: the
    projections are *not* reduced, because reducing them is what those
    steps do.

    The disjunct's two tuple variables are replaced *before* the witness
    goes in, and the order is not a matter of taste: the witness is built
    from the pattern's own variables, and `_disjunct` names its variables
    `a` and `b`, which a pattern may use itself -- `While b I c` does, and
    its `b` has a different type from the variable being abstracted, so
    abstracting over the witness first is refused ("wrong type") and would
    silently capture if the types happened to agree.
    """
    from core import datgen
    d = datgen._disjunct(T, constrs, pairs[k])
    a, b = Var('a', T), Var('b', T)
    body = Lambda(a, Lambda(b, d))(call)(pat).beta_norm()
    if witness is None:
        return body
    binder = _exists_body(body)
    if binder is None:
        return None
    return binder.subst_bound(witness)


def _decrease_steps(arg_types, r, tcall, eq, dmap, seen=None):
    """The steps that prove one recursive call's decrease obligation.

    The obligation is the relation applied to the call and to the
    equation's own pattern.  A datatype with one recursive constructor
    argument has the identity-shaped relation `b = C a`, and the sequence
    is the projection rewrites, the witness and the identity, exactly as
    it always was.  More than one makes the relation a disjunction, and
    the sequence then also walks to the disjunct this call occupies.

    In that case the witness is given *before* the projections are
    reduced, so that the reductions close the goal: a goal closed by a
    rewrite creates no item, while an instantiated identity left over as
    an item is one both calls of an equation land on (`Plus a1 a2 = Plus
    a1 a2`, from either side).  The stable-ID layer keys items by
    proposition, so the second call's goal would vanish into the first
    one's already-closed item and the step after it would have nothing to
    rewrite.

    `seen` collects the instances the emitted proof has already produced.
    A call whose instance is already there ends at its own `inst`, which
    resolves the goal to that item and creates nothing; the caller owns
    the set, so the calls of one equation see each other's.
    """
    from core import datgen
    T = arg_types[r]
    pattern = _eq_args(eq)[r]
    tree = _tuple_of(eq)
    call = _proj_term(arg_types, r, tcall)
    pat = _proj_term(arg_types, r, tree)
    constrs = _registered_constrs(T)
    pairs = datgen.subterm_pairs(T, constrs)
    if len(pairs) == 1:
        disj = _relation(T)(call)(pat).beta_norm()
        proj = _reduce_used(disj, dmap)[1]
        closes = _reduce(disj, dmap).is_reflexive()
        steps = ['rewrite %s' % rule for rule in proj]
        if not closes:
            witness = _decrease_witness(T, constrs, pairs, pattern, call, dmap)
            if witness is None and _exists_body(disj) is not None:
                # The pattern is not one of the constructor's immediate
                # arguments (`Plus (Plus a b) c`, with the call on `b`):
                # the disjunct binds a witness the pattern cannot give, so
                # the obligation cannot be discharged.  Saying so keeps the
                # definition's axioms instead of emitting a proof whose
                # `eq_refl` has nothing to close.
                raise FunGenError(
                    'recursion: the call %s is not an immediate subterm of '
                    'the pattern %s, so the relation built for %s cannot '
                    'reach it' % (_prints(call), _prints(pattern), _printt(T)))
            if witness is not None:
                steps.append('inst "%s"' % _arg_text(witness))
            steps.append('rule eq_refl')
        elif not proj:
            # Recursion on a single argument: the projections are the
            # identity, so no projection rule applies and the obligation
            # already reads `t = t`.  It still needs its closing step --
            # `closes` only says the last rewrite closes the goal, and
            # there is no rewrite here.
            steps.append('rule eq_refl')
        return steps, closes or steps[-1] == 'rule eq_refl'
    k = _disjunct_index(constrs, pairs, pattern, call, dmap)
    if k is None:
        raise FunGenError(
            'recursion: no disjunct of the subterm relation of %s states '
            'that the call %s is a subterm of the pattern %s'
            % (_printt(T), _prints(call), _prints(pattern)))
    witness = _decrease_witness(T, constrs, pairs, pattern, call, dmap)
    body = _disjunct_instance(T, constrs, pairs, k, call, pat, witness)
    steps = _disjunct_chain(len(pairs), k)
    if witness is not None:
        steps.append('inst "%s"' % _arg_text(witness))
    if seen is not None and body in seen:
        # The instance is already an item of this proof, so `inst` resolves
        # the goal to it and creates nothing: the obligation is discharged
        # by the step just emitted and the proof stops there.
        return steps, True
    if seen is not None:
        seen.add(body)
    reduced, proj = _reduce_used(body, dmap)
    steps.extend('rewrite %s' % rule for rule in proj)
    if not reduced.is_reflexive():
        raise FunGenError(
            'recursion: the decrease obligation %s of %s does not reduce to '
            'an identity' % (_prints(reduced), _prints(pattern)))
    if not proj:
        # No projection to reduce: the instantiated disjunct already reads
        # `t = t`, and only the reflexivity rule closes it.
        steps.append('rule eq_refl')
    return steps, True


def _body_term(name, arg_types, res_type, eqs, positions, p=None):
    """The `<c>_H g p = ...` right hand side, as a term.

    The equations are read in source order, so the body is the chain

        if c_1 then b_1 else (if c_2 then b_2 else ... else b_n)

    where `c_i` tests the pattern of equation i and `b_i` is its right hand
    side.  With one equation there is no test at all, and the chain is
    built from the last equation backwards so the two-equation case reads
    exactly as it always did.

    With p omitted the body is built over the tuple variable (the def
    item); passing a literal tuple gives the shape the goal takes for
    that equation, which is what decides the projection/destructor
    rewrites its proof needs.
    """
    Tup = tupled_type(arg_types)
    positions = _as_positions(positions)
    if len(positions) > 1:
        return _nested_body(name, arg_types, res_type, eqs, positions, p)
    if p is None:
        p = Var('p', Tup)
    lhs = [_eq_args(eq) for eq in eqs]
    body = _branch_body(name, arg_types, res_type, eqs[-1], positions, p)
    for i in range(len(eqs) - 2, -1, -1):
        b = _branch_body(name, arg_types, res_type, eqs[i], positions, p)
        cond = branch_condition(lhs[i], positions, p, i)
        body = Const('IF', TFun(BoolType, TFun(
            res_type, TFun(res_type, res_type))))(cond)(b)(body)
    return body


def _nested_body(name, arg_types, res_type, eqs, positions, p=None):
    """The body functional as a chain of one test per (equation, position).

    A definition that matches on several arguments takes a branch when all
    of its positions match.  The chain says so by *nesting* the tests
    rather than conjoining them:

        if t_1 then (if t_2 then b_i else rest) else rest

    Each step of a proof is then a single test -- `if_P` where it holds for
    the equation's own tuple, `if_not_P` where the constructors differ --
    which is the machinery the single-position chain already has, and every
    step's item count is the fixed one that machinery was calibrated with.
    A conjunction would need a step that closes a contradiction, and that
    step creates one item or none depending on the proof state.
    """
    Tup = tupled_type(arg_types)
    if p is None:
        p = Var('p', Tup)
    lhs = [_eq_args(eq) for eq in eqs]
    ifty = TFun(BoolType, TFun(res_type, TFun(res_type, res_type)))

    def chain(i):
        body = _branch_body(name, arg_types, res_type, eqs[i], positions, p)
        if i == len(eqs) - 1:
            return body
        rest = chain(i + 1)
        poses = _pattern_positions(lhs[i], positions)
        for k in range(len(poses) - 1, -1, -1):
            pos = poses[k]
            cond = _cond_of(lhs[i][pos], projection(p, arg_types, pos),
                            _pos_tag(i, k, len(poses)))
            body = Const('IF', ifty)(cond)(body)(rest)
        return body

    return chain(0)


def _body_prop(name, arg_types, res_type, eqs, positions, p=None):
    """The `<c>_H g p = ...` right hand side, printed."""
    return _prints(_body_term(name, arg_types, res_type, eqs, positions, p))


def _rel_body(arg_types, r, order=None, relation=None):
    """The relation as a lambda over the tuple variables p and q.

    The def's right hand side is the whole lambda: `wf <c>_rel` is
    unfolded by rewriting the unapplied constant, which only works if the
    definitional equation is `c_rel = (%p. %q. ...)`.

    `relation` is the relation the user wrote: it *is* the definitional
    right hand side, as it stands, so that the obligations stated with it
    are the obligations the unfolded goal has.

    `order` is the measure chain the search kept: the body is then the
    `mlex_prod` chain over it, ending at the empty relation.  An empty
    order is a definition with no recursive call, which descends nowhere;
    its relation is the empty one, well founded by `wf_false`, and every
    obligation is vacuous -- the only relation its own projections (`the`,
    `fst`, `snd`) can have, since their destructor is the function being
    defined.  None keeps the datatype's subterm relation, lifted through
    the projection, which is what a definition the measures cannot express
    descends through.
    """
    Tup = _printt(tupled_type(arg_types))
    if relation is not None:
        return _prints(relation)
    if order is not None:
        # The chain is already a function of the two tuples, so it is the
        # definitional right hand side as it stands.  Wrapping it in
        # `%p. %q. ... p q` would leave the unfoldings with a lambda where
        # the rules state `mlex_prod f R` (`wf_mlex`) or a plain
        # application (the equation's condition), and neither matcher sees
        # through that: `rule` compares the conclusion with the goal.
        return _measure_chain_text(arg_types, order)
    T = arg_types[r]
    p = Var('p', tupled_type(arg_types))
    q = Var('q', tupled_type(arg_types))
    body = _relation(T)(_proj_term(arg_types, r, p))(
        _proj_term(arg_types, r, q)).beta_norm()
    return "%%p::%s. %%q::%s. %s" % (Tup, Tup, _prints(body))


def _wf_fact(prover, cname, arg_types, g):
    """Derive `wf <c>_rel` as a fact of the surrounding goal.

    A cut plus the theorem, rather than a forward step: the theorem is
    polymorphic, and forwarding it would leave its type variables
    unmatched.  The cut's proposition carries the ascription that pins
    them, and the theorem's conclusion is exactly that proposition, so
    the rule closes it.
    """
    c = prover.step('cut "%s" goal=%d' % (_rel_wf_prop(cname, arg_types), g))
    prover.step('← rule %s_rel_wf goal=%d' % (cname, c), new=0)
    return c


def _in_def_fact(prover, cname, arg_types, res_type, g):
    """Derive the fixpoint equation as a fact, the same way."""
    c = prover.step('cut "%s" goal=%d'
                    % (_in_def_prop(cname, arg_types, res_type), g))
    prover.step('← unfold %s_in_def goal=%d' % (cname, c), new=0)
    return c


def _emit_closing(prover, closing, g, lines=False):
    """Write the last steps of a comparison: a tree of cuts and rules.

    Returns the stable ID of the fact that closes `g`, which is not always
    `g` itself.  A `rule` closes its goal in place when the fact it derives
    is the goal's own theorem, and lays out a line when that fact is a
    *different* theorem: the fact then gets a new ID and the goal's is
    consumed.  The second case is an induction branch, where the goal
    carries the branch's hypotheses and a comparison lemma's conclusion
    carries none; `_def_entry`'s goals have no hypotheses, so there the
    two coincide.  `lines` says which of the two this proof is, because
    the difference is not visible in the step itself.

    The distinction reaches up the tree: a cut node closes its goal with
    the fact the node below it produced, so the `facts=[...]` the outer
    rule takes has to name *that* fact -- the cut's own ID is consumed by
    the rule below whenever that rule laid out a line.
    """
    if closing.kind == 'rule':
        if lines:
            return prover.step('← rule %s goal=%d' % (closing.theorem, g))
        prover.step('← rule %s goal=%d' % (closing.theorem, g), new=0)
        return g
    c = prover.step('cut "%s" goal=%d' % (closing.prop, g))
    fact = _emit_closing(prover, closing.sub, c, lines)
    if lines:
        return prover.step('← rule %s goal=%d facts=[%d]'
                           % (closing.theorem, g, fact))
    # The premise here is the cut's own goal, whose hypotheses are the
    # goal's, so the fact this rule derives *is* the goal's theorem and
    # the step closes in place.
    prover.step('← rule %s goal=%d facts=[%d]' % (closing.theorem, g, fact),
                new=0)
    return g


def _measure_obligation(prover, order, arg_types, call, pat, dmap, sizes, mdefs,
                        g, name, i, lines=False):
    """One recursive call's decrease, walked through the measure chain.

    The call is discharged at the first column where it strictly
    decreases, so the walk is the columns up to and including that one.
    Each column's cell is stated and proved first -- the cell is what the
    rule for that column takes as a premise, and it has to be the very
    proposition the rule states (`mlex_leq`'s `f x <= f y`), so it is cut
    with the measure applied the way the relation applies it and the
    proof starts by beta-reducing that application.

    The chain is then built from the strict column outward: `mlex_less`
    needs only the strict cell, and every weaker column before it needs
    its cell plus the relation of the tail.  The outermost cut is the
    equation's own obligation, which is what discharges the condition
    `cut_def` leaves in the equation's goal.
    """
    walk = measure.row(order, call, pat, dmap, sizes, mdefs)
    if walk is None:
        raise FunGenError(
            'fun %s: the measure order does not discharge the recursive '
            'call of equation %d' % (name, i + 1))
    cell_facts = []
    for _, c in walk:
        cell = prover.step('cut "%s" goal=%d' % (c.prop, g))
        cur = cell
        if c.beta:
            cur = prover.step('← beta goal=%d' % cur)
        for step in c.steps:
            cur = prover.step('← rewrite %s goal=%d' % (step, cur))
        _emit_closing(prover, c.closing, cur, lines)
        cell_facts.append(cell)
    call_text, pat_text = _arg_text(call), _arg_text(pat)
    tail = None
    for j in range(len(walk) - 1, -1, -1):
        chain = _measure_chain_text(arg_types, order, j)
        c = prover.step('cut "%s %s %s" goal=%d'
                        % (chain, call_text, pat_text, g))
        if j == len(walk) - 1:
            prover.step('← rule mlex_less goal=%d facts=[%d]'
                        % (c, cell_facts[j]), new=0)
        else:
            prover.step('← rule mlex_leq goal=%d facts=[%d,%d]'
                        % (c, cell_facts[j], tail), new=0)
        tail = c
    return tail


# ---------------------------------------------------------------------------
# Coverage: the exhaustive disjunction over the equations' patterns.
# ---------------------------------------------------------------------------


_OUT = object()
"""An equation a split ruled out: its pattern names another constructor."""


def _constr_pattern(t):
    """Whether `t` is a constructor of its type applied to arguments.

    A plain variable is the *general* pattern -- the equation it belongs to
    constrains nothing at that spot -- and a split there has to keep every
    equation, which is what separates the two.
    """
    h, _ = t.strip_comb()
    if h.is_var():
        return False
    constrs = _constr_names(t.get_type())
    return constrs is not None and h.name in constrs


def _pred_names():
    """Names to offer the induction rule's predicate, in order."""
    yield 'P'
    for i in itertools.count(1):
        yield 'P%d' % i


def _case_var_names():
    """Names to offer the case rule's variable, in order.

    The datatype case rule calls it `x` and the induction rule here calls
    it `p`; the parameters of a definition are usually one of those, so
    the numbered variants are what a definition over a variable `p` gets.
    """
    yield 'p'
    yield 'x'
    for i in itertools.count(1):
        yield 'p%d' % i


def _pattern_vars_in(args):
    """The Vars a pattern's arguments bind, in order of appearance.

    A nullary constructor binds nothing and a nested one binds its own
    arguments, in order.  This is the order the disjunct's `?` prefix lists
    the variables in, and therefore the order the leaf's `inst` steps have
    to consume them in: `inst` takes the outermost binder first.
    """
    res = []
    for a in args:
        if a.is_var():
            res.append(a)
        elif a.is_const() and not a.strip_comb()[1]:
            continue
        else:
            res.extend(_pattern_vars_in(a.strip_comb()[1]))
    return res


def _coverage_prop(lhs, p):
    """`(?v_1. p = P_1) | ... | (?v_n. p = P_n)`, right-nested.

    One disjunct per equation, in source order, each binding exactly the
    variables its pattern has.  The disjunction says that `p` is *some*
    instance of one of the patterns, which is what the induction rule's
    case split consumes: a disjunct gives one branch, with the equation
    `p = <pattern>` to rewrite the goal by.
    """
    res = None
    for args in reversed(lhs):
        body = Eq(p, tupled_arg(args))
        for v in reversed(_pattern_vars_in(args)):
            body = Exists(v, body)
        res = body if res is None else Or(body, res)
    return res


def _induct_prop(arg_types, lhs, calls, P=None):
    """`(!v_1. <IH_1> --> P P_1) --> ... --> (!p. P p)`, the induction rule.

    One premise per equation: quantify the pattern's variables, put the
    induction hypothesis `P <call>` of each recursive call of the equation
    in front, and conclude `P <pattern>`.  The rule's conclusion is about
    an arbitrary `p`, so a proof by induction is `rule <c>_induct`, and the
    premises are exactly the obligations the branches of that proof leave:
    a branch for an equation with no call is discharged by its own premise,
    one with calls needs the hypotheses first.

    This is Isabelle's `f.induct` (`Function/induction_schema.ML`,
    `mk_ind_goal`), specialised to the case it does not need a sum type
    for: every equation's premise is about the same tuple type, so the
    "sum of branch predicates" collapses to a conjunction of implications
    and the case split is a disjunction over the patterns rather than a
    `sumcases`.
    """
    Tup = tupled_type(arg_types)
    if P is None:
        P = Var('P', TFun(Tup, BoolType))
    prems = []
    for i, args in enumerate(lhs):
        body = P(tupled_arg(args))
        for t in reversed(calls[i]):
            body = Implies(P(t), body)
        for v in reversed(_pattern_vars_in(args)):
            body = Forall(v, body)
        prems.append(body)
    res = Forall(Var('p', Tup), P(Var('p', Tup)))
    for pre in reversed(prems):
        res = Implies(pre, res)
    return res


def _cases_prop(lhs, P, p):
    """`(⋀v̄₁. P P₁) ⟹ ... ⟹ P p`, one premise per equation.

    A datatype's case rule has this shape (`defcheck.datatype_axioms`):
    the predicate is a variable the consumer instantiates with the goal,
    and the conclusion is about an arbitrary `p`.  Each premise binds
    exactly the variables its pattern has, so a branch of the rule is the
    goal at one clause of the definition, and instantiating the premise's
    variables is what turns it into that branch.
    """
    prems = []
    for args in lhs:
        body = P(tupled_arg(args))
        for v in reversed(_pattern_vars_in(args)):
            body = Forall(v, body)
        prems.append(body)
    res = P(p)
    for pre in reversed(prems):
        res = Implies(pre, res)
    return res


def _cases_entry(cname, arg_types, eqs, lhs):
    """The `<c>_cases` item: the definition's own case rule and its proof.

    `(⋀v̄₁. P P₁) ⟹ ... ⟹ (⋀v̄ₙ. P Pₙ) ⟹ P p`

    A datatype states the same theorem for its constructors
    (`defcheck.datatype_axioms`), and the same consumer reads both: the
    `type_cases` method with `cases_thm` naming this theorem instead of
    the type's own.  The difference is what the branches are -- the
    *definition's* clauses, nested patterns and the `= undefined` equation
    of a hole included, rather than the constructor list -- which is what
    a proof about the function wants and what a datatype split cannot give
    (`drop2`'s `Suc 0` is a branch of its own here and none at all there).

    The proof reads the coverage disjunction the other way round:
    `<c>_exhaustive` gives `p` as some instance of a pattern, `disjE` and
    `elim` hand each branch that equation and the pattern's variables, and
    the branch's premise is applied at exactly those variables -- the
    `inst` + `apply_prev` closing the induction rule's own branches use.
    """
    Tup = tupled_type(arg_types)
    ng = len(eqs)
    # The predicate's name and the case variable's have to be names no
    # equation uses: they are free in the statement, and a pattern variable
    # of the same name would shadow them inside its premise.
    taken = set()
    for eq in eqs:
        for v in eq.get_vars():
            taken.add(v.name)
    pred_name = next(c for c in _pred_names() if c not in taken)
    pname = next(c for c in _case_var_names() if c not in taken)
    P = Var(pred_name, TFun(Tup, BoolType))
    p = Var(pname, Tup)
    lines = ['theorem %s_cases' % cname,
             '  fixes %s' % _typenames([P, p]),
             '  prop %s' % _prints(_cases_prop(lhs, P, p)),
             'proof']
    prover = _Proof()
    names = _Names()
    # The branch's `elim`s take their names from the pattern's variables,
    # with `_Names` appending a count: a variable `P` is handed `P1`, `P2`,
    # ... -- and one of those may be the name the predicate itself took
    # (`filter` binds its predicate as `P`).  Counting the statement's own
    # allocations as done is what keeps the two apart; the preemption
    # `_induct_entry` does is the same rule, spelled out as a range.
    for nm in (pred_name, pname):
        base = nm.rstrip('0123456789')
        if base != nm:
            names.used[base] = max(names.used.get(base, 0),
                                   int(nm[len(base):]))
    # The premises are the branch goals the rule leaves, and in this proof
    # they are facts: one per equation, in source order, at IDs 1..ng.
    g = prover.ids('\u2190 intro goal=0', ng + 1)[-1]
    prem = list(range(1, ng + 1))
    d = prover.step('\u2192 forward %s_exhaustive param_p=%s goal=%d'
                    % (cname, pname, g))

    def one(goal, exf, k):
        """Equation k: `exf` states its disjunct, `goal` is `P p`."""
        env = {}
        pvars = _pattern_vars_in(lhs[k])
        for v in pvars:
            nm = names.alloc(v.name)
            env[v.name] = Var(nm, v.T)
            e = prover.ids('elim %s goal=%d facts=[%d]' % (nm, goal, exf), 3)
            exf, goal = e[1], e[2]
        # The premise instantiated at the branch's own variables is the
        # goal's proposition after the equation has been used, so the
        # rewrite that substitutes it closes the goal on that item by
        # itself and lays out no line of its own.
        inst = prem[k]
        for v in pvars:
            inst = prover.step('\u2190 inst "%s" goal=%d facts=[%d]'
                               % (env[v.name].name, goal, inst))
        prover.step('\u2190 rewrite source=prev goal=%d facts=[%d]'
                    % (goal, exf), new=0)

    def split(goal, d, k, n):
        """`d` states `D_k ∨ ... ∨ D_{k+n-1}`; `goal` is `P p`."""
        if n == 1:
            return one(goal, d, k)
        two = prover.ids('\u2190 rule disjE goal=%d facts=[%d]' % (goal, d), 2)
        f1 = prover.ids('\u2190 intro goal=%d' % two[0], 2)
        one(f1[1], f1[0], k)
        f2 = prover.ids('\u2190 intro goal=%d' % two[1], 2)
        split(f2[1], f2[0], k + 1, n - 1)

    split(g, d, 0, ng)
    lines.extend(prover.text())
    lines.append('qed')
    return lines


def _coverage_entry(cname, arg_types, eqs, lhs):
    """The `<c>_exhaustive` item: every input is one of the patterns.

    The split walks the *patterns*, not the input: `type_cases` on the
    tuple, then on each position whose patterns are not all variables, and
    down into the arguments of the constructor a branch chose.  A leaf
    realises exactly one equation -- `_complete_equations` has subtracted the
    patterns apart before the emission sees them -- so that equation's
    disjunct is reached with `disjI`, its pattern's variables are given as
    the witnesses the split recorded, and `eq_refl` closes.

    This is the completeness half of Isabelle's pattern check
    (`Function/pat_completeness.ML`, `prove_completeness`), the same
    routine `Function/induction_schema.ML` reuses to split its induction
    schema.  It is a mechanism on purpose, not a proof written once: the
    induction rule and pattern completeness are two consumers of it.
    """
    Tup = tupled_type(arg_types)
    p = Var('p', Tup)
    lines = ['theorem %s_exhaustive' % cname,
             '  fixes p :: %s' % _printt(Tup),
             '  prop %s' % _prints(_coverage_prop(lhs, p)),
             'proof']
    prover = _Proof()
    names = _Names()

    def leaf(goal, alive, envs):
        cands = [i for i in range(len(eqs)) if alive[i]]
        if len(cands) != 1:
            raise FunGenError(
                'fun %s: %d equations match the same input; the coverage '
                'split needs exactly one branch per input, so the patterns '
                'have to be pairwise disjoint'
                % (cname, len(cands)))
        i = cands[0]
        for rule in _disjunct_chain(len(eqs), i):
            goal = prover.step('%s goal=%d' % (rule, goal))
        for v in _pattern_vars_in(_eq_args(eqs[i])):
            goal = prover.step('inst "%s" goal=%d'
                               % (_arg_text(envs[i][v.name]), goal))
        prover.step('rule eq_refl goal=%d' % goal, new=0)

    def split(goal, spots, alive, envs):
        """Close `goal` by splitting `spots`.

        spots -- (term, pats) pairs still to split.  `pats[i]` is equation
                 i's pattern there: a term, `_OUT` when an earlier split
                 ruled the equation out, None when the equation's pattern
                 never reached this spot (its parent was a variable).
        alive -- per equation, whether it is still a candidate.
        envs  -- per equation, the value each of its pattern variables has
                 taken.  The spot's term is that value: the split replaced
                 it by the constructor application, so no term has to be
                 rebuilt for the leaf's `inst` steps.
        """
        if not spots:
            return leaf(goal, alive, envs)
        t, pats = spots[0]
        if not any(x is not _OUT and x is not None and _constr_pattern(x)
                   for x in pats):
            # Nothing here tells the equations apart: a pattern variable
            # takes the whole term as it stands.
            for i, x in enumerate(pats):
                if x is not None and x is not _OUT and x.is_var():
                    envs[i][x.name] = t
            return split(goal, spots[1:], alive, envs)
        constrs = _registered_constrs(t.get_type())
        if not constrs:
            raise FunGenError(
                'fun %s: the pattern at %s is not a constructor pattern of '
                'a datatype' % (cname, _prints(t)))
        ids = prover.ids('type_cases %s goal=%d' % (t.name, goal),
                         len(constrs))
        for k, constr in enumerate(constrs):
            g = ids[k]
            argT, _ = constr['type'].strip_type()
            nms = [names.alloc('u') for _ in argT]
            if nms:
                g = prover.ids('intro "%s" goal=%d' % (', '.join(nms), g),
                               len(nms) + 1)[-1]
            targs = [Var(nm, Ty) for nm, Ty in zip(nms, argT)]
            term = Const(constr['name'], constr['type'])(*targs)
            sub_alive = list(alive)
            sub_envs = [dict(e) for e in envs]
            # One spot per argument of this constructor, unfilled to begin
            # with: an equation whose pattern here is a variable never
            # reaches them, and one that named another constructor is out.
            sub = [(targs[a], [None] * len(pats)) for a in range(len(argT))]
            for i, x in enumerate(pats):
                if x is None or x is _OUT:
                    continue
                if x.is_var():
                    sub_envs[i][x.name] = term
                    continue
                h, xargs = x.strip_comb()
                if h.name != constr['name']:
                    sub_alive[i] = False
                    continue
                for a, xa in enumerate(xargs):
                    sub[a][1][i] = xa
            split(g, sub + spots[1:], sub_alive, sub_envs)

    # The tuple, one `type_cases` per nesting level.  A one-argument
    # definition has no tuple at all and the argument itself is the whole
    # of `p`.
    goal = 0
    comps = []
    cur, rest = p, list(arg_types)
    while len(rest) > 1:
        goal = prover.ids('type_cases %s goal=%d' % (cur.name, goal), 1)[0]
        a, b = names.alloc('a'), names.alloc('b')
        goal = prover.ids('intro "%s, %s" goal=%d' % (a, b, goal), 3)[-1]
        comps.append(Var(a, rest[0]))
        cur = Var(b, tupled_type(rest[1:]))
        rest = rest[1:]
    comps.append(cur)
    split(goal,
          [(comps[j], [lhs[i][j] for i in range(len(eqs))])
           for j in range(len(arg_types))],
          [True] * len(eqs), [dict() for _ in eqs])
    lines.extend(prover.text())
    lines.append('qed')
    return lines


class _RenamedEq:
    """An equation whose left hand side carries the split's own variables.

    The branch's `elim` replaces the pattern's variables by fresh names
    (`n1`, `m1` -- `_Names` hands out a variant because the same name and
    type twice would be one stable id and the second line would create
    nothing), so the call terms the equation's right hand side mentions no
    longer name anything in scope.  The obligation has to be computed from
    the renamed equation: `_decrease_steps` reads the left hand side only
    (`_eq_args` strips the head, `_tuple_of` the tuple), so a stand-in
    carrying that suffices.
    """

    def __init__(self, lhs):
        self.lhs = lhs


def _induct_entry(name, cname, arg_types, res_type, eqs, positions, calls,
                  dmap, order=None, sizes=None, mdefs=None, relation=None,
                  descent=None, used=None):
    """The `<c>_induct` item: the induction rule and its proof.

    The rule's statement is `_induct_prop`; the proof is Isabelle's
    `induction_schema_tac` (Function/induction_schema.ML) with the sum
    type left out:

    * `wf_induct` on the definition's own relation gives the relation
      induction hypothesis `!y. <c>_rel y p --> P y`;
    * `<c>_exhaustive` says `p` is some instance of one of the patterns,
      and `disjE` -- once per disjunct, since the disjunction is
      right-nested -- turns that into one branch per equation;
    * a branch takes its pattern apart with one `elim` per pattern
      variable, rewrites `P p` into `P <pattern>` by the equation it just
      obtained, and closes: an equation with no recursive call is its own
      premise instantiated at the pattern's variables, and one with calls
      instantiates each call's induction hypothesis, states that call's
      decrease obligation and proves it with the same machinery the
      equation's own proof uses, then applies the premise.

    The obligation is stated against the *pattern* (`<c>_rel <call>
    <pattern>`), which is what every proof of one is about, so the
    relation is unfolded and the equation `p = <pattern>` substituted
    before it is proved -- except on the measure path, where the chain
    cut `_measure_obligation` states would then be the goal itself and
    would create no item at all; there the substitution happens after the
    chain fact exists and closes the goal by `rule trivial`.
    """
    lhs = [_eq_args(eq) for eq in eqs]
    Tup = tupled_type(arg_types)
    r = positions[0]
    ng = len(eqs)
    # `calls` holds each call's argument sequence; every use here is of the
    # tupled argument, which is what the function constant takes and what
    # the relation and the induction hypothesis are stated over.
    tcalls = [[tupled_arg(c) for c in calls[i]] for i in range(ng)]
    # The predicate's name has to be one the equations do not use: `filter`
    # binds its predicate as `P`, and a fixed `P` here then makes the
    # quantifier and the pattern's variable clash in type
    # (`abstract_over: wrong type`).
    taken = set()
    for eq in eqs:
        for v in eq.get_vars():
            taken.add(v.name)
    # ... nor one the branch's own name allocation will hand out: `_Names`
    # makes `P1` from a pattern variable `P`, and the predicate must not be
    # the name the `elim` of that variable introduces.
    for base in list(taken):
        for i in range(1, 8):
            taken.add('%s%d' % (base, i))
    pred_name = next(c for c in _pred_names() if c not in taken)
    P = Var(pred_name, TFun(Tup, BoolType))
    lines = ['theorem %s_induct' % cname,
             '  fixes %s :: %s ⇒ bool' % (pred_name, _printt(Tup)),
             '  prop %s' % _prints(_induct_prop(arg_types, lhs, tcalls, P)),
             'proof']
    prover = _Proof()
    names = _Names()
    seen = set()

    def obligation(goal, tcall, k, req):
        """Prove the decrease obligation `goal` is (the relation, unfolded).

        `goal` already reads `<body> <call> ...`, the relation having been
        unfolded, and `tcall`/`req` are the call and the equation renamed
        into the branch's own variables.  Which machinery proves it is the
        same choice `_def_entry` makes for the equation's own proof, so the
        two proofs of one definition cannot disagree about what the
        obligation is.

        Returns the fact stating the obligation when the caller still has
        to close `goal` against it, and None when `goal` is closed here.
        The subterm relation's steps are *about the pattern* -- they reduce
        the projections of the tuple the pattern is -- so that path is the
        one that needs `goal` to be the substituted form already.  The
        measure chain and a relation the user wrote are stated with the
        pattern by construction, so their fact is the bridge and the
        substitution happens after it exists.
        """
        if order is not None:
            return _measure_obligation(prover, order, arg_types, tcall,
                                       _tuple_of(req), dmap, sizes, mdefs,
                                       goal, name, k, lines=True)
        if descent:
            return _given_obligation(prover, arg_types, r, relation, tcall,
                                     _tuple_of(req), descent, goal, name, k,
                                     used, lines=True)
        steps, closes = _decrease_steps(arg_types, r, tcall, req, dmap, seen)
        # A call whose instance the proof already produced ends at its own
        # `inst`: that step resolves the goal to the item that is there and
        # creates nothing (`_decrease_steps` says so), where every other
        # closing -- `rule eq_refl`, a rewrite that leaves an identity --
        # lays out a line in a branch whose goal carries hypotheses.
        last_new = 0 if steps and steps[-1].startswith('inst') else 1
        cur = goal
        for j, step in enumerate(steps):
            # Even the step that discharges the obligation lays out a line
            # here: an induction branch's goal carries the hypotheses the
            # `elim`s introduced, so the fact the step derives is a
            # different theorem from the goal and the engine exports the
            # step instead of rewriting the goal in place (`_def_entry`'s
            # branch goals carry none, which is why its counts are the
            # `new=0` ones).
            cur = prover.step('← %s goal=%d' % (step, cur),
                              new=last_new if j == len(steps) - 1 else 1) or cur
        return None

    def one(goal, eqf, k):
        """Equation k: `eqf` states its disjunct, `goal` is `P p`.

        The branch's disjunction has already been introduced by the caller
        (`split` takes the `D_k --> P p` apart, and with one equation the
        fact is the disjunct itself), so this starts at the equation.
        """
        vnames = {}
        env = {}
        for v in _pattern_vars_in(lhs[k]):
            nm = names.alloc(v.name)
            vnames[v.name] = nm
            env[v.name] = Var(nm, v.T)
            e = prover.ids('elim %s goal=%d facts=[%d]' % (nm, goal, eqf), 3)
            eqf, goal = e[1], e[2]
        # The substitution turns `P p` into `P <pattern>`.  Where the
        # equation has no call and the pattern has no variable, that
        # proposition is the equation's own premise -- a fact already in
        # scope -- so the goal closes by itself and the rewrite lays out
        # no new line; everywhere else the proposition is new.
        pvars = _pattern_vars_in(lhs[k])
        autocloser = not tcalls[k] and not pvars
        goal = prover.step('← rewrite source=prev goal=%d facts=[%d]'
                           % (goal, eqf), new=0 if autocloser else 1) or goal
        # The equation's own names are out of scope from here on: the
        # `elim`s above bound the fresh ones, so every term taken from the
        # equation -- the calls, the pattern the obligation is stated
        # against -- has to be renamed into them.
        ren_call = [_subst(c, env) for c in tcalls[k]]
        ren_eq = _RenamedEq(f_const(*[_subst(a, env) for a in lhs[k]]))
        if not tcalls[k]:
            # An equation whose pattern has no variable (`g [] = []`) has a
            # premise with nothing to quantify, so the premise itself is
            # already the instance that matches the goal -- and since it is
            # a fact already in scope, the goal closes on the substitution
            # above by itself (a target whose proposition equals an item's
            # is closed automatically).  Only a pattern with variables
            # needs the instantiations and the closing step that follows.
            inst = prem[k]
            for v in pvars:
                inst = prover.step('← inst "%s" goal=%d facts=[%d]'
                                   % (vnames[v.name], goal, inst))
            if pvars:
                prover.step('← rule trivial goal=%d facts=[%d]'
                            % (goal, inst), new=0)
            return
        pfacts = []
        for tcall in ren_call:
            imp = prover.step('← inst "%s" goal=%d facts=[%d]'
                              % (_arg_text(tcall), goal, ih))
            cut = prover.step('cut "%s_rel %s %s" goal=%d'
                              % (cname, _arg_text(tcall), pname, goal))
            if order is not None or descent:
                # The measure chain's cut and the user's lemma both state the
                # obligation with the *pattern*, which is what the equation's
                # own proof cuts against its branch goal -- so the machinery
                # runs on the cut goal, and the relation is unfolded and the
                # equation substituted afterwards to meet the fact it
                # produced.
                fact = obligation(cut, tcall, k, ren_eq)
                # The unfolding already contracts the redex the relation
                # lambda's application makes -- the rewriter reduces there --
                # so no `beta` belongs here, exactly as in the branch below
                # and in `_def_entry`'s own walk of the same relation.
                cur = prover.step('← rewrite %s_rel_def goal=%d' % (cname, cut))
                # Substituting the equation into the unfolded relation
                # produces exactly the proposition the obligation above
                # states, so the engine finds that item already in its table
                # and lays out no new line -- and the goal, now being that
                # proposition, is closed by the in-scope item itself.  There
                # is no closing step to emit.
                prover.step('← rewrite source=prev goal=%d facts=[%d]'
                            % (cur, eqf), new=0)
            else:
                # The unfold already contracts the redex the lambda's
                # application makes (the rewriter reduces there), so there
                # is no `beta` to emit; the subterm relation's steps are
                # about the pattern, so the substitution comes first -- and
                # it rewrites the goal in place, the substituted form being
                # the proposition the relation's own subterm instance is.
                same_eq = _unfold_is_the_equality(
                    arg_types, r, tcall, Var(pname, Tup),
                    _subst(_tuple_of(eqs[k]), env))
                cur = prover.step('← rewrite %s_rel_def goal=%d' % (cname, cut),
                                  new=0 if same_eq else 1) or cut
                if same_eq:
                    # The obligation *is* the equation the branch just
                    # obtained, so the goal closes on that fact by itself
                    # and there is nothing left to substitute or prove.
                    pass
                else:
                    cur = prover.step('← rewrite source=prev goal=%d facts=[%d]'
                                      % (cur, eqf))
                    obligation(cur, tcall, k, ren_eq)
            pfacts.append(prover.step('→ forward goal=%d facts=[%d,%d]'
                                      % (goal, imp, cut)))
        inst = prem[k]
        for v in pvars:
            inst = prover.step('← inst "%s" goal=%d facts=[%d]'
                               % (vnames[v.name], goal, inst))
        prover.step('← apply_prev goal=%d facts=[%s]'
                    % (goal, ",".join(str(x) for x in [inst] + pfacts)),
                    new=0)

    def split(goal, d, k, n):
        """`d` states `D_k ∨ … ∨ D_{k+n-1}`; `goal` is `P p`."""
        if n == 1:
            return one(goal, d, k)
        two = prover.ids('← rule disjE goal=%d facts=[%d]' % (goal, d), 2)
        f1 = prover.ids('← intro goal=%d' % two[0], 2)
        one(f1[1], f1[0], k)
        f2 = prover.ids('← intro goal=%d' % two[1], 2)
        split(f2[1], f2[0], k + 1, n - 1)

    g = prover.ids('← intro goal=0', ng + 1)[-1]
    prem = list(range(1, ng + 1))
    # `param_R` carries the ascription: a bare `<c>_rel` leaves the parser
    # with nothing to instantiate a polymorphic relation from, and
    # `forward <c>_rel_wf` cannot instantiate one either (`unmatched type
    # variable ?'a` -- it does not read the goal's proposition).  With the
    # ascription the rule states `wf <c>_rel` as a subgoal of its own, and
    # that subgoal is closed at the *end*: closing it here rewrites its line
    # in place, and the branch split below is then refused as an illegal
    # dependence because the lines have shifted under it.
    ids = prover.ids('← rule wf_induct param_R="(%s_rel::%s)" goal=%d'
                     % (cname, _rel_ty_text(arg_types), g), 2)
    wf_goal, g = ids[0], ids[1]
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    pname = names.alloc('p')
    ids = prover.ids('← intro %s goal=%d' % (pname, g), 3)
    ih, g = ids[1], ids[2]
    d0 = prover.step('→ forward %s_exhaustive param_p=%s goal=%d'
                     % (cname, pname, g))
    split(g, d0, 0, ng)
    prover.step('← rule %s_rel_wf goal=%d' % (cname, wf_goal))
    lines.extend(prover.text())
    lines.append('qed')
    return lines


def _name_taken(name):
    """Whether the theory already states a theorem of this name.

    The generator runs with the theory as loaded so far, so this is the
    same question the loader will ask -- and asking it here keeps a
    hand-written rule in the file instead of colliding with it.
    """
    from kernel import theory
    try:
        theory.get_theorem(name)
        return True
    except Exception:
        return False


def _def_entry(name, cname, arg_types, res_type, eqs, positions, i, conds,
               rules, tcalls, dmap, order=None, sizes=None, mdefs=None,
               relation=None, descent=None, used=None):
    """Proof of equation i, whichever branch of the chain it is.

    The body functional is the if-chain over the equations in source
    order, so the branch is reached by refuting the tests of the equations
    before it and then taking its own -- except the last equation, which is
    the chain's else branch and has no test of its own.

    Once the branch is selected, a right hand side without a recursive call
    is the source's own term, with the pattern's variables taken apart by
    the destructors and every projection reduced; one with calls instead
    carries one decrease obligation per distinct call, each of which
    `cut_def` turns into the condition selecting that call.
    """
    prover = _Proof()
    names = _Names()
    r = positions[0]
    t = _arg_text(_tuple_of(eqs[i]))
    g = prover.step('← unfold %s_def goal=0' % cname)
    a = _wf_fact(prover, cname, arg_types, g)
    d = _in_def_fact(prover, cname, arg_types, res_type, g)
    if not tcalls:
        g = prover.step('← rewrite wfrec_eq goal=%d facts=[%d,%d]' % (g, a, d))
    else:
        fp = "%s_in %s = wfrec_H %s_rel %s_H %s_in %s" % (
            cname, t, cname, cname, cname, t)
        c = prover.step('cut "%s" goal=%d' % (fp, g))
        prover.step('← rule wfrec_eq goal=%d facts=[%d,%d]' % (c, a, d), new=0)
        g = prover.step('← rewrite source=prev goal=%d facts=[%d]' % (g, c))
    # What the branch's body reads once the sweeps have reduced it, against
    # the equation's own right hand side: with the branch selected, the goal
    # is exactly this equality, so the step that selects it closes the goal
    # when the two sides are already the same term, and `rest` is the
    # reduction the sweeps did not cover (a redex inside the right hand
    # side, which only the source mentions).
    after = Eq(_reduce(_branch_body(name, arg_types, res_type, eqs[i],
                                    positions, _tuple_of(eqs[i])), dmap),
               eqs[i].rhs)
    rest = _reduce_used(after, dmap)[1]
    final = _reduce(after, dmap)
    closes_now = final.is_reflexive() and not rest
    # A branch with no test of its own (a single equation) and no call has
    # no step left to close the goal: the body *is* the right hand side,
    # so the last step that touched the goal did it -- the last sweep, or
    # the unfolding of the body functional when nothing was swept.
    closes_early = closes_now and not tcalls and i == 0 and len(eqs) == 1
    g = prover.step('← unfold wfrec_H_def goal=%d' % g)
    if closes_early and not rules:
        prover.step('← unfold %s_H_def goal=%d' % (cname, g), new=0)
        return prover.text()
    g = prover.step('← unfold %s_H_def goal=%d' % (cname, g))
    for k, rule in enumerate(rules):
        last = (k == len(rules) - 1)
        if last and closes_early:
            prover.step('← rewrite %s goal=%d' % (rule, g), new=0)
        else:
            g = prover.step('← rewrite %s goal=%d' % (rule, g))
    if len(positions) > 1:
        # The chain has one `if` per (equation, position), so the branch is
        # reached by taking or refuting each of them in order; nothing else
        # about the equation's proof changes.
        g = _multi_navigation(prover, names, arg_types, positions, eqs, i, g,
                              dmap, conds, last_closes=closes_now)
    for j in range(i) if len(positions) == 1 else []:
        neg = _condition_negation(prover, names, arg_types, positions, eqs,
                                  i, j, g, conds[i][j])
        # The last of these is the step that selects the branch when the
        # equation is the chain's else (the last one); it closes the goal
        # when the branch's body is already the equation's right hand side.
        last_nav = (j == i - 1) and (i == len(eqs) - 1) and closes_now
        g = prover.step('← rewrite if_not_P goal=%d facts=[%d]' % (g, neg),
                        new=0 if last_nav else 1) or g
    # The instance the branch's own test leaves behind, when it has one: a
    # decrease obligation of this branch can turn out to be that very
    # proposition (see the loop below).
    test_inst = None
    if i < len(eqs) - 1 and len(positions) == 1:
        c2, test_inst = _condition_fact(prover, arg_types, positions, eqs, i,
                                        conds[i][i], g, dmap)
        g = prover.step('← rewrite if_P goal=%d facts=[%d]' % (g, c2),
                        new=0 if closes_now else 1) or g
    # Which step selected the branch: the chain's last equation has no test
    # of its own, and a single-equation definition has no chain at all.
    selected_by_step = (i < len(eqs) - 1) or i > 0
    if not tcalls:
        if closes_now and selected_by_step:
            return prover.text()
        # The branch is the right hand side itself, and no obligation (and
        # no `cut`) arises; what is left is the reduction the sweeps did
        # not cover, which closes the goal when it ends on an identity.
        if not final.is_reflexive():
            raise FunGenError(
                'fun %s: equation %d does not reduce to its own right hand '
                'side (%s against %s)'
                % (name, i + 1, _prints(_reduce(after.lhs, dmap)),
                   _prints(after.rhs)))
        c3 = g
        for k, rule in enumerate(rest):
            if k == len(rest) - 1:
                prover.step('← rewrite %s goal=%d' % (rule, c3), new=0)
            else:
                c3 = prover.step('← rewrite %s goal=%d' % (rule, c3))
        if not rest and not closes_early:
            # With `closes_early` the last sweep rule already closed the
            # goal (the branch body *is* the right hand side), so the
            # reflexivity step would be emitted against a closed goal.
            prover.step('← rule eq_refl goal=%d' % c3, new=0)
        return prover.text()
    eq = eqs[i]
    facts = []
    # The instances the obligations of this equation have already produced,
    # shared between them: two calls of one equation can land on the same
    # instance, and then the second one's `inst` resolves to the first one's
    # item instead of creating one (`_decrease_steps`).
    seen = set()
    for tcall in tcalls:
        if descent:
            facts.append(_given_obligation(prover, arg_types, r, relation,
                                           tcall, _tuple_of(eq), descent, g,
                                           name, i, used))
            continue
        if order is not None:
            facts.append(_measure_obligation(prover, order, arg_types, tcall,
                                             _tuple_of(eq), dmap, sizes, mdefs,
                                             g, name, i))
            continue
        obligation_prop = _decrease_prop(arg_types, r, tcall, _tuple_of(eq))
        if test_inst is not None and test_inst[0] == obligation_prop:
            # The branch's own test already stated and discharged exactly this
            # proposition.  A pattern whose only variable is the recursive
            # argument (`TriS t`) is the case: the test's instance is `C t =
            # C t`, and the obligation, the relation being the subterm one, is
            # that same identity.  The stable-ID layer keys items by
            # proposition, so cutting it again would create nothing; the
            # instance item is the fact the obligation's `if_P` takes.
            facts.append(test_inst[1])
            continue
        c_cut = prover.step('cut "%s" goal=%d' % (obligation_prop, g))
        # The steps are computed from the obligation's own term -- the one
        # the cut above states, with the projections of both the call and
        # the pattern -- because that is what the goal has: computing them
        # from the two projections separately emits steps the sweep has
        # already cleared, and deduping them loses a level when the
        # projection is nested (`snd (snd p)`, three arguments and up).
        steps, closes = _decrease_steps(arg_types, r, tcall, eq, dmap, seen)
        c3 = c_cut
        for k3, step in enumerate(steps):
            last = (k3 == len(steps) - 1)
            if last and closes:
                # `closes` says the last step discharges the obligation: the
                # reflexivity rule always does, a rewrite when it leaves an
                # identity, and the `inst` that ends a repeated instance.
                prover.step('← %s goal=%d' % (step, c3), new=0)
            else:
                c3 = prover.step('← %s goal=%d' % (step, c3))
        facts.append(c_cut)
    g = prover.step('← rewrite %s_rel_def goal=%d' % (cname, g))
    g = prover.step('← rewrite cut_def goal=%d' % g)
    # One `if_P` per distinct call: `cut_def` turned every `g (call)` into
    # `if R call p then …`, and each condition matches only its own
    # obligation, so the step discharges exactly that occurrence -- the
    # last one closes the goal.  They take the *cut*'s ID, not the
    # obligation's own proof, because that proof may have ended on an
    # instance (`inst` on an existential, a rewrite rule for nat) whose
    # proposition is not the condition.
    for k, c_cut in enumerate(facts):
        last = (k == len(facts) - 1)
        g = prover.step('← rewrite if_P goal=%d facts=[%d]' % (g, c_cut),
                        new=0 if last else 1) or g
    return prover.text()


def _require_in_scope(arg_types, r, order=None, relation=None):
    """Names the emitted items and proofs depend on.

    A definition is only expanded when the file can actually see them:
    the generated proofs reference the well-founded-recursion combinators
    (from the `wf` theory) and, through the relation, the datatype's
    well-foundedness lemma.  A file that imports neither keeps the current
    axiomatization instead of getting items that cannot even be parsed.

    A definition without a recursive call needs no relation to descend
    through: its relation is the empty one, whose well-foundedness is
    `wf_false`.  That is what makes the datatype's own projections (`the`,
    `fst`, `snd`) and the pattern-matching predicates expandable at all --
    their destructor is the very function being defined, so no subterm
    relation over them exists.

    A measure chain additionally needs the mlex machinery and the nat
    comparison lemmas its cells are closed with; the size functions of the
    argument datatypes are checked as the columns are built, since a
    datatype without one contributes no column instead.
    """
    from kernel import theory
    needed = ['wfrec_eq', 'wfrec_H_def', 'cut_def', 'if_P', 'if_not_P',
              'eq_refl']
    if len(arg_types) > 1:
        # A definition with several arguments is built over the tupled
        # argument and reads the components back through the projections,
        # whose proofs reduce with prod's own rules.  A single-argument
        # definition has no tuple: requiring them there is a false gate,
        # and for prod itself, which defines them, a circular one.
        needed += ['fst_def_1', 'snd_def_1']
    if relation is not None:
        # The user's own relation: nothing of the measure machinery is
        # needed for it, but the chain of rewrites that reaches the
        # fixpoint is the same, and the datatype's well-foundedness lemma
        # is replaced by the user's `wf` theorem, which names its own
        # prerequisites.
        pass
    elif order is None:
        needed.append('wf_measure_gen')
        needed.append('ineq_sym')
        needed.append(_subterm(arg_types[r])[1])
    elif not order:
        needed.append('wf_false')
    else:
        needed += ['wf_false', 'wf_mlex', 'mlex_prod_def', 'mlex_less',
                   'mlex_leq']
        needed += measure.ARITH + measure.CLOSING_LEMMAS
    for th_name in needed:
        try:
            theory.get_theorem(th_name)
        except Exception:
            raise FunGenError(
                'the well-founded-recursion machinery (%s) is not in scope; '
                'add the wf/list theory to this file imports' % th_name)


def _expand(data, declared=None):
    from syntax import parser
    from core import context
    from kernel import theory
    name = data['name']
    ty = parser.parse_type(data['type'])
    cname = theory.thy.get_overload_const_name(name, ty)
    with context.fresh_context(defs={name: ty}):
        eqs = [context.parse_term(rule['prop']) for rule in data['rules']]
    # The arity comes from the equations' own left hand sides, not from
    # stripping the declared type: a type abbreviation in the result
    # (`'a multiset` is `'a ⇒ nat`) makes the declaration look like one
    # argument more than the definition has, and the recursive calls are
    # then looked for at the wrong arity and not found.
    arity = len(_eq_args(eqs[0]))
    arg_types, res_type = _strip_type(ty, arity)
    lhs = [_eq_args(eq) for eq in eqs]
    positions = recursion_positions(arg_types, lhs)
    if not positions:
        raise FunGenError('fun %s: a definition without constructor patterns '
                          'is not emitted yet' % name)
    r = positions[0]
    # The recursion position has to be a datatype: the split below takes the
    # patterns apart by its constructors.  This is the only check the emitter
    # still makes on the shape of the equations -- whether they overlap is no
    # longer refused, it is *subtracted* (`_complete_equations`), which is
    # also what fills a definition's holes with `undefined`.
    for pos in positions:
        if _constr_names(arg_types[pos]) is None:
            raise FunGenError(
                'fun %s: recursion on argument %d is not supported: %s '
                'is not a datatype' % (name, pos + 1, _printt(arg_types[pos])))
    # `_missing` is what the definition leaves undefined: the catchall's
    # survivors, which are also equations of the group emitted below, so the
    # record of them is the `= undefined` equation itself and not a report.
    eqs, eq_texts, _missing = _complete_equations(
        name, arg_types, res_type, eqs,
        [rule['prop'] for rule in data['rules']])
    lhs = [_eq_args(eq) for eq in eqs]
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    # A recursive call may stand in any equation, and several calls in one
    # equation are fine as long as they ask for the same thing: the body
    # then mentions one `g (...)` term rather than several, so one
    # obligation covers them all (`filter` and `remdups` recurse on the
    # same tail in both branches).  No call at all is fine too -- that
    # equation needs no decrease.
    calls = []
    for eq in eqs:
        tuples = []
        for c in _calls(eq.rhs, f_const, len(arg_types)):
            if c not in tuples:
                tuples.append(c)
        calls.append(tuples)
    _require_in_scope(arg_types, r, None if any(calls) else [])

    dmap = _destructor_maps(arg_types, positions, lhs)
    rules = [_reduce_used(_body_term(name, arg_types, res_type, eqs, positions,
                                     _tuple_of(eq)), dmap)[1] for eq in eqs]
    # `conds[i][j]` is the test of equation j as this branch's goal has it,
    # one entry per recursion position: the projection already reduced to
    # the branch's own pattern.
    conds = [[[_reduce(_cond_of(lhs[j][pos],
                                projection(_tuple_of(eqs[i]), arg_types, pos),
                                _pos_tag(j, k, len(poses_j))), dmap)
               for k, pos in enumerate(poses_j)]
              for j, poses_j in ((j, _pattern_positions(lhs[j], positions))
                                 for j in range(i + 1))]
             for i in range(len(eqs))]
    measures, relation, wf_lemma, descent = fun_clauses(data, eqs, name, ty)
    if relation is not None:
        # The relation is the user's: nothing is inferred, and there is no
        # fallback to the datatype's subterm relation -- the definition
        # descends through *that* relation, and the obligations below are
        # discharged from the named lemmas or the definition is not emitted
        # at all (`expand_item` lets the error out, since the structural
        # check that makes an axiom safe is not being asked).
        for lemma in descent + [wf_lemma]:
            try:
                theory.get_theorem(lemma)
            except Exception:
                raise FunGenError(
                    'fun %s: %s is not in the theory yet; the lemmas a '
                    'relation is discharged with have to be stated before '
                    'the definition' % (name, lemma))
        order, sizes, mdefs = None, {}, {}
        used = set()
        _require_in_scope(arg_types, r, order, relation)
    elif measures:
        # A given measure goes through the search's own machinery -- the
        # same named constants, the same cells, the same chain -- so it
        # needs the same machinery to be in scope, and it is not tried
        # against anything else: the user asked for *this* measure.
        order = _given_measures(arg_types, cname, measures)
        sizes, mdefs = _measure_tables(
            _measure_registry(cname, arg_types, (name, cname))[0], order)
        used = set()
        _require_in_scope(arg_types, r, order)
    else:
        used = set()
        order, sizes, mdefs = _measure_order(arg_types, (name, cname), cname,
                                             eqs, calls, dmap)
        try:
            _require_in_scope(arg_types, r, order)
        except FunGenError:
            if len(positions) > 1:
                # The subterm relation is stated for one argument; a
                # definition matching on several needs the measures, and
                # saying so is better than emitting a relation that descends
                # through only one of them.
                raise
            # The measure machinery is not in scope in this file (the nat
            # comparisons its cells are closed with, most often).  The
            # datatype's own subterm relation is the relation rule left, the
            # same one that was used before the measures existed: a file that
            # cannot see them keeps the items it always had, instead of losing
            # the definition to an axiom.
            order, sizes, mdefs = None, {}, {}
            _require_in_scope(arg_types, r, order)
    entries = [_entry([text]) for text in _measure_defs(cname, arg_types,
                                                        order)]
    entries += [_entry([text]) for text in _def_entries(
        name, cname, arg_types, res_type,
        _body_prop(name, arg_types, res_type, eqs, positions),
        _rel_body(arg_types, r, order, relation))]
    entries.append(_entry(_rel_wf_entry(cname, arg_types, r, order, relation,
                                        wf_lemma)))
    for i, eq in enumerate(eqs):
        eq_text = _equation_text(name, ty, eq_texts[i], eq)
        text = ['theorem %s_def_%d' % (cname, i + 1),
                '  fixes %s' % _typenames(sorted(eq.get_vars(),
                                                 key=lambda v: v.name)),
                '  prop %s' % eq_text,
                '  [hint_rewrite]',
                'proof']
        text.extend(_def_entry(name, cname, arg_types, res_type, eqs,
                               positions, i, conds, rules[i],
                               [tupled_arg(c) for c in calls[i]], dmap,
                               order, sizes, mdefs, relation, descent, used))
        text.append('qed')
        entries.append(_entry(text))
    for lemma in descent:
        if lemma not in used:
            raise FunGenError(
                'fun %s: the `descent` lemma %s is not the obligation of any '
                'call; every lemma given has to discharge one' % (name, lemma))
    # A theory may state these rules by hand (`nat.pyhol` has
    # `nat_less_induct`, `wfrec_example` has `wfx_induct` as the shape to
    # generate).  The written one wins: emitting a second theorem of the
    # same name is an item the loader refuses, and the hand-written one is
    # the one the rest of the file was written against.  The case rule is
    # yielded on its own name below, so a file that writes only one of the
    # three keeps the other two.
    declared = declared or set()
    if ('%s_exhaustive' % cname) in declared or ('%s_induct' % cname) in declared:
        return entries
    try:
        entries.append(_entry(_coverage_entry(cname, arg_types, eqs, lhs)))
    except FunGenError:
        # The split enumerates each position's constructors, so it can only
        # be closed where the equations have a pattern for every input.  A
        # definition may leave a hole -- `drop2 0` with `drop2 (Suc (Suc n))`
        # leaves `Suc 0` -- and then there is no such theorem.  The
        # definition is sound as it stands (the body's chain is defined for
        # every input, the last equation being its else branch), and neither
        # item is part of it: dropping them is the honest outcome.  Letting
        # the error out would make the whole definition fall back to axioms,
        # turning every equation the emitter derives today back into an
        # assumption -- a regression, not a refusal.
        pass
    else:
        if ('%s_cases' % cname) not in declared:
            # The case rule is the coverage theorem's content in the shape
            # a case split consumes (see `_cases_entry`), so it is emitted
            # exactly where that theorem is -- and a file that states one
            # of them by hand keeps its own.
            try:
                entries.append(_entry(_cases_entry(cname, arg_types, eqs, lhs)))
            except FunGenError:
                pass
        try:
            entries.append(_entry(_induct_entry(
                name, cname, arg_types, res_type, eqs, positions, calls, dmap,
                order, sizes, mdefs, relation, descent, used)))
        except FunGenError:
            # Same rule as the coverage theorem above: the induction rule is
            # not part of the definition, so a definition the rule cannot be
            # stated for keeps the items it has instead of falling back to
            # axioms.
            pass
    # The relation item names the measure constants defined in this group,
    # so it can only be parsed after them -- the loader does exactly that.
    # What is checked here is everything up to and including the body
    # functional: the items that name nothing inside the group.
    _require_parsable_defs(entries[:len(order or []) + 1], name)
    return entries


def _require_parsable_prop(name, ty, text, eq):
    """Refuse an equation whose text cannot be typed as an item.

    The emitted equations are the source's own text, parsed by the item
    parser with the definition's constant already in the theory.  It is
    typed from the item's `fixes` variables, so every type variable of
    the definition has to be pinned by one of them or named in the text
    itself (`butlast [] = []` pins nothing and its `[]` stays untyped;
    `distinct ([]::'a list) ⟷ true` names its variable and parses).
    The loader drops an item it cannot parse, which would leave the file
    with a definition whose first equation is missing, so the definition
    keeps its axioms instead.
    """
    named = set(re.findall(r"'[A-Za-z_][A-Za-z0-9_]*", text))
    carried = set()
    for v in eq.get_vars():
        for tv in v.T.get_tvars():
            carried.add("'" + tv.name)
    missing = [tv.name for tv in ty.get_tvars()
               if "'" + tv.name not in named | carried]
    if missing:
        raise FunGenError(
            'fun %s: the equation %s carries neither the type variable %s '
            'nor anything to pin it down, so the emitted item cannot be typed'
            % (name, text, ", ".join("'" + m for m in missing)))


def _equation_text(name, ty, text, eq):
    """The text of an emitted equation, in a form the item parser keeps.

    It is the source's own text whenever that can be typed, and the
    equation with the types the source left implicit written out
    otherwise: a variable-free equation has nothing else to carry the
    definition's type variables (`butlast [] = []` becomes
    `butlast ([]::'a list) = ([]::'a list)`), and an item the loader
    cannot type is dropped, which would leave the file with a definition
    whose first equation is missing.

    An equation the emitter made rather than read -- a pattern subtraction
    left it narrower than the source, or the catchall contributed it -- has no
    source text, and is printed from its term.
    """
    if text is None:
        # An equation the emitter made rather than read.  Its head cannot be
        # printed: the constant being defined is not in the theory yet, and the
        # printer looks its signature up.  So the text is assembled the way
        # `_ascribed_eq` assembles it, with whatever ascriptions the source
        # would have had to write to pin the definition's type variables down.
        text = _ascribed_eq(name, eq, _missing_type_vars(ty, '', eq))
    missing = _missing_type_vars(ty, text, eq)
    if not missing:
        return text
    printed = _ascribed_eq(name, eq, set(missing))
    if _missing_type_vars(ty, printed, eq):
        _require_parsable_prop(name, ty, text, eq)
    return printed


def _ascribed_eq(name, eq, missing):
    """The equation written out with the given type variables named.

    The item parser types an equation from the item's `fixes` variables
    and from the definition's own type, and it is the latter that is
    instantiated with fresh *anonymous* variables there: a type variable
    no `fixes` variable mentions stays untyped and the item does not
    parse.  Naming it in the text is what fixes it.  The head is written
    as the plain name, so printing never has to look up the constant
    being defined, which is not in the theory yet.
    """
    _, args = eq.lhs.strip_comb()
    parts = [name] + [_arg_ascribed(a, missing) for a in args]
    return "%s = %s" % (" ".join(parts), _ascribed_term(eq.rhs, missing))


def _ascribed_term(t, missing):
    """A term, ascribed with its own type when that names a missing one."""
    text = _prints(t)
    Ty = t.get_type()
    if any("'" + tv.name in missing for tv in Ty.get_tvars()):
        text = "(%s::%s)" % (text, _printt(Ty))
    return text


def _arg_ascribed(t, missing):
    """A term in argument position: ascribed, and parenthesized when compound.

    `T` applied to `Suc 0` has to be written `T (Suc 0)`; the ascription
    brings the parentheses along only when one is needed, so a compound
    argument whose type names nothing missing would otherwise be printed
    bare and parse as two arguments.
    """
    Ty = t.get_type()
    if any("'" + tv.name in missing for tv in Ty.get_tvars()):
        return "(%s::%s)" % (_prints(t), _printt(Ty))
    return _arg_text(t)


def _missing_type_vars(ty, text, eq):
    """The definition's type variables the given text cannot pin down."""
    named = set(re.findall(r"'[A-Za-z_][A-Za-z0-9_]*", text))
    carried = set()
    for v in eq.get_vars():
        for tv in v.T.get_tvars():
            carried.add("'" + tv.name)
    return [tv.name for tv in ty.get_tvars()
            if "'" + tv.name not in named | carried]


def _require_parsable_defs(entries, name):
    """Refuse a group whose body functional or relation does not parse.

    Those two are the only items of the group that name nothing inside
    it, so they can be checked before the group is applied.  The
    functional of a definition whose result type the printer mistypes --
    `('a × 'b) list` prints as `'a × 'b list`, i.e. `'a × ('b list)` --
    does not parse, and then the constant it defines never registers and
    every later item of the file that mentions it fails with it.
    """
    from core import items
    for data in entries:
        item = items.parse_item(data)
        if item.error is not None:
            raise FunGenError('fun %s: the emitted %s does not parse: %s'
                              % (name, item.name, item.error))


def _has_clauses(data):
    """Whether the definition carries a relation or a measure.

    A definition that does is not left axiomatized when its proof does not
    come off: the relation or the measure *is* the justification, and the
    structural check that would make the equations consistent as axioms is
    not being asked (`core/items.py`), so a failure has to be reported
    rather than swallowed.
    """
    return bool(data.get('measure') or data.get('relation'))


def expand_item(data, declared=None):
    """Item dicts for a `fun` definition, or None to keep it axiomatized.

    None means the definition is outside the supported increment, so the
    caller keeps the current mechanism; nothing is silently approved.
    Set HOLPY_FUNGEN_DEBUG to see the underlying exception instead.

    A definition that carries a relation or a measure is the exception:
    it has no current mechanism to keep, so its errors are let out (`_has_
    clauses`).
    """
    try:
        return _expand(data, declared)
    except FunGenError:
        if _has_clauses(data):
            raise
        return None
    except Exception:
        if os.environ.get('HOLPY_FUNGEN_DEBUG') or _has_clauses(data):
            raise
        return None

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

from kernel.type import TFun, TConst, BoolType
from kernel.term import Lambda, Var, Const, Eq, Abs
from syntax import printer
from syntax.logicops import Exists, is_exists, Not, is_not
from syntax.settings import global_setting

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


def recursion_position(arg_types, eq_lhs_args):
    """Index of the argument carrying constructor patterns, or None."""
    positions = set()
    for args in eq_lhs_args:
        for i, a in enumerate(args):
            h, _ = a.strip_comb()
            if h.is_const():
                constrs = _constr_names(arg_types[i])
                if constrs and h.name in constrs:
                    positions.add(i)
    if not positions:
        return None
    if len(positions) != 1:
        raise FunGenError(
            "constructor patterns on arguments %s; exactly one argument "
            "may carry them" % ", ".join(str(i + 1) for i in sorted(positions)))
    return min(positions)


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
        return h(*[_subst(a, env) for a in args])
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


def _cond_of(pat, proj):
    """The test that `proj` matches `pat`.

    A pattern with no variable of its own is an equality.  Otherwise the
    variables are bound by one existential over their tuple, so the test
    is exactly as strong as the pattern and can be discharged (or refuted)
    with a single `elim` -- no pattern subtraction is needed for a set of
    equations whose patterns have distinct constructor roots.
    """
    leaves = _pattern_leaves(pat)
    if not leaves:
        return Eq(proj, pat)
    types = [a.get_type() for a in leaves]
    w = Var('_w', tupled_type(types))
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


def variable_env(lhs_args, r, p=None):
    """Term for each source variable in terms of the tuple term p.

    Plain arguments become projections; the pattern variables at the
    recursion position become destructor applications, following a nested
    pattern down to its leaves.  Passing the literal tuple of an equation
    gives the body in exactly the shape the goal has after the
    corresponding rewrites.
    """
    arg_types = [a.get_type() for a in lhs_args]
    if p is None:
        p = Var('p', tupled_type(arg_types))
    env = {}
    for i, a in enumerate(lhs_args):
        if i == r:
            continue
        if not a.is_var():
            raise FunGenError(
                "argument %d is not a plain variable; only argument %d may "
                "carry patterns" % (i + 1, r + 1))
        env[a.name] = projection(p, arg_types, i)
    _bind_pattern(lhs_args[r], projection(p, arg_types, r), env)
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


def branch_condition(lhs_args, r, p):
    """Condition testing the recursion argument against a pattern.

    A nullary constructor is tested by equality; a constructor with
    arguments by an existential over its pattern variables, since those are
    not in scope in the condition.
    """
    arg_types = [a.get_type() for a in lhs_args]
    return _cond_of(lhs_args[r], projection(p, arg_types, r))


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


def _rel_wf_entry(cname, arg_types, r, recursive=True):
    """The `wf` obligation: the relation is well-founded.

    The relation def is a lambda, so `rewrite` unfolds it in the
    unapplied goal `wf <c>_rel` without a beta redex; the lift through
    the projection is `wf_measure_gen`, instantiated explicitly because
    its pattern `?R (?m x) (?m y)` does not match a projection
    application on its own.

    The empty relation of a definition without recursive calls is the one
    case that needs no lift: `wf_false` is its well-foundedness directly.
    """
    prop = _rel_wf_prop(cname, arg_types)
    prover = _Proof()
    g = prover.step('← rewrite %s_rel_def goal=0' % cname)
    if not recursive:
        prover.step('← rule wf_false goal=%d' % g, new=0)
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


def _condition_negation(prover, names, arg_types, r, eqs, i, j, g, cond):
    """A fact that equation j's test fails in branch i.

    The cut states exactly the test as the goal has it -- the branch's own
    pattern on the left, the constructor of equation j on the right -- so
    `if_not_P` can rewrite with it.  It is refuted from the datatype's
    distinctness axiom, whose conclusion is the negation of an equation
    between the two constructors: when the axiom already reads the way the
    test does, `rule` closes the cut with it directly; otherwise the test
    (an existential when the pattern has variables, an equality otherwise)
    is taken apart, its equation flipped to the axiom's own order, and
    `resolve` closes the goal with the axiom and that equation.  Nothing
    here depends on how many arguments either constructor takes.
    """
    cj = _constr_name(_eq_args(eqs[j]), r)
    ci = _constr_name(_eq_args(eqs[i]), r)
    th_name, th = _distinct_neq(arg_types[r].name, cj, ci)
    if th is None:
        raise FunGenError(
            'no distinctness axiom for the constructors %s and %s of %s; '
            'without one the branch of %s cannot be ruled out'
            % (cj, ci, _printt(arg_types[r]), cj))
    left, right = _neq_sides(th)
    # The axiom states the pair in its own order; the test's own order is
    # the branch's pattern on the left.
    matches = left.strip_comb()[0].name == ci
    c = prover.step('cut "%s" goal=%d' % (_prints(Not(cond)), g))
    if not is_exists(cond) and matches:
        prover.step('← rule %s goal=%d' % (th_name, c), new=0)
        return c
    c1 = prover.step('← rule negI goal=%d' % c)
    # `negI` leaves `cond ==> false`: the hypothesis it creates is the
    # test itself (an implication introduces no variable, so it has no
    # name), and taking the existential apart turns it into an equation.
    ids = prover.ids('← intro goal=%d' % c1, 2)
    eq, g2 = ids[0], ids[1]
    if is_exists(cond):
        ids = prover.ids('→ elim "%s" goal=%d facts=[%d]'
                         % (_exists_var(cond), g2, eq), 3)
        eq, g2 = ids[1], ids[2]
    if not matches:
        eq = prover.step('→ rewrite target=fact eq_sym_eq sym=false '
                         'goal=%d facts=[%d]' % (g2, eq))
    prover.step('← resolve %s goal=%d facts=[%d]' % (th_name, g2, eq), new=0)
    return c


def _condition_fact(prover, arg_types, r, eqs, i, cond, g, dmap):
    """Cut the branch's own test and prove it from the pattern.

    The test is the pattern against itself: an equality when the pattern
    has no variable, and an existential over the variables otherwise,
    which `inst` turns into that equality with the witness tuple of the
    pattern's own variables.  The reduce closes it exactly when its last
    rewrite leaves an identity.
    """
    c = prover.step('cut "%s" goal=%d' % (_prints(cond), g))
    if not is_exists(cond):
        prover.step('← rule eq_refl goal=%d' % c, new=0)
        return c
    pat = _eq_args(eqs[i])[r]
    leaves = _pattern_leaves(pat)
    wit = _leaf_tuple(leaves)
    c2 = prover.step('← inst %s goal=%d' % (_arg_text(wit), c))
    body = _subst(cond.arg.body, {_exists_var(cond): wit})
    reduced = _reduce(body, dmap)
    rules = _reduce_used(body, dmap)[1]
    for k, rule in enumerate(rules):
        if k == len(rules) - 1 and reduced.is_reflexive():
            prover.step('← rewrite %s goal=%d' % (rule, c2), new=0)
        else:
            c2 = prover.step('← rewrite %s goal=%d' % (rule, c2))
    if not rules or not reduced.is_reflexive():
        prover.step('← rule eq_refl goal=%d' % c2, new=0)
    return c


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
            try:
                theory.get_theorem(rule)
            except Exception:
                continue
            res[dname] = (constr['name'], j, rule)
    return res


def _destructor_maps(arg_types, r):
    """The destructor map for a definition's arguments.

    Both ends are needed: the recursion component's (`Pre`, `hd`, ...) and
    the tuple's (`fst`, `snd`), since the emitted bodies mention both.
    """
    T = arg_types[r]
    res = _destructor_map(T)
    if len(arg_types) > 1:
        res.update(_destructor_map(tupled_type(arg_types)))
    return res


def destructor(constr_name, j, t):
    """The j-th argument of a constructor pattern, as a term in t."""
    from core import datgen
    from kernel import theory
    T = t.get_type()
    dname, rule = datgen.destructor_names(T.name, constr_name, j)
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


def _decrease_closes(arg_types, r, tcall, t):
    """Whether the projection rules themselves close the obligation.

    The obligation is the relation applied to the recursive call and the
    pattern; for nat that is an equality the rules resolve to an identity
    (`Suc m = Suc m`), so the last rule closes the goal.  For list it is an
    existential, which no rewrite can close.  This is the one place the
    emitted counter depends on the method layer's automatic closing, and it
    is decided here from the terms, not by asking: the reduced obligation is
    reflexive.
    """
    T = arg_types[r]
    call = _proj_term(arg_types, r, tcall)
    pat = _proj_term(arg_types, r, t)
    return _reduce(_relation(T)(call)(pat).beta_norm(),
                   _destructor_maps(arg_types, r)).is_reflexive()


def _decrease_witness(arg_types, r, tcall, t, eq):
    """The pattern variable that witnesses an existential obligation.

    The obligation is the relation applied to the recursive call and the
    pattern.  Where the pattern's constructor has an argument that is not
    the datatype itself (`x # xs`, `SCons s x`), the obligation is an
    existential, and the witness is the pattern's own variable at that
    position -- the very term the equation's right hand side is written
    with.  A constructor with several such arguments would need a tuple of
    them, which is not emitted yet; an equality obligation (nat's `Suc`)
    needs no witness at all.
    """
    T = arg_types[r]
    call = _proj_term(arg_types, r, tcall)
    pat = _proj_term(arg_types, r, t)
    obl = _reduce(_relation(T)(call)(pat).beta_norm(),
                  _destructor_maps(arg_types, r))
    if not is_exists(obl):
        return None
    _, pargs = _eq_args(eq)[r].strip_comb()
    free = [k for k, a in enumerate(pargs) if a.get_type() != T]
    if len(free) != 1:
        raise FunGenError(
            'the decrease obligation is an existential with %d pattern '
            'variables other than the recursive one; the witness would be '
            'a tuple of them' % len(free))
    return pargs[free[0]].name


def _branch_body(name, arg_types, res_type, eq, r, tup):
    """One equation's right hand side as the body functional writes it."""
    g = Var('g', TFun(tupled_type(arg_types), res_type))
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    return replace(eq.rhs, f_const, len(arg_types),
                   variable_env(_eq_args(eq), r, tup), g)


def _body_term(name, arg_types, res_type, eqs, r, p=None):
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
    if p is None:
        p = Var('p', Tup)
    lhs = [_eq_args(eq) for eq in eqs]
    body = _branch_body(name, arg_types, res_type, eqs[-1], r, p)
    for i in range(len(eqs) - 2, -1, -1):
        b = _branch_body(name, arg_types, res_type, eqs[i], r, p)
        cond = branch_condition(lhs[i], r, p)
        body = Const('IF', TFun(BoolType, TFun(
            res_type, TFun(res_type, res_type))))(cond)(b)(body)
    return body


def _body_prop(name, arg_types, res_type, eqs, r, p=None):
    """The `<c>_H g p = ...` right hand side, printed."""
    return _prints(_body_term(name, arg_types, res_type, eqs, r, p))


def _rel_body(arg_types, r, recursive=True):
    """The relation as a lambda over the tuple variables p and q.

    The def's right hand side is the whole lambda: `wf <c>_rel` is
    unfolded by rewriting the unapplied constant, which only works if the
    definitional equation is `c_rel = (%p. %q. ...)`.  The body is the
    datatype's component relation applied to the projected tuple
    components, so it is the same proposition the lifted condition is.

    A definition without a recursive call descends nowhere: its relation is
    the empty one, which is well founded (`wf_false`) and makes every
    obligation vacuous.  The datatype's own projections have no subterm
    relation to use -- their destructor is the function being defined --
    so this is the only relation available to them.
    """
    Tup = _printt(tupled_type(arg_types))
    if not recursive:
        return "%%p::%s. %%q::%s. false" % (Tup, Tup)
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


def _def_entry(name, cname, arg_types, res_type, eqs, r, i, conds, rules,
               tcall, dmap):
    """Proof of equation i, whichever branch of the chain it is.

    The body functional is the if-chain over the equations in source
    order, so the branch is reached by refuting the tests of the equations
    before it and then taking its own -- except the last equation, which is
    the chain's else branch and has no test of its own.

    Once the branch is selected, a right hand side without a recursive call
    is the source's own term, with the pattern's variables taken apart by
    the destructors and every projection reduced; one with a call instead
    carries the decrease obligation, which `cut_def` turns into the
    condition selecting the call.
    """
    prover = _Proof()
    names = _Names()
    t = _arg_text(_tuple_of(eqs[i]))
    g = prover.step('← unfold %s_def goal=0' % cname)
    a = _wf_fact(prover, cname, arg_types, g)
    d = _in_def_fact(prover, cname, arg_types, res_type, g)
    if tcall is None:
        g = prover.step('← rewrite wfrec_eq goal=%d facts=[%d,%d]' % (g, a, d))
    else:
        fp = "%s_in %s = wfrec_H %s_rel %s_H %s_in %s" % (
            cname, t, cname, cname, cname, t)
        c = prover.step('cut "%s" goal=%d' % (fp, g))
        prover.step('← rule wfrec_eq goal=%d facts=[%d,%d]' % (c, a, d), new=0)
        g = prover.step('← rewrite source=prev goal=%d facts=[%d]' % (g, c))
    g = prover.step('← unfold wfrec_H_def goal=%d' % g)
    g = prover.step('← unfold %s_H_def goal=%d' % (cname, g))
    for rule in rules:
        g = prover.step('← rewrite %s goal=%d' % (rule, g))
    # What the branch's body reads once the sweeps have reduced it, against
    # the equation's own right hand side: with the branch selected, the goal
    # is exactly this equality, so the step that selects it closes the goal
    # when the two sides are already the same term, and `rest` is the
    # reduction the sweeps did not cover (a redex inside the right hand
    # side, which only the source mentions).
    after = Eq(_reduce(_branch_body(name, arg_types, res_type, eqs[i], r,
                                    _tuple_of(eqs[i])), dmap), eqs[i].rhs)
    rest = _reduce_used(after, dmap)[1]
    final = _reduce(after, dmap)
    closes_now = final.is_reflexive() and not rest
    for j in range(i):
        neg = _condition_negation(prover, names, arg_types, r, eqs, i, j, g,
                                  conds[i][j])
        # The last of these is the step that selects the branch when the
        # equation is the chain's else (the last one); it closes the goal
        # when the branch's body is already the equation's right hand side.
        last_nav = (j == i - 1) and (i == len(eqs) - 1) and closes_now
        g = prover.step('← rewrite if_not_P goal=%d facts=[%d]' % (g, neg),
                        new=0 if last_nav else 1) or g
    if i < len(eqs) - 1:
        c2 = _condition_fact(prover, arg_types, r, eqs, i, conds[i][i], g, dmap)
        g = prover.step('← rewrite if_P goal=%d facts=[%d]' % (g, c2),
                        new=0 if closes_now else 1) or g
    # Which step selected the branch: the chain's last equation has no test
    # of its own, and a single-equation definition has no chain at all.
    selected_by_step = (i < len(eqs) - 1) or i > 0
    if tcall is None:
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
        if not rest:
            prover.step('← rule eq_refl goal=%d' % c3, new=0)
        return prover.text()
    eq = eqs[i]
    obligation_prop = _decrease_prop(arg_types, r, tcall, _tuple_of(eq))
    if i < len(eqs) - 1 and is_exists(conds[i][i]):
        # Both this branch's test (once its witness is given) and the
        # decrease obligation would state the same proposition, and the
        # stable-ID layer keys items by proposition: the second one reuses
        # the first one's ID, which no emitted `goal=` can name.  A
        # one-argument datatype reaches this whenever a recursive equation
        # with a constructor pattern stands before the chain's end -- its
        # obligation is the identity `C t = C t`.  The way out is to test
        # with a generated discriminator per constructor instead of the
        # existential, which is what `case` compiles to.
        wit = _leaf_tuple(_pattern_leaves(_eq_args(eq)[r]))
        test = _subst(conds[i][i].arg.body, {_exists_var(conds[i][i]): wit})
        if _prints(test) == obligation_prop:
            raise FunGenError(
                'fun %s: equation %d tests its pattern with an existential '
                'and then states the same proposition as its decrease '
                'obligation (%s); the two would share a stable ID'
                % (name, i + 1, obligation_prop))
    c_cut = prover.step('cut "%s" goal=%d' % (obligation_prop, g))
    # The rules are taken from the obligation's own term -- the one the
    # cut above states, with the projections of both the call and the
    # pattern -- because that is what the goal has: computing them from
    # the two projections separately emits steps the sweep has already
    # cleared, and deduping them loses a level when the projection is
    # nested (`snd (snd p)`, three arguments and up).
    obligation = _relation(arg_types[r])(_proj_term(arg_types, r, tcall))(
        _proj_term(arg_types, r, _tuple_of(eq))).beta_norm()
    proj = _reduce_used(obligation, dmap)[1]
    closes = _decrease_closes(arg_types, r, tcall, _tuple_of(eq))
    c3 = c_cut
    for i3, rule in enumerate(proj):
        last = (i3 == len(proj) - 1)
        if last and closes:
            prover.step('← rewrite %s goal=%d' % (rule, c3), new=0)
        else:
            c3 = prover.step('← rewrite %s goal=%d' % (rule, c3))
    if not closes:
        witness = _decrease_witness(arg_types, r, tcall, _tuple_of(eq), eq)
        if witness is not None:
            c3 = prover.step('← inst %s goal=%d' % (witness, c3))
        prover.step('← rule eq_refl goal=%d' % c3, new=0)
    elif not proj:
        # Recursion on a single argument: the projections are the
        # identity, so no projection rule applies and the obligation
        # already reads `t = t`.  It still needs its closing step --
        # `closes` only says the last *rewrite* closes the goal, and
        # there is no rewrite here.  The step creates nothing, so the
        # counters below are unaffected.
        prover.step('← rule eq_refl goal=%d' % c3, new=0)
    g = prover.step('← rewrite %s_rel_def goal=%d' % (cname, g))
    g = prover.step('← rewrite cut_def goal=%d' % g)
    # `if_P` discharges the goal's condition with the obligation itself,
    # so it takes the *cut*'s ID: the obligation's own proof may have
    # ended on an instance (`inst` on the list's existential, a rewrite
    # rule for nat), whose proposition is not the condition.
    prover.step('← rewrite if_P goal=%d facts=[%d]' % (g, c_cut), new=0)
    return prover.text()


def _require_in_scope(arg_types, r, recursive=True):
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
    """
    from kernel import theory
    needed = ['wfrec_eq', 'wfrec_H_def', 'cut_def', 'if_P', 'if_not_P',
              'eq_refl', 'snd_def_1', 'fst_def_1']
    if recursive:
        needed.append('wf_measure_gen')
        needed.append('ineq_sym')
        needed.append(_subterm(arg_types[r])[1])
    else:
        needed.append('wf_false')
    for th_name in needed:
        try:
            theory.get_theorem(th_name)
        except Exception:
            raise FunGenError(
                'the well-founded-recursion machinery (%s) is not in scope; '
                'add the wf/list theory to this file imports' % th_name)


def _expand(data):
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
    r = recursion_position(arg_types, lhs)
    if r is None:
        raise FunGenError('fun %s: a definition without constructor patterns '
                          'is not emitted yet' % name)
    # Each equation matches one constructor at the recursion position, and
    # the roots have to be pairwise distinct: the branch chain decides by
    # `t = C _` alone, so two equations with the same root would need the
    # more specific pattern to be subtracted from the more general one
    # (Isabelle's sequential mode does exactly that).  The tests of the
    # earlier branches are refuted with the datatype's distinctness axioms,
    # which is why a non-nullary pattern's test is an existential over one
    # witness tuple: `elim` takes it apart in one step.
    roots = []
    for i, args in enumerate(lhs):
        cname_i = _constr_name(args, r)
        constrs = _constr_names(arg_types[r])
        if constrs is None or cname_i not in constrs:
            raise FunGenError(
                'fun %s: the pattern %s at argument %d is not a constructor '
                'pattern of %s' % (name, _prints(args[r]), r + 1,
                                   _printt(arg_types[r])))
        roots.append(cname_i)
    if len(set(roots)) != len(roots):
        dup = [c for c in roots if roots.count(c) > 1][0]
        raise FunGenError(
            'fun %s: %s is the constructor of more than one equation; '
            'overlapping patterns need pattern subtraction, which this '
            'emitter does not do' % (name, dup))
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
        if len(tuples) > 1:
            raise FunGenError(
                'fun %s: %d distinct recursive calls in one equation; the '
                'emitter handles one so far' % (name, len(tuples)))
        calls.append(tuples[0] if tuples else None)
    recursive = any(c is not None for c in calls)
    _require_in_scope(arg_types, r, recursive)

    dmap = _destructor_maps(arg_types, r)
    rules = [_reduce_used(_body_term(name, arg_types, res_type, eqs, r,
                                     _tuple_of(eq)), dmap)[1] for eq in eqs]
    # `conds[i][j]` is the test of equation j as this branch's goal has it:
    # the projection already reduced to the branch's own pattern.
    conds = [[_reduce(_cond_of(lhs[j][r],
                               _proj_term(arg_types, r, _tuple_of(eqs[i]))),
                      dmap)
              for j in range(i + 1)] for i in range(len(eqs))]
    entries = [_entry([text]) for text in _def_entries(
        name, cname, arg_types, res_type,
        _body_prop(name, arg_types, res_type, eqs, r),
        _rel_body(arg_types, r, recursive))]
    entries.append(_entry(_rel_wf_entry(cname, arg_types, r, recursive)))
    for i, eq in enumerate(eqs):
        eq_text = _equation_text(name, ty, data['rules'][i]['prop'], eq)
        text = ['theorem %s_def_%d' % (cname, i + 1),
                '  fixes %s' % _typenames(sorted(eq.get_vars(),
                                                 key=lambda v: v.name)),
                '  prop %s' % eq_text,
                '  [hint_rewrite]',
                'proof']
        text.extend(_def_entry(name, cname, arg_types, res_type, eqs, r, i,
                               conds, rules[i],
                               tupled_arg(calls[i]) if calls[i] else None,
                               dmap))
        text.append('qed')
        entries.append(_entry(text))
    _require_parsable_defs(entries[:2], name)
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
    """
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
    parts = [name] + [_ascribed_term(a, missing) for a in args]
    return "%s = %s" % (" ".join(parts), _ascribed_term(eq.rhs, missing))


def _ascribed_term(t, missing):
    """A term, ascribed with its own type when that names a missing one."""
    text = _prints(t)
    Ty = t.get_type()
    if any("'" + tv.name in missing for tv in Ty.get_tvars()):
        text = "(%s::%s)" % (text, _printt(Ty))
    return text


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


def expand_item(data):
    """Item dicts for a `fun` definition, or None to keep it axiomatized.

    None means the definition is outside the supported increment, so the
    caller keeps the current mechanism; nothing is silently approved.
    Set HOLPY_FUNGEN_DEBUG to see the underlying exception instead.
    """
    try:
        return _expand(data)
    except FunGenError:
        return None
    except Exception:
        if os.environ.get('HOLPY_FUNGEN_DEBUG'):
            raise
        return None

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
from syntax.logicops import Exists, is_exists
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
    recursion position become destructor applications.  Passing the
    literal tuple of an equation gives the body in exactly the shape the
    goal has after the corresponding rewrites.
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
    pattern = lhs_args[r]
    head, args = pattern.strip_comb()
    for j, a in enumerate(args):
        if not a.is_var():
            raise FunGenError(
                "nested pattern in %s is not supported" %
                printer.print_term(pattern))
        env[a.name] = destructor(head.name, j, projection(p, arg_types, r))
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
        raise FunGenError(
            "a binder in an equation's right hand is not supported: %s" %
            printer.print_term(t))
    if t.is_var() and t.name in env:
        return env[t.name]
    return t


def branch_condition(lhs_args, r, p):
    """Condition testing the recursion argument against a pattern.

    A nullary constructor is tested by equality; a constructor with
    arguments by an existential, since the pattern's variables are not in
    scope in the condition.
    """
    arg_types = [a.get_type() for a in lhs_args]
    proj = projection(p, arg_types, r)
    head, args = lhs_args[r].strip_comb()
    if not args:
        return Eq(proj, lhs_args[r])
    binders = [Var("_a%d" % (j + 1), a.get_type()) for j, a in enumerate(args)]
    res = Eq(proj, head(*binders))
    for v in reversed(binders):
        res = Exists(v, res)
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


def _sweep_once(t, dmap):
    """One sweep: (term, rules) as `rewrite`'s own conv would leave them.

    `rewrite` in goal mode goes through `top_sweep_conv` (core/conv/
    core.py), which tries the rule at a node and, *when it fires there*,
    stops on that path; it descends into function, argument and binder
    body only where nothing fired.  So one step rewrites the top-most
    redexes and leaves a redex nested under another one for the next step
    -- which is why the emitted step sequence is one rule per *pass*, and
    why the same rule can appear twice in a row when the projections are
    nested (`snd (snd p)`, as three-argument definitions have).
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

    res = rec(t)
    return res, _dedupe(rules)


def _reduce_used(t, dmap):
    """(fully reduced term, the rewrite steps the goal needs, in order).

    A step is one `rewrite`, which sweeps; each pass takes the rules the
    top-most redexes need, and the term is swept again for the next level.
    """
    steps = []
    while True:
        t2, rules = _sweep_once(t, dmap)
        if not rules:
            return t, steps
        steps.extend(rules)
        t = t2


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


def _rel_wf_entry(cname, arg_types, r):
    """The `wf` obligation: the relation is well-founded.

    The relation def is a lambda, so `rewrite` unfolds it in the
    unapplied goal `wf <c>_rel` without a beta redex; the lift through
    the projection is `wf_measure_gen`, instantiated explicitly because
    its pattern `?R (?m x) (?m y)` does not match a projection
    application on its own.
    """
    T = arg_types[r]
    Rr, lemma = _subterm(T)
    prop = _rel_wf_prop(cname, arg_types)
    prover = _Proof()
    g = prover.step('← rewrite %s_rel_def goal=0' % cname)
    if len(arg_types) > 1:
        m_ty = _printt(TFun(tupled_type(arg_types), T))
        g = prover.step('← rule wf_measure_gen param_R="%s" param_m="(%s::%s)" '
                        'goal=%d' % (Rr, _prints(_proj_const(arg_types, r)),
                                     m_ty, g))
    prover.step('← rule %s goal=%d' % (lemma, g), new=0)
    return ['theorem %s_rel_wf' % cname, '  prop %s' % prop,
            'proof'] + prover.text() + ['qed']


def _negate_condition(prover, th, th_name, pattern_vars, goal_id, nullary_pat,
                      rec_pat):
    """Derive the negation of the computed condition of a nullary pattern.

    The first branch's condition is `proj = <nullary constructor>`; the
    recursive branch needs its negation.  The datatype's distinctness
    axiom gives `not (nullary = C args)`; ineq_sym flips it.  The axiom's
    schematic variables (named `param_<x>` for each `?x` in its
    statement) are instantiated with the pattern's bound variables in
    order.
    """
    svars = sorted(set(re.findall(r"\?([A-Za-z_][A-Za-z0-9_']*)",
                                  _prints(th.prop))))
    args = " ".join("param_%s=%s" % (
        v, pattern_vars[j] if j < len(pattern_vars) else v)
        for j, v in enumerate(svars))
    f1 = prover.step("→ forward %s %s goal=%d" % (th_name, args, goal_id))
    return prover.step(
        '→ forward ineq_sym param_x="%s" param_y="%s" goal=%d facts=[%d]'
        % (_arg_text(nullary_pat), _arg_text(rec_pat), goal_id, f1))


def _proj_term(arg_types, r, t):
    """Projection of component r, as a term (identity for one argument)."""
    return projection(t, arg_types, r) if len(arg_types) > 1 else t


def _proj_const(arg_types, r):
    """The projection as a plain function, for `wf_measure_gen`'s map.

    Two arguments is the emitter's limit.  The relation side is
    arity-generic (the `wf` obligations of three-argument definitions
    replay), but the equation proofs are not: the projection rewrites are
    taken from the *body*'s reduction, while the goal at that point also
    contains the condition, whose projections can need one more level
    (`snd (snd p)`), so a step lands with no redex to fire on
    (`fst_def_1`).  Fixing it means computing the steps for the goal's own
    term per equation, not for the body.
    """
    Tup = tupled_type(arg_types)
    T = arg_types[r]
    return Const('fst' if r == 0 else 'snd', TFun(Tup, T))


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


def _body_term(name, arg_types, res_type, eqs, r, p=None):
    """The `<c>_H g p = ...` right hand side, as a term.

    With p omitted the body is built over the tuple variable (the def
    item); passing a literal tuple gives the shape the goal takes for
    that equation, which is what decides the projection/destructor
    rewrites its proof needs.
    """
    Tup = tupled_type(arg_types)
    if p is None:
        p = Var('p', Tup)
    g = Var('g', TFun(Tup, res_type))
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    lhs = [_eq_args(eq) for eq in eqs]
    b1 = replace(eqs[0].rhs, f_const, len(arg_types),
                 variable_env(lhs[0], r, p), g)
    b2 = replace(eqs[1].rhs, f_const, len(arg_types),
                 variable_env(lhs[1], r, p), g)
    cond = branch_condition(lhs[0], r, p)
    return Const('IF', TFun(BoolType, TFun(
        res_type, TFun(res_type, res_type))))(cond)(b1)(b2)


def _body_prop(name, arg_types, res_type, eqs, r, p=None):
    """The `<c>_H g p = ...` right hand side, printed."""
    return _prints(_body_term(name, arg_types, res_type, eqs, r, p))


def _rel_body(arg_types, r):
    """The relation as a lambda over the tuple variables p and q.

    The def's right hand side is the whole lambda: `wf <c>_rel` is
    unfolded by rewriting the unapplied constant, which only works if the
    definitional equation is `c_rel = (%p. %q. ...)`.  The body is the
    datatype's component relation applied to the projected tuple
    components, so it is the same proposition the lifted condition is.
    """
    T = arg_types[r]
    Tup = _printt(tupled_type(arg_types))
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


def _def_base_entry(name, cname, arg_types, res_type, eq, r, cond, prop,
                    rules):
    """Proof of the nullary-constructor equation (the if-true branch).

    Everything is computed before the condition is cut, so the cut's
    proposition is exactly the goal's condition and the branch body is
    already in the source's shape when `if_P` selects it.
    """
    prover = _Proof()
    g = prover.step('← unfold %s_def goal=0' % cname)
    a = _wf_fact(prover, cname, arg_types, g)
    d = _in_def_fact(prover, cname, arg_types, res_type, g)
    g = prover.step('← rewrite wfrec_eq goal=%d facts=[%d,%d]' % (g, a, d))
    g = prover.step('← unfold wfrec_H_def goal=%d' % g)
    g = prover.step('← unfold %s_H_def goal=%d' % (cname, g))
    for rule in rules:
        g = prover.step('← rewrite %s goal=%d' % (rule, g))
    c = prover.step('cut "%s" goal=%d' % (_prints(cond), g))
    prover.step('← rule eq_refl goal=%d' % c, new=0)
    prover.step('← rewrite if_P goal=%d facts=[%d]' % (g, c), new=0)
    return prover.text()


def _def_rec_entry(name, cname, arg_types, res_type, eq, r, lhs_null, tcall,
                   rules):
    """Proof of the recursive equation (the else branch).

    The wfrec equation is instantiated in its own cut: rewriting the main
    goal with it directly would also rewrite the right hand side, where
    the same constant occurs with different arguments.
    """
    T = arg_types[r]
    t = _arg_text(_tuple_of(eq))
    prover = _Proof()
    g = prover.step('← unfold %s_def goal=0' % cname)
    a = _wf_fact(prover, cname, arg_types, g)
    d = _in_def_fact(prover, cname, arg_types, res_type, g)
    fp = "%s_in %s = wfrec_H %s_rel %s_H %s_in %s" % (
        cname, t, cname, cname, cname, t)
    c = prover.step('cut "%s" goal=%d' % (fp, g))
    prover.step('← rule wfrec_eq goal=%d facts=[%d,%d]' % (c, a, d), new=0)
    g = prover.step('← rewrite source=prev goal=%d facts=[%d]' % (g, c))
    g = prover.step('← unfold wfrec_H_def goal=%d' % g)
    g = prover.step('← unfold %s_H_def goal=%d' % (cname, g))
    for rule in rules:
        g = prover.step('← rewrite %s goal=%d' % (rule, g))

    th_name, th = _distinct_neq(
        arg_types[r].name, _constr_name(lhs_null, r),
        _constr_name(_eq_args(eq), r))
    if th is None:
        raise FunGenError('fun %s: no distinctness axiom found for the two '
                          'constructors' % name)
    neg = _negate_condition(prover, th, th_name, _pattern_vars(eq, r), g,
                            lhs_null[r], _eq_args(eq)[r])
    g = prover.step('← rewrite if_not_P goal=%d facts=[%d]' % (g, neg))
    dmap = _destructor_maps(arg_types, r)
    if tcall is None:
        # No recursive call in this equation: the else branch is the right
        # hand side itself, with the pattern's variables taken apart by
        # destructors, and no obligation (and no `cut`) arises.  The
        # projections still have to be reduced for the goal to read as the
        # equation does.
        proj = _reduce_used(_proj_term(arg_types, r, _tuple_of(eq)), dmap)[1]
        for n, rule in enumerate(proj):
            if n == len(proj) - 1:
                prover.step('← rewrite %s goal=%d' % (rule, g), new=0)
            else:
                g = prover.step('← rewrite %s goal=%d' % (rule, g))
        prover.step('← rule eq_refl goal=%d' % g, new=0)
        return prover.text()
    c_cut = prover.step('cut "%s" goal=%d'
                        % (_decrease_prop(arg_types, r, tcall, _tuple_of(eq)), g))
    proj = _dedupe(_reduce_used(_proj_term(arg_types, r, _tuple_of(eq)),
                                dmap)[1]
                   + _reduce_used(_proj_term(arg_types, r, tcall), dmap)[1])
    closes = _decrease_closes(arg_types, r, tcall, _tuple_of(eq))
    c3 = c_cut
    for i, rule in enumerate(proj):
        last = (i == len(proj) - 1)
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


def _require_in_scope(arg_types, r):
    """Names the emitted items and proofs depend on.

    A definition is only expanded when the file can actually see them:
    the generated proofs reference the well-founded-recursion combinators
    (from the `wf` theory) and, through the relation, the datatype's
    well-foundedness lemma.  A file that imports neither keeps the current
    axiomatization instead of getting items that cannot even be parsed.
    """
    from kernel import theory
    needed = ['wfrec_eq', 'wfrec_H_def', 'cut_def', 'if_P', 'if_not_P',
              'wf_measure_gen', 'ineq_sym', 'eq_refl', 'snd_def_1',
              'fst_def_1', _subterm(arg_types[r])[1]]
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
    if len(arg_types) > 2:
        raise FunGenError('fun %s: %d arguments; the emitter handles two so '
                          'far' % (name, len(arg_types)))
    lhs = [_eq_args(eq) for eq in eqs]
    r = recursion_position(arg_types, lhs)
    if r is None:
        raise FunGenError('fun %s: a definition without constructor patterns '
                          'is not emitted yet' % name)
    if len(eqs) != 2:
        raise FunGenError('fun %s: %d equations; the emitter handles two '
                          'branches so far' % (name, len(eqs)))
    _, nullary_args = lhs[0][r].strip_comb()
    if nullary_args:
        raise FunGenError('fun %s: the nullary-constructor equation must come '
                          'first' % name)
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    if _calls(eqs[0].rhs, f_const, len(arg_types)):
        raise FunGenError('fun %s: the nullary-constructor equation must not '
                          'be recursive' % name)
    calls = _calls(eqs[1].rhs, f_const, len(arg_types))
    # Several recursive calls are fine as long as they ask for the same
    # thing: the body then mentions one `g (...)` term rather than several,
    # so one obligation covers them all (`filter` and `remdups` recurse on
    # the same tail in both branches).  No call at all is fine too -- the
    # equation needs no decrease -- which is the shape of a definition over
    # a datatype such as nat's `Pre`.
    tuples = []
    for c in calls:
        if c not in tuples:
            tuples.append(c)
    if len(tuples) > 1:
        raise FunGenError(
            'fun %s: %d distinct recursive calls in one equation; the '
            'emitter handles one so far' % (name, len(tuples)))
    _require_in_scope(arg_types, r)

    dmap = _destructor_maps(arg_types, r)
    cond = _reduce(branch_condition(lhs[0], r, _tuple_of(eqs[0])), dmap)
    rules = [_reduce_used(_body_term(name, arg_types, res_type, eqs, r,
                                     _tuple_of(eq)), dmap)[1] for eq in eqs]
    entries = [_entry([text]) for text in _def_entries(
        name, cname, arg_types, res_type,
        _body_prop(name, arg_types, res_type, eqs, r), _rel_body(arg_types, r))]
    entries.append(_entry(_rel_wf_entry(cname, arg_types, r)))
    for i, eq in enumerate(eqs):
        eq_text = _equation_text(name, ty, data['rules'][i]['prop'], eq)
        text = ['theorem %s_def_%d' % (cname, i + 1),
                '  fixes %s' % _typenames(sorted(eq.get_vars(),
                                                 key=lambda v: v.name)),
                '  prop %s' % eq_text,
                '  [hint_rewrite]',
                'proof']
        if i == 0:
            text.extend(_def_base_entry(name, cname, arg_types, res_type, eq,
                                        r, cond, eq_text, rules[0]))
        else:
            text.extend(_def_rec_entry(name, cname, arg_types, res_type, eq, r,
                                       lhs[0],
                                       tupled_arg(calls[0]) if calls else None,
                                       rules[1]))
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

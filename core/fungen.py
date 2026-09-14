"""Expansion of a `fun` definition, transformation layer (phase 4).

A `fun` definition is no longer axiomatized: it expands into a group of
ordinary items whose equations are *derived* from well-foundedness.  This
module is the term-level transformation; the proof templates that turn
its result into items come next and live elsewhere.

For `fun f :: T1 => ... => Tn => Tr` with equations over the tupled
argument p : Tup it produces

  * `<f>_H`, the body functional: branches are the equations' right
    hands, every source variable written as a projection of p, every
    recursive call `f a1 .. an` replaced by `g (a1 .. an)`;
  * `<f>_measure`, the measure on the tupled argument (absent when the
    equations have no recursive calls).

The internal fixpoint constant is uncurried over the tuple because
wf_rec_exists's domain is a single argument; the user-facing curried
constant is defined through it, so equations keep the source's shape.

Everything outside this increment is reported as FunGenError instead of
being guessed at:

  * at most one argument may carry constructor patterns;
  * at most two equations, so the body is `if c then b1 else b2`;
  * a binder (lambda) in an equation's right hand is not traversed;
  * the destructors rewriting a pattern variable are `Pre` (nat) and
    `hd`/`tl` (list); another datatype needs constructor-argument
    destructors, which do not exist yet.
"""
from kernel.type import TFun, TConst, BoolType
from kernel.term import Var, Const, Eq
from syntax import printer
from syntax.logicops import Exists
from syntax.settings import global_setting

NatType = TConst('nat')


class FunGenError(Exception):
    """Raised when a definition is outside the current increment."""


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


def plain_env(lhs_args):
    """Term for each source variable, all of them projections."""
    arg_types = [a.get_type() for a in lhs_args]
    p = Var('p', tupled_type(arg_types))
    env = {}
    for i, a in enumerate(lhs_args):
        if not a.is_var():
            raise FunGenError(
                "argument %s is not a plain variable" %
                printer.print_term(a))
        env[a.name] = projection(p, arg_types, i)
    return env


def variable_env(lhs_args, r):
    """Term for each source variable in terms of the tuple p.

    Plain arguments become projections; the pattern variables at the
    recursion position become destructor applications.  The tuple
    variable is `p` of the tupled argument type.
    """
    arg_types = [a.get_type() for a in lhs_args]
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
    """Substitute source variables; replace `f a1 .. an` by `g (a1 .. an)`."""
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


def expand_body(name, arg_types, res_type, eq_props):
    """Body functional prop and measure prop, printed for the item format.

    Returns (h_prop, measure_prop); measure_prop is None when the
    equations have no recursive calls (the relation is then empty).
    """
    n = len(arg_types)
    eq_lhs_args = [eq.lhs.strip_comb()[1] for eq in eq_props]
    r = recursion_position(arg_types, eq_lhs_args)

    if r is None:
        if len(eq_props) != 1:
            raise FunGenError(
                "fun %s: several equations without constructor patterns "
                "are not supported" % name)
    elif len(eq_props) != 2:
        raise FunGenError(
            "fun %s: %d equations; the body emitter handles two branches "
            "so far" % (name, len(eq_props)))

    Tup = tupled_type(arg_types)
    p = Var('p', Tup)
    g = Var('g', TFun(Tup, res_type))
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))

    with global_setting(unicode=True):
        if r is None:
            env = plain_env(eq_lhs_args[0])
            body = replace(eq_props[0].rhs, f_const, n, env, g)
            return ("%s_H g p = %s" % (name, printer.print_term(body)),
                    None)

        env1 = variable_env(eq_lhs_args[0], r)
        env2 = variable_env(eq_lhs_args[1], r)
        b1 = replace(eq_props[0].rhs, f_const, n, env1, g)
        b2 = replace(eq_props[1].rhs, f_const, n, env2, g)
        cond = branch_condition(eq_lhs_args[0], r, p)
        body = Const('IF', TFun(BoolType, TFun(res_type, TFun(res_type, res_type))))(cond)(b1)(b2)
        h_prop = "%s_H g p = %s" % (name, printer.print_term(body))
        measure = _measure_prop(name, arg_types, r, p)
        return h_prop, measure


def _measure_prop(name, arg_types, r, p):
    """Measure prop on the tupled argument, or raise for unsupported."""
    T = arg_types[r]
    proj = projection(p, arg_types, r)
    with global_setting(unicode=True):
        if T == NatType:
            return "%s_measure p = %s" % (name, printer.print_term(proj))
        if T.is_tconst() and T.name == 'list':
            return "%s_measure p = length (%s)" % (
                name, printer.print_term(proj))
    raise FunGenError(
        "fun %s: no size measure is known for recursion on %s; attach a "
        "relation" % (name, printer.print_type(T)))


# ---------------------------------------------------------------------------
# Item emission.
#
# The generated proofs are the chains validated by hand in
# library/wfrec_example.pyhol (nat) and in the list development; they are
# emitted as item text in the *existing* format -- literal stable IDs with
# the `#[N]` annotations that pin them -- and parsed back by the ordinary
# item parser, so nothing about the .pyhol surface changes.
# ---------------------------------------------------------------------------

class _Proof:
    """Emit a proof block while allocating the stable IDs it pins."""

    def __init__(self):
        self.lines = []
        self.n = 1

    def step(self, text, new=1):
        """Append a step; return the IDs of its new items (creation order).

        new=0 for a step that closes its goal and creates nothing.
        """
        self.lines.append('  ' + text)
        ids = list(range(self.n, self.n + new))
        self.n += new
        for i in ids:
            self.lines.append('    #[%d]' % i)
        return ids

    def text(self):
        return self.lines


def _prints(t):
    with global_setting(unicode=True):
        return printer.print_term(t)


def _typenames(vars_):
    return ", ".join("%s :: %s" % (v.name, printer.print_type(v.T))
                     for v in vars_)


def _fixes(eq):
    return sorted(eq.get_vars(), key=lambda v: v.name)


def _distinct_neq(tyname, c1, c2):
    """Name of the distinctness axiom for two constructors, or None."""
    from kernel import theory
    for name in ("%s_%s_%s_neq" % (tyname, c1, c2),
                 "%s_%s_%s_neq" % (tyname, c2, c1)):
        try:
            return name, theory.get_theorem(name)
        except Exception:
            continue
    return None, None


def _arg_text(t):
    """A term used as an argument: applications need parentheses.

    The printer writes applications in functional style, so `Pair a b` as
    a function argument would be read back as `(f a) b` without them.
    """
    text = _prints(t)
    return "(%s)" % text if t.is_comb() else text


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
    import re
    svars = sorted(set(re.findall(r"\?([A-Za-z_][A-Za-z0-9_']*)",
                                  _prints(th.prop))))
    args = " ".join("param_%s=%s" % (
        v, pattern_vars[j] if j < len(pattern_vars) else v)
        for j, v in enumerate(svars))
    f1 = prover.step("→ forward %s %s goal=%d" % (th_name, args, goal_id))[0]
    f2 = prover.step(
        '→ forward ineq_sym param_x="%s" param_y="%s" goal=%d facts=[%d]'
        % (_arg_text(nullary_pat), _arg_text(rec_pat), goal_id, f1))[0]
    return f2


def _entry(lines):
    """Parse an emitted entry back with the ordinary item parser."""
    from syntax import pyhol
    item, _ = pyhol._parse_item(lines, 0)
    return item


def _tuple_of(eq, r):
    return tupled_arg(eq.lhs.strip_comb()[1])


def _pattern_vars(eq, r):
    """Bound variables of the pattern at the recursion position."""
    _, args = eq.lhs.strip_comb()[1][r].strip_comb()
    return [a.name for a in args if a.is_var()]


def _defs(name, arg_types, res_type, h_prop, measure_prop):
    """The four definitional entries."""
    Tup = tupled_type(arg_types)
    n = len(arg_types)
    with global_setting(unicode=True):
        h_ty = printer.print_type(TFun(TFun(Tup, res_type), TFun(Tup, res_type)))
        m_ty = printer.print_type(TFun(Tup, NatType))
        in_ty = printer.print_type(TFun(Tup, res_type))
        f_ty = printer.print_type(TFun(*(list(arg_types) + [res_type])))
    res = ['def %s_H :: %s = %s' % (name, h_ty, h_prop)]
    if measure_prop is not None:
        res.append('def %s_measure :: %s = %s' % (name, m_ty, measure_prop))
        res.append('def %s_in :: %s = %s' % (name, in_ty,
                                              _in_def_prop(name)))
    xs = [Var('x%d' % (i + 1), arg_types[i]) for i in range(n)]
    res.append('def %s :: %s = %s %s = %s_in %s' % (
        name, f_ty, name, " ".join(x.name for x in xs), name,
        _arg_text(tupled_arg(xs))))
    return res


def _measure_type(name, arg_types, res_type):
    """Printed type of the measure constant (Tup => nat)."""
    with global_setting(unicode=True):
        return printer.print_type(TFun(tupled_type(arg_types), NatType))


def _in_type(arg_types, res_type):
    """Printed type of the internal fixpoint constant (Tup => Tr)."""
    with global_setting(unicode=True):
        return printer.print_type(TFun(tupled_type(arg_types), res_type))


def _in_def_cut(name, in_ty):
    """The def equation as a cut, ascribed so the parser can type it."""
    return "(%s_in::%s) = (SOME g. !z. g z = wfrec_H (measure %s_measure) %s_H g z)" % (
        name, in_ty, name, name)


def _in_def_prop(name):
    """The fixpoint definition's equation, as emitted in its def item."""
    return ("%s_in = (SOME g. !z. g z = wfrec_H (measure %s_measure) %s_H g z)"
            % (name, name, name))


def _wf_entry(name, m_ty):
    """The `wf` obligation.

    The measure is ascribed its type: for a polymorphic definition the
    unapplied constant leaves the parser's type inference with nothing to
    instantiate its type variables from (`wf (measure f_measure)` alone is
    not typeable), while the ascription pins them.
    """
    if m_ty is None:
        return ['theorem %s_wf' % name, '  prop wf (%x. %y. false)', 'proof',
                '  ← rule wf_false goal=0', 'qed']
    return ['theorem %s_wf' % name,
            '  prop wf (measure (%s_measure::%s))' % (name, m_ty),
            'proof', '  ← rule wf_measure goal=0', 'qed']


def _uses(t, const_name):
    """Whether t contains an application of the given constant."""
    if t.is_comb():
        h, _ = t.strip_comb()
        if h.is_const() and h.name == const_name:
            return True
        return _uses(t.fun, const_name) or _uses(t.arg, const_name)
    if t.is_abs():
        return _uses(t.body, const_name)
    return False


def _projection_rules(t):
    """Projection rewrites computing the fst/snd applications in t.

    At most one rule per shape the emitter supports (two source
    arguments), so a single pass each suffices.
    """
    rules = []
    if _uses(t, 'snd'):
        rules.append('snd_def_1')
    if _uses(t, 'fst'):
        rules.append('fst_def_1')
    return rules


def _body_in_tuple(name, arg_types, res_type, eq, r):
    """The equation's right hand as a term in the tuple variable p."""
    env = variable_env(eq.lhs.strip_comb()[1], r)
    f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
    return replace(eq.rhs, f_const, len(arg_types), env, Var('g', None))


def _def_proof(name, arg_types, res_type, eq, r, cond0, body, m_ty,
               in_ty):
    """Proof of the nullary-constructor equation (the if-true branch).

    The condition's projections are computed only inside the condition's
    own cut: the `if_P` fact has to match the goal's condition, which a
    greedy projection rewrite in the goal would have computed away.  The
    body's projections are computed after `if_P`, when the condition is
    gone.
    """
    t = _arg_text(_tuple_of(eq, r))
    base = _Proof()
    g = 0
    g = base.step('← unfold %s_def goal=%d' % (name, g))[0]
    a = base.step('→ forward wf_measure param_m="(%s_measure::%s)" goal=%d'
                 % (name, m_ty, g))[0]
    d = base.step('cut "%s" goal=%d' % (_in_def_cut(name, in_ty), g))[0]
    base.step('← unfold %s_in_def goal=%d' % (name, d), new=0)
    fp = "%s_in %s = wfrec_H (measure %s_measure) %s_H %s_in %s" % (
        name, t, name, name, name, t)
    c = base.step('cut "%s" goal=%d' % (fp, g))[0]
    base.step('← rule wfrec_eq goal=%d facts=[%d,%d]' % (c, a, d), new=0)
    g = base.step('← rewrite source=prev goal=%d facts=[%d]' % (g, c))[0]
    g = base.step('← unfold wfrec_H_def goal=%d' % g)[0]
    g = base.step('← unfold %s_H_def goal=%d' % (name, g))[0]
    c2 = base.step('cut "%s" goal=%d' % (_prints(cond0), g))[0]
    rules = _projection_rules(cond0)
    if len(rules) == 1:
        # The rewrite computes the projection and the cut closes by
        # reflexivity (pattern = pattern).
        base.step('← rewrite %s goal=%d' % (rules[0], c2), new=0)
    else:
        base.step('← rule eq_refl goal=%d' % c2, new=0)
    body_rules = _projection_rules(body)
    g2 = base.step('← rewrite if_P goal=%d facts=[%d]' % (g, c2),
                   new=(1 if body_rules else 0))
    for i, rule in enumerate(body_rules):
        last = (i == len(body_rules) - 1)
        g2 = base.step('← rewrite %s goal=%d' % (rule, g2[0]),
                       new=(0 if last else 1))
    return base.text()


def _def_proof_recursive(name, arg_types, res_type, eq, r, lhs_null,
                         cond0, m_ty, in_ty):
    """Proof of the recursive equation (the else branch)."""
    n = len(arg_types)
    t = _arg_text(_tuple_of(eq, r))
    calls = _calls(eq.rhs, Const(name, TFun(*(list(arg_types) + [res_type]))), n)
    if len(calls) != 1:
        raise FunGenError(
            'fun %s: %d recursive calls in one equation; the emitter handles '
            'one so far' % (name, len(calls)))
    tcall = _arg_text(tupled_arg(calls[0]))
    prover = _Proof()
    g = 0
    g = prover.step('← unfold %s_def goal=%d' % (name, g))[0]
    a = prover.step('→ forward wf_measure param_m="(%s_measure::%s)" goal=%d'
                   % (name, m_ty, g))[0]
    d = prover.step('cut "%s" goal=%d' % (_in_def_cut(name, in_ty), g))[0]
    prover.step('← unfold %s_in_def goal=%d' % (name, d), new=0)
    fp = "%s_in %s = wfrec_H (measure %s_measure) %s_H %s_in %s" % (
        name, t, name, name, name, t)
    c = prover.step('cut "%s" goal=%d' % (fp, g))[0]
    prover.step('← rule wfrec_eq goal=%d facts=[%d,%d]' % (c, a, d), new=0)
    g = prover.step('← rewrite source=prev goal=%d facts=[%d]' % (g, c))[0]
    g = prover.step('← unfold wfrec_H_def goal=%d' % g)[0]
    g = prover.step('← unfold %s_H_def goal=%d' % (name, g))[0]
    if n >= 2:
        g = prover.step('← rewrite snd_def_1 goal=%d' % g)[0]
        g = prover.step('← rewrite fst_def_1 goal=%d' % g)[0]
    for rule in _destructor_rules(eq, r):
        g = prover.step('← rewrite %s goal=%d' % (rule, g))[0]
    th_name, th = _distinct_neq(
        arg_types[r].name, _constr_name(lhs_null, r),
        _constr_name(eq.lhs.strip_comb()[1], r))
    if th is None:
        raise FunGenError('fun %s: no distinctness axiom found for the two '
                          'constructors' % name)
    neg = _negate_condition(
        prover, th, th_name, _pattern_vars(eq, r), g, lhs_null[r],
        eq.lhs.strip_comb()[1][r])
    g = prover.step('← rewrite if_not_P goal=%d facts=[%d]' % (g, neg))[0]
    c3 = prover.step('cut "measure %s_measure %s %s" goal=%d'
                     % (name, tcall, t, g))[0]
    d = c3
    for rule in _measure_rules(arg_types[r], name):
        d = prover.step('← rewrite %s goal=%d' % (rule, d))[0]
    prover.step('← rule lesseq_refl goal=%d' % d, new=0)
    g = prover.step('← rewrite cut_def goal=%d' % g)[0]
    prover.step('← rewrite if_P goal=%d facts=[%d]' % (g, c3), new=0)
    return prover.text()


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


def _constr_name(lhs_args, r):
    head, _ = lhs_args[r].strip_comb()
    return head.name


def _destructor_rules(eq, r):
    """Rewrite rules computing the pattern variables of the pattern at r.

    One rule per constructor argument: `Suc m` needs only Pre's second
    rule; `x # xs` needs both hd and tl.
    """
    name = _constr_name(eq.lhs.strip_comb()[1], r)
    if name == 'Suc':
        return ['Pre_def_2']
    if name == 'cons':
        return ['hd_def_1', 'tl_def_1']
    return []


def _measure_rules(T, name):
    """Rewrite chain proving `measure M tcall trec` for the datatype.

    Followed by `lesseq_refl`, which closes the resulting `n <= n`.
    """
    if T == NatType:
        return ['measure_def', '%s_measure_def' % name, 'fst_def_1',
                'less_Suc_lesseq']
    if T.is_tconst() and T.name == 'list':
        # The call's tuple carries the tail directly, so the measure's
        # `length (snd p)` reduces with snd_def_1 alone.
        return ['measure_def', '%s_measure_def' % name, 'snd_def_1',
                'length_def_2', 'less_Suc_lesseq']
    raise FunGenError(
        'no decrease chain known for recursion on %s' %
        printer.print_type(T))



def expand_item(data):
    """Item dicts for a `fun` definition, or None to keep it axiomatized.

    None means the definition is outside the supported increment, so the
    caller keeps the current mechanism; nothing is silently approved.
    """
    try:
        return _expand(data)
    except FunGenError:
        return None


def _require_in_scope(arg_types):
    """Names the emitted items and proofs depend on.

    A definition is only expanded when the file can actually see them:
    the generated proofs reference the well-founded-recursion combinators
    (from the `wf` theory) and, through the measure, nat's comparison
    lemmas.  A file that imports neither keeps the current axiomatization
    instead of getting items that cannot even be parsed.
    """
    from kernel import theory
    needed = ['wfrec_eq', 'wfrec_H_def', 'cut_def', 'wf_measure',
              'less_Suc_lesseq', 'lesseq_refl']
    for name in needed:
        try:
            theory.get_theorem(name)
        except Exception:
            raise FunGenError(
                'the well-founded-recursion machinery (%s) is not in scope; '
                'add the wf theory to this file imports' % name)


def _expand(data):
    from syntax import parser
    from core import context
    name = data['name']
    ty = parser.parse_type(data['type'])
    arg_types, res_type = ty.strip_type()
    with context.fresh_context(defs={name: ty}):
        eqs = [context.parse_term(rule['prop']) for rule in data['rules']]
    if len(arg_types) > 2:
        raise FunGenError(
            'fun %s: %d arguments; the emitter handles two so far'
            % (name, len(arg_types)))
    _require_in_scope(arg_types)
    lhs_args = [eq.lhs.strip_comb()[1] for eq in eqs]
    r = recursion_position(arg_types, lhs_args)
    h_prop, measure_prop = expand_body(name, arg_types, res_type, eqs)
    m_ty = _measure_type(name, arg_types, res_type)

    entries = []
    for text in _defs(name, arg_types, res_type, h_prop, measure_prop):
        entries.append(_entry([text]))
    entries.append(_entry(_wf_entry(name, m_ty if measure_prop is not None
                                    else None)))

    if r is None:
        raise FunGenError('fun %s: non-recursive expansion not emitted yet'
                          % name)
    if len(eqs) != 2:
        raise FunGenError('fun %s: %d equations; the proof emitter handles '
                          'two branches so far' % (name, len(eqs)))
    _, nullary_args = lhs_args[0][r].strip_comb()
    if nullary_args:
        raise FunGenError('fun %s: the nullary-constructor equation must '
                          'come first' % name)
    cond0 = branch_condition(lhs_args[0], r, _tuple_of(eqs[0], r))
    for i, eq in enumerate(eqs):
        text = ['theorem %s_def_%d' % (name, i + 1),
                '  fixes %s' % _typenames(_fixes(eq)),
                '  prop %s' % data['rules'][i]['prop'],
                'proof']
        if i == 0:
            text.extend(_def_proof(
                name, arg_types, res_type, eq, r, cond0,
                _body_in_tuple(name, arg_types, res_type, eq, r), m_ty,
                _in_type(arg_types, res_type)))
        else:
            text.extend(_def_proof_recursive(name, arg_types, res_type, eq, r,
                                             lhs_args[0], cond0, m_ty,
                                             _in_type(arg_types, res_type)))
        text.append('qed')
        entries.append(_entry(text))
    return entries



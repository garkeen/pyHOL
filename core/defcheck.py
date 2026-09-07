"""Definition-legality checks and axiom recipes for `def.ind`
(fun) and `type.ind` (datatype) items.

A `fun` definition is accepted only if its equations are structural
recursion, following the mechanism of HOL Light's
new_recursive_definition:

  * exactly one argument has constructor patterns, in every equation;
  * the other arguments are plain variables;
  * every recursive call is on a direct constructor argument of the
    left-hand side pattern (of the recursion argument; the other call
    arguments may be arbitrary terms, e.g. `TL l`).

Equations that pass the check are consistent: a function satisfying
them exists (by induction on the recursion argument), so they may be
added as axioms.

This module is the gatekeeper of the axiom assumption rule for
definitions (audit §7.2/§7.3): structural recursion, strict
positivity, and the axiom recipes emitted by `datatype` (distinct /
inject / induct / cases) and `inductive` (_cases / _induct) items.
mk_axiom below is the single loading point for these theory axioms.

"""

import itertools

from kernel.type import TVar, TConst, TFun, BoolType
from kernel.term import Var, Const, Implies, Eq, Forall
from syntax.logicops import And, Not
from kernel.thm import Thm
from kernel import extension
from util.name import get_variant_names
from kernel import theory


class StructRecursionError(Exception):
    pass


def _constr_names(T):
    """Return the set of constructor names of the type T, or None if T
    is not an inductive datatype.

    """
    if not T.is_tconst():
        return None
    constrs = theory.thy.get_datatype_constrs(T.name)
    if constrs is None:
        return None
    return {c.name for c in constrs}


def _classify_args(args, Targs):
    """Classify the arguments of an equation lhs.

    Returns (patterns, vars, others): the positions where the argument
    is an application of a constructor of its type, a plain variable,
    or something else.

    """
    patterns = []
    vars = []
    others = []
    for i, (a, T) in enumerate(zip(args, Targs)):
        if a.is_var():
            vars.append(i)
            continue
        constrs = _constr_names(T)
        h, _ = a.strip_comb()
        if constrs is not None and h.is_const() and h.name in constrs:
            patterns.append(i)
        else:
            others.append(i)
    return patterns, vars, others


def _walk(t, f_const, n, r, pattern_args, name, eq_no, in_call=False,
          no_pattern=False):
    """Check the recursive calls in the term t.

    Every application of f_const is checked.  A partial application
    (fewer than n arguments) is a recursive call only when it does not
    form the fun part of a larger application of f_const.  In any
    recursive call the recursion argument (if applied) must be one of
    the pattern_args (the direct constructor arguments of the left-hand
    side pattern).

    """
    if t.is_comb():
        h, cargs = t.strip_comb()
        is_call = (h == f_const)
        if is_call and not in_call:
            if no_pattern:
                raise StructRecursionError(
                    "fun %s: equation %d: recursive call without any "
                    "constructor pattern" % (name, eq_no))
            if r >= len(cargs):
                raise StructRecursionError(
                    "fun %s: equation %d: recursive call with %d "
                    "arguments, expected %d" % (
                        name, eq_no, len(cargs), n))
            if cargs[r] not in pattern_args:
                raise StructRecursionError(
                    "fun %s: equation %d: recursive call is not on a "
                    "subterm of the left-hand side pattern" % (
                        name, eq_no))
        _walk(t.fun, f_const, n, r, pattern_args, name, eq_no,
              in_call=is_call, no_pattern=no_pattern)
        _walk(t.arg, f_const, n, r, pattern_args, name, eq_no,
              in_call=False, no_pattern=no_pattern)
    elif t.is_abs():
        _walk(t.body, f_const, n, r, pattern_args, name, eq_no,
              in_call=False, no_pattern=no_pattern)


def _occurs(name, U):
    """Whether the type constructor with the given name occurs
    anywhere in the type U.

    """
    if U.is_tconst():
        return U.name == name or any(_occurs(name, a) for a in U.args)
    return False


def _check_positive(name, U, cname, i):
    """Check that the datatype name occurs strictly positive in the
    type U (an argument of the constructor cname).

    """
    if U.is_fun():
        if _occurs(name, U.domain_type()):
            raise StructRecursionError(
                "datatype %s: constructor %s: negative occurrence of %s "
                "in the domain of argument %d" % (
                    name, cname, name, i))
        _check_positive(name, U.range_type(), cname, i)
    elif U.is_tconst():
        if U.name == name:
            return
        for a in U.args:
            if _occurs(name, a):
                raise StructRecursionError(
                    "datatype %s: constructor %s: occurrence of %s "
                    "inside %s is not supported" % (name, cname, name, U))
    # Type variables contain no occurrence of name.


def check_datatype_positivity(name, constrs):
    """Check that the datatype name occurs strictly positive in the
    arguments of its constructors.  Raises StructRecursionError if not.

    constrs is a list of parsed constructor dicts with 'name' and
    'type' fields.

    """
    for constr in constrs:
        args, result = constr['type'].strip_type()
        if not result.is_tconst() or result.name != name:
            raise StructRecursionError(
                "datatype %s: constructor %s does not return the "
                "datatype" % (name, constr['name']))
        for i, a in enumerate(args):
            _check_positive(name, a, constr['name'], i + 1)


def check_fun_recursion(name, type, rules):
    """Check that the equations of the fun `name :: type` are
    structural recursion.

    rules is a list of {'prop': equality term}.  Raises
    StructRecursionError if the check fails.

    """
    Targs, _ = type.strip_type()
    n = len(Targs)

    # Find the positions with constructor patterns across all equations.
    pattern_positions = set()
    for rule in rules:
        _, args = rule['prop'].lhs.strip_comb()
        patterns, _, _ = _classify_args(args, Targs)
        pattern_positions.update(patterns)

    f_const = Const(name, type)

    if not pattern_positions:
        # No constructor patterns at all: allow only if there are no
        # recursive calls.
        for i, rule in enumerate(rules):
            _walk(rule['prop'].rhs, f_const, n, 0, [], name, i + 1,
                  no_pattern=True)
        return

    if len(pattern_positions) > 1:
        raise StructRecursionError(
            "fun %s: constructor patterns on arguments %s; only one "
            "argument may have patterns" % (
                name, ", ".join(str(i + 1) for i in sorted(pattern_positions))))

    r = min(pattern_positions)

    constrs_seen = set()
    for i, rule in enumerate(rules):
        prop = rule['prop']
        _, args = prop.lhs.strip_comb()
        patterns, _, others = _classify_args(args, Targs)

        if r not in patterns:
            raise StructRecursionError(
                "fun %s: equation %d: argument %d must have a constructor "
                "pattern in every equation" % (name, i + 1, r + 1))

        bad = [j + 1 for j in others]
        if bad:
            raise StructRecursionError(
                "fun %s: equation %d: arguments %s must be plain variables "
                "(only argument %d may have constructor patterns)" % (
                    name, i + 1, ", ".join(str(j) for j in bad), r + 1))

        h, _ = args[r].strip_comb()
        if h.name in constrs_seen:
            raise StructRecursionError(
                "fun %s: duplicate equations for constructor %s" % (
                name, h.name))
        constrs_seen.add(h.name)

        # Direct constructor arguments of the pattern at position r.
        _, pattern_args = args[r].strip_comb()

        _walk(prop.rhs, f_const, n, r, pattern_args, name, i + 1)


# ---------------------------------------------------------------------------
# Axiom recipes.  Theorem construction for theory axioms emitted by
# datatype / inductive / fun definitions goes through mk_axiom, the
# single loading point of the axiom assumption rule (audit §7.3).
# ---------------------------------------------------------------------------

def mk_axiom(prop):
    """Make the theorem for a theory axiom.

    The only place outside the kernel where a Thm may be constructed
    for loading into a theory: definition-legality checks
    (structural recursion, strict positivity) have already been
    performed by the time this is called.
    """
    return Thm(prop)


def datatype_axioms(name, args, constrs):
    """Axiom extensions for a datatype: projection functions (state
    only), constructor distinctness, injectivity, induction, cases.

    name -- name of the datatype.
    args -- list of type-argument names.
    constrs -- list of parsed constructor dicts with 'name', 'type',
      'cname', 'args' fields.

    """
    res = []
    tvars = [TVar(targ) for targ in args]
    T = TConst(name, *tvars)

    # Projection functions are registered only for the memory-program
    # state datatype.  For other datatypes their field names would
    # clash with the same-named free variables in inductive rules
    # (e.g. f in Sem_basic vs the f of Basic).
    if name == 'state':
        # Field names that occur in exactly one constructor can serve as
        # projection functions; duplicated field names have no
        # well-defined projection and are skipped.
        field_names = [nm for c in constrs for nm in c['args']]
        unique_fields = {nm for nm in field_names if field_names.count(nm) == 1}
        for constr in constrs:
            if constr['args']:
                argT, _ = constr['type'].strip_type()
                constr_args = [Var(nm, T2) for nm, T2 in zip(constr['args'], argT)]
                A = Const(constr['name'], constr['type'])
                for proj_name, arg in zip(constr['args'], constr_args):
                    if proj_name not in unique_fields:
                        continue
                    proj_T = TFun(T, arg.get_type())
                    res.append(extension.Constant(proj_name, proj_T))
                    proj = Const(proj_name, proj_T)
                    res.append(extension.Theorem(
                        "%s_%s" % (name, proj_name),
                        mk_axiom(Eq(proj(A(*constr_args)), arg))))

    # Non-equality theorems.
    for constr1, constr2 in itertools.combinations(constrs, 2):
        # For each A x_1 ... x_m and B y_1 ... y_n, get the theorem
        # ~ A x_1 ... x_m = B y_1 ... y_n.
        argT1, _ = constr1['type'].strip_type()
        argT2, _ = constr2['type'].strip_type()
        lhs_vars = [Var(nm, T) for nm, T in zip(constr1['args'], argT1)]
        # Give the two sides disjoint variable names.  Otherwise the
        # same-named variables would be identified by alpha-conversion
        # (e.g. Cond ?b ?c1 ?c2 = While ?b ?I ?c), weakening the theorem.
        lhs_names = [v.name for v in lhs_vars]
        rhs_names = get_variant_names(constr2['args'], lhs_names)
        rhs_vars = [Var(nm, T) for nm, T in zip(rhs_names, argT2)]
        A = Const(constr1['name'], constr1['type'])
        B = Const(constr2['name'], constr2['type'])
        lhs = A(*lhs_vars)
        rhs = B(*rhs_vars)
        neq = Not(Eq(lhs, rhs))
        th_name = "%s_%s_%s_neq" % (name, constr1['name'], constr2['name'])
        res.append(extension.Theorem(th_name, mk_axiom(neq)))

    # Injectivity theorems.
    for constr in constrs:
        # For each A x_1 ... x_m with m > 0, get the theorem
        # A x_1 ... x_m = A x_1' ... x_m' --> x_1 = x_1' & ... & x_m = x_m'
        if constr['args']:
            argT, _ = constr['type'].strip_type()
            lhs_vars = [Var(nm, T) for nm, T in zip(constr['args'], argT)]
            rhs_vars = [Var(nm + "1", T) for nm, T in zip(constr['args'], argT)]
            A = Const(constr['name'], constr['type'])
            assum = Eq(A(*lhs_vars), A(*rhs_vars))
            concls = [Eq(var1, var2) for var1, var2 in zip(lhs_vars, rhs_vars)]
            concl = And(*concls)
            th_name = "%s_%s_inject" % (name, constr['name'])
            res.append(extension.Theorem(th_name, mk_axiom(Implies(assum, concl))))

    # The inductive theorem.
    var_P = Var("P", TFun(T, BoolType))
    ind_assums = []
    for constr in constrs:
        A = Const(constr['name'], constr['type'])
        argT, _ = constr['type'].strip_type()
        args_ = [Var(nm, T2) for nm, T2 in zip(constr['args'], argT)]
        C = var_P(A(*args_))
        As = [var_P(Var(nm, T2)) for nm, T2 in zip(constr['args'], argT) if T2 == T]
        ind_assum = Implies(*(As + [C]))
        for arg in reversed(args_):
            ind_assum = Forall(arg, ind_assum)
        ind_assums.append(ind_assum)
    ind_concl = var_P(Var("x", T))
    th_name = name + "_induct"
    res.append(extension.Theorem(th_name, mk_axiom(Implies(*(ind_assums + [ind_concl])))))
    res.append(extension.Attribute(th_name, "var_induct"))

    # The cases theorem: one branch per constructor, without
    # induction hypotheses (used by the datatype_cases tactic).
    case_assums = []
    for constr in constrs:
        A = Const(constr['name'], constr['type'])
        argT, _ = constr['type'].strip_type()
        args_ = [Var(nm, T2) for nm, T2 in zip(constr['args'], argT)]
        case_assum = var_P(A(*args_))
        for arg in reversed(args_):
            case_assum = Forall(arg, case_assum)
        case_assums.append(case_assum)
    case_concl = var_P(Var("x", T))
    th_name = name + "_cases"
    res.append(extension.Theorem(th_name, mk_axiom(Implies(*(case_assums + [case_concl])))))

    return res


def inductive_case_induct_axioms(name, type, cname, rules):
    """Axiom extensions for an inductive predicate: the case rule and
    the rule-induction rule (in the style of HOL Light's
    new_inductive).

    name -- name of the inductive predicate (constant).
    type -- type of the constant.
    cname -- expanded name of the constant (for linking).
    rules -- list of {'name': ..., 'prop': ...} introduction rules.

    """
    res = []
    Targs, _ = type.strip_type()
    vars = []
    for i, Targ in enumerate(Targs):
        vars.append(Var("_a" + str(i+1), Targ))

    P = Var("P", BoolType)
    pred = Const(name, type)
    assum0 = pred(*vars)
    assums = []
    for rule in rules:
        prop = rule['prop']
        As, C = prop.strip_implies()
        eq_assums = [Eq(var, arg) for var, arg in zip(vars, C.args)]
        assum = Implies(*(eq_assums + As), P)
        for var in reversed(prop.get_vars()):
            assum = Forall(var, assum)
        assums.append(assum)

    prop = Implies(*([assum0] + assums + [P]))
    res.append(extension.Theorem(cname + "_cases", mk_axiom(prop)))

    # Rule-induction rule: for each introduction rule, the inductive
    # premises are kept as facts and the induction hypotheses are added.
    P = Var("P", TFun(*(Targs + [BoolType])))
    ind_assums = []
    for rule in rules:
        prop = rule['prop']
        As, C = prop.strip_implies()
        rargs = C.args
        prems = []
        for A in As:
            f, aargs = A.strip_comb()
            if f == Const(name, type):
                prems.append(A)
                prems.append(P(*aargs))
            else:
                prems.append(A)
        ind_assum = Implies(*(prems + [P(*rargs)]))
        for var in reversed(prop.get_vars()):
            ind_assum = Forall(var, ind_assum)
        ind_assums.append(ind_assum)
    ind_vars = [Var("_a" + str(i + 1), Targ) for i, Targ in enumerate(Targs)]
    ind_concl = Implies(pred(*ind_vars), P(*ind_vars))
    for var in reversed(ind_vars):
        ind_concl = Forall(var, ind_concl)
    # The conclusion is forall-quantified (as in HOL Light's
    # new_inductive), so the rule tactic can match the quantified
    # argument variables against the goal via first-order matching,
    # instantiating P with the goal's predicate directly.
    res.append(extension.Theorem(cname + "_induct",
                                 mk_axiom(Implies(*(ind_assums + [ind_concl])))))
    res.append(extension.Attribute(cname + "_induct", "var_induct"))

    return res
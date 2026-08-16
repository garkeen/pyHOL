"""Structural-recursion check for `fun` (def.ind) definitions.

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

"""

from kernel import theory
from kernel.term import Const


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
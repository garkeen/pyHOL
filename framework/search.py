# framework/search.py - Pattern-net theorem index for suggest/search.
#
# Replaces the "iterate all theorems and match each one" approach:
# theorems are indexed by the head skeleton of their conclusion
# (Isabelle's net.ML idea: key_of_term). Queries use subterms of the
# goal/fact as keys to retrieve candidates, which are then matched
# exactly. Complexity: O(all theorems) -> O(candidates).
#
# Two index layers:
# - the GLOBAL net: every theorem of the current theory, regardless of
#   hint attributes (fixes audit finding C1: unattributed theorems were
#   invisible to all search).
# - CATEGORY nets: per hint_* attribute, for mode-specific search.
#
# hint_* attributes keep their established meaning (search suggestions
# only); the global net makes them unnecessary for direct closure.

from kernel import theory
from framework import matcher

# Cache key: theory object id + theorem count signature.
_cache_sig = None
_global_net = None
_category_nets = None

HINT_CATEGORIES = ('hint_rewrite', 'hint_rewrite_sym', 'hint_backward',
                   'hint_backward1', 'hint_forward', 'hint_resolve')


def key_of_term(t):
    """Head skeleton key of a term (variable-free pattern).

    Constants keep their names; variables (free, bound, schematic)
    collapse to a single wildcard so that differently named variables
    hit the same net slot. Applications and abstractions recurse.
    """
    if t.is_var() or t.is_svar() or t.is_bound():
        return 'V'
    if t.is_const():
        return 'C:' + t.name
    if t.is_comb():
        return ('APP', key_of_term(t.fun), key_of_term(t.arg))
    if t.is_abs():
        return ('ABS', key_of_term(t.body))
    return 'V'


def _subterm_keys(t, acc, depth=0, max_depth=6):
    """Collect the skeleton keys of all subterms of t (bounded depth)."""
    if depth > max_depth:
        return
    acc.add(key_of_term(t))
    if t.is_comb():
        _subterm_keys(t.fun, acc, depth + 1, max_depth)
        _subterm_keys(t.arg, acc, depth + 1, max_depth)
    elif t.is_abs():
        _subterm_keys(t.body, acc, depth + 1, max_depth)


def _theory_sig():
    """Cheap signature detecting theory changes (identity + size)."""
    thy = theory.thy
    if thy is None:
        return None
    data = thy.get_data('theorems')
    return (id(thy), len(data))


def _rebuild():
    """(Re)build the nets for the current theory."""
    global _cache_sig, _global_net, _category_nets
    _global_net = {}
    _category_nets = {c: {} for c in HINT_CATEGORIES}
    thy = theory.thy
    attrs = thy.get_data('attributes')
    for name, th in thy.get_data('theorems').items():
        key = key_of_term(th.concl)
        _global_net.setdefault(key, []).append(name)
        th_attrs = attrs.get(name, ())
        for c in HINT_CATEGORIES:
            if c in th_attrs:
                _category_nets[c].setdefault(key, []).append(name)
    _cache_sig = _theory_sig()


def _ensure():
    if _cache_sig != _theory_sig():
        _rebuild()


def lookup_net(t, *, category=None):
    """Return theorem names whose conclusion skeleton matches the
    skeleton of t exactly (whole-term keys).

    category=None queries the global net (all theorems); otherwise one
    of HINT_CATEGORIES.
    """
    _ensure()
    net = _global_net if category is None else _category_nets[category]
    return list(net.get(key_of_term(t), []))


def candidates_for(t, *, category=None):
    """Return candidate theorem names for rewriting/matching any
    subterm of t: union of net lookups over the subterm skeleton keys.
    """
    _ensure()
    net = _global_net if category is None else _category_nets[category]
    keys = set()
    _subterm_keys(t, keys)
    res = []
    seen = set()
    for k in keys:
        for name in net.get(k, []):
            if name not in seen:
                seen.add(name)
                res.append(name)
    return res


def exact_match_theorems(goal_prop):
    """Theorems whose whole conclusion first-order-matches goal_prop
    (C1/C6 closure candidates). Returns a list of theorem names.

    Uses the global net for candidate retrieval, then exact matching;
    no hint attributes are consulted.
    """
    names = candidates_for(goal_prop)
    res = []
    for name in names:
        th = theory.get_theorem(name)
        try:
            matcher.first_order_match(th.prop, goal_prop)
        except matcher.MatchException:
            continue
        res.append(name)
    return res

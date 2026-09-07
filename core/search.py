# framework/search.py - Pattern-net theorem index for suggest/search.
#
# Replaces the "iterate all theorems and match each one" approach:
# theorems are indexed by the head skeleton of their conclusion
# (Isabelle's net.ML idea: key_of_term). Skeleton keys collapse
# variables to a wildcard 'V'; lookup matches wildcard-aware, so a
# schematic pattern like ?A & ?B finds a concrete goal B & C and vice
# versa. Entries are bucketed by the outermost head constant for
# pruning; patterns whose head is itself schematic go to a generic
# bucket that is always consulted. Complexity: O(all theorems) ->
# O(bucket).
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
from core import matcher

# Cache key: theory object id + theorem count signature.
_cache_sig = None
_global_net = None
_category_nets = None
_assum_nets = None

HINT_CATEGORIES = ('hint_rewrite', 'hint_rewrite_sym', 'hint_backward',
                   'hint_backward1', 'hint_forward', 'hint_resolve')


def key_of_term(t):
    """Head skeleton key of a term.

    Constants keep their names; variables (free, bound, schematic)
    collapse to the wildcard 'V' (on BOTH the pattern and the query
    side: schematic goal parts are instantiable too). Applications and
    abstractions recurse.
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


def _head_of_key(key):
    """Outermost head constant name of a skeleton key, or None when the
    head is schematic (generic bucket)."""
    if isinstance(key, str):
        return key[2:] if key.startswith('C:') else None
    # ('APP', fun_key, arg_key): descend into the function part
    return _head_of_key(key[1])


def _key_match(pat, key):
    """Wildcard-aware skeleton match: 'V' on either side matches any
    subtree (schematic variables are instantiable in both directions).
    """
    if pat == 'V' or key == 'V':
        return True
    if isinstance(pat, str) or isinstance(key, str):
        return pat == key
    if pat[0] != key[0] or len(pat) != len(key):
        return False
    return all(_key_match(p, k) for p, k in zip(pat[1:], key[1:]))

class _Net:
    """Skeleton-key bucket index with wildcard matching."""
    def __init__(self):
        self.buckets = {}   # head constant name -> list of [key, [names]]
        self.generic = []   # entries whose head is schematic

    def insert(self, key, name):
        head = _head_of_key(key)
        entries = self.buckets.setdefault(head, []) if head is not None \
            else self.generic
        for e in entries:
            if e[0] == key:
                e[1].append(name)
                return
        entries.append([key, [name]])

    def lookup_key(self, key):
        """Theorem names whose stored key wildcard-matches key."""
        res = []
        head = _head_of_key(key)
        entries = list(self.generic)
        if head is not None:
            entries += self.buckets.get(head, [])
        # A pattern stored under a different concrete head can still
        # match when the QUERY side is schematic in the head position;
        # entries whose stored head is concrete but differs from a
        # concrete query head cannot match, hence the bucket pruning.
        if head is None:
            entries = self.generic + sum(self.buckets.values(), [])
        for e in entries:
            if _key_match(e[0], key):
                res.extend(e[1])
        return res


def _theory_sig():
    """Cheap signature detecting theory changes (identity + size)."""
    thy = theory.thy
    if thy is None:
        return None
    data = thy.get_data('theorems')
    return (id(thy), len(data))


def _rebuild():
    """(Re)build the nets for the current theory."""
    global _cache_sig, _global_net, _category_nets, _assum_nets
    _global_net = _Net()
    _category_nets = {c: _Net() for c in HINT_CATEGORIES}
    _assum_nets = {c: _Net() for c in HINT_CATEGORIES}
    thy = theory.thy
    attrs = thy.get_data('attributes')
    for name, th in thy.get_data('theorems').items():
        concl = th.concl
        key = key_of_term(concl)
        _global_net.insert(key, name)
        # Rewriting matches either SIDE of an equality conclusion
        # (rewr_conv on ?A = ?B can rewrite via ?A or via ?B).
        side_keys = []
        if concl.is_equals():
            side_keys = [key_of_term(concl.lhs), key_of_term(concl.rhs)]
        th_attrs = attrs.get(name, ())
        for c in HINT_CATEGORIES:
            if c in th_attrs:
                _category_nets[c].insert(key, name)
                for sk in side_keys:
                    _category_nets[c].insert(sk, name)
                # Forward reasoning matches theorem ASSUMPTIONS against
                # facts: index every assumption skeleton.
                for a in th.assums:
                    _assum_nets[c].insert(key_of_term(a), name)
    _cache_sig = _theory_sig()


def _ensure():
    if _cache_sig != _theory_sig():
        _rebuild()


def lookup_net(t, *, category=None):
    """Return theorem names whose conclusion skeleton wildcard-matches
    the skeleton of t (whole terms).

    category=None queries the global net (all theorems); otherwise one
    of HINT_CATEGORIES.
    """
    _ensure()
    net = _global_net if category is None else _category_nets[category]
    return net.lookup_key(key_of_term(t))


def candidates_for(t, *, category=None):
    """Return candidate theorem names for rewriting/matching any
    subterm of t: union of net lookups over the subterm skeleton keys.
    Bare-variable subterms are skipped (their key matches everything
    and would defeat pruning).
    """
    _ensure()
    net = _global_net if category is None else _category_nets[category]
    keys = set()
    _subterm_keys(t, keys)
    keys.discard('V')
    res = []
    seen = set()
    for k in keys:
        for name in net.lookup_key(k):
            if name not in seen:
                seen.add(name)
                res.append(name)
    return res


def forward_candidates_for(t, *, category='hint_forward'):
    """Candidate theorem names whose ASSUMPTION skeletons wildcard-match
    a subterm of t (forward reasoning: theorem premises are matched
    against facts).
    """
    _ensure()
    net = _assum_nets[category]
    keys = set()
    _subterm_keys(t, keys)
    keys.discard('V')
    res = []
    seen = set()
    for k in keys:
        for name in net.lookup_key(k):
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

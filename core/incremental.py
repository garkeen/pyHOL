"""Incremental verification: file-level dependency chain + suffix reuse.

Why this exists
===============
Re-playing a whole library on every edit is wasteful, and `--force`
throws the cache away entirely.  This module drives
`verify.validate_theory_info` over the theory DAG so that:

* a file whose source and imports are unchanged is not replayed;
* a file whose source changed replays only from its first changed item
  (suffix reuse -- see verify.validate_theory_info);
* every file importing a changed file is re-validated too (a change
  anywhere upstream invalidates this file's cache via the imports
  epoch, so no stale green survives);
* deleting a theorem drops its verdict immediately (basic.drop_status).

Data structures
===============
Nothing heavy is needed: the numbers here are tiny (tens of files,
hundreds of items per file).

* reverse import map -- `reverse_imports()`: file -> files importing it,
  built once from `basic.theory_cache[*]['imports']`;
* per-file item hash list -- `basic.theory_cache[f]['item_hashes']`,
  computed at parse time from each item's exact source block, so
  `first_diff_index` finds the first edited item in O(n) comparisons;
* imports epoch -- `imports_epoch(f)`: a hash over f's imports' names,
  each imported file's own source hash, and their epochs, so a change
  to any upstream file propagates transitively without any per-theorem
  graph.
"""
from core import basic


def first_diff_index(old, new):
    """Index of the first differing element of two hash lists.

    Returns len(new) when `new` is a prefix of `old` (trailing items
    deleted), and 0 when there is no cache to compare against.
    """
    if not old:
        return 0
    n = min(len(old), len(new))
    for i in range(n):
        if old[i] != new[i]:
            return i
    if len(old) == len(new):
        return n
    return n


def reverse_imports():
    """Return {file: [files that import it directly]}."""
    if not basic.theory_cache:
        basic.load_metadata()
    rev = {}
    for name, cache in basic.theory_cache.items():
        for imp in cache.get('imports', ()):
            rev.setdefault(imp, []).append(name)
    return rev


def imports_epoch(filename, _memo=None):
    """Fingerprint of everything `filename` imports, transitively.

    Recomputed from the current in-memory theory cache.  The fingerprint
    covers the import names, each imported file's own source hash, and
    their epochs, so an edit upstream -- not just a change of the import
    graph -- changes this value, which invalidates the dependent file's
    cache even when its own source is untouched.

    Deliberately does NOT include `filename`'s own source hash: the
    caller compares the own hash separately, so that a local edit can
    still reuse the unchanged prefix (suffix replay).
    """
    import hashlib
    if _memo is None:
        _memo = {}
    if filename in _memo:
        return _memo[filename]
    cache = basic.theory_cache.get(filename)
    parts = []
    for imp in (cache.get('imports', ()) if cache else ()):
        imp_cache = basic.theory_cache.get(imp)
        # `or ''` covers an import whose content has not been loaded
        # (metadata-only cache entry): the name and the nested epoch are
        # still in the fingerprint, so the value changes once it loads.
        imp_source = (imp_cache.get('source_hash') if imp_cache else None) or ''
        parts.append('%s:%s:%s' % (imp, imp_source, imports_epoch(imp, _memo)))
    value = hashlib.sha1('|'.join(parts).encode('utf-8')).hexdigest()
    _memo[filename] = value
    return value


def validate_incremental(filenames=None, *, trust=frozenset(), force=False,
                         report=None):
    """Validate `filenames` (default: the whole library) incrementally.

    Validates in import order, and pushes in every file that imports a
    file whose verdict changed, so downstream caches never go stale.

    report -- optional callable(file, reused, start, changed) for
    progress output.

    Returns {file: (statuses, errors)} for everything validated.
    """
    from core import verify

    if not basic.theory_cache:
        basic.load_metadata()
    if filenames is None:
        filenames = sorted(basic.theory_cache.keys())

    order = basic.get_import_order(list(filenames))
    rev = reverse_imports()
    queued = set(order)
    queue = list(order)
    results = {}
    changed_files = set()

    while queue:
        name = queue.pop(0)
        prev = dict(basic.load_status_data(name).get('theorems', {}))
        statuses, errors, info = verify.validate_theory_info(
            name, force=force, trust=trust)
        results[name] = (statuses, errors)
        changed = statuses != prev
        if changed:
            changed_files.add(name)
        if report is not None:
            report(name, info['reused'], info['start'], changed)
        if changed:
            for dep in rev.get(name, ()):
                if dep not in queued:
                    queued.add(dep)
                    queue.append(dep)

    if report is not None:
        report('__done__', False, 0, changed_files)
    return results

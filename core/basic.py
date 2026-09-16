# Author: Bohua Zhan
import os
import json
import hashlib
import importlib

from kernel import theory
from kernel.theory import TheoryException
from core import items
from syntax import parser
from syntax import pyhol

import sys

"""
Cache of parsed theories.

Each theory stores a 'timestamp' field, for the last modification
time of the corresponding file.

In the contents, instead of each item is the parsed item as
well as the corresponding extension.

"""
theory_cache = dict()

dirname = os.path.dirname(os.path.dirname(__file__))  # project root

def _lib_dirs():
    """Directories holding hand-written theory files (search order).

    Deliberately excludes imperative/programs/: auto-generated .pyhol
    from program verification must stay isolated from the main IDE and
    from library validation.  They are only reachable on demand through
    program_dir() (see inject_program_metadata / save_user_file).
    """
    return [
        os.path.join(dirname, 'library/'),
    ]

def program_dir():
    """Directory holding imperative program sources (.imp) and their
    auto-generated verification .pyhol.  Nothing here is part of the
    theory library or shown by the main IDE."""
    return os.path.join(dirname, 'imperative/programs/')

def user_dir():
    """Returns the primary library directory (backward compat)."""
    return os.path.join(dirname, 'library/')

def user_file(filename):
    """Return pyhol file path for the given theory name.

    Searches library/ first, then imperative/programs/ (so the program
    IDE can load auto-generated .pyhol).  If the file does not exist
    yet, defaults to library/ (for new file creation).
    """
    for d in _lib_dirs() + [program_dir()]:
        path = os.path.join(d, filename + '.pyhol')
        if os.path.exists(path):
            return path
    return os.path.join(dirname, 'library/' + filename + '.pyhol')

def save_user_file(filename):
    """Return the write path for the given theory name.

    Auto-generated program .pyhol must never land in library/: if a
    matching file already exists in imperative/programs/ (or the
    corresponding .imp program exists), the write goes there.  Only
    genuinely new files fall back to library/.
    """
    prog_path = os.path.join(program_dir(), filename + '.pyhol')
    if os.path.exists(prog_path) or os.path.exists(prog_path[:-6] + '.imp'):
        return prog_path
    return user_file(filename)

def inject_program_metadata(filename):
    """Register metadata for an imperative/programs .pyhol on demand.

    Keeps auto-generated program theories out of load_metadata() (and
    therefore out of the main IDE file list and library validation),
    while still allowing the program IDE to load and prove them
    through the regular theory-cache APIs.
    """
    path = os.path.join(program_dir(), filename + '.pyhol')
    if os.path.exists(path) and filename not in theory_cache:
        data = load_pyhol_data(filename)
        theory_cache[filename] = {
            'imports': data['imports'],
            'domains': data.get('domains', []),
            'description': data['description']
        }

def _status_cache_dir():
    """Directory holding proof-status .json caches (top-level .cache/)."""
    return os.path.join(dirname, '.cache')

# Proof-status tables, migrated out of the kernel (audit §7.4): the
# status of a theorem entry is output of the verification pipeline
# (core/verify), not logical-kernel data.  core/verify writes here;
# loading (load_theory) backfills from the .json cache and defaults
# thm entries without a cached status to UNPROVED.
statuses = dict()
errors = dict()

def set_status(name, status):
    """Record the proof status of a theorem."""
    statuses[name] = status

def set_error(name, error):
    """Set the error message for a theorem (or None to clear it)."""
    errors[name] = error

def drop_status(name):
    """Remove a theorem's status and error entirely.

    Used when a theorem is deleted from its source: its cached verdict
    must disappear from the in-memory tables at once, not linger as a
    stale entry until the process restarts.
    """
    statuses.pop(name, None)
    errors.pop(name, None)


def clear_statuses():
    """Clear the proof-status tables.

    Statuses accumulate across load_theory calls (each load backfills
    from its .json cache), mirroring the old kernel-table behavior;
    starting a fresh session or theory switch resets them here.
    """
    statuses.clear()
    errors.clear()

def get_all_statuses():
    """Return a copy of all theorem statuses."""
    return dict(statuses)

def get_all_errors():
    """Return a copy of all recorded theorem error messages."""
    return dict(errors)

def status_cache_file(filename):
    """Return .json cache path under top-level .cache/."""
    return os.path.join(_status_cache_dir(), filename + '.json')

def load_status(filename):
    """Load proof status from .json cache into the status table.

    Entries for theorems that no longer exist in the current source are
    skipped: a deleted theorem must not be resurrected in memory by a
    stale cache file (the status tables accumulate across loads, so a
    name once dropped would otherwise come back on the next load).
    """
    path = status_cache_file(filename)
    if not os.path.exists(path):
        return
    with open(path, encoding='utf-8') as f:
        data = json.load(f)
    cache = theory_cache.get(filename)
    if cache is not None:
        valid = {item.name for item in cache['content']
                 if item.ty in ('thm', 'thm.ax')}
    else:
        valid = None
    for name, status in data.get('theorems', {}).items():
        if valid is not None and name not in valid:
            continue
        set_status(name, status)

def save_status(filename, status_dict, *, item_hashes=None, source_hash=None,
                imports_epoch=None):
    """Save proof status to .json cache.

    item_hashes/source_hash record the source fingerprint the statuses
    were computed from, so a later run can tell which items changed
    (defaults are taken from theory_cache when available).
    imports_epoch fingerprints the imported theories' epochs at
    validation time, so a change anywhere upstream invalidates this
    file's cache even when its own source is untouched.
    """
    path = status_cache_file(filename)
    os.makedirs(_status_cache_dir(), exist_ok=True)
    cache = theory_cache.get(filename, {})
    if item_hashes is None:
        item_hashes = cache.get('item_hashes')
    if source_hash is None:
        source_hash = cache.get('source_hash')
    meta = {'theory': filename,
            'source_mtime': os.path.getmtime(user_file(filename))}
    if source_hash is not None:
        meta['source_hash'] = source_hash
    if item_hashes is not None:
        meta['item_hashes'] = item_hashes
    if imports_epoch is not None:
        meta['imports_epoch'] = imports_epoch
    with open(path, 'w', encoding='utf-8') as f:
        json.dump({'meta': meta, 'theorems': status_dict}, f,
                  indent=2, ensure_ascii=False)


def load_status_data(filename):
    """Return the raw .json status cache dict ({} if absent)."""
    path = status_cache_file(filename)
    if not os.path.exists(path):
        return {}
    with open(path, encoding='utf-8') as f:
        return json.load(f)


def is_cache_valid(filename):
    """Check if the .json cache is up-to-date with the .pyhol source.

    Uses the recorded source content hash when present (so touching a
    file without editing it does not invalidate the cache), falling
    back to mtime for caches written by older versions.
    """
    path = status_cache_file(filename)
    if not os.path.exists(path):
        return False
    data = load_status_data(filename)
    meta = data.get('meta', {})
    if 'source_hash' in meta:
        cache = theory_cache.get(filename)
        return cache is not None and meta['source_hash'] == cache.get('source_hash')
    return meta.get('source_mtime') == os.path.getmtime(user_file(filename))

def load_pyhol_data(filename):
    """Load pyhol data for the given theory name."""
    with open(user_file(filename), encoding='utf-8') as f:
        text = f.read()
    return pyhol.parse_pyhol(text)

def load_metadata():
    """Load metadata for all theory files across all library directories."""
    theory_cache.clear()
    for d in _lib_dirs():
        if not os.path.isdir(d):
            continue
        for f in os.listdir(d):
            if f.endswith('.pyhol'):
                filename = f[:-6]
                data = load_pyhol_data(filename)
                timestamp = os.path.getmtime(user_file(filename))
                theory_cache[filename] = {
                    'imports': data['imports'],
                    'domains': data.get('domains', []),
                    'description': data['description']
                }

    # Immediately check for topological order.
    check_topological_sort()

def check_topological_sort():
    """Check the import relations have no cycles."""
    for name in theory_cache.keys():
        theory_cache[name]['visited'] = False
    
    count = 0
    def dfs(name, path):
        """Perform depth-first search.

        name - current theory name.
        path - list of theory names on the current search path,
               not including the current theory.

        """
        nonlocal count
        if theory_cache[name]['visited']:
            return

        if name in path:
            id = path.index(name)
            cycle = path[id:] + (name,)
            raise TheoryException("Cycle in imports: %s" % (', '.join(cycle)))

        for import_name in theory_cache[name]['imports']:
            dfs(import_name, path + (name,))
        theory_cache[name]['order'] = count
        theory_cache[name]['visited'] = True
        count += 1

    for name in sorted(theory_cache.keys()):
        if not theory_cache[name]['visited']:
            dfs(name, tuple())

def get_import_order(filenames):
    """Obtain the order of loading theories for fulfilling
    the imports in the theory given by the list of filenames.

    """
    if not theory_cache:
        load_metadata()

    depend_list = []
    def dfs(name):
        if name in depend_list:
            return
        else:
            for import_name in theory_cache[name]['imports']:
                dfs(import_name)
            depend_list.append(name)
    
    for name in filenames:
        dfs(name)

    return depend_list

def load_theory_cache(filename):
    """Load the content of the given theory into cache.
    
    Return the theory cache as a dictionary.

    """
    if not theory_cache:
        load_metadata()

    if filename not in theory_cache:
        inject_program_metadata(filename)
    if filename not in theory_cache:
        raise TheoryException("theory %s not found (not in library/ or imperative/programs/)" % filename)

    cache = theory_cache[filename]
    timestamp = os.path.getmtime(user_file(filename))

    if 'timestamp' in cache and timestamp == cache['timestamp']:
        # No need to update cache
        return cache

    # Load all required macros and methods for this file.
    # Core macros (and the z3 oracle macro) are always loaded.
    # The sympy solver registers real/nat comparison procedures
    # into the generic auto engine on import.  (The omega integer
    # procedure is registered by theories/integer, i.e. when the
    # integer domain is loaded -- audit 3: solvers are pure.)
    from core.macro import registry, z3  # noqa: F401
    try:
        from solvers import sympywrapper  # noqa: F401
    except ImportError:
        pass

    # Load domain packages declared in the .pyhol header.
    # Domain packages live in theories/<name>/ and register their
    # conv/macro/method via decorators on import.  For example,
    # logic.pyhol declares `domains logic`, which activates the
    # propositional-logic automation bound to it.
    data = load_pyhol_data(filename)
    for domain_name in data.get('domains', []):
        try:
            importlib.import_module('theories.' + domain_name)
        except ImportError as e:
            import sys
            print(f"Warning: failed to load domain '{domain_name}': {e}", file=sys.stderr)

    # Imperative program verification is not a theories/ package; the
    # hoare theory activates it directly.
    if filename == 'hoare':
        from imperative import imp  # noqa: F401

    # Load all imported theories
    depend_list = get_import_order(cache['imports'])

    with theory.fresh_theory():
        for prev_name in depend_list:
            prev_cache = load_theory_cache(prev_name)
            for item in prev_cache['content']:
                # _apply_item (not a bare unchecked_extend): the imports'
                # parser-side state -- type abbreviations, class declarations
                # -- has to be in place before the current file is parsed.
                _apply_item(item)

        # Use this theory to parse the content of current theory
        cache['timestamp'] = timestamp
        data = load_pyhol_data(filename)
        with open(user_file(filename), encoding='utf-8') as f:
            source_text = f.read()
        source_lines = source_text.split('\n')
        cache['source_hash'] = hashlib.sha1(
            source_text.encode('utf-8')).hexdigest()
        cache['item_hashes'] = []
        cache['content'] = []

        def _load_group(group):
            """Hash, parse and register a group of consecutive items.

            A `fun` definition in the group expands into its own group
            (phase 4): its equations are then derived from a
            well-foundedness obligation instead of being asserted.  The
            expansion happens here, where the loader reaches the block, so
            the items before it are already registered -- the generator
            prints terms mentioning them (hd/tl, the datatype's own
            destructors) and would otherwise fail to type them.  Derived
            items share the parent block's `_src`, so editing the `fun`
            block invalidates the group whole.

            Definitions outside what the generator supports keep the
            current axiomatization: their equations show up as AXIOM in the
            status table.  Set HOLPY_FUNGEN_DEBUG to see the exception.
            """
            for item in group:
                if item.get('ty') == 'def.ind':
                    from core import fungen
                    try:
                        derived = fungen.expand_item(item)
                    except Exception:
                        if os.environ.get('HOLPY_FUNGEN_DEBUG'):
                            raise
                        derived = None
                    if derived is not None:
                        for derived_item in derived:
                            derived_item['_src'] = item.get('_src')
                        _load_group(derived)
                        continue
                # Hash the item's exact source block (see syntax.pyhol
                # `_src`), so the incremental verifier can tell which
                # items changed instead of invalidating the whole file.
                src = item.get('_src')
                if src is not None:
                    block = '\n'.join(source_lines[src[0]:src[1]])
                else:
                    block = json.dumps(item, sort_keys=True, default=str)
                cache['item_hashes'].append(
                    hashlib.sha1(block.encode('utf-8')).hexdigest())
                item = items.parse_item(item)
                cache['content'].append(item)
                if item.error is None:
                    try:
                        theory.thy.unchecked_extend(item.get_extension())
                    except TheoryException:
                        pass  # Skip duplicates

        # The datatypes whose size family is not generated yet.  A size
        # family is a generated `fun`, and its equations use the
        # destructor family and state a comparison (`<ty>_size_less`), so
        # in the file that defines those itself (nat's `less`, list's
        # `hd`/`tl`) it can only be generated once they are there.  It is
        # therefore attempted after every item, until it goes through:
        # generating it at the first point it can be is what lets the
        # file's *own* definitions use it as a measure -- with the family
        # left to the end of the file, `map` and `filter` over the
        # datatype declared above it find no size for that argument and
        # fall back to the subterm relation.
        pending_sizes = [item_data for item_data in data['content']
                         if item_data.get('ty') == 'type.ind']

        def _size_family_ready():
            """Whether a size family can be proved in the theory yet.

            Its one fact compares two sizes and is proved by the same
            rewrites a measure cell uses (see datgen's `size_less_lines`),
            so the family can only be generated once those lemmas are in
            scope.  In the file that states them itself (nat) that is
            later than the datatype -- and later than the comparison --
            and generating the family before it would register an item
            whose proof does not replay.
            """
            from core import datgen
            from kernel import theory
            for name in datgen.SIZE_LESS_DEPS:
                try:
                    theory.get_theorem(name)
                except Exception:
                    return False
            return True

        def _generate_sizes():
            from core import datgen
            still = []
            if not _size_family_ready():
                return list(pending_sizes)
            for datatype in pending_sizes:
                try:
                    derived = datgen.expand_size(datatype)
                except Exception:
                    if os.environ.get('HOLPY_DATGEN_DEBUG'):
                        raise
                    derived = None
                if derived is None or not _size_family_ready():
                    still.append(datatype)
                    continue
                for derived_item in derived:
                    derived_item['_src'] = datatype.get('_src')
                _load_group(derived)
            return still

        for index, item_data in enumerate(data['content']):
            # A datatype expands into the well-foundedness of its subterm
            # relation, which `fun` recursion on it descends through, and
            # into its destructor family (datgen).  The block itself is
            # registered first -- it is what declares the type and the
            # constructor axioms the generated proofs cite; the relation
            # and the destructors are generated next, and the size family
            # last, since its equations are themselves a generated `fun`
            # and are expanded by the machinery above.  A file that states
            # the lemma itself gets nothing generated.  Set
            # HOLPY_DATGEN_DEBUG to see a generator exception instead of
            # the silent fallback.
            _load_group([item_data])
            if item_data.get('ty') == 'type.ind':
                from core import datgen
                derived = datgen.expand_item(item_data, data['content'])
                if derived is not None:
                    for derived_item in derived:
                        derived_item['_src'] = item_data.get('_src')
                    _load_group(derived)
            if pending_sizes:
                pending_sizes = _generate_sizes()

    return cache

def _apply_item(item):
    """Extend the theory with a parsed item, and re-register the
    parser-side state that does not live in the theory.

    Type abbreviations (`typeabbrev`) and class declarations (`class`) are
    parser state rather than theory extensions, so replaying a theory has to
    restore them alongside the extensions; see syntax.parser.clear_type_abbrevs
    and syntax.parser.clear_classes.

    """
    if item.error is not None:
        return
    try:
        theory.thy.unchecked_extend(item.get_extension())
    except TheoryException:
        pass  # Skip duplicates
    if item.ty == 'type.abbrev':
        parser.add_type_abbrev(item.name, item.args, item.defn)
    elif item.ty == 'class':
        parser.add_class(item.name, *item.entries)


def load_theory(filename: str, *, limit=None):
    """Load the theory with the given theory name.
    
    Optional limit is a pair (ty, name) specifying the first item
    that should not be loaded.
    
    """
    load_theory_cache(filename)
    
    cache = theory_cache[filename]

    # Load imported theories
    depend_list = get_import_order(cache['imports'])

    theory.thy = theory.EmptyTheory()
    parser.clear_type_abbrevs()
    parser.clear_classes()
    for prev_name in depend_list:
        prev_cache = load_theory_cache(prev_name)
        for item in prev_cache['content']:
            _apply_item(item)

    if limit == 'start':
        return None

    # Take the portion of content up to (and not including) limit
    content = cache['content']
    found_limit = False
    for item in content:
        if limit and item.ty == limit[0] and item.name == limit[1]:
            found_limit = True
            break

        if item.error is None:
            _apply_item(item)

    if limit and not found_limit:
        raise TheoryException("load_theory: limit %s not found" % str(limit))

    # Load cached proof status; thm entries without a cached status
    # default to UNPROVED (the status table lives here, not in the
    # kernel -- audit §7.4).
    load_status(filename)
    for item in cache['content']:
        if item.ty == 'thm' and item.name not in statuses:
            set_status(item.name, 'UNPROVED')

    return None

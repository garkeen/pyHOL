# Author: Bohua Zhan
import io
import os
import json
import importlib

from kernel import term
from kernel.term import Var
from kernel import theory
from kernel.theory import Theory, TheoryException
from kernel.thm import Thm
from kernel import extension
from server import items
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

"""
Cache of item mapping.

A mapping from (ty, name) to (theory_name, timestamp, index).

"""
item_index = dict()

dirname = os.path.dirname(__file__)

def user_dir():
    """Returns directory for the user."""
    return os.path.join(dirname, '../library/')

def user_file(filename):
    """Return pyhol file for the user and given filename."""
    return os.path.join(dirname, '../library/' + filename + '.pyhol')

def status_cache_file(filename):
    """Return status cache file path for the given theory name."""
    return os.path.join(dirname, '../library/' + filename + '.json')

def load_status(filename):
    """Load proof status from .json cache into thy.thm_status."""
    path = status_cache_file(filename)
    if not os.path.exists(path):
        return
    with open(path, encoding='utf-8') as f:
        data = json.load(f)
    for name, status in data.get('theorems', {}).items():
        theory.thy.set_status(name, status)

def save_status(filename, status_dict):
    """Save proof status to .json cache."""
    path = status_cache_file(filename)
    source_mtime = os.path.getmtime(user_file(filename))
    with open(path, 'w', encoding='utf-8') as f:
        json.dump({'meta': {'theory': filename, 'source_mtime': source_mtime},
                   'theorems': status_dict}, f, indent=2, ensure_ascii=False)

def is_cache_valid(filename):
    """Check if the .json cache is up-to-date with the .pyhol source."""
    path = status_cache_file(filename)
    if not os.path.exists(path):
        return False
    with open(path, encoding='utf-8') as f:
        data = json.load(f)
    return data.get('meta', {}).get('source_mtime') == os.path.getmtime(user_file(filename))

def load_pyhol_data(filename):
    """Load pyhol data for the given theory name."""
    with open(user_file(filename), encoding='utf-8') as f:
        text = f.read()
    return pyhol.parse_pyhol(text)

def load_metadata():
    """Load metadata for all theory files."""
    theory_cache.clear()
    item_index.clear()
    for f in os.listdir(user_dir()):
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

    cache = theory_cache[filename]
    timestamp = os.path.getmtime(user_file(filename))

    if 'timestamp' in cache and timestamp == cache['timestamp']:
        # No need to update cache
        return cache

    # Load all required macros and methods for this file.
    # Core macros are always loaded.
    from logic.macros import core  # Always load core macros

    # Load domain packages declared in the .pyhol header.
    # This replaces the old hardcoded if-chain:
    #   if filename == 'logic': from logic.macros import z3
    #   if filename == 'expr': from logic.macros import expr
    #   ...
    # Domain packages live in domains/<name>/ and register their
    # conv/macro/method via decorators on import.
    data = load_pyhol_data(filename)
    for domain_name in data.get('domains', []):
        try:
            importlib.import_module('domains.' + domain_name)
        except ImportError as e:
            import sys
            print(f"Warning: failed to load domain '{domain_name}': {e}", file=sys.stderr)

    # Legacy fallback: if the .pyhol has no 'domains' header, load
    # domain code via the old if-chain. Theories that have been migrated
    # to declare `domains <name>` use the new path above and skip this.
    if not data.get('domains'):
        if filename == 'logic':
            from logic.macros import z3
        if filename == 'hoare':
            from imperative import imp

    # Load all imported theories
    depend_list = get_import_order(cache['imports'])

    with theory.fresh_theory():
        for prev_name in depend_list:
            prev_cache = load_theory_cache(prev_name)
            for item in prev_cache['content']:
                if item.error is None:
                    try:
                        theory.thy.unchecked_extend(item.get_extension())
                    except TheoryException:
                        pass  # Skip duplicates

        # Use this theory to parse the content of current theory
        cache['timestamp'] = timestamp
        data = load_pyhol_data(filename)
        cache['content'] = []
        for index, item in enumerate(data['content']):
            item = items.parse_item(item)
            cache['content'].append(item)
            if item.error is None:
                try:
                    exts = item.get_extension()
                    theory.thy.unchecked_extend(exts)
                    for ext in exts:
                        if ext.is_constant():
                            name = ext.ref_name
                        else:
                            name = ext.name
                        item_index[(ext.ty, name)] = (filename, timestamp, index)
                except TheoryException:
                    pass  # Skip duplicates

    return cache

def query_item_index(filename, ext_ty, name):
    """Query the item index."""

    # Make sure the theory (and all its dependencies) are indexed
    load_theory_cache(filename)

    if (ext_ty, name) in item_index:
        filename, timestamp, index = item_index[(ext_ty, name)]
        if timestamp == os.path.getmtime(user_file(filename)):
            return filename, index
        else:
            return None
    else:
        return None

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
    for prev_name in depend_list:
        prev_cache = load_theory_cache(prev_name)
        for item in prev_cache['content']:
            if item.error is None:
                try:
                    theory.thy.unchecked_extend(item.get_extension())
                except TheoryException:
                    pass  # Skip duplicates

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
            try:
                theory.thy.unchecked_extend(item.get_extension())
            except TheoryException:
                pass  # Skip duplicates

    if limit and not found_limit:
        raise TheoryException("load_theory: limit %s not found" % str(limit))

    # Load cached proof status
    load_status(filename)
    for item in cache['content']:
        if item.ty == 'thm' and theory.thy.get_status(item.name) is None:
            theory.thy.set_status(item.name, 'UNPROVED')

    return None

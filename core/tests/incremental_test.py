"""Tests for incremental (cache-aware) verification.

Real source files are never edited: a source change is simulated by
mutating the parsed theory cache (which is exactly what differ, after a
reload, when a file changes).  tearDown re-validates the theory from
disk so the .json status cache is left truthful.
"""

import unittest

from core import basic, incremental, verify
import method.stable_state  # noqa: F401  (wires the replay pipeline)

F = 'logic_base'


class IncrementalTest(unittest.TestCase):
    def setUp(self):
        basic.load_metadata()
        for fn in basic.get_import_order([F]):
            basic.load_theory_cache(fn)

    def tearDown(self):
        basic.load_metadata()
        for fn in basic.get_import_order([F]):
            basic.load_theory_cache(fn)
        verify.validate_theory(F, force=True, trust=frozenset())

    def _thm_names(self, content):
        return [it.name for it in content if it.ty in ('thm', 'thm.ax')]

    def testFirstDiffIndex(self):
        self.assertEqual(incremental.first_diff_index(None, ['a']), 0)
        self.assertEqual(incremental.first_diff_index(['a', 'b'], ['a', 'b']), 2)
        self.assertEqual(incremental.first_diff_index(['a', 'b'], ['a', 'c']), 1)
        # Deletion: new is a prefix of old -> replay only the deleted tail.
        self.assertEqual(incremental.first_diff_index(['a', 'b', 'c'], ['a', 'b']), 2)

    def testSecondRunReusesCache(self):
        # Start from no cache so the first run must replay.
        import os
        path = basic.status_cache_file(F)
        if os.path.exists(path):
            os.remove(path)
        st1, _, info1 = verify.validate_theory_info(F, trust=frozenset())
        self.assertFalse(info1['reused'])
        st2, _, info2 = verify.validate_theory_info(F, trust=frozenset())
        self.assertTrue(info2['reused'])
        self.assertEqual(st1, st2)

    def testTailEditReplaysOnlyTail(self):
        verify.validate_theory(F, trust=frozenset())
        cache = basic.theory_cache[F]
        n = len(cache['item_hashes'])
        cache['item_hashes'] = cache['item_hashes'][:-1] + ['changed']
        cache['source_hash'] = 'mutated'
        _, _, info = verify.validate_theory_info(F, trust=frozenset())
        self.assertFalse(info['reused'])
        self.assertEqual(info['start'], n - 1)
        self.assertEqual(info['start'], n - 1)

    def testDeletedTheoremLosesItsVerdict(self):
        verify.validate_theory(F, trust=frozenset())
        cache = basic.theory_cache[F]
        names = self._thm_names(cache['content'])
        victim = names[-1]
        # Simulate deleting the last theorem (and anything after it).
        keep = max(i for i, it in enumerate(cache['content'])
                   if it.name == victim)
        cache['content'] = cache['content'][:keep]
        cache['item_hashes'] = cache['item_hashes'][:keep]
        cache['source_hash'] = 'mutated'

        statuses, _, info = verify.validate_theory_info(F, trust=frozenset())
        self.assertFalse(info['reused'])
        self.assertNotIn(victim, statuses)
        # Gone from the in-memory table and from the persisted cache.
        self.assertNotIn(victim, basic.get_all_statuses())
        self.assertNotIn(victim, basic.load_status_data(F).get('theorems', {}))

    def testImportsEpochExcludesOwnSource(self):
        # A file's own source hash must not move its imports epoch,
        # otherwise a local edit could never reuse a prefix.
        before = incremental.imports_epoch(F)
        basic.theory_cache[F]['source_hash'] = 'changed-own-source'
        self.assertEqual(incremental.imports_epoch(F), before)


if __name__ == '__main__':
    unittest.main()

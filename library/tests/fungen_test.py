# Tests for the `fun` expansion (phase 4) at the library level.

"""Active: `nat`'s recursive definitions are born with a well-foundedness
proof -- the cache holds the generated group (`<c>_rel`, `<c>_H`,
`<c>_in`, `<c>_rel_wf` and the two equations) for every one of them, and
no equation is left as an axiom.  A representative item per shape the
templates branch on is replayed here as well, and no item of either
theory is left unparsed.

Passive: the shapes still outside the increment stay as `def.ind` items,
i.e. axiomatized.  In `nat` and `prod` those are the datatype's own
projections (`Pre`, `fst`, `snd` -- they cannot use themselves as
destructors).  In `list` they are the definitions whose *emitted text*
does not survive being written as an item: `rev`/`butlast`/`concat`
because their first equation has no variable to carry the item's type
variables (`rev [] = []`) and `butlast`/`concat` do not name them,
`zip` because the printer writes its result type `('a × 'b) list` as
`'a × 'b list` (i.e. `'a × ('b list)`), plus the definitions with more
than two arguments, more than one recursive call or a single equation.
That boundary is asserted here so it cannot widen unnoticed.
"""

import unittest

from core import basic


# The definitions the generator expands today: every recursive `fun` in
# nat.pyhol except the projections (Pre, fst, snd).
EXPANDED = ['plus', 'times', 'power', 'Sigma', 'less_eq', 'less', 'minus',
            'even', 'odd', 'fact']
# `fst`/`snd` are prod's own projections; `Pre` is nat's.
STILL_AXIOMATIZED = {'nat': ['Pre'], 'prod': ['fst', 'snd']}
# list.pyhol's recursive definitions: the ones the generator emits, and
# the ones it leaves axiomatized.
LIST_EXPANDED = ['append', 'distinct', 'drop', 'itrev', 'map', 'nth', 'take']
LIST_STILL_AXIOMATIZED = ['rev', 'butlast', 'concat', 'zip', 'length', 'set',
                          'filter', 'remdups', 'foldr', 'foldl',
                          'list_update', 'last', 'hd', 'tl']


class FunGenLibraryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay
        basic.load_metadata()

    def setUp(self):
        for fn in basic.get_import_order(['nat']):
            basic.load_theory_cache(fn)
        self.content = basic.theory_cache['nat']['content']

    def _items(self, name):
        return [item for item in self.content if item.name == name]

    def _by_name(self, name, thy='nat'):
        for fn in basic.get_import_order([thy]):
            basic.load_theory_cache(fn)
        for item in basic.theory_cache[thy]['content']:
            if item.name == name:
                return item
        return None

    def test_every_item_parses(self):
        """No emitted item is left unparsed.

        An item the loader cannot parse is dropped from the theory, so a
        group that cannot be parsed must not be emitted at all: it would
        take the constant it defines with it and every later item of the
        file that mentions that constant.  The generator keeps the
        axioms for such a definition instead (rev, butlast, concat and
        zip today), and this asserts no half-parsed group survives.
        """
        for thy in ('nat', 'list'):
            for fn in basic.get_import_order([thy]):
                basic.load_theory_cache(fn)
            broken = [(item.name, item.error) for item
                      in basic.theory_cache[thy]['content']
                      if item.error is not None]
            self.assertEqual(broken, [], 'unparsed items in %s' % thy)

    def test_generated_items_replay(self):
        """The shapes the templates distinguish replay to no open goal.

        One per shape the emitted proofs branch on: recursion on the
        first and on the second argument of a two-argument definition,
        recursion on a single argument (the decrease obligation is
        already an identity there), and the list's existential
        obligation, whose proof ends on an instance rather than on the
        obligation itself.
        """
        from core import context
        from core.verify import COMPUTATION_ORACLES, _replay
        from kernel import theory
        for thy, name in [('nat', 'nat_plus_def_2'), ('nat', 'nat_less_def_2'),
                          ('nat', 'fact_def_2'), ('nat', 'nat_plus_rel_wf'),
                          ('list', 'map_def_2'), ('list', 'itrev_def_2')]:
            item = self._by_name(name, thy)
            self.assertIsNotNone(item, 'no generated item %s' % name)
            with theory.fresh_theory():
                context.set_context(thy, limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=COMPUTATION_ORACLES)
            self.assertEqual(gaps, 0, '%s has %d open goal(s)' % (name, gaps))

    def test_recursive_funs_are_derived(self):
        """Each recursive `fun` yields its group, equations proved."""
        for name in EXPANDED:
            cname = {'plus': 'nat_plus', 'times': 'nat_times',
                     'power': 'nat_nat_power', 'less_eq': 'nat_less_eq',
                     'less': 'nat_less', 'minus': 'nat_minus'}.get(name, name)
            # No `fun` item survives: the definition is expanded.
            self.assertEqual(
                [it for it in self._items(name) if it.ty == 'def.ind'], [],
                '%s is still an axiomatized fun' % name)
            for generated in ['%s_H' % cname, '%s_rel' % cname,
                              '%s_in' % cname]:
                self.assertTrue(self._items(generated),
                                'missing generated constant %s' % generated)
            wf = self._items('%s_rel_wf' % cname)
            self.assertEqual([it.ty for it in wf], ['thm'],
                             '%s_rel_wf should be a proved theorem' % cname)
            self.assertTrue(wf[0].steps, '%s_rel_wf has no proof' % cname)
            for i in (1, 2):
                eqs = self._items('%s_def_%d' % (cname, i))
                self.assertEqual(
                    [it.ty for it in eqs], ['thm'],
                    '%s_def_%d is not a derived theorem' % (cname, i))
                self.assertTrue(eqs[0].steps,
                                '%s_def_%d has no proof' % (cname, i))

    def test_no_equation_is_an_axiom(self):
        """`thm.ax` must not name any equation of an expanded fun."""
        for item in self.content:
            if item.ty == 'thm.ax':
                self.assertNotRegex(item.name, r'_def_\d+$',
                                    '%s is still asserted' % item.name)

    def test_projection_layer_still_axiomatized(self):
        """The datatype's own projections are outside the increment."""
        for thy, names in STILL_AXIOMATIZED.items():
            for name in names:
                items = [it for it in basic.theory_cache[thy]['content']
                         if it.name == name]
                self.assertIn('def.ind', [it.ty for it in items],
                              '%s in %s unexpectedly expanded' % (name, thy))

    def test_list_expansion_boundary(self):
        """Which list definitions are derived, and which keep their axioms."""
        content = basic.theory_cache['list']['content']
        for cname in LIST_EXPANDED:
            wf = self._by_name('%s_rel_wf' % cname, 'list')
            self.assertIsNotNone(wf, 'missing %s_rel_wf' % cname)
            self.assertEqual(wf.ty, 'thm', '%s_rel_wf is not a theorem' % cname)
            self.assertTrue(wf.steps, '%s_rel_wf has no proof' % cname)
        for name in LIST_STILL_AXIOMATIZED:
            items = [it for it in content if it.name == name]
            self.assertIn('def.ind', [it.ty for it in items],
                          '%s in list unexpectedly expanded' % name)


if __name__ == '__main__':
    unittest.main()

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
destructors).  In `list` they are the definitions with a single
equation, more than two arguments or more than one recursive call, the
projections `hd`/`tl`, and `set` (whose rules do not parse where it
stands).  That boundary is asserted here so it cannot widen unnoticed.
"""

import unittest

from core import basic


# The definitions the generator expands today: every recursive `fun` in
# nat.pyhol except the projections (Pre, fst, snd).
EXPANDED = ['plus', 'times', 'power', 'Sigma', 'less_eq', 'less', 'minus',
            'even', 'odd', 'fact']
# The projections are still axiomatized: their destructor would be the very
# function being defined (`Pre (Suc n) = n`, `fst (Pair a b) = a`), and a
# file below them cannot import the wf machinery either.
# Every `fun` of these four theories is derived now, the datatype's own
# projections included: their destructor is the generated one of the same
# position (`nat_Suc_1`, `list_cons_2`, `prod_Pair_1`, `option_SomeC_1`),
# which is defined by THE and does not mention the function being defined
# (see core/datgen.py `generated_destructor_names`).
STILL_AXIOMATIZED = {}
# list.pyhol's recursive definitions: the ones the generator emits, and the
# ones it leaves axiomatized.
LIST_EXPANDED = ['append', 'butlast', 'concat', 'distinct', 'drop', 'filter',
                 'foldl', 'foldr', 'itrev', 'last', 'length', 'list_update',
                 'map', 'nth', 'remdups', 'rev', 'set', 'take', 'zip']
LIST_STILL_AXIOMATIZED = []
DERIVED_PROJECTIONS = [('nat', 'Pre'), ('list', 'hd'), ('list', 'tl'),
                       ('prod', 'fst'), ('prod', 'snd'), ('option', 'the')]
# Definitions whose recursion is not on a datatype's subterm relation: the
# four projections from `scalarValue` recurse nowhere, so their relation is
# the empty one, and `tsum`/`tleaf` are the three-constructor samples of
# wfrec_example (the chain of tests, with a test that carries variables in
# the middle and no recursion at all in `tleaf`).
NONSTRUCTURAL = [('gcl', 'scalar_is_nat'), ('gcl', 'scalar_is_bool'),
                 ('gcl', 'scalar_of_nat'), ('gcl', 'scalar_of_bool'),
                 ('wfrec_example', 'tsum'), ('wfrec_example', 'tleaf')]


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
        already an identity there), the list's existential obligation,
        whose proof ends on an instance rather than on the obligation
        itself, and the equations whose types the emitter has to write
        out (`length`'s first equation), whose body has to be kept whole
        (`rev`, whose body ends in a list literal) or whose result type
        the printer used to mangle (`zip`).
        """
        from core import context
        from core.verify import COMPUTATION_ORACLES, _replay
        from kernel import theory
        for thy, name in [('nat', 'nat_plus_def_2'), ('nat', 'nat_less_def_2'),
                          ('nat', 'fact_def_2'), ('nat', 'nat_plus_rel_wf'),
                          ('list', 'map_def_2'), ('list', 'itrev_def_2'),
                          ('list', 'length_def_1'), ('list', 'rev_def_2'),
                          ('list', 'zip_def_2')]:
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

    def test_two_column_lexicographic_recursion(self):
        """`lexnat` needs two measures, and its walk uses both mlex rules.

        Its third equation keeps the first argument and decreases the
        second, so no single measure covers it: the relation is a
        two-column `mlex_prod` chain, and the call that only does not
        increase at the first column is discharged at the second with
        `mlex_leq` (`mlex_less` alone would not do it).
        """
        from core.verify import COMPUTATION_ORACLES, _replay
        from core import context
        from kernel import theory
        cname = 'lexnat'
        rel = self._by_name('%s_rel' % cname, 'measure_example')
        self.assertIsNotNone(rel, '%s did not expand' % cname)
        self.assertEqual([it.name for it in
                          basic.theory_cache['measure_example']['content']
                          if it.name == cname and it.ty == 'def.ind'], [],
                         '%s is still an axiomatized fun' % cname)
        # Two columns: `wf` peels `wf_mlex` once per measure.
        wf_steps = [st.get('theorem') for st in
                    self._by_name('%s_rel_wf' % cname, 'measure_example').steps]
        self.assertEqual(wf_steps.count('wf_mlex'), 2,
                         'the relation is not a two-column chain: %s'
                         % wf_steps)
        for name in ['%s_m1' % cname, '%s_m2' % cname]:
            self.assertIsNotNone(self._by_name(name, 'measure_example'),
                                 'no measure constant %s' % name)
        for name in ['%s_def_1' % cname, '%s_def_2' % cname,
                     '%s_def_3' % cname, '%s_rel_wf' % cname]:
            item = self._by_name(name, 'measure_example')
            self.assertIsNotNone(item, 'missing %s' % name)
            with theory.fresh_theory():
                context.set_context('measure_example', limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=COMPUTATION_ORACLES)
            self.assertEqual(gaps, 0, '%s has %d open goal(s)' % (name, gaps))
        steps = [st.get('theorem') for st in
                 self._by_name('%s_def_3' % cname, 'measure_example').steps]
        self.assertIn('mlex_leq', steps,
                      'the two-column walk never used mlex_leq')

    def test_no_equation_is_an_axiom(self):
        """`thm.ax` must not name any equation of an expanded fun."""
        for item in self.content:
            if item.ty == 'thm.ax':
                self.assertNotRegex(item.name, r'_def_\d+$',
                                    '%s is still asserted' % item.name)

    def test_projection_layer_is_derived(self):
        """The datatype's own projections are derived too.

        Their destructor is the function being defined, so the body is
        written with the generated destructor of the same position: for
        `tl` that is `list_cons_2`, for `Pre` it is `nat_Suc_1`, and
        neither mentions the function.
        """
        for thy, name in DERIVED_PROJECTIONS:
            self._by_name('dummy', thy)  # load the theory
            items = [it for it in basic.theory_cache[thy]['content']
                     if it.name == name]
            self.assertEqual([it.ty for it in items], ['def'],
                             '%s in %s is still an axiomatized fun' % (name, thy))
            self.assertIsNotNone(self._by_name('%s_rel_wf' % name, thy),
                                 'no %s_rel_wf in %s' % (name, thy))

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

    def test_nonstructural_definitions_are_derived(self):
        """Definitions whose relation is not a subterm relation.

        `scalarValue` has no recursive constructor at all, so no subterm
        relation over it exists; `tleaf` matches on three constructors
        without recursing.  Both expand with the empty relation, whose
        well-foundedness is `wf_false`, and `tsum` recurses over the third
        constructor of a datatype of three.
        """
        for thy, name in NONSTRUCTURAL:
            for fn in basic.get_import_order([thy]):
                basic.load_theory_cache(fn)
            items = [it for it in basic.theory_cache[thy]['content']
                     if it.name == name]
            self.assertEqual([it.ty for it in items], ['def'],
                             '%s in %s is still axiomatized' % (name, thy))
            rel_wf = self._by_name('%s_rel_wf' % name, thy)
            self.assertEqual(rel_wf.ty, 'thm', '%s_rel_wf is not a theorem' % name)
            self.assertTrue(rel_wf.steps, '%s_rel_wf has no proof' % name)


if __name__ == '__main__':
    unittest.main()

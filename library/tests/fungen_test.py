# Tests for the `fun` expansion (phase 4) at the library level.

"""Active: every recursive `fun` of the library is born with a
well-foundedness proof -- the cache holds the generated group (`<c>_rel`,
`<c>_H`, `<c>_in`, `<c>_rel_wf` and the equations) for each of them, and
no equation is left as an axiom anywhere.  A representative item per shape
the templates branch on is replayed here as well, and no item of either
theory is left unparsed.

The relation a definition descends through is the measure chain the search
found (`wf_mlex` once per column down to `wf_false`, each call discharged
at the first column where it strictly decreases).  The datatype's own
subterm relation is what is left for the definitions a measure cannot
express, above all the datatype's size function itself -- its only
candidate measure would be the constant being defined.  Both routes are
asserted here, and so is the size family of a datatype whose constructors
recurse more than once: that size is what Isabelle's datatype package
gives such a constructor, and what `lexicographic_order` then finds.

Passive: the shapes still outside the increment stay as `def.ind` items,
i.e. axiomatized.  Nothing is left there today; the lists below say which
shapes used to be, so their return would be noticed.
"""

import unittest

from core import basic


# The recursive definitions of nat.pyhol, projections included.
EXPANDED = ['plus', 'times', 'power', 'Sigma', 'less_eq', 'less', 'minus',
            'even', 'odd', 'fact']
# Empty since the datatype's own projections were derived: their destructor
# would be the very function being defined (`Pre (Suc n) = n`,
# `fst (Pair a b) = a`), which is why the emitter uses the generated one of
# the same position instead (`nat_Suc_1`, `list_cons_2`, `prod_Pair_1`,
# `option_SomeC_1`; see core/datgen.py `generated_destructor_names`).
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

    def test_a_definition_with_a_hole_gets_its_items(self):
        """The equation set is completed with `undefined`, so the rules exist.

        `hd (x # xs) = x` says nothing about `[]`, and `the (SomeC x) = x`
        nothing about `None`.  Isabelle's sequential `fun` completes such a set
        with a catchall `f x1 ... xn = undefined` and splits it
        (`Function/fun.ML`: `add_catchall`, then
        `Function_Split.split_all_equations`), so the input no equation covered
        becomes an equation of its own and the completeness and induction rules
        are statable.  The same subtraction runs here, which is why `hd [] =
        undefined`, `tl [] = undefined` and `the None = undefined` are
        equations of these definitions rather than holes the generator walks
        around -- and why both rules are emitted for them, and replayed here.
        `dbl`, `drop2` and `exdrop` are the harder half: their hole is `Suc 0`,
        which differs from the equation next to it only *inside* the `Suc`, so
        the branch that rules it out peels that constructor with its injectivity
        first (`_pattern_neq`) -- and `exdrop` goes through a user-written
        relation and descent lemma, whose rule lays out a line in an induction
        branch just as a comparison lemma does.
        """
        from core.verify import COMPUTATION_ORACLES, _replay
        from core import context
        from kernel import theory
        for thy, name in [('list', 'hd_def_2'), ('list', 'tl_def_2'),
                          ('list', 'last_def_2'), ('option', 'the_def_2'),
                          ('measure_example', 'dbl_def_3'),
                          ('measure_example', 'drop2_def_3'),
                          ('measure_example', 'exdrop_def_3'),
                          ('list', 'hd_exhaustive'), ('list', 'tl_induct'),
                          ('list', 'last_induct'), ('option', 'the_exhaustive'),
                          ('option', 'the_induct'),
                          ('measure_example', 'dbl_exhaustive'),
                          ('measure_example', 'dbl_induct'),
                          ('measure_example', 'drop2_induct'),
                          ('measure_example', 'exdrop_exhaustive'),
                          ('measure_example', 'exdrop_induct')]:
            item = self._by_name(name, thy)
            self.assertIsNotNone(item, 'missing %s' % name)
            self.assertEqual(item.ty, 'thm', '%s is not a theorem' % name)
            self.assertTrue(item.steps, '%s has no proof' % name)
            with theory.fresh_theory():
                context.set_context(thy, limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=COMPUTATION_ORACLES)
            self.assertEqual(gaps, 0, '%s has %d open goal(s)' % (name, gaps))

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

    def test_arithmetic_measures_expand(self):
        """Measures that need the arithmetic engine, not just the `Suc`
        rules: a literal coefficient, and a sum the call wrote in the
        other order.

        `qdbl`'s cell is a comparison of two products (`3 * n` against
        `3 * Suc n`): the literal comes apart into the spine and the
        product distributes, so the comparison is additive.  `swapdec`'s
        cell is a sum in the other order (`n + m` against `m + n` with a
        `Suc` over it), which only meets once the atoms are sorted -- and
        the swap is emitted *positionally* (`loc=`), because one `rewrite
        add_comm` step applies the theorem at every sum of the goal
        rather than at the one pair the engine planned.
        """
        from core.verify import COMPUTATION_ORACLES, _replay
        from core import context
        from kernel import theory
        for cname in ('qdbl', 'swapdec'):
            self.assertIsNotNone(
                self._by_name('%s_rel' % cname, 'measure_example'),
                '%s did not expand' % cname)
        for name in ['qdbl_def_1', 'qdbl_def_2', 'qdbl_exhaustive',
                     'qdbl_induct', 'qdbl_rel_wf',
                     'swapdec_def_1', 'swapdec_def_2', 'swapdec_exhaustive',
                     'swapdec_induct', 'swapdec_rel_wf']:
            item = self._by_name(name, 'measure_example')
            self.assertIsNotNone(item, 'missing %s' % name)
            with theory.fresh_theory():
                context.set_context('measure_example', limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=COMPUTATION_ORACLES)
            self.assertEqual(gaps, 0, '%s has %d open goal(s)' % (name, gaps))
        steps = self._by_name('swapdec_def_2', 'measure_example').steps
        swaps = [st for st in steps if st.get('theorem') == 'add_comm']
        self.assertTrue(swaps, 'the sum was never sorted: %s'
                        % [st.get('theorem') for st in steps])
        self.assertTrue(all(st.get('loc') for st in swaps),
                        'a commutativity step was emitted globally, which '
                        'the replay applies at every sum of the goal')
        self.assertIn('distrib_l', [st.get('theorem') for st in
                                    self._by_name('qdbl_def_2',
                                                  'measure_example').steps])

    def test_size_carries_multi_recursive_datatypes(self):
        """A constructor that recurses more than once.

        Isabelle's datatype package gives `Plus a1 a2` the size
        `1 + size a1 + size a2`, and `lexicographic_order` finds it: a
        definition over such a datatype descends through the size and the
        subterm relation is never consulted for it.  holpy derives that
        size as an ordinary `fun`, so the size function itself is the one
        definition whose relation *is* the subterm relation -- a
        disjunction over the recursive arguments -- and its `wf` goes
        through `wf_measure_gen` while `aval`'s goes through `wf_mlex`.
        """
        from core.verify import COMPUTATION_ORACLES, _replay
        from core import context
        from kernel import theory
        for name in (['aexp_size_def_%d' % k for k in (1, 2, 3, 4)]
                     + ['aexp_size_less_%d' % k for k in (1, 2, 3, 4)]
                     + ['aexp_size_rel_wf', 'aval_rel_wf',
                        'aval_def_3', 'aval_def_4']):
            item = self._by_name(name, 'expr')
            self.assertIsNotNone(item, 'missing %s' % name)
            self.assertEqual(item.ty, 'thm', '%s is not a theorem' % name)
            self.assertTrue(item.steps, '%s has no proof' % name)
        self.assertEqual(
            [it for it in basic.theory_cache['expr']['content']
             if it.ty == 'def.ind'], [],
            'expr still has an axiomatized fun')
        # `aval` descends through the size: its relation is a one-column
        # `mlex_prod` chain, and the obligation is closed by `mlex_less`.
        wf_steps = self._theorems('aval_rel_wf', 'expr')
        self.assertIn('wf_mlex', wf_steps,
                      'the aval relation is not a measure chain')
        self.assertNotIn('aexp_wf_subterm', wf_steps,
                         'aval descends through the subterm relation')
        self.assertIn('mlex_less', self._theorems('aval_def_3', 'expr'),
                      'aval does not descend through a measure')
        # The size function's own recursion is the one that is not: its
        # relation is the datatype's subterm relation, so its `wf` is that
        # relation's own lemma (`wf_measure_gen` only enters for a
        # definition of several arguments, where the relation is lifted
        # through the projection).
        self.assertIn('aexp_wf_subterm', self._theorems('aexp_size_rel_wf',
                                                        'expr'),
                      'the size function descends through a measure')
        # `tri3` recurses three times in one constructor: one `size_less`
        # per recursive position, and a definition that takes that size as
        # its measure.
        for name in ('tri3_size_less_%d' % k for k in (1, 2, 3)):
            item = self._by_name(name, 'measure_example')
            self.assertIsNotNone(item, 'missing %s' % name)
            self.assertEqual(item.ty, 'thm', '%s is not a theorem' % name)
        self.assertIsNotNone(self._by_name('t3count_m1', 'measure_example'),
                             't3count did not find the size as a measure')
        # `t3count`'s second call is the one whose cell is not a lemma on
        # its own: `size y <= size x + (size y + size z)` needs
        # `le_add_left_mono` to peel the surplus atom off a sub-comparison
        # `le_add` proves, so the closing is a tree and not a single rule.
        # In an induction branch the goal carries the branch's hypotheses
        # while a comparison lemma's conclusion carries none, so each rule
        # in that tree lays out a line and consumes the goal it closes --
        # the outer one has to name the fact the inner one produced.  The
        # item is replayed below, which is what judges those IDs.
        self.assertIsNotNone(self._by_name('t3count_induct', 'measure_example'),
                             't3count did not get an induction rule')
        # `hoare`'s `com` is parametric (`'a com`) and recurses twice in a
        # constructor (`Seq`, `Cond`).  `While b I c` also names an argument
        # `b` -- the name `_disjunct` binds its own tuple variable with -- so
        # the pattern's variables have to go into the disjunct only after
        # that binder is gone; abstracting over the witness first is refused
        # ("abstract_over: wrong type") and would capture silently if the
        # two types agreed.
        for name in ('com_size', 'com_size_rel_wf',
                     'com_size_def_3', 'com_size_def_4'):
            item = self._by_name(name, 'hoare')
            self.assertIsNotNone(item, 'missing %s' % name)
        self.assertEqual(self._by_name('com_size_rel_wf', 'hoare').ty, 'thm',
                         'com_size_rel_wf is not a theorem')
        # `wfrec_example`'s `tri` puts the recursive equation in the middle
        # of the chain (`TriZ | TriS t | TriO`), so its branch test has to be
        # *proved*, and that test's instance (`TriS t = TriS t`) is the
        # decrease obligation itself.  The two are one proposition, so one
        # item serves both -- a second `cut` would create nothing, the
        # stable-ID layer keying items by proposition.
        for name in ('tri_size', 'tri_size_rel_wf', 'tri_size_def_2'):
            self.assertIsNotNone(self._by_name(name, 'wfrec_example'),
                                 'missing %s' % name)
        # `tsum :: tri ⇒ nat` has no `nat` argument, so its only candidate
        # measure is the size the datatype just got; its relation is then a
        # `mlex` chain rather than `tri`'s subterm relation, which is what
        # `tleaf` (no recursion at all) still uses.
        self.assertIn('wf_mlex', self._theorems('tsum_rel_wf', 'wfrec_example'),
                      'tsum did not take the size as its measure')
        # The three shapes the emitted proofs branch on: two calls landing
        # on one instance (`seen`), a position past the first of several
        # (the peel chain), three calls in one equation, and a test whose
        # instance is the obligation.  `t3count_induct` is the fourth: a
        # cell whose closing is a cut tree rather than one rule.
        for thy, name in [('expr', 'aexp_size_def_3'),
                          ('expr', 'aexp_size_less_2'),
                          ('measure_example', 'tri3_size_def_2'),
                          ('measure_example', 'tri3_size_less_3'),
                          ('measure_example', 't3count_def_2'),
                          ('measure_example', 't3count_induct'),
                          ('hoare', 'com_size_def_4'),
                          ('wfrec_example', 'tri_size_def_2')]:
            item = self._by_name(name, thy)
            self.assertIsNotNone(item, 'missing %s' % name)
            with theory.fresh_theory():
                context.set_context(thy, limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=COMPUTATION_ORACLES)
            self.assertEqual(gaps, 0, '%s has %d open goal(s)' % (name, gaps))

    def test_definitions_with_a_clause(self):
        """Definitions that carry a measure, or a relation and its proofs.

        The structural check is what makes an *axiomatized* definition safe;
        one that carries a clause derives its equations from a termination
        proof instead, so the check is not asked and the emitter descends
        through what the clause says.  `drop2` and `exdrop` are the shape
        the check refuses (`n` is not a direct argument of the pattern
        `Suc (Suc n)`): the first carries the measure, the second the
        relation with the file's own `wf` and descent lemmas.
        """
        from core.verify import COMPUTATION_ORACLES, _replay
        from core import context
        from kernel import theory
        for cname in ('drop2', 'exdrop'):
            wf = self._by_name('%s_rel_wf' % cname, 'measure_example')
            self.assertIsNotNone(wf, 'missing %s_rel_wf' % cname)
            self.assertEqual(wf.ty, 'thm', '%s_rel_wf is not a theorem' % cname)
            self.assertTrue(wf.steps, '%s_rel_wf has no proof' % cname)
        # The measure the file wrote becomes a column like any other.
        self.assertIsNotNone(self._by_name('drop2_m1', 'measure_example'),
                             'the given measure is not a measure column')
        self.assertIn('wf_mlex',
                      self._theorems('drop2_rel_wf', 'measure_example'),
                      'the given measure is not on a chain')
        # The relation is the file's, and so are the proofs of it.
        self.assertIn('ex_less_wf',
                      self._theorems('exdrop_rel_wf', 'measure_example'),
                      'the relation was not proved from the file\'s wf lemma')
        self.assertIn('ex_drop_dec',
                      self._theorems('exdrop_def_2', 'measure_example'),
                      'the obligation was not discharged from the file\'s lemma')
        for name in ('drop2_def_2', 'exdrop_def_2'):
            item = self._by_name(name, 'measure_example')
            with theory.fresh_theory():
                context.set_context('measure_example', limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=COMPUTATION_ORACLES)
            self.assertEqual(gaps, 0, '%s has %d open goal(s)' % (name, gaps))

    def _theorems(self, name, thy):
        """The theorems one generated item's steps cite."""
        item = self._by_name(name, thy)
        self.assertIsNotNone(item, 'missing %s' % name)
        return [st.get('theorem') for st in item.steps]

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

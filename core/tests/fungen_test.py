"""Unit test for the fun expansion's transformation layer.

The emitted *proofs* are not asserted here: they are produced by asking
the method layer what each step does (core.verify.probe_steps), which
core is not allowed to depend on.  Their end-to-end effect -- every
`fun` equation derived, none left as an axiom -- is checked by
library/tests/fungen_test.py, and by the library validation itself.
"""

import unittest

from kernel.term import Const, Var
from kernel.type import TFun, TConst, TVar
from core import basic
from core import context
from core import fungen
from core.measure import Closing

NatType = TConst('nat')


class FunGenTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('nat')

    def _eqs(self, name, ty, props):
        with context.fresh_context(defs={name: ty}):
            return [context.parse_term(prop) for prop in props]

    def _plan(self, name, ty, props):
        """(arg_types, res_type, r, eqs) for the given equations."""
        arg_types, res_type = ty.strip_type()
        eqs = self._eqs(name, ty, props)
        lhs = [fungen._eq_args(eq) for eq in eqs]
        r = fungen.recursion_position(arg_types, lhs)
        return arg_types, res_type, r, eqs

    def test_nat_structural(self):
        # fun wfgen :: nat => nat => nat
        #   | wfgen 0 n = n
        #   | wfgen (Suc m) n = Suc (wfgen m n)
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type, r, eqs = self._plan('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        self.assertEqual(r, 0)
        # p = (x, n): the recursion position is projected as fst p, the
        # pattern variable m becomes Pre (fst p), and the recursive call
        # receives the tuple (Pre (fst p), snd p).
        self.assertEqual(
            fungen._body_prop('wfgen', arg_types, res_type, eqs, r),
            'if fst p = 0 then snd p'
            ' else Suc (g (Pair (Pre (fst p)) (snd p)))')
        # The relation is the recursion component's own well-founded
        # relation lifted through the projection, as a lambda.
        self.assertEqual(fungen._rel_body(arg_types, r),
                         '%p::nat × nat. %q::nat × nat. fst q = Suc (fst p)')
        # The decrease obligation is written with the projections still
        # un-reduced: that is the shape the goal's condition has, and the
        # projection rules are applied inside the obligation's own proof.
        f_const = Const('wfgen', ty)
        calls = fungen._calls(eqs[1].rhs, f_const, 2)
        tcall = fungen.tupled_arg(calls[0])
        self.assertEqual(
            fungen._decrease_prop(arg_types, r, tcall, fungen._tuple_of(eqs[1])),
            'fst (Pair (Suc m) n) = Suc (fst (Pair m n))')

    def test_list_structural(self):
        # fun wfmap :: ('a => 'b) => 'a list => 'b list
        #   | wfmap f [] = []
        #   | wfmap f (x # xs) = f x # wfmap f xs
        basic.load_theory('list')
        ta, tb = TVar('a'), TVar('b')
        ty = TFun(TFun(ta, tb), TFun(TConst('list', ta), TConst('list', tb)))
        arg_types, res_type, r, eqs = self._plan('wfmap', ty, [
            'wfmap f [] = []',
            'wfmap f (x # xs) = f x # wfmap f xs'])
        self.assertEqual(r, 1)
        # p = (f, xs): the list is snd p, the pattern variables are
        # x = hd (snd p) and xs = tl (snd p).
        self.assertEqual(
            fungen._body_prop('wfmap', arg_types, res_type, eqs, r),
            'if snd p = [] then []'
            ' else fst p (hd (snd p)) # g (Pair (fst p) (tl (snd p)))')
        self.assertEqual(
            fungen._rel_body(arg_types, r),
            '%p::(\'a ⇒ \'b) × \'a list. %q::(\'a ⇒ \'b) × \'a list.'
            ' ∃w. snd q = w # snd p')

    def test_decrease_reduction(self):
        """The projection/destructor rules the emitted propositions need."""
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type, r, eqs = self._plan('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        body = fungen._body_term('wfgen', arg_types, res_type, eqs, r,
                                 fungen._tuple_of(eqs[1]))
        red, rules = fungen._reduce_used(body, fungen._destructor_maps(arg_types, r))
        # Pre (Suc m) reduces to m, so Pre's second rule is needed; the
        # projections in the condition and in the recursive call's tuple
        # are computed away with fst/snd.
        self.assertEqual(rules, ['fst_def_1', 'snd_def_1', 'Pre_def_2'])
        self.assertEqual(fungen._prints(red),
                         'if Suc m = 0 then n else Suc (g (Pair m n))')

    def test_chain_over_three_equations(self):
        """The body is the equations' chain, in source order.

        Every equation's pattern becomes a test; a test with variables is
        an existential over one witness tuple, so `elim` takes it apart in
        one step whichever way the pattern is nested.
        """
        ty = TFun(NatType, NatType)
        arg_types, res_type, r, eqs = self._plan('g3', ty, [
            'g3 0 = 0',
            'g3 (Suc 0) = 1',
            'g3 (Suc (Suc n)) = 2'])
        # A pattern without a variable of its own is an equality -- the
        # nested `Suc 0` included -- and one with variables is an
        # existential over their tuple, whose witness is named after the
        # equation so that two of them in one proof cannot share an ID.
        cond = lambda k: fungen._prints(
            fungen.branch_condition(fungen._eq_args(eqs[k]), 0,
                                    fungen.Var('p', NatType), k))
        self.assertEqual(cond(0), 'p = 0')
        self.assertEqual(cond(1), 'p = Suc 0')
        self.assertEqual(cond(2), '∃_w3. p = Suc (Suc _w3)')
        self.assertEqual(
            fungen._body_prop('g3', arg_types, res_type, eqs, 0),
            'if p = 0 then (0::nat) else if p = Suc 0 then 1 else 2')

    def test_rejects_shapes_it_cannot_emit(self):
        """Shapes the emitter cannot prove its items for raise instead."""
        ty = TFun(NatType, NatType)
        # No argument carries a constructor pattern: there is nothing to
        # branch on and no recursion to justify.
        with self.assertRaises(fungen.FunGenError):
            fungen._expand({'name': 'f', 'type': printer_type(ty),
                            'rules': [{'prop': 'f n = n'}]})
        # Two equations with the same constructor root: the chain decides
        # by `t = C _` alone, so the more specific pattern would have to be
        # subtracted from the more general one.
        with self.assertRaises(fungen.FunGenError):
            fungen._expand({'name': 'g', 'type': printer_type(ty),
                            'rules': [{'prop': 'g (Suc n) = n'},
                                      {'prop': 'g (Suc m) = m'}]})

    def test_writes_out_types_an_equation_cannot_carry(self):
        """An equation is emitted with the types it cannot carry written out.

        The item parser types an equation from the item's `fixes`
        variables, so a variable-free equation has to name the
        definition's type variables in its own text; otherwise the loader
        drops the item, and with it the definition it belongs to.  The
        types written out are the printed ones, which read back as
        themselves (`('a × 'b) list` used to print as `'a × ('b list)`).
        """
        basic.load_theory('list')
        ta = TVar('a')
        ty = TFun(TConst('list', ta), TConst('list', ta))
        entries = fungen._expand(
            {'name': 'g2', 'type': printer_type(ty),
             'rules': [{'prop': 'g2 [] = []'},
                       {'prop': 'g2 (x # xs) = g2 xs'}]})
        by_name = {entry['name']: entry for entry in entries}
        self.assertEqual(by_name['g2_def_1']['prop'],
                         "g2 ([]::'a list) = ([]::'a list)")
        # The source's own text is kept whenever it carries the types.
        self.assertEqual(by_name['g2_def_2']['prop'], 'g2 (x # xs) = g2 xs')
        self.assertEqual(fungen._printt(TConst('list', TConst('prod', ta, TVar('b')))),
                         "('a × 'b) list")

    def test_equation_text_names_its_types(self):
        """An equation that cannot carry its types is written out with them.

        The item parser types an equation from the item's `fixes`
        variables, so a variable-free equation has to name the
        definition's type variables in its own text or the loader drops
        the item -- and with it the definition it belongs to.
        """
        basic.load_theory('list')
        ta = TVar('a')
        ty = TFun(TConst('list', ta), TConst('list', ta))
        with context.fresh_context(defs={'butlast': ty}):
            eq = context.parse_term('butlast [] = []')
        self.assertEqual(
            fungen._equation_text('butlast', ty, 'butlast [] = []', eq),
            "butlast ([]::'a list) = ([]::'a list)")
        # The source's own text is kept whenever it can carry them.
        self.assertEqual(
            fungen._equation_text('butlast', ty, "butlast ([]::'a list) = []",
                                  eq),
            "butlast ([]::'a list) = []")

    def test_body_kept_whole(self):
        """A body ending in a list literal is bracketed.

        A `def` item is a single line and its parser reads a trailing
        `[...]` group as that item's attribute list, which would leave
        the body truncated at the operator before it.
        """
        self.assertEqual(fungen._kept_whole('g (tl p) @ [hd p]'),
                         '(g (tl p) @ [hd p])')
        self.assertEqual(fungen._kept_whole('g (tl p)'), 'g (tl p)')

    def test_induct_statement_matches_the_hand_written_rule(self):
        """The induction rule's statement, equation by equation.

        One premise per equation -- the pattern's variables quantified, the
        induction hypothesis of every recursive call in front, the pattern
        as the conclusion -- and `!p. P p` at the end.  The shape below is
        the one library/wfrec_example.pyhol carries by hand as
        `wfx_induct`, whose equations are these; generating it is what
        makes a definition usable for proving anything about it.
        """
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type, r, eqs = self._plan('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        calls = [[], [fungen.tupled_arg([Var('m', NatType), Var('n', NatType)])]]
        self.assertEqual(
            fungen._prints(fungen._induct_prop(arg_types, lhs, calls)),
            '(∀n. P (Pair 0 n)) ⟶'
            ' (∀m. ∀n. P (Pair m n) ⟶ P (Pair (Suc m) n)) ⟶'
            ' (∀p. P p)')

    def test_closing_tree_carries_the_fact_the_sub_proof_made(self):
        """A cut node takes the fact below it, which is not always the cut.

        A `rule` closes its goal in place when the fact it derives is the
        goal's own theorem, and lays out a line when it is a different one.
        An induction branch's goal carries the branch's hypotheses and a
        comparison lemma's conclusion carries none, so in that context the
        two differ: the goal's stable ID is consumed and the fact gets a
        new one.  A cut node's outer rule takes the inner rule's fact as
        its premise and has to name *that* ID; naming the cut, which the
        inner rule just consumed, is a reference the replay cannot resolve.
        """
        tree = Closing('cut', 'le_add_left_mono', prop='a <= b',
                       sub=Closing('rule', 'le_add'))
        branch = fungen._Proof()
        self.assertEqual(fungen._emit_closing(branch, tree, 7, lines=True), 3)
        self.assertEqual(branch.text(), [
            '  cut "a <= b" goal=7',
            '  ← rule le_add goal=1',
            '  ← rule le_add_left_mono goal=7 facts=[2]',
        ])

    def test_closing_tree_in_place_keeps_the_cut_id(self):
        """Where the goal has no hypotheses the cut's own ID is the fact.

        `_def_entry`'s goals are hypothesis-free, so the rule it applies
        derives the goal's own theorem and closes in place: nothing is
        consumed and the cut's ID stands.  The same tree, emitted in that
        context, names the cut and closes its outer goal in place too.
        """
        tree = Closing('cut', 'le_add_left_mono', prop='a <= b',
                       sub=Closing('rule', 'le_add'))
        equation = fungen._Proof()
        self.assertEqual(fungen._emit_closing(equation, tree, 7), 7)
        self.assertEqual(equation.text(), [
            '  cut "a <= b" goal=7',
            '  ← rule le_add goal=1',
            '  ← rule le_add_left_mono goal=7 facts=[1]',
        ])

    def test_subtraction_narrows_an_overlapping_equation(self):
        """A later equation means "the equations before it did not match".

        `g x (Suc y)` overlaps `g (Suc x) y` where both arguments are a `Suc`.
        Subtracting the first equation leaves exactly that region out of the
        second, so the second becomes `g 0 (Suc y)`: the sequential reading of
        `fun`, which is also what the branch chain emits.  The two equations
        together still leave `g 0 0` -- neither matches it -- so the catchall
        contributes that too, and it is the one entry reported as missing.
        """
        ty = TFun(NatType, TFun(NatType, NatType))
        with context.fresh_context(defs={'g': ty}):
            eqs = [context.parse_term(prop) for prop in
                   ['g (Suc x) y = y', 'g x (Suc y) = x']]
        arg_types, res_type = ty.strip_type()
        out, texts, missing = fungen._complete_equations(
            'g', arg_types, res_type, eqs, ['g (Suc x) y = y', 'g x (Suc y) = x'])
        self.assertEqual(len(out), 3)
        self.assertEqual(fungen._prints(fungen._eq_args(out[1])[0]), '(0::nat)')
        self.assertEqual(fungen._constr_name(fungen._eq_args(out[1]), 1), 'Suc')
        self.assertEqual(len(missing), 1)
        self.assertEqual([fungen._prints(a)
                          for a in fungen._eq_args(missing[0])],
                         ['(0::nat)', '(0::nat)'])
        # The first equation is untouched, so it keeps the source's text.
        self.assertEqual(texts[0], 'g (Suc x) y = y')
        self.assertIsNone(texts[1])

    def test_a_redundant_equation_is_refused(self):
        """An equation the ones before it already cover decides nothing.

        Isabelle refuses these too ("Equation is redundant (covered by
        preceding clauses)"): the branch chain is a sequence of tests, so a
        later equation may narrow an earlier one but not repeat it.
        """
        ty = TFun(NatType, NatType)
        arg_types, res_type, r, eqs = self._plan('g', ty, [
            'g (Suc n) = 0',
            'g (Suc 0) = 1'])
        with self.assertRaises(fungen.FunGenError):
            fungen._complete_equations('g', arg_types, res_type, eqs,
                                       [None, None])

    def test_a_hole_at_another_constructor_is_filled(self):
        """`g (Suc n) = n` leaves `0`, and `0` is a constructor of its own.

        The catchall's survivor joins the equation set -- the definition is
        `undefined` there, which is what Isabelle's sequential `fun` does with
        a missing pattern -- and is reported as the missing one.  Its text is
        None: there is no source text for an equation the emitter made.
        """
        ty = TFun(NatType, NatType)
        arg_types, res_type, r, eqs = self._plan('g', ty, ['g (Suc n) = n'])
        out, texts, missing = fungen._complete_equations(
            'g', arg_types, res_type, eqs, ['g (Suc n) = n'])
        self.assertEqual(len(out), 2)
        self.assertEqual(len(missing), 1)
        self.assertEqual(fungen._prints(fungen._eq_args(missing[0])[0]),
                         '(0::nat)')
        self.assertEqual(fungen._prints(missing[0].rhs), '(undefined::nat)')
        self.assertIsNone(texts[1])

    def test_a_hole_one_level_down_is_filled(self):
        """`g 0` and `g (Suc (Suc n))` leave `Suc 0`, and it is filled.

        The missing pattern differs from its neighbour `Suc (Suc n)` only
        *inside* a constructor, so ruling one out needs that constructor's
        injectivity first -- `_pattern_neq` peels the shared `Suc` and refutes
        the argument that differs.  A `nat` is shallow enough that a hole in it
        is always this shape, so this is the case that decides whether a
        definition with a gap over `nat` (`dbl`, whose recursion skips a
        constructor) can be given rules at all.
        """
        ty = TFun(NatType, NatType)
        arg_types, res_type, r, eqs = self._plan('g', ty, [
            'g 0 = 0',
            'g (Suc (Suc n)) = 2'])
        out, texts, missing = fungen._complete_equations(
            'g', arg_types, res_type, eqs, ['g 0 = 0', 'g (Suc (Suc n)) = 2'])
        self.assertEqual(len(out), 3)
        self.assertEqual(len(missing), 1)
        self.assertEqual(fungen._prints(fungen._eq_args(missing[0])[0]),
                         'Suc 0')

    def test_patterns_meeting_a_variable_cannot_be_told_apart(self):
        """A variable where the other pattern carries a constructor.

        `g x` agrees with every pattern of its type, so no branch can rule the
        other equation out -- which is what `_chain_separable` asks before it
        lets a filled set through: a set that cannot be emitted has to keep the
        definition as it is, because an emission that fails takes the whole
        definition back to axioms.
        """
        self.assertTrue(fungen._patterns_differ(
            Const('Suc', TFun(NatType, NatType))(Const('zero', NatType)),
            Const('zero', NatType)))
        self.assertFalse(fungen._patterns_differ(
            Var('n', NatType), Const('zero', NatType)))
        # Nested: `Suc 0` and `Suc (Suc n)` are told apart one level down.
        self.assertTrue(fungen._patterns_differ(
            Const('Suc', TFun(NatType, NatType))(Const('zero', NatType)),
            Const('Suc', TFun(NatType, NatType))(
                Const('Suc', TFun(NatType, NatType))(Var('n', NatType)))))
        self.assertFalse(fungen._patterns_differ(
            Const('Suc', TFun(NatType, NatType))(Var('n', NatType)),
            Const('Suc', TFun(NatType, NatType))(Var('m', NatType))))

    def test_coverage_walks_the_patterns(self):
        """The coverage proof splits the input along the *patterns*.

        It is Isabelle's `prove_completeness`
        (Function/pat_completeness.ML) which Function/induction_schema.ML
        reuses for its case split.  The step sequence below is the one the
        hand-written `wfx_exhaustive` in library/wfrec_example.pyhol
        carries, ID for ID: `type_cases` on the tuple, then on the one
        position whose patterns are not all variables, then into the
        constructor's argument; the branch that names `0` takes the first
        disjunct and the one under `Suc` the second, each instantiating its
        pattern's variables -- `m` from the split, `n` from the position
        that stayed a variable -- and closing on `eq_refl`.
        """
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type, r, eqs = self._plan('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        lines = fungen._coverage_entry('wfgen', arg_types, eqs, lhs)
        self.assertEqual(lines[0], 'theorem wfgen_exhaustive')
        self.assertEqual(lines[1], '  fixes p :: nat × nat')
        self.assertEqual(lines[2],
                         '  prop (∃n. p = Pair 0 n) ∨ (∃m. ∃n. p = Pair (Suc m) n)')
        self.assertEqual(lines[3:], [
            'proof',
            '  type_cases p goal=0',
            '  intro "a1, b1" goal=1',
            '  type_cases a1 goal=4',
            '  rule disjI1 goal=5',
            '  inst "b1" goal=7',
            '  rule eq_refl goal=8',
            '  intro "u1" goal=6',
            '  rule disjI2 goal=10',
            '  inst "u1" goal=11',
            '  inst "b1" goal=12',
            '  rule eq_refl goal=13',
            'qed'])

    def test_coverage_descends_into_nested_patterns(self):
        """A nested pattern splits again on the constructor's argument.

        `Suc (Suc n)` sits one constructor below `Suc`, so the branch that
        took `Suc` has to be split once more before a leaf can tell
        equation 2 (`Suc 0`) from equation 3.  The two `disjI2` steps of
        the third leaf are the chain to the last disjunct of a
        three-way `∨`.
        """
        ty = TFun(NatType, NatType)
        arg_types, res_type, r, eqs = self._plan('g3', ty, [
            'g3 0 = 0',
            'g3 (Suc 0) = 1',
            'g3 (Suc (Suc n)) = 2'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        lines = fungen._coverage_entry('g3', arg_types, eqs, lhs)
        self.assertEqual(lines[1], '  fixes p :: nat')
        self.assertEqual(
            lines[2],
            '  prop p = 0 ∨ p = Suc 0 ∨ (∃n. p = Suc (Suc n))')
        self.assertEqual(lines[3:], [
            'proof',
            '  type_cases p goal=0',
            '  rule disjI1 goal=1',
            '  rule eq_refl goal=3',
            '  intro "u1" goal=2',
            '  type_cases u1 goal=5',
            '  rule disjI2 goal=6',
            '  rule disjI1 goal=8',
            '  rule eq_refl goal=9',
            '  intro "u2" goal=7',
            '  rule disjI2 goal=11',
            '  rule disjI2 goal=12',
            '  inst "u2" goal=13',
            '  rule eq_refl goal=14',
            'qed'])

    def test_coverage_splits_a_nested_tuple(self):
        """A three-argument definition's tuple is split once per level.

        `p :: nat × (nat × nat)` is one `type_cases` and one `intro` to get
        the first component and a pair, then another to get the remaining
        two.  The position that carries the patterns is split after that,
        and the two positions that stay variables never are.
        """
        ty = TFun(NatType, TFun(NatType, TFun(NatType, NatType)))
        arg_types, res_type, r, eqs = self._plan('f3', ty, [
            'f3 0 n k = n',
            'f3 (Suc m) n k = f3 m n k'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        lines = fungen._coverage_entry('f3', arg_types, eqs, lhs)
        self.assertEqual(lines[1], '  fixes p :: nat × nat × nat')
        self.assertEqual(
            lines[2],
            '  prop (∃n. ∃k. p = Pair 0 (Pair n k))'
            ' ∨ (∃m. ∃n. ∃k. p = Pair (Suc m) (Pair n k))')
        self.assertEqual(lines[3:], [
            'proof',
            '  type_cases p goal=0',
            '  intro "a1, b1" goal=1',
            '  type_cases b1 goal=4',
            '  intro "a2, b2" goal=5',
            '  type_cases a1 goal=8',
            '  rule disjI1 goal=9',
            '  inst "a2" goal=11',
            '  inst "b2" goal=12',
            '  rule eq_refl goal=13',
            '  intro "u1" goal=10',
            '  rule disjI2 goal=15',
            '  inst "u1" goal=16',
            '  inst "a2" goal=17',
            '  inst "b2" goal=18',
            '  rule eq_refl goal=19',
            'qed'])

    def test_coverage_rejects_a_hole_in_the_patterns(self):
        """Inputs no equation matches have no branch to take.

        `g3` leaves `Suc 0` uncovered, so the leaf under `Suc 0` realises
        no equation and the disjunction cannot be closed there.  Saying so
        is the point: an induction rule whose branches do not cover its
        inputs proves nothing about them, and a `fun` whose equations do
        not cover its inputs is not a total function.
        """
        ty = TFun(NatType, NatType)
        arg_types, res_type, r, eqs = self._plan('g3', ty, [
            'g3 0 = 0',
            'g3 (Suc (Suc n)) = 2'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        with self.assertRaises(fungen.FunGenError):
            fungen._coverage_entry('g3', arg_types, eqs, lhs)

    def test_disjunct_chain(self):
        """The introductions that walk to one disjunct of a right-nested `|`.

        Every disjunct before the last is `disjI2` once per level it is
        nested under and `disjI1` on itself; the last one is `disjI2` all
        the way down and has no `disjI1`.  Emitting one there asks the
        goal to split a disjunct that is already the whole goal, which is
        how the first version of the multi-recursive-argument support
        failed on the last disjunct of the `Plus` relation.
        """
        self.assertEqual(fungen._disjunct_chain(4, 0), ['rule disjI1'])
        self.assertEqual(fungen._disjunct_chain(4, 1),
                         ['rule disjI2', 'rule disjI1'])
        self.assertEqual(fungen._disjunct_chain(4, 2),
                         ['rule disjI2', 'rule disjI2', 'rule disjI1'])
        self.assertEqual(fungen._disjunct_chain(4, 3),
                         ['rule disjI2', 'rule disjI2', 'rule disjI2'])
        # One disjunct is no disjunction at all: the goal is already the
        # disjunct, so there is nothing to introduce (and a datatype with
        # a single recursive argument never reaches this path).
        self.assertEqual(fungen._disjunct_chain(1, 0), [])

    def test_cases_entry_reads_the_coverage_backwards(self):
        """The case rule is the coverage theorem's content, consumed.

        `<c>_exhaustive` says the input is some instance of a pattern;
        `<c>_cases` is that disjunction read as a rule -- one premise per
        equation, applied at the very variables `elim` takes off the
        disjunct.  It is the shape a datatype's `<ty>_cases` has
        (`defcheck.datatype_axioms`), so `type_cases` with `cases_thm`
        naming it consumes it the same way: the predicate is instantiated
        with the goal and the case variable with the expression to split.

        The step sequence below is the one the emitted `wfgen_cases`
        carries, ID for ID: `intro` lays the premises out at IDs 1..ng
        with the goal after them, `forward` brings the disjunction in, and
        a branch eliminates its disjunct's witnesses and instantiates its
        own premise at exactly those variables -- the `inst` that closes
        `_induct_entry`'s branches, without the induction hypotheses and
        the decrease obligations.
        """
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type, r, eqs = self._plan('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        lines = fungen._cases_entry('wfgen', arg_types, eqs, lhs)
        self.assertEqual(lines[0:3], [
            'theorem wfgen_cases',
            '  fixes P :: nat × nat ⇒ bool, p :: nat × nat',
            '  prop (∀n. P (Pair 0 n)) ⟶ (∀m. ∀n. P (Pair (Suc m) n))'
            ' ⟶ P p'])
        self.assertEqual(lines[3:], [
            'proof',
            '  ← intro goal=0',
            '  → forward wfgen_exhaustive param_p=p goal=3',
            '  ← rule disjE goal=3 facts=[4]',
            '  ← intro goal=5',
            '  elim n1 goal=8 facts=[7]',
            '  ← inst "n1" goal=11 facts=[1]',
            '  ← rewrite source=prev goal=11 facts=[10]',
            '  ← intro goal=6',
            '  elim m1 goal=14 facts=[13]',
            '  elim n2 goal=17 facts=[16]',
            '  ← inst "m1" goal=20 facts=[2]',
            '  ← inst "n2" goal=20 facts=[21]',
            '  ← rewrite source=prev goal=20 facts=[19]',
            'qed'])

    def test_the_case_rule_yields_to_a_written_one(self):
        """A file that states `<c>_cases` itself keeps its own.

        The generator asks the same question the loader will: the name is
        taken, so the emitted rule would be a second item of that name and
        the file's own is the one the rest of the file was written
        against.  Each rule is yielded on its own name, so a file that
        writes only the case rule keeps the coverage and induction rules.
        """
        rules = [{'prop': 'wfgen 0 n = n'},
                 {'prop': 'wfgen (Suc m) n = Suc (wfgen m n)'}]
        data = {'ty': 'def.ind', 'name': 'wfgen',
                'type': 'nat ⇒ nat ⇒ nat', 'rules': rules}
        names = [item['name'] for item in fungen._expand(dict(data))]
        self.assertIn('wfgen_cases', names)
        self.assertIn('wfgen_exhaustive', names)
        self.assertIn('wfgen_induct', names)
        names = [item['name'] for item in
                 fungen._expand(dict(data), declared={'wfgen_cases'})]
        self.assertNotIn('wfgen_cases', names)
        self.assertIn('wfgen_exhaustive', names)

    def test_the_case_rule_avoids_the_patterns_own_names(self):
        """The predicate and the case variable miss the equations' names.

        Both are free in the statement, so a pattern variable of the same
        name would shadow them inside its premise; and the names the
        proof's `elim`s are handed are those variables with a count
        appended, so one of *those* may be the name the predicate took
        (`filter` binds its predicate as `P`, and the first elimination
        there would want `P1`).  A definition whose pattern binds `P`
        therefore gets `P1` for the predicate and `P2` for the
        elimination.
        """
        arg_types, res_type, r, eqs = self._plan(
            'g', TFun(NatType, NatType), ['g 0 = 0', 'g (Suc P) = P'])
        lhs = [fungen._eq_args(eq) for eq in eqs]
        lines = fungen._cases_entry('g', arg_types, eqs, lhs)
        self.assertEqual(lines[1], '  fixes P1 :: nat ⇒ bool, p :: nat')
        self.assertEqual(lines[2], '  prop P1 0 ⟶ (∀P. P1 (Suc P)) ⟶ P1 p')
        self.assertIn('  elim P2 goal=', '\n'.join(lines))

    def test_clause_decides_the_structural_check(self):
        """A relation or a measure replaces the structural check.

        The check is what makes the equations safe *as axioms*; a
        definition that carries a relation or a measure derives them from
        a termination proof instead, so the check is the wrong question --
        and a definition the check refuses (`f n` is not a direct argument
        of the pattern) is accepted once the clause says what it descends
        through.
        """
        from core import items
        rules = [{'prop': 'f 0 = 0'}, {'prop': 'f (Suc (Suc n)) = f n'}]
        data = {'ty': 'def.ind', 'name': 'f', 'type': "nat ⇒ nat",
                'rules': rules}
        self.assertIsNotNone(items.parse_item(dict(data)).error,
                             'the structural check accepted a deep call')
        for clause in ({'measure': ['"%p. p"']},
                       {'relation': ['"%p q. p < q"'],
                        'wf': ['"w"'], 'descent': ['"d"']}):
            item = items.parse_item(dict(data, **clause))
            self.assertIsNone(item.error, 'a clause did not carry it: %s'
                              % item.error)
            self.assertIsNotNone(item.measures or item.relation)

    def test_a_size_with_its_parameters_filled_in(self):
        """The candidate measures a container's type admits.

        A size takes one measure per type parameter, so the measure of a
        `nat list` is `list_size id` and of an `'a list` is
        `list_size zero_measure` -- the search builds them by itself, out
        of the sizes its argument types' datatypes have.  A datatype with
        no parameter (the `tri` of measure_example) keeps the plain size,
        which is why nothing about the existing measures changes.
        """
        basic.load_theory('list')
        list_of_nat = TConst('list', NatType)
        list_of_var = TConst('list', TVar('a'))
        _, measures = fungen._measure_registry(
            'f', [list_of_nat, list_of_var], ('f', 'f'))
        self.assertEqual(len(measures), 2)
        self.assertEqual([m.kind for m in measures], ['size', 'size'])
        self.assertEqual([m.size_name for m in measures],
                         ['list_size', 'list_size'])
        self.assertEqual([m.def_name for m in measures], ['f_m1', 'f_m2'])
        self.assertEqual([t.name for m in measures for t in m.mterms],
                         ['id', 'zero_measure'])
        # The family the cells unfold the size with: one measure argument,
        # and the constructor's own summands.
        sizes, _ = fungen._measure_registry(
            'f', [list_of_nat], ('f', 'f'))
        arity, table = sizes['list_size']
        self.assertEqual(arity, 1)
        self.assertEqual(table['nil'][1], [])
        self.assertEqual(table['cons'][1], [('param', 0, 0), ('rec', 1)])

    def test_a_position_nothing_measures_contributes_no_column(self):
        """An argument whose type has no size at all is left out.

        A function type has no measure, and neither does an `'a` that no
        container wraps: the search then has no column for that position,
        and `infer` reports no order rather than an unsound one.
        """
        func_T = TFun(NatType, NatType)
        _, measures = fungen._measure_registry(
            'f', [NatType, func_T], ('f', 'f'))
        self.assertEqual([m.pos for m in measures], [0])
        self.assertEqual(measures[0].kind, 'nat')


def printer_type(ty):
    from syntax import printer
    with __import__('syntax.settings', fromlist=['x']).global_setting(
            unicode=True):
        return printer.print_type(ty)


if __name__ == '__main__':
    unittest.main()

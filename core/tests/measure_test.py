"""Unit tests for the recursion-relation inference (core/measure.py).

The properties asserted here are the ones the emitter consumes: what a
call does at a measure (the cell's proposition, the rewrite steps that
normalize it, and the last steps that close it), and which order of
columns the search ends up with.  The measures are written the way the
emitter writes them -- as named constants, whose defining equation is the
cell's first step.

The size measure and the whole emitted proof are covered end to end by
`library/measure_example.pyhol` (a datatype of the file's own, so a size
function exists) and by library/tests/fungen_test.py.
"""

import unittest

from kernel.term import Const, Var
from kernel.type import TFun, TConst
from core import basic
from core import fungen
from core import measure

NatType = TConst('nat')


class MeasureTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('nat')
        self.arg_types = [NatType, NatType]
        self.dmap = fungen._destructor_maps(self.arg_types, 0)

    def _named(self, pos, name='m1'):
        """A measure at `pos`, named the way the emitter names one."""
        m = measure.Measure(pos, self.arg_types, 'nat', def_name=name)
        self.assertTrue(m.is_named())
        return m, m.tables()

    def _cell(self, pos, call, lhs):
        m, mdefs = self._named(pos)
        return measure.cell(m, call, lhs, self.dmap, {}, mdefs)

    def _pair(self, a, b):
        return fungen.tupled_arg([a, b])

    def test_one_measure_suffices(self):
        # A call on the predecessor of the first argument: the measure is
        # that argument, and the cell is one `Suc` apart.
        m_var, n_var = Var('m', NatType), Var('n', NatType)
        suc = Const('Suc', TFun(NatType, NatType))
        c = self._cell(0, self._pair(m_var, n_var),
                       self._pair(suc(m_var), n_var))
        self.assertEqual(c.kind, 'lt')
        # The cell is stated with the measure applied and not reduced:
        # that is the proposition `mlex_less` matches as its premise (the
        # matcher is first-order and does not reduce a redex).
        self.assertEqual(c.prop, '(m1) (Pair m n) < (m1) (Pair (Suc m) n)')
        # The measure's defining equation first, then the projection, then
        # the comparison itself.
        self.assertEqual(c.steps,
                         ['m1_def', 'fst_def_1', 'less_Suc_lesseq'])
        self.assertEqual(c.closing.kind, 'rule')
        self.assertEqual(c.closing.theorem, 'lesseq_refl')
        self.assertFalse(c.beta)

    def test_equal_measure_is_not_increasing(self):
        # The call keeps the measured argument: the cell is the weak one,
        # and `lesseq_refl` closes it after the projections are reduced.
        m_var, n_var = Var('m', NatType), Var('n', NatType)
        c = self._cell(0, self._pair(m_var, n_var), self._pair(m_var, n_var))
        self.assertEqual(c.kind, 'le')
        self.assertEqual(c.steps, ['m1_def', 'fst_def_1'])
        self.assertEqual(c.closing.theorem, 'lesseq_refl')

    def test_extra_suc_on_the_right_is_absorbed(self):
        # A call two constructors down (the cell is `n <= Suc n` after the
        # peel): the surplus `Suc` comes off through `le_suc_right`, whose
        # sub-comparison is the reflexive one.
        n_var = Var('n', NatType)
        suc = Const('Suc', TFun(NatType, NatType))
        call = fungen.tupled_arg([n_var])
        lhs = fungen.tupled_arg([suc(suc(n_var))])
        m = measure.Measure(0, [NatType], 'nat', def_name='dbl_m1')
        c = measure.cell(m, call, lhs, fungen._destructor_maps([NatType], 0),
                         {}, m.tables())
        self.assertEqual(c.kind, 'lt')
        self.assertEqual(c.steps, ['dbl_m1_def', 'less_Suc_lesseq'])
        self.assertEqual(c.closing.kind, 'cut')
        self.assertEqual(c.closing.theorem, 'le_suc_right')
        # The sub-comparison is what is left once the `Suc` is off.
        self.assertEqual(c.closing.prop, 'n <= n')
        self.assertEqual(c.closing.sub.theorem, 'lesseq_refl')

    def test_atom_added_on_the_left(self):
        # A sum on the right that does not start with the left side's atom:
        # `le_add_left_mono` adds it, and the sub-comparison is proved
        # first.
        a_var, b_var = Var('a', NatType), Var('b', NatType)
        plus = Const('plus', TFun(NatType, NatType, NatType))
        c = self._cell(0, self._pair(a_var, b_var),
                       self._pair(plus(b_var, a_var), a_var))
        self.assertEqual(c.kind, 'le')
        self.assertEqual(c.closing.kind, 'cut')
        self.assertEqual(c.closing.theorem, 'le_add_left_mono')
        # The atom the left side does not start with (`b`) is dropped
        # from the right end, and what is left is the reflexive one.
        self.assertEqual(c.closing.prop, 'a <= a')
        self.assertEqual(c.closing.sub.theorem, 'lesseq_refl')

    def test_no_order_reported(self):
        # `f (Suc m) n = f (n + 1) m` descends nowhere: neither measure can
        # be shown not to increase, so the search reports nothing and the
        # caller keeps the subterm relation.
        measures = [measure.Measure(pos, self.arg_types, 'nat')
                    for pos in range(2)]
        plus = Const('plus', TFun(NatType, NatType, NatType))
        suc = Const('Suc', TFun(NatType, NatType))
        call = self._pair(plus(Var('n', NatType), Const('one', NatType)),
                          Var('m', NatType))
        lhs = self._pair(suc(Var('m', NatType)), Var('n', NatType))
        self.assertIsNone(measure.infer(measures, [(call, lhs)], self.dmap))

    def test_the_second_measure_carries_the_first_one_s_leftovers(self):
        # The order is the pair: the first column is strictly decreasing
        # for the call on the first argument, and the call that keeps it
        # (only `<=` there) is left to the second column.
        m1 = measure.Measure(0, self.arg_types, 'nat', def_name='c_m1')
        m2 = measure.Measure(1, self.arg_types, 'nat', def_name='c_m2')
        mdefs = dict(m1.tables(), **m2.tables())
        m_var, n_var = Var('m', NatType), Var('n', NatType)
        suc = Const('Suc', TFun(NatType, NatType))
        calls = [(self._pair(m_var, n_var), self._pair(suc(m_var), n_var)),
                 (self._pair(m_var, n_var), self._pair(m_var, suc(n_var)))]
        order = measure.infer([m1, m2], calls, self.dmap, {}, mdefs)
        self.assertEqual(order, [m1, m2])
        # The second call walks the first column (weak) and stops at the
        # second, which is strict.
        walk = measure.row(order, calls[1][0], calls[1][1], self.dmap, {},
                           mdefs)
        self.assertEqual([c.kind for _, c in walk], ['le', 'lt'])
        self.assertEqual(walk[0][1].steps, ['c_m1_def', 'fst_def_1'])


if __name__ == '__main__':
    unittest.main()

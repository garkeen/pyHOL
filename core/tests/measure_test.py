"""Unit tests for the recursion-relation inference (core/measure.py).

The properties asserted here are the inference's, not the library's: which
measures a definition's argument types admit, what a call does at each of
them, and which order of columns the search ends up with.  The samples are
written for the test -- a definition that needs one measure, one that needs
two (the second only for the calls the first leaves untouched), one that
has no order at all, and one whose measure is a datatype's size.
"""

import unittest

from kernel.term import Const, Var
from kernel.type import TFun, TConst, TVar
from core import basic
from core import context
from core import fungen
from core import measure

NatType = TConst('nat')


def nat_size_map(xs):
    """The size equations of `list`, as the inference wants them."""
    return {'list_size': {'nil': ('list_size_def_1', []),
                          'cons': ('list_size_def_2', [xs])}}


class MeasureTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('list')

    def _plan(self, name, ty, props):
        """(arg_types, r, eqs, calls, dmap) for the given equations."""
        with context.fresh_context(defs={name: ty}):
            eqs = [context.parse_term(prop) for prop in props]
        arity = len(fungen._eq_args(eqs[0]))
        arg_types, res_type = fungen._strip_type(ty, arity)
        lhs = [fungen._eq_args(eq) for eq in eqs]
        r = fungen.recursion_position(arg_types, lhs)
        f_const = Const(name, TFun(*(list(arg_types) + [res_type])))
        calls = []
        for eq in eqs:
            for c in fungen._calls(eq.rhs, f_const, arity):
                calls.append((fungen.tupled_arg(c), fungen._tuple_of(eq)))
        return arg_types, r, eqs, calls, fungen._destructor_maps(arg_types, r)

    def _infer(self, name, ty, props, size_of=lambda T: None, sizes=None):
        arg_types, r, eqs, calls, dmap = self._plan(name, ty, props)
        ms = measure.candidate_measures(arg_types, size_of)
        return measure.infer(ms, calls, dmap, sizes), (arg_types, calls, dmap, ms)

    def test_one_measure_suffices(self):
        """Two natural-number arguments, recursion on the first.

        The second position gives a column too (`n <= n`), but a column
        needs a strict cell somewhere and that one has none, so the search
        keeps the first.
        """
        ty = TFun(NatType, TFun(NatType, NatType))
        order, (arg_types, calls, dmap, ms) = self._infer('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        self.assertEqual(len(ms), 2)
        self.assertEqual([m.pos for m in order], [0])
        cells = [measure.cell(m, call, lhs, dmap) for m in order
                 for call, lhs in calls]
        self.assertEqual([c.kind for c in cells], ['lt'])
        # The cell is stated with the projections still unreduced:
        # that is the shape the goal's condition has, and the
        # projections are opened inside the cell's own proof.
        self.assertEqual(cells[0].prop,
                         'fst (Pair m n) < fst (Pair (Suc m) n)')
        self.assertEqual(cells[0].steps,
                         ['fst_def_1', 'less_Suc_lesseq', 'lesseq_refl'])

    def test_lexicographic_order_needs_two(self):
        """No single measure covers both calls, so the chain has two.

        The first call moves to a bigger first argument (no measure can
        take it as non-increasing there) while the second argument grows
        too; the second call keeps the first argument and decreases the
        second.  The second column alone cannot take the first call, so
        the first column has to come first and the rest is left to the
        second -- which is the chain `m_1 <*mlex*> m_2`.
        """
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type = fungen._strip_type(ty, 2)
        m, n = Var('m', NatType), Var('n', NatType)
        suc = Const('Suc', TFun(NatType, NatType))
        # The two rows a definition with a call of each shape produces.
        rows = [(fungen.tupled_arg([m, suc(n)]),
                 fungen.tupled_arg([suc(m), n])),
                (fungen.tupled_arg([suc(m), n]),
                 fungen.tupled_arg([suc(m), suc(n)]))]
        dmap = fungen._destructor_maps(arg_types, 0)
        ms = measure.candidate_measures(arg_types, lambda T: None)
        self.assertEqual(sorted(m.pos for m in ms), [0, 1])
        order = measure.infer(ms, rows, dmap)
        self.assertEqual([m.pos for m in order], [0, 1])
        first = [measure.cell(m, rows[0][0], rows[0][1], dmap) for m in order]
        second = [measure.cell(m, rows[1][0], rows[1][1], dmap) for m in order]
        self.assertEqual([c.kind if c else None for c in first], ['lt', None])
        self.assertEqual([c.kind if c else None for c in second], ['le', 'lt'])

    def test_no_order_is_reported_as_such(self):
        """A call that grows its own argument has no measure to offer."""
        ty = TFun(NatType, NatType)
        order, _ = self._infer('grow', ty, [
            'grow 0 = 0',
            'grow (Suc m) = grow (Suc (Suc m))'])
        self.assertIsNone(order)

    def test_datatype_size_is_a_measure(self):
        """A list argument is measured by its generated size."""
        ta, tb = TVar('a'), TVar('b')
        ty = TFun(TFun(ta, tb), TFun(TConst('list', ta), TConst('list', tb)))
        with context.fresh_context(defs={'wfmap': ty}):
            eqs = [context.parse_term(p) for p in [
                'wfmap f [] = []',
                'wfmap f (x # xs) = f x # wfmap f xs']]
        arg_types, res_type = fungen._strip_type(ty, 2)
        lhs = [fungen._eq_args(eq) for eq in eqs]
        r = fungen.recursion_position(arg_types, lhs)
        dmap = fungen._destructor_maps(arg_types, r)
        f_const = Const('wfmap', ty)
        calls = [(fungen.tupled_arg(c), fungen._tuple_of(eq))
                 for eq in eqs for c in fungen._calls(eq.rhs, f_const, 2)]
        xs = fungen._pattern_vars(eqs[1], r)[1]
        sizes = nat_size_map(fungen.Var(xs, TConst('list', ta)))

        def size_of(T):
            return 'list_size' if (T.is_tconst() and T.name == 'list') else None

        ms = measure.candidate_measures(arg_types, size_of)
        # The function argument has no measure; the list position has one.
        self.assertEqual([m.pos for m in ms], [1])
        order = measure.infer(ms, calls, dmap, sizes)
        self.assertEqual([m.pos for m in order], [1])
        c = measure.cell(order[0], calls[0][0], calls[0][1], dmap, sizes)
        self.assertEqual(c.kind, 'lt')
        self.assertEqual(c.prop, 'list_size (snd (Pair f xs))'
                         ' < list_size (snd (Pair f (x # xs)))')
        # Both sides are reduced for the comparison: `tl` by its rule, the
        # size by its equation, `1 + _` by `add_1_left`.
        self.assertEqual(c.steps, ['snd_def_1', 'list_size_def_2',
                                   'add_1_left', 'less_Suc_lesseq',
                                   'lesseq_refl'])


if __name__ == '__main__':
    unittest.main()

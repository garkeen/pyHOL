"""Unit test for the fun expansion's transformation layer.

The emitted *proofs* are not asserted here: they are produced by asking
the method layer what each step does (core.verify.probe_steps), which
core is not allowed to depend on.  Their end-to-end effect -- every
`fun` equation derived, none left as an axiom -- is checked by
library/tests/fungen_test.py, and by the library validation itself.
"""

import unittest

from kernel.term import Const
from kernel.type import TFun, TConst, TVar
from core import basic
from core import context
from core import fungen

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
        # existential over their tuple.
        self.assertEqual(
            fungen._prints(fungen.branch_condition(fungen._eq_args(eqs[0]), 0,
                                                   fungen.Var('p', NatType))),
            'p = 0')
        self.assertEqual(
            fungen._prints(fungen.branch_condition(fungen._eq_args(eqs[1]), 0,
                                                   fungen.Var('p', NatType))),
            'p = Suc 0')
        self.assertEqual(
            fungen._prints(fungen.branch_condition(fungen._eq_args(eqs[2]), 0,
                                                   fungen.Var('p', NatType))),
            '∃_w. p = Suc (Suc _w)')
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


def printer_type(ty):
    from syntax import printer
    with __import__('syntax.settings', fromlist=['x']).global_setting(
            unicode=True):
        return printer.print_type(ty)


if __name__ == '__main__':
    unittest.main()

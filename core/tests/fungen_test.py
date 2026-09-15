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
            ' ?z::\'a. snd q = z # snd p')

    def test_decrease_reduction(self):
        """The projection/destructor rules the emitted propositions need."""
        ty = TFun(NatType, TFun(NatType, NatType))
        arg_types, res_type, r, eqs = self._plan('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        body = fungen._body_term('wfgen', arg_types, res_type, eqs, r,
                                 fungen._tuple_of(eqs[1]))
        red, rules = fungen._reduce_used(body)
        # Pre (Suc m) reduces to m, so Pre's second rule is needed; the
        # projections in the condition and in the recursive call's tuple
        # are computed away with fst/snd.
        self.assertEqual(rules, ['fst_def_1', 'snd_def_1', 'Pre_def_2'])
        self.assertEqual(fungen._prints(red),
                         'if Suc m = 0 then n else Suc (g (Pair m n))')

    def test_rejects_unsupported_shapes(self):
        """Shapes outside the increment raise instead of being guessed."""
        ty3 = TFun(NatType, TFun(NatType, TFun(NatType, NatType)))
        with self.assertRaises(fungen.FunGenError):
            fungen._expand({'name': 'f', 'type': printer_type(ty3),
                            'rules': [{'prop': 'f 0 n k = n'}]})
        ty = TFun(NatType, NatType)
        with self.assertRaises(fungen.FunGenError):
            fungen._expand({'name': 'g', 'type': printer_type(ty),
                            'rules': [{'prop': 'g (Suc n) = Suc n'}]})

    def test_rejects_unwritable_items(self):
        """What the emitted text cannot carry is not emitted at all.

        The loader drops an item it cannot parse, so a group whose text
        does not type -- an equation with no variable to carry the
        item's type variables, or a type the printer writes in a way the
        parser reads back differently -- must keep the axioms instead of
        being emitted.
        """
        basic.load_theory('list')
        ta, tb = TVar('a'), TVar('b')
        ty = TFun(TConst('list', ta), TConst('list', ta))
        with self.assertRaises(fungen.FunGenError):
            fungen._expand({'name': 'g2', 'type': printer_type(ty),
                            'rules': [{'prop': 'g2 [] = []'},
                                      {'prop': 'g2 (x # xs) = g2 xs'}]})
        # `('a × 'b) list` prints as `'a × 'b list`, i.e. `'a × ('b list)`.
        with self.assertRaises(fungen.FunGenError):
            fungen._printt(TConst('list', TConst('prod', ta, tb)))


def printer_type(ty):
    from syntax import printer
    with __import__('syntax.settings', fromlist=['x']).global_setting(
            unicode=True):
        return printer.print_type(ty)


if __name__ == '__main__':
    unittest.main()

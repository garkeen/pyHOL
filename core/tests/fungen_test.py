"""Unit test for the fun expansion's transformation layer."""

import unittest

from kernel.type import TFun, TConst, TVar
from core import basic
from core import context
from core import fungen

NatType = TConst('nat')


class FunGenTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('nat')
        basic.load_theory('list')

    def _eqs(self, name, ty, props):
        with context.fresh_context(defs={name: ty}):
            return [context.parse_term(prop) for prop in props]

    def testNatStructural(self):
        # fun wfgen :: nat => nat => nat
        #   | wfgen 0 n = n
        #   | wfgen (Suc m) n = Suc (wfgen m n)
        ty = TFun(NatType, TFun(NatType, NatType))
        eqs = self._eqs('wfgen', ty, [
            'wfgen 0 n = n',
            'wfgen (Suc m) n = Suc (wfgen m n)'])
        h_prop, measure = fungen.expand_body(
            'wfgen', [NatType, NatType], NatType, eqs)
        # p = (x, n): the recursion position is projected as fst p, the
        # pattern variable m becomes Pre (fst p), and the recursive call
        # receives the tuple (Pre (fst p), snd p).
        self.assertEqual(
            h_prop,
            'wfgen_H g p = if fst p = 0 then snd p'
            ' else Suc (g (Pair (Pre (fst p)) (snd p)))')
        self.assertEqual(measure, 'wfgen_measure p = fst p')

    def testListStructural(self):
        # fun wfmap :: ('a => 'b) => 'a list => 'b list
        #   | wfmap f [] = []
        #   | wfmap f (x # xs) = f x # wfmap f xs
        ta, tb = TVar('a'), TVar('b')
        ty = TFun(TFun(ta, tb), TFun(TConst('list', ta), TConst('list', tb)))
        eqs = self._eqs('wfmap', ty, [
            'wfmap f [] = []',
            'wfmap f (x # xs) = f x # wfmap f xs'])
        h_prop, measure = fungen.expand_body(
            'wfmap', [TFun(ta, tb), TConst('list', ta)], TConst('list', tb),
            eqs)
        # p = (f, xs): the list is snd p, the pattern variables are
        # x = hd (snd p) and xs = tl (snd p).
        self.assertEqual(
            h_prop,
            'wfmap_H g p = if snd p = [] then []'
            ' else fst p (hd (snd p)) # g (Pair (fst p) (tl (snd p)))')
        self.assertEqual(measure, 'wfmap_measure p = length (snd p)')


if __name__ == '__main__':
    unittest.main()

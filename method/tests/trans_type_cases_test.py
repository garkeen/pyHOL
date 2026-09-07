"""Unit tests for the trans method (TRANS_TAC) and the type_cases
method (datatype case analysis via generated <tyname>_cases theorems).
"""

import unittest

from kernel import theory
from kernel.proofterm import TacticException
from core import context
from method.stable_state import StableProofState

from method.tests.method_test import test_method


class TransMethodTest(unittest.TestCase):
    def testTransNat(self):
        test_method(self, 'nat', vars={'A': 'nat'},
                    concl='A + 0 = 0 + A',
                    method_name='trans', args={'s': 'A'},
                    gaps=['A + 0 = A', 'A = 0 + A'])

    def testTransReal(self):
        # Neither side is reflexive; the reflexive side of a trans
        # step would be skipped and a trivial side auto-closed.
        test_method(self, 'real', vars={'x': 'real', 'y': 'real'},
                    concl='x + y = y + x',
                    method_name='trans', args={'s': 'x + y + 0'},
                    gaps=['x + y = x + y + 0', 'x + y + 0 = y + x'])

    def testTransNotEquality(self):
        test_method(self, 'logic', vars={'A': 'bool'},
                    concl='A & A',
                    method_name='trans', args={'s': 'A'},
                    failed=TacticException)

    def testTransMissingParam(self):
        # Without the middle term the method fails (the frontend asks
        # for it via the sig before sending).
        test_method(self, 'nat', vars={'A': 'nat'},
                    concl='A + 0 = 0 + A',
                    method_name='trans',
                    failed=KeyError)


class TypeCasesMethodTest(unittest.TestCase):
    def testNatCasesTheorem(self):
        context.set_context('nat')
        th = theory.get_theorem('nat_cases')
        self.assertEqual(
            str(th.prop),
            '?P 0 --> (!n. ?P (Suc n)) --> ?P ?x')

    def testListCasesTheorem(self):
        context.set_context('list')
        th = theory.get_theorem('list_cases')
        self.assertEqual(
            str(th.prop),
            '?P [] --> (!x. !xs. ?P (x # xs)) --> ?P ?x')

    def testTypeCasesNat(self):
        test_method(self, 'nat', vars={'n': 'nat'},
                    concl='n = zero | (?m. n = Suc m)',
                    method_name='type_cases', args={'case': 'n'},
                    gaps=['(0::nat) = 0 | (?m. 0 = Suc m)',
                          '!n. Suc n = 0 | (?m. Suc n = Suc m)'])

    def testTypeCasesList(self):
        test_method(self, 'list', vars={'xs': 'nat list'},
                    concl='xs = nil | (?x. (?xs2. xs = cons x xs2))',
                    method_name='type_cases', args={'case': 'xs'},
                    gaps=['([]::nat list) = [] | (?x. (?xs2. ([]::nat list) = cons x xs2))',
                          '!x. !xs. cons x xs = ([]::nat list) | (?x2. (?xs2. cons x xs = cons x2 xs2))'])

    def testTypeCasesNotDatatype(self):
        # Suc has function type: not a type constructor application.
        test_method(self, 'nat', vars={'n': 'nat'},
                    concl='n = zero | (?m. n = Suc m)',
                    method_name='type_cases', args={'case': 'Suc'},
                    failed=AssertionError)

    def testFullProofNatCases(self):
        """Prove |- !n. n = zero | (?m. n = Suc m) end to end via the
        stable-ID pipeline, then kernel-check the result."""
        context.set_context('nat', vars={'n': 'nat'})
        sps = StableProofState.create('!n. n = zero | (?m. n = Suc m)', {'n': 'nat'})
        steps = [
            {'method_name': 'intro', 'goal': 0, 'names': 'n'},
            {'method_name': 'type_cases', 'case': 'n'},
        ]
        for step in steps:
            self.assertTrue(sps.apply_method_dict(step), step)

        def first_goal():
            lines = sps.json_data()['proof']
            return [l for l in lines if l['is_goal']][0]['sid']

        # Zero branch
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'rule', 'theorem': 'disjI1', 'goal': first_goal()}))
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'refl', 'goal': first_goal()}))
        # Suc branch
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'intro', 'goal': first_goal(), 'names': 'n1'}))
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'rule', 'theorem': 'disjI2', 'goal': first_goal()}))
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'inst', 'goal': first_goal(), 's': 'n1'}))
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'refl', 'goal': first_goal()}))
        self.assertEqual(sps.num_gaps, 0)
        th = sps.check_proof(no_gaps=True)
        self.assertEqual(str(th.prop), '!n. n = 0 | (?m. n = Suc m)')


if __name__ == "__main__":
    unittest.main()

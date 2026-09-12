# theories/nat/tests/macro_test.py - test_macro cases for the nat macros.
#
# The nat macros were previously only exercised indirectly (library
# replay, interval/function convs).  With the adapter refactor
# (ARCHITECTURE_AUDIT.md §7.3, second half: proof logic moved to
# module-level *_proof functions, macro classes are thin adapters) the
# eval / get_proof_term / verify chain of each macro gets direct
# test_macro coverage here, per AGENTS.md ("宏用 test_macro").

import unittest

from theories.logic.tests.logic_test import test_macro
from core.method import has_method


class NatMacroTest(unittest.TestCase):
    def testNatNorm(self):
        test_macro(self, 'nat', 'nat_norm', args='(2::nat) + 3 = 5',
                   res='(2::nat) + 3 = 5')
        # Unequal sides: normalization assertion must fail.
        test_macro(self, 'nat', 'nat_norm', args='(2::nat) + 3 = 6',
                   res='(2::nat) + 3 = 6', failed=AssertionError)

    def testNatConstIneq(self):
        test_macro(self, 'nat', 'nat_const_ineq', args='~((2::nat) = 3)',
                   res='~((2::nat) = 3)')
        # m = n: out of scope, must fail.
        test_macro(self, 'nat', 'nat_const_ineq', args='~((2::nat) = 2)',
                   res='~((2::nat) = 2)', failed=AssertionError)

    def testNatConstLessEq(self):
        test_macro(self, 'nat', 'nat_const_less_eq', args='(2::nat) <= 5',
                   res='(2::nat) <= 5')
        # m > n: out of scope, must fail.
        test_macro(self, 'nat', 'nat_const_less_eq', args='(5::nat) <= 2',
                   res='(5::nat) <= 2', failed=AssertionError)

    def testNatConstLess(self):
        test_macro(self, 'nat', 'nat_const_less', args='(2::nat) < 5',
                   res='(2::nat) < 5')
        # m > n: out of scope, must fail.
        test_macro(self, 'nat', 'nat_const_less', args='(5::nat) < 2',
                   res='(5::nat) < 2', failed=AssertionError)

    def testNatConstComparisonsAsMethods(self):
        """The two constant-comparison macros are also exposed as
        interactive methods (theories/nat/method.py), so a .pyhol step
        can close a constant nat comparison in one line.  Before that
        registration they were reachable only as macros.
        """
        # test_macro loads the nat theory, which registers the domain
        # methods as a side effect of importing theories/nat/method.py.
        test_macro(self, 'nat', 'nat_const_less', args='(2::nat) < 5',
                   res='(2::nat) < 5')
        self.assertTrue(has_method('nat_const_less'))
        self.assertTrue(has_method('nat_const_less_eq'))


if __name__ == "__main__":
    unittest.main()
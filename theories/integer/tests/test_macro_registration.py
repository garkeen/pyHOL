# Author: Bohua Zhan
# Step 1b regression test (ARCHITECTURE_AUDIT.md §8 step 1):
#
#   The integer macros moved from conv.py to macro.py. Registration is
#   by decorator at import time -- this test guards against the move
#   dropping a registration, and against conv.py re-growing macros.

import unittest

from kernel.theory import global_macros


INTEGER_MACROS = [
    'int_norm',
    'int_eval',
    'int_eq_macro',
    'int_ineq',
    'int_ineq_mul_const',
    'int_const_ineq',
    'int_multiple_ineq_equiv',
    'omega_norm_int_ineq',
    'int_eq_comparison',
]


class IntegerMacroRegistrationTest(unittest.TestCase):
    def testAllRegistered(self):
        import theories.integer  # noqa: F401  (triggers registration)
        missing = [name for name in INTEGER_MACROS if name not in global_macros]
        self.assertEqual(missing, [])

    def testConvHasNoMacros(self):
        """conv.py must not define Macro subclasses (audit iron law:
        conv 不得出现宏名)."""
        import theories.integer.conv as integer_conv
        from kernel.macro import Macro
        for name in dir(integer_conv):
            obj = getattr(integer_conv, name)
            if isinstance(obj, type) and issubclass(obj, Macro):
                self.fail("conv.py defines macro class: %s" % name)


if __name__ == "__main__":
    unittest.main()

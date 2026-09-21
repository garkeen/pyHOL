# End-to-end validation of imperative-compiled VC theories.
#
# Cross-layer by nature: .imp -> compile -> VC .pyhol -> validate_theory
# (which replays through the method-layer steps->lines translation).
# The method import below is the assembly step, not a layer dependency:
# core/verify takes its replay function from an injection point
# (set_replay_fn), and method.stable_state is what registers it.  Tests
# are consumers and are exempt from the import-direction lints (see
# core/tests/test_import_direction.py), so this file lives next to the
# compiler it drives.

import unittest

from core import basic
import method.stable_state  # noqa: F401  -- wires the replay pipeline
from core import verify
from imperative.imp_compile import compile_file


class ImpValidateTest(unittest.TestCase):
    def test_validate_compiled(self):
        basic.load_metadata()
        for name in ['mult_add_loop', 'if_demo']:
            res, _ = verify.validate_theory(
                name, force=True,
                trust=frozenset({'nat_eval', 'int_eval', 'int_const_ineq',
                                  'real_eval', 'real_norm', 'real_const_eq',
                                  'real_compare', 'real_const_ineq',
                                  'real_eq_comparison', 'sympy', 'z3'}))
            # All VC theorems should be VALID.
            for thm_name, status in res.items():
                self.assertEqual(status, 'VALID',
                                 "%s/%s" % (name, thm_name))


if __name__ == "__main__":
    unittest.main()

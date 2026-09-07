"""z3-free unit tests for the proofrec decision nets and helpers.

The z3 package must be importable (proofrec pulls in its constants) but
the z3 SOLVER is never invoked: these tests exercise the reconstruction
machinery directly -- occurs check, ground numeral evaluation, atom
decision nets, conditional schematic discharging, propositional net.
"""

import unittest
import importlib.util

z3_available = importlib.util.find_spec("z3") is not None


@unittest.skipUnless(z3_available, "proofrec imports z3 constants")
class ProofrecUnitTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from framework import basic
        basic.load_theory('smt')

    def _parse(self, vars_, s):
        from framework import context
        context.set_context('smt', vars=vars_)
        return context.parse_term(s)

    def _assert_gapfree(self, pt):
        self.assertIsNotNone(pt)
        self.assertNotEqual(pt.rule, 'sorry')
        self.assertEqual(len(pt.gaps), 0)

    def test_occurs(self):
        from solvers.proofrec import _occurs
        x = self._parse({'x': 'int', 'y': 'int'}, 'x')
        y = self._parse({'x': 'int', 'y': 'int'}, 'y')
        t = self._parse({'x': 'int', 'y': 'int'}, 'x + (1::int)')
        self.assertTrue(_occurs(x, x))
        self.assertTrue(_occurs(x, t))
        self.assertFalse(_occurs(y, t))

    def test_ground_eval_div_mod_power(self):
        from solvers.proofrec import _ground_eval
        for goal in ('(7::nat) DIV (2::nat) = (3::nat)',
                     '(7::nat) MOD (2::nat) = (1::nat)',
                     '(2::nat) ^ (3::nat) = (8::nat)',
                     '(5::nat) DIV (1::nat) = (5::nat)'):
            self._assert_gapfree(_ground_eval(self._parse({}, goal)))

    def test_refute_ground_eq(self):
        from syntax.logicops import Not
        from solvers.proofrec import _refute_atom
        atom = self._parse({}, '(1::int) = (0::int)')
        pt = _refute_atom(atom)
        self._assert_gapfree(pt)
        self.assertEqual(pt.prop, Not(atom))  # ⊢ ¬(1 = 0)

    def test_atom_bool_net_negated_eq(self):
        from syntax.logicops import true, Not
        from syntax.numeral import Eq
        from solvers.proofrec import _atom_bool_net
        inner = self._parse({}, '(1::int) = (0::int)')
        tm = Eq(Not(inner), true)
        self._assert_gapfree(_atom_bool_net(tm))

    def test_cond_schematic_fun_upd_other(self):
        from solvers.proofrec import (schematic_rules_rewr_cond,
                                     _smt_theorem_names, SCHEMATIC_EXTRA)
        lhs = self._parse({'f': 'int => int'}, '(f)(0 := 3) 1')
        rhs = self._parse({'f': 'int => int'}, 'f 1')
        thms = _smt_theorem_names('r') + SCHEMATIC_EXTRA
        self._assert_gapfree(schematic_rules_rewr_cond(thms, lhs, rhs))

    def test_decision_net_prop(self):
        from syntax.numeral import Eq
        from solvers.proofrec import rewrite_decision_net
        lhs = self._parse({'p': 'bool', 'q': 'bool'}, 'p | q')
        rhs = self._parse({'p': 'bool', 'q': 'bool'}, 'q | p')
        self._assert_gapfree(rewrite_decision_net(Eq(lhs, rhs)))


if __name__ == "__main__":
    unittest.main()

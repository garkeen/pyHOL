"""Smoke tests for Z3 proof reconstruction (prover/proofrec.py).

These tests require the external z3 package and are skipped automatically
when it is not installed.  Run explicitly with:

    python -m pytest prover/tests/proofrec_smoke_test.py -v

Pass criterion: proofrec.proofrec returns a proof with rule != 'sorry'
and no gaps for every goal.
"""

import unittest
import importlib.util

z3_available = importlib.util.find_spec("z3") is not None


@unittest.skipUnless(z3_available, "z3 not installed")
class ProofrecSmokeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from framework import basic
        basic.load_theory('smt')

    def _run(self, vars_, goal):
        from framework import context
        from syntax.parser import parse_term
        from prover import z3wrapper, proofrec
        context.set_context('smt', vars=vars_)
        t = parse_term(goal)
        proof, assertions = z3wrapper.solve_and_proof(t)
        r = proofrec.proofrec(proof, assertions=assertions)
        self.assertNotEqual(r.rule, 'sorry', str(r.gaps))
        self.assertEqual(len(r.gaps), 0, str(r.gaps))

    # propositional (SAT net / rewrite_bool)
    def test_prop(self):
        self._run({'p': 'bool', 'q': 'bool', 'r': 'bool'},
                  '(p --> q) --> (q --> r) --> p --> r')

    def test_prop_disj(self):
        self._run({'p': 'bool', 'q': 'bool'}, 'p | q --> q | p')

    # integer th-lemma path (real_eval_conv must not crash on variables)
    def test_int_thlemma(self):
        self._run({'x': 'int'}, 'x >= 3 --> x >= 1')

    # constant arithmetic (z3wrapper numerals must be z3 values)
    def test_int_const(self):
        self._run({}, '(3::int) + 2 = 5')

    def test_int_eq_chain(self):
        self._run({'x': 'int', 'y': 'int'}, 'x = y --> y = x')

    # real th-lemma path
    def test_real_thlemma(self):
        self._run({'a': 'real'}, 'a >= 3 --> a >= 1')

    def test_arith_assume(self):
        self._run({'x': 'int', 'y': 'int'}, 'x + y = 5 --> x + y = 5')

    # quantifier instantiation and rewrite under binders
    def test_quant(self):
        self._run({'s': 'nat => nat'}, '(!n. s n = 0) --> s 2 = 0')

    # skolemization (exists_thm + Some + delete_redundant discharge)
    def test_skolemize(self):
        self._run({'P': 'nat => bool'}, '(?x. P x) --> (?y. P y)')

    # function application / update (z3 Select/Store translation)
    def test_fun_upd(self):
        self._run({'f': 'int => int'}, '(f)(0 := 3) 0 = 3')


if __name__ == "__main__":
    unittest.main()

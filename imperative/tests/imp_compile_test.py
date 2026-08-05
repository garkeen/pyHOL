# Author: AI assistant

"""Tests for the .imp to .pyhol compiler."""

import unittest
import os

from logic import basic
from server import monitor
from imperative.imp_compile import parse_imp, compile_programs, compile_file, CompileError


PROGRAMS_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))), 'imperative', 'programs')


def compile_to_programs(name):
    """Compile programs/<name>.imp and write the result to programs/<name>.pyhol."""
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        'programs', name + '.imp')
    pyhol, num_vcs, vcs = compile_file(path)
    with open(os.path.join(PROGRAMS_DIR, name + '.pyhol'), 'w', encoding='utf-8') as f:
        f.write(pyhol)
    return pyhol, num_vcs, vcs


class ImpCompileTest(unittest.TestCase):

    def test_parse_imp(self):
        text = """theory t
imports hoare

program p
  vars: a: nat, b: nat, A: nat
  pre: a == 0
  post: b == A
  body:
    while (a != A) {
      [b == a] b := a;
      a := a + 1
    }
"""
        imp_file = parse_imp(text)
        self.assertEqual(imp_file.theory, "t")
        self.assertEqual(imp_file.imports, ["hoare"])
        self.assertEqual(len(imp_file.programs), 1)
        prog = imp_file.programs[0]
        self.assertEqual(prog.name, "p")
        self.assertEqual(prog.vars, [("a", "nat"), ("b", "nat"), ("A", "nat")])
        self.assertEqual(prog.pre, "a == 0")
        self.assertEqual(prog.post, "b == A")
        self.assertIn("while", prog.body)

    def test_parse_multi_program(self):
        text = """theory t
imports hoare

program p1
  vars: a: nat
  pre: true
  post: a == 0
  body:
    a := 0

program p2
  vars: b: nat
  pre: true
  post: b == 1
  body:
    b := 1
"""
        imp_file = parse_imp(text)
        self.assertEqual(len(imp_file.programs), 2)
        self.assertEqual(imp_file.programs[0].name, "p1")
        self.assertEqual(imp_file.programs[1].name, "p2")

    def test_parse_errors(self):
        # Missing body.
        with self.assertRaises(CompileError):
            parse_imp("program p\nvars: a: nat\npre: true\npost: true")
        # Multiple programs.
        with self.assertRaises(CompileError):
            parse_imp("theory t\nprogram p\nprogram q\nvars: a: nat\npre: true\npost: true\nbody:\nskip")

    def test_compile_mult_add_loop(self):
        pyhol, num_vcs, vcs = compile_to_programs('mult_add_loop')
        self.assertEqual(num_vcs, 3)
        self.assertEqual(len(vcs), 3)
        self.assertIn("theorem mult_add_loop_vc_0", pyhol)
        self.assertIn("theorem mult_add_loop_vc_1", pyhol)
        self.assertIn("theorem mult_add_loop_vc_2", pyhol)
        self.assertEqual(pyhol.count(": z3"), 3)

    def test_compile_if_demo(self):
        pyhol, num_vcs, vcs = compile_to_programs('if_demo')
        self.assertEqual(num_vcs, 1)
        self.assertIn("theorem if_demo_vc_0", pyhol)
        self.assertIn("z3", pyhol)

    def test_validate_compiled(self):
        basic.load_metadata()
        for name in ['mult_add_loop', 'if_demo']:
            res = monitor.validate_theory(name, force=True)
            # All VC theorems should be VALID.
            for thm_name, status in res.items():
                self.assertEqual(status, 'VALID', "%s/%s" % (name, thm_name))

    def test_int_not_supported(self):
        text = """theory t
program p
  vars: a: int
  pre: true
  post: a == 0
  body:
    a := 0
"""
        with self.assertRaises(CompileError):
            compile_programs(parse_imp(text))

    def test_undeclared_variable(self):
        text = """theory t
program p
  vars: a: nat
  pre: true
  post: a == 0
  body:
    a := b
"""
        with self.assertRaises(CompileError):
            compile_programs(parse_imp(text))

    def test_compile_for_loop(self):
        text = """theory sum_demo
imports hoare
program sum_demo
  vars: x: nat, i: nat, n: nat
  pre: x == 0
  post: x == n
  body:
    for (i := 0; i < n; i++) { [x == i & i <= n] x := x + 1 }
"""
        pyhol, num_vcs, vcs = compile_programs(parse_imp(text))
        self.assertEqual(num_vcs, 3)
        self.assertTrue(all(vc['smt'] for vc in vcs), "all VCs of the for loop should be green")

    def test_compile_break_continue(self):
        text = """theory cont_demo
imports hoare
program cont_demo
  vars: x: nat, i: nat
  pre: x == 0
  post: (i <= 1 & x == i) | (2 <= i & x == i - 1)
  body:
    for (i := 0; i < 3; i++) {
      [(i <= 1 & x == i) | (2 <= i & x == i - 1)]
      if (i == 1) then continue else x := x + 1
    }
"""
        pyhol, num_vcs, vcs = compile_programs(parse_imp(text))
        self.assertEqual(num_vcs, 3)
        self.assertTrue(all(vc['smt'] for vc in vcs), "break/continue loop VCs should be green")

    def test_break_early_exit(self):
        text = """theory break_demo
imports hoare
program break_demo
  vars: x: nat
  pre: x == 0
  post: x == 2
  body:
    while (true) { [x <= 2] if (x == 2) then break else x := x + 1 }
"""
        pyhol, num_vcs, vcs = compile_programs(parse_imp(text))
        self.assertEqual(num_vcs, 3)
        self.assertTrue(all(vc['smt'] for vc in vcs), "break loop VCs should be green")

    def test_bad_post_produces_red_vc(self):
        text = """theory bad_demo
imports hoare
program bad_demo
  vars: a: nat, b: nat
  pre: a == 1 & b == 1
  post: b == 3
  body:
    a := a + 1;
    b := b + 1
"""
        pyhol, num_vcs, vcs = compile_programs(parse_imp(text))
        self.assertEqual(num_vcs, 1)
        self.assertFalse(vcs[0]['smt'], "a wrong postcondition should produce a red VC")
        self.assertIn("sorry", pyhol, "unprovable VC should get sorry")

    def test_break_outside_loop_error(self):
        text = """theory t
program p
  vars: a: nat
  pre: true
  post: a == 0
  body:
    break
"""
        with self.assertRaises(CompileError):
            compile_programs(parse_imp(text))


if __name__ == '__main__':
    unittest.main()

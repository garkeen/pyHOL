"""Unit test for items module."""

import unittest

from kernel import theory
from framework import basic
from server import items
from syntax import printer
from syntax.settings import global_setting


class ItemsTest(unittest.TestCase):
    def testDatatypeNat(self):
        basic.load_theory('logic_base')
        nat_item = items.parse_item({
            "args": [],
            "constrs": [
                {"args": [], "name": "zero", "type": "nat"},
                {"args": ["n"], "name": "Suc", "type": "nat => nat"}
            ],
            "name": "nat",
            "ty": "type.ind"
        })
        self.assertIsNone(nat_item.error)
        ext = nat_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type nat 0",
            "Constant zero :: nat",
            "Constant Suc :: nat => nat",
            "Theorem nat_zero_Suc_neq: ~(0 = Suc n)",
            "Theorem nat_Suc_inject: Suc n = Suc n1 --> n = n1",
            "Theorem nat_induct: P 0 --> (!n. P n --> P (Suc n)) --> P x",
            "Attribute nat_induct [var_induct]",
            "Theorem nat_cases: P 0 --> (!n. P (Suc n)) --> P x"
        ]

        with global_setting(unicode=False):
            self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testDatatypeList(self):
        basic.load_theory('logic_base')
        list_item = items.parse_item({
            "args": ["a"],
            "constrs": [
                {"args": [], "name": "nil", "type": "'a list"},
                {"args": ["x", "xs"], "name": "cons", "type": "'a => 'a list => 'a list"}
            ],
            "name": "list",
            "ty": "type.ind"
        })
        self.assertIsNone(list_item.error)
        ext = list_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type list 1",
            "Constant nil :: 'a list",
            "Constant cons :: 'a => 'a list => 'a list",
            "Theorem list_nil_cons_neq: ~([] = x # xs)",
            "Theorem list_cons_inject: x # xs = x1 # xs1 --> x = x1 & xs = xs1",
            "Theorem list_induct: P [] --> (!x1. !xs. P xs --> P (x1 # xs)) --> P x",
            "Attribute list_induct [var_induct]",
            "Theorem list_cases: P [] --> (!x1. !xs. P (x1 # xs)) --> P x"
        ]

        with global_setting(unicode=False):
            self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testDatatypeProd(self):
        basic.load_theory('logic_base')
        prod_item = items.parse_item({
            "args": ["a", "b"],
            "constrs": [
                {"args": ["a", "b"], "name": "Pair", "type": "'a => 'b => ('a, 'b) prod"}
            ],
            "name": "prod",
            "ty": "type.ind"
        })
        self.assertIsNone(prod_item.error)
        ext = prod_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type prod 2",
            "Constant Pair :: 'a => 'b => ('a, 'b) prod",
            "Theorem prod_Pair_inject: Pair a b = Pair a1 b1 --> a = a1 & b = b1",
            "Theorem prod_induct: (!a. !b. P (Pair a b)) --> P x",
            "Attribute prod_induct [var_induct]",
            "Theorem prod_cases: (!a. !b. P (Pair a b)) --> P x"
        ]

        with global_setting(unicode=False):
            self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testFunPlus(self):
        basic.load_theory('nat', limit=('def', 'one'))
        plus_item = items.parse_item({
            "name": "plus",
            "rules": [
                {"prop": "0 + n = n"},
                {"prop": "Suc m + n = Suc (m + n)"}
            ],
            "ty": "def.ind",
            "type": "nat ⇒ nat ⇒ nat"
        })
        self.assertIsNone(plus_item.error)
        ext = plus_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Constant plus :: nat => nat => nat",
            "Theorem plus_def_1: 0 + n = n",
            "Attribute plus_def_1 [hint_rewrite]",
            "Theorem plus_def_2: Suc m + n = Suc (m + n)",
            "Attribute plus_def_2 [hint_rewrite]"
        ]

        with global_setting(unicode=False):
            self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testPredEven(self):
        basic.load_theory('nat', limit=('def', 'one'))
        even_item = items.parse_item({
            "name": "even",
            "rules": [
                {"name": "even_zero", "prop": "even 0"},
                {"name": "even_Suc", "prop": "even n --> even (Suc (Suc n))"}
            ],
            "ty": "def.pred",
            "type": "nat => bool"
        })
        self.assertIsNone(even_item.error)
        ext = even_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Constant even :: nat => bool",
            "Theorem even_zero: even 0",
            "Attribute even_zero [hint_backward]",
            "Theorem even_Suc: even n --> even (Suc (Suc n))",
            "Attribute even_Suc [hint_backward]",
            "Theorem even_cases: even _a1 --> (_a1 = 0 --> P) --> (!n. _a1 = Suc (Suc n) --> even n --> P) --> P",
            "Theorem even_induct: P 0 --> (!n. even n --> P n --> P (Suc (Suc n))) --> (!_a1. even _a1 --> P _a1)",
            "Attribute even_induct [var_induct]"
        ]

        with global_setting(unicode=False):
            self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))


class StructRecursionTest(unittest.TestCase):
    """The structural-recursion check for fun (def.ind) definitions."""

    def testFunRecurseParamTransform(self):
        # EL-style: recursion on nat, the list parameter is transformed
        # by rev in the recursive call.  This must pass.
        basic.load_theory('list')
        item = items.parse_item({
            "name": "el",
            "rules": [
                {"prop": "el 0 l = l"},
                {"prop": "el (Suc n) l = el n (rev l)"}
            ],
            "ty": "def.ind",
            "type": "nat => 'a list => 'a list"
        })
        self.assertIsNone(item.error)

    def testFunBadMultiPatterns(self):
        # Constructor patterns on two arguments (the current nth
        # definition) must be rejected.
        basic.load_theory('list')
        item = items.parse_item({
            "name": "nth",
            "rules": [
                {"prop": "nth (x # xs) 0 = x"},
                {"prop": "nth (x # xs) (Suc n) = nth xs n"}
            ],
            "ty": "def.ind",
            "type": "'a list => nat => 'a"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('only one argument may have patterns', str(item.error))

    def testFunBadNotSubterm(self):
        # A recursive call on the whole pattern (Suc n) rather than a
        # subterm (n) must be rejected.
        basic.load_theory('nat', limit=('def', 'one'))
        item = items.parse_item({
            "name": "bad",
            "rules": [
                {"prop": "bad 0 = 0"},
                {"prop": "bad (Suc n) = bad (Suc n)"}
            ],
            "ty": "def.ind",
            "type": "nat => nat"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('not on a subterm', str(item.error))

    def testFunBadNoPattern(self):
        # Recursive calls with no constructor pattern at all must be
        # rejected.
        basic.load_theory('nat', limit=('def', 'one'))
        item = items.parse_item({
            "name": "bad",
            "rules": [
                {"prop": "bad n = bad n"}
            ],
            "ty": "def.ind",
            "type": "nat => nat"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('without any constructor pattern', str(item.error))

    def testFunBadDuplicate(self):
        # Two equations for the same constructor must be rejected.
        basic.load_theory('nat', limit=('def', 'one'))
        item = items.parse_item({
            "name": "bad",
            "rules": [
                {"prop": "bad 0 = 0"},
                {"prop": "bad 0 = 1"}
            ],
            "ty": "def.ind",
            "type": "nat => nat"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('duplicate equations', str(item.error))

    def testFunBadParamNotVar(self):
        # A non-recursion argument with a non-variable pattern must be
        # rejected.
        basic.load_theory('nat', limit=('def.ind', 'plus'))
        item = items.parse_item({
            "name": "bad",
            "rules": [
                {"prop": "bad 0 (m + 1) = 0"},
                {"prop": "bad (Suc n) m = n"}
            ],
            "ty": "def.ind",
            "type": "nat => nat => nat"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('must be plain variables', str(item.error))

    def testDatatypeBadNegative(self):
        # A constructor whose argument has the datatype in a function
        # domain (negative occurrence) must be rejected.
        basic.load_theory('logic_base')
        item = items.parse_item({
            "args": [],
            "constrs": [
                {"args": ["f"], "name": "B", "type": "(bad => bad) => bad"}
            ],
            "name": "bad",
            "ty": "type.ind"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('negative occurrence', str(item.error))

    def testDatatypeBadNested(self):
        # An occurrence of the datatype inside another datatype (here
        # 'bad list') is not supported and must be rejected.
        basic.load_theory('list')
        item = items.parse_item({
            "args": [],
            "constrs": [
                {"args": ["l"], "name": "B", "type": "bad list => bad"}
            ],
            "name": "bad",
            "ty": "type.ind"
        })
        self.assertIsNotNone(item.error)
        self.assertIn('not supported', str(item.error))

    def testDatatypePositive(self):
        # The datatype in the range of a function argument is a
        # strictly positive occurrence and must be accepted.
        basic.load_theory('nat', limit=('def', 'one'))
        item = items.parse_item({
            "args": [],
            "constrs": [
                {"args": ["f"], "name": "B", "type": "(nat => bad) => bad"}
            ],
            "name": "bad",
            "ty": "type.ind"
        })
        self.assertIsNone(item.error)


if __name__ == "__main__":
    unittest.main()

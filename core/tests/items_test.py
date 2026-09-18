"""Unit test for items module."""

import unittest

from kernel import theory
from core import basic
from core import items
from syntax import parser
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


    def testQuotient(self):
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
        theory.thy.unchecked_extend(nat_item.get_extension())
        rel_item = items.parse_item({
            "name": "myrel", "type": "nat => nat => bool", "ty": "def.ax"})
        theory.thy.unchecked_extend(rel_item.get_extension())

        quot_item = items.parse_item({
            "name": "myq", "abs": "mk_myq", "rep": "dest_myq",
            "rel": "myrel", "ty": "type.quot"})
        self.assertIsNone(quot_item.error)
        self.assertEqual(quot_item.args, [])
        ext = quot_item.get_extension()
        theory.thy.unchecked_extend(ext)
        ext_output = [
            "Type myq 0",
            "Constant mk_myq :: (nat => bool) => myq",
            "Constant dest_myq :: myq => nat => bool",
            "Theorem myq_abs_rep: !a. mk_myq (dest_myq a) = a",
            "Theorem myq_rep_abs: !s. (?x. s = myrel x) <--> dest_myq (mk_myq s) = s"
        ]

        with global_setting(unicode=False):
            self.assertEqual(printer.print_extensions(ext), '\n'.join(ext_output))

    def testQuotientBadRelation(self):
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
        theory.thy.unchecked_extend(nat_item.get_extension())
        # Not a relation: nat => nat, not nat => nat => bool.
        bad_rel = items.parse_item({
            "name": "badrel", "type": "nat => nat", "ty": "def.ax"})
        theory.thy.unchecked_extend(bad_rel.get_extension())

        bad_item = items.parse_item({
            "name": "badq", "abs": "mk_bad", "rep": "dest_bad",
            "rel": "badrel", "ty": "type.quot"})
        self.assertIsNotNone(bad_item.error)
        self.assertIn("A => A => bool", str(bad_item.error))


    def testTypeAbbrev(self):
        basic.load_theory('logic_base')
        ab_item = items.parse_item({
            "name": "set", "args": ["a"], "def": "'a => bool",
            "ty": "type.abbrev"})
        self.assertIsNone(ab_item.error)
        self.assertEqual(ab_item.defn, parser.parse_type("'a => bool"))
        # No theory extension: abbreviations are parser state only, so
        # no type constant and no axiom enters the theory.
        self.assertEqual(ab_item.get_extension(), [])
        # Uses are expanded away, in postfix type syntax.
        self.assertEqual(parser.parse_type("bool set"),
                         parser.parse_type("bool => bool"))

    def testTypeAbbrevBadVar(self):
        basic.load_theory('logic_base')
        bad_item = items.parse_item({
            "name": "foo", "args": ["a"], "def": "'a => 'b",
            "ty": "type.abbrev"})
        self.assertIsNotNone(bad_item.error)
        self.assertIn("not parameters", str(bad_item.error))


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
        # A plain theorem: the `fun` items around it are expanded by
        # the generator whenever the method layer is loaded, so a
        # limit naming one of them would depend on that.
        basic.load_theory('nat', limit=('thm', 'add_0_right'))
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


class MutualFunTest(unittest.TestCase):
    """`fun ... and ...`: one item for the group, nothing registered yet.

    The block is parsed -- and its equations are read with every function
    of the group in scope, which is what a call across the group needs --
    but it is not emitted: the sum encoding that justifies the recursion
    covers the group as a whole.  Until that lands the block reports
    itself and registers nothing, least of all axioms, which no
    structural check could make consistent for a call that crosses
    functions.

    """

    def _block(self, groups=None):
        return items.parse_item({
            "ty": "def.ind",
            "groups": groups or [
                {"name": "even2", "type": "nat => bool",
                 "rules": [{"prop": "even2 0 = true"},
                           {"prop": "even2 (Suc n) = odd2 n"}]},
                {"name": "odd2", "type": "nat => bool",
                 "rules": [{"prop": "odd2 0 = false"},
                           {"prop": "odd2 (Suc n) = even2 n"}]},
            ]})

    def testGroupIsOneItemAndReportsTheGap(self):
        basic.load_theory('nat', limit=('def', 'one'))
        item = self._block()
        self.assertIsNotNone(item.error)
        self.assertIn('not emitted yet', str(item.error))
        self.assertEqual(item.name, 'even2 and odd2')
        self.assertEqual([g['name'] for g in item.groups], ['even2', 'odd2'])
        self.assertEqual(len(item.parsed_groups), 2)

    def testGroupRegistersNothing(self):
        # No constant and no equation theorem: the block has neither.
        basic.load_theory('nat', limit=('def', 'one'))
        self._block()
        with self.assertRaises(theory.TheoryException):
            theory.get_theorem('even2_def_1')
        with self.assertRaises(theory.TheoryException):
            theory.get_theorem('odd2_def_2')

    def testGroupRefusesAxioms(self):
        basic.load_theory('nat', limit=('def', 'one'))
        item = self._block()
        with self.assertRaises(items.ItemException) as ctx:
            item.get_extension()
        self.assertIn('emitted, not axiomatized', str(ctx.exception))

    def testGroupRulesBelongToTheirFunction(self):
        # Equations are still each function's own: the head of a rule's
        # left hand side is the function it defines.  (Reading the
        # *right* hand side is where the sibling comes in.)
        basic.load_theory('nat', limit=('def', 'one'))
        item = self._block(groups=[
            {"name": "even3", "type": "nat => bool",
             "rules": [{"prop": "odd3 0 = true"}]},
            {"name": "odd3", "type": "nat => bool",
             "rules": [{"prop": "odd3 (Suc n) = even3 n"}]}])
        self.assertIsNotNone(item.error)
        self.assertIn('wrong head of lhs', str(item.error))

    def testGroupTakesNoClauses(self):
        # A mutual block's termination covers the group, so a per
        # function `measure` / `relation` is not read (and not silently
        # ignored either).
        basic.load_theory('nat', limit=('def', 'one'))
        item = self._block(groups=[
            {"name": "even4", "type": "nat => bool",
             "measure": ["n"],
             "rules": [{"prop": "even4 (Suc n) = even4 n"}]}])
        self.assertIsNotNone(item.error)
        self.assertIn('mutual block', str(item.error))

    def testSingleFunctionKeepsTheFlatShape(self):
        # The one-function case is untouched: same data keys, same
        # attributes, no `groups`.
        basic.load_theory('nat', limit=('def', 'one'))
        item = items.parse_item({
            "name": "f2", "type": "nat => nat",
            "rules": [{"prop": "f2 0 = 0"}], "ty": "def.ind"})
        self.assertIsNone(item.error)
        self.assertIsNone(item.groups)
        self.assertEqual(item.name, 'f2')


if __name__ == "__main__":
    unittest.main()

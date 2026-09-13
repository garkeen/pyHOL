# Tests for the type-class sugar (`'a::C` annotations).

"""Class annotations are sugar for a premise on the statement.

Active: the type grammar accepts (and drops) `'a::C`; `with_class_premises`
turns annotations into a premise (deduped, in first-seen order); the
annotation stays in the item text, so .pyhol round-trips it.
Passive: an unregistered class is rejected, so is a `::` annotation that does
not sit on a type variable, and a term-level type annotation in the prop is
not mistaken for a class annotation.
"""

import unittest

from syntax import parser, pyhol


class ClassSugarTest(unittest.TestCase):
    def testTypeGrammarDropsAnnotation(self):
        """`'a::linorder` parses to the type variable `'a`."""
        self.assertEqual(str(parser.parse_type("'a::linorder", check_type=False)),
                         "'a")
        T = parser.parse_type("('a::linorder, 'b) tree", check_type=False)
        self.assertEqual(str(T), "('a, 'b) tree")

    def testPremiseInjection(self):
        # `linorder` constrains both operations: holpy's `less` and `less_eq`
        # are independent overloaded constants, so the annotation states a
        # law predicate for each.
        prop = parser.with_class_premises("x <= x", "'a::linorder")
        self.assertEqual(
            prop,
            "linorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶ "
            "linorder_lt (less::'a ⇒ 'a ⇒ bool) ⟶ x <= x")

    def testSingleOperationClassInjectsOnePremise(self):
        prop = parser.with_class_premises("x <= x", "'a::order")
        self.assertEqual(prop,
                         "order (less_eq::'a ⇒ 'a ⇒ bool) ⟶ x <= x")

    def testLawlessClassInjectsNothing(self):
        # Isabelle's `ord` states the two constants and no laws; it is
        # accepted as a marker.
        self.assertEqual(parser.with_class_premises("x <= x", "'a::ord"),
                         "x <= x")

    def testPremiseInjectionDedupes(self):
        prop = parser.with_class_premises("x <= y", "'a::order", "'a::order")
        self.assertEqual(prop, "order (less_eq::'a ⇒ 'a ⇒ bool) ⟶ x <= y")

    def testSeveralConstraintsKeepOrder(self):
        prop = parser.with_class_premises("P", "'a::order", "'b::preorder")
        self.assertEqual(
            prop,
            "order (less_eq::'a ⇒ 'a ⇒ bool) ⟶ "
            "preorder (less_eq::'b ⇒ 'b ⇒ bool) ⟶ P")

    def testAddClassRegistersSeveralPremises(self):
        try:
            parser.add_class('_test_two_ops',
                             ('preorder', (('less_eq', "'%s ⇒ '%s ⇒ bool"),)),
                             ('linorder_lt', (('less', "'%s ⇒ '%s ⇒ bool"),)))
            prop = parser.with_class_premises("P", "'a::_test_two_ops")
            self.assertEqual(
                prop,
                "preorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶ "
                "linorder_lt (less::'a ⇒ 'a ⇒ bool) ⟶ P")
        finally:
            parser.CLASSES.pop('_test_two_ops', None)

    def testNoAnnotationNoChange(self):
        self.assertEqual(
            parser.with_class_premises("x <= x", "nat", "x <= x"), "x <= x")

    def testUnknownClassRejected(self):
        with self.assertRaises(parser.ParserError) as cm:
            parser.with_class_premises("x <= x", "'a::no_such_class")
        self.assertIn('no_such_class', str(cm.exception))

    def testConcreteTypeAnnotationRejected(self):
        with self.assertRaises(parser.ParserError):
            parser.with_class_premises("x <= x", "nat::linorder")

    def testPropTypeAnnotationIsNotAClassAnnotation(self):
        """`(less_eq :: nat ⇒ nat ⇒ bool)` in a prop is a term annotation."""
        prop = "preorder (less_eq :: nat ⇒ nat ⇒ bool)"
        self.assertEqual(parser.with_class_premises(prop, "nat"), prop)

    def testPyholRoundTripKeepsAnnotation(self):
        src = ("theory t\nimports\n\ntheorem th\n"
               "  fixes x :: 'a::linorder\n  prop x <= x\n")
        d = pyhol.parse_pyhol(src)
        item = d['content'][0]
        self.assertEqual(item['vars'], {'x': "'a::linorder"})
        self.assertEqual(item['prop'], 'x <= x')
        text = pyhol.export_pyhol(d)
        self.assertIn("'a::linorder", text)
        self.assertIn('x <= x', text)

    def testFunSignatureKeepsAnnotationAsMarker(self):
        """A definition may carry the annotation too; it stays a marker there
        (its equations are uniform in the instance), so no premise appears."""
        src = ("theory t\nimports\n\nfun f :: 'a::linorder => bool\n"
               "  | f x = f x\n")
        d = pyhol.parse_pyhol(src)
        item = d['content'][0]
        self.assertEqual(item['type'], "'a::linorder ⇒ bool")
        self.assertEqual(item['rules'][0]['prop'], 'f x = f x')


if __name__ == '__main__':
    unittest.main()

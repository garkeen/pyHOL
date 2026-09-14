# Tests for the type-class sugar (`'a::C` annotations).

"""Class annotations are sugar for a premise on the statement.

The class and its laws are *library* content: a `class` item (see
library/order.pyhol) registers them with the parser, so `syntax/` holds only
the generic mechanism -- annotation, lookup, premise text.  Nothing here
pre-populates the registry by hand: the tests load the library theory that
declares the classes, so a broken declaration fails them.

Active: the type grammar accepts (and drops) `'a::C`; the library's
declarations inject one premise per law (`'a::linorder` states three), with the
annotated variable renamed; the annotation stays in the item text, so .pyhol
round-trips it; a `class` declaration round-trips too.
Passive: an unregistered class is rejected with a message naming it, a `::`
annotation that does not sit on a type variable is rejected, a term-level type
annotation in the prop is not mistaken for a class annotation, and a malformed
`class` declaration is reported rather than silently dropped.
"""

import unittest

from core import basic
from syntax import parser, pyhol


class ClassSugarTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        basic.load_metadata()
        # Register the library's classes exactly as a theory load does.
        basic.load_theory('order')

    def testLibraryDeclaresTheClasses(self):
        """The declarations live in library/order.pyhol, next to the
        predicates they name."""
        content = basic.theory_cache['order']['content']
        decls = {it.name: it.body for it in content if it.ty == 'class'}
        self.assertEqual(set(decls),
                         {'ord', 'preorder', 'order', 'linorder'})
        self.assertEqual(decls['ord'], '')
        self.assertIn('preorder (less_eq :: ', decls['preorder'])
        self.assertIn('linorder (less_eq :: ', decls['linorder'])
        self.assertIn('linorder_lt (less :: ', decls['linorder'])
        self.assertIn('linorder_lt_le (less_eq :: ', decls['linorder'])

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
            "linorder_lt (less::'a ⇒ 'a ⇒ bool) ⟶ "
            "linorder_lt_le (less_eq::'a ⇒ 'a ⇒ bool) (less::'a ⇒ 'a ⇒ bool) ⟶ "
            "x <= x")

    def testPremiseTypesFollowTheAnnotatedVariable(self):
        """The declaration writes the operations at the class's own variable;
        the premise speaks about the annotated one."""
        prop = parser.with_class_premises("x <= x", "'b::linorder")
        self.assertIn("linorder (less_eq::'b ⇒ 'b ⇒ bool)", prop)
        self.assertIn("linorder_lt (less::'b ⇒ 'b ⇒ bool)", prop)
        self.assertNotIn("'a", prop)

    def testSingleOperationClassInjectsOnePremise(self):
        prop = parser.with_class_premises("x <= x", "'a::order")
        self.assertEqual(
            prop,
            "order (less_eq::'a ⇒ 'a ⇒ bool) ⟶ "
            "linorder_lt_le (less_eq::'a ⇒ 'a ⇒ bool) (less::'a ⇒ 'a ⇒ bool) ⟶ "
            "x <= x")

    def testLawlessClassInjectsNothing(self):
        # Isabelle's `ord` states the two constants and no laws; it is
        # accepted as a marker.
        self.assertEqual(parser.with_class_premises("x <= x", "'a::ord"),
                         "x <= x")

    def testPremiseInjectionDedupes(self):
        prop = parser.with_class_premises("x <= y", "'a::order", "'a::order")
        self.assertEqual(
            prop,
            "order (less_eq::'a ⇒ 'a ⇒ bool) ⟶ "
            "linorder_lt_le (less_eq::'a ⇒ 'a ⇒ bool) (less::'a ⇒ 'a ⇒ bool) ⟶ "
            "x <= y")

    def testSeveralConstraintsKeepOrder(self):
        prop = parser.with_class_premises("P", "'a::order", "'b::preorder")
        self.assertEqual(
            prop,
            "order (less_eq::'a ⇒ 'a ⇒ bool) ⟶ "
            "linorder_lt_le (less_eq::'a ⇒ 'a ⇒ bool) (less::'a ⇒ 'a ⇒ bool) ⟶ "
            "preorder (less_eq::'b ⇒ 'b ⇒ bool) ⟶ "
            "linorder_lt_le (less_eq::'b ⇒ 'b ⇒ bool) (less::'b ⇒ 'b ⇒ bool) ⟶ P")

    def testAddClassRegistersSeveralPremises(self):
        """A registry entry may constrain several operations; the premise is
        the predicate applied to all of them."""
        try:
            parser.add_class('_test_two_ops',
                             ('linorder_lt_le', [('less_eq', "'a ⇒ 'a ⇒ bool"),
                                                 ('less', "'a ⇒ 'a ⇒ bool")]))
            prop = parser.with_class_premises("P", "'a::_test_two_ops")
            self.assertEqual(
                prop,
                "linorder_lt_le (less_eq::'a ⇒ 'a ⇒ bool) (less::'a ⇒ 'a ⇒ bool)"
                " ⟶ P")
        finally:
            parser.CLASSES.pop('_test_two_ops', None)

    def testNoAnnotationNoChange(self):
        self.assertEqual(
            parser.with_class_premises("x <= x", "nat", "x <= x"), "x <= x")

    def testUnknownClassRejected(self):
        """An annotation naming a class nobody declares is rejected, and the
        message says which classes are known."""
        with self.assertRaises(parser.ParserError) as cm:
            parser.with_class_premises("x <= x", "'a::no_such_class")
        msg = str(cm.exception)
        self.assertIn('no_such_class', msg)
        self.assertIn('linorder', msg)

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

    def testClassItemRoundTrip(self):
        """A `class` declaration parses (multi-line, like datatype) and is
        exported as one line that parses back to the same body."""
        src = ("theory t\nimports\n\n"
               "class c = p1 (a :: 'a ⇒ bool),\n"
               "          p2 (b :: 'a ⇒ bool, c :: 'a ⇒ 'a ⇒ bool)\n")
        d = pyhol.parse_pyhol(src)
        item = d['content'][0]
        self.assertEqual(item['ty'], 'class')
        self.assertEqual(item['name'], 'c')
        text = pyhol.export_pyhol(d)
        again = pyhol.parse_pyhol(text)['content'][0]
        self.assertEqual(again['body'], item['body'])

    def testMalformedClassDeclarationReported(self):
        """A declaration that is not `pred (op :: type)` becomes an error
        item instead of being dropped silently."""
        data = {'ty': 'class', 'name': 'c', 'body': 'oops'}
        from core import items
        item = items.parse_item(data)
        self.assertIsNotNone(item.error)
        self.assertIn('class declaration', str(item.error))

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

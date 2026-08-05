# Author: Bohua Zhan

import unittest

from imperative import parser2
from imperative.com import Skip, Assign, Seq, Cond, While
from imperative.expr import Var, Op


class Parser2Test(unittest.TestCase):
    def testParseSkip(self):
        c = parser2.com_parser.parse("skip")
        self.assertIsInstance(c, Skip)

    def testParseAssign(self):
        c = parser2.com_parser.parse("x := x + 1")
        self.assertIsInstance(c, Assign)
        self.assertEqual(c.v.name, "x")

    def testParseSeq(self):
        c = parser2.com_parser.parse("x := x + 1; y := y + 1")
        self.assertIsInstance(c, Seq)
        self.assertIsInstance(c.c1, Assign)
        self.assertIsInstance(c.c2, Assign)

    def testParseIf(self):
        c = parser2.com_parser.parse("if (a != 0) then a := 0 else skip")
        self.assertIsInstance(c, Cond)
        self.assertIsInstance(c.c1, Assign)
        self.assertIsInstance(c.c2, Skip)

    def testParseWhile(self):
        c = parser2.com_parser.parse("while (a != A) {[b == a * B] b := b + B; a := a + 1}")
        self.assertIsInstance(c, While)
        self.assertIsInstance(c.c, Seq)

    def testParseCond(self):
        c = parser2.cond_parser.parse("a == 0 & b == 1")
        self.assertIsInstance(c, Op)
        self.assertEqual(c.op, "&")


if __name__ == "__main__":
    unittest.main()

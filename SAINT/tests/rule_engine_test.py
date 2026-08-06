"""Unit tests for the data-driven rule engine.

Focus on the general rewrite engine (``apply_rewrite_rules`` /
``RewriteTrigonometric``), the ambient-variable mechanism (TR0) and the step
driver (``apply_step``).  The trigonometric rules themselves are data stored in
base.calc, not code.

"""

import unittest

from SAINT import parser, rules
from SAINT.context import Context
from SAINT.poly import normalize


def load_ctx():
    ctx = Context()
    ctx.load_book('base')
    return ctx


class RewriteTrigonometricTest(unittest.TestCase):
    """Data-driven Fu-style trigonometric rewrite rules."""

    def rewrite(self, rule, expr_str):
        ctx = load_ctx()
        e = parser.parse_expr(expr_str)
        return rules.RewriteTrigonometric(rule).eval(e, ctx)

    def assert_rewrite(self, rule, expr_str, expected):
        result = self.rewrite(rule, expr_str)
        self.assertEqual(str(result), expected,
                         "%s(%s) != %s" % (rule, expr_str, expected))

    def assert_rewrite_normalized(self, rule, expr_str, expected):
        """Compare up to polynomial normalization (term ordering etc.)."""
        ctx = load_ctx()
        conds = ctx.get_conds()
        result = self.rewrite(rule, expr_str)
        r = normalize(result, conds)
        e = normalize(parser.parse_expr(expected), conds)
        self.assertEqual(str(r), str(e),
                         "%s(%s) !~ %s" % (rule, expr_str, expected))

    def test_TR1(self):
        self.assert_rewrite('TR1', 'sec(x)', '1 / cos(x)')
        self.assert_rewrite('TR1', 'csc(x)', '1 / sin(x)')
        self.assert_rewrite('TR1', 'sec(2 * x)', '1 / cos(2 * x)')
        self.assert_rewrite_normalized('TR1', 'sec(x) ^ 2', 'cos(x) ^ -2')

    def test_TR2(self):
        self.assert_rewrite('TR2', 'tan(x)', 'sin(x) / cos(x)')
        self.assert_rewrite('TR2', 'cot(x)', 'cos(x) / sin(x)')
        self.assert_rewrite('TR2', 'tan(x) ^ 2', '(sin(x) / cos(x)) ^ 2')

    def test_TR5(self):
        self.assert_rewrite('TR5', 'sin(x) ^ 2', '1 - cos(x) ^ 2')
        self.assert_rewrite('TR5', 'sin(x) ^ 2 + 1', '1 - cos(x) ^ 2 + 1')

    def test_TR6(self):
        self.assert_rewrite('TR6', 'cos(x) ^ 2', '1 - sin(x) ^ 2')

    def test_TR7(self):
        self.assert_rewrite('TR7', 'sin(x) ^ 2', '(1 - cos(2 * x)) / 2')
        self.assert_rewrite('TR7', 'cos(x) ^ 2', '(1 + cos(2 * x)) / 2')

    def test_TR8(self):
        self.assert_rewrite('TR8', 'sin(x) * cos(y)',
                            '1/2 * (sin(y + x) - sin(y - x))')
        self.assert_rewrite('TR8', 'cos(x) * sin(y)',
                            '1/2 * (sin(x + y) - sin(x - y))')
        self.assert_rewrite('TR8', 'sin(x) * sin(y)',
                            '-1/2 * (cos(x - y) - cos(x + y))')

    def test_TR9(self):
        self.assert_rewrite('TR9', 'sin(x) + sin(y)',
                            '2 * sin((x + y) / 2) * cos((x - y) / 2)')
        self.assert_rewrite('TR9', 'cos(x) - cos(y)',
                            '-2 * sin((x + y) / 2) * sin((x - y) / 2)')

    def test_TR10(self):
        self.assert_rewrite('TR10', 'sin(x + y)',
                            'sin(x) * cos(y) + cos(x) * sin(y)')
        self.assert_rewrite('TR10', 'cos(x - y)',
                            'cos(x) * cos(y) + sin(x) * sin(y)')

    def test_TR10i(self):
        self.assert_rewrite('TR10i', 'sin(x) + cos(x)',
                            'sqrt(2) * sin(x + pi / 4)')
        self.assert_rewrite('TR10i', 'sin(x) - cos(x)',
                            '-sqrt(2) * cos(x + pi / 4)')

    def test_TR11(self):
        self.assert_rewrite('TR11', 'sin(2 * x)', '2 * sin(x) * cos(x)')
        self.assert_rewrite('TR11', 'cos(2 * x)', 'cos(x) ^ 2 - sin(x) ^ 2')

    def test_TR22_prefers_whole_expression(self):
        # 1 + tan(x)^2 must reduce to sec(x)^2, not to 1 + (sec(x)^2 - 1).
        self.assert_rewrite('TR22', '1 + tan(x) ^ 2', 'sec(x) ^ 2')
        # The sum may be stored in either order.
        self.assert_rewrite('TR22', 'tan(x) ^ 2 + 1', 'sec(x) ^ 2')
        self.assert_rewrite('TR22', '1 + cot(x) ^ 2', 'csc(x) ^ 2')
        # Without the leading 1, the subterm rule applies.
        self.assert_rewrite('TR22', 'tan(x) ^ 2', 'sec(x) ^ 2 - 1')

    def test_TR111(self):
        self.assert_rewrite('TR111', '1 / cos(x) ^ 2', 'sec(x) ^ 2')
        self.assert_rewrite_normalized('TR111', 'cos(x) ^ -2', 'sec(x) ^ 2')
        self.assert_rewrite_normalized('TR111', 'sin(x) ^ -3', 'csc(x) ^ 3')


class TR0AmbientVariableTest(unittest.TestCase):
    """TR0 introduces (sin v)^2 + (cos v)^2, with v the integral variable."""

    def test_rewrite_constant_factor(self):
        ctx = load_ctx()
        e = parser.parse_expr('INT u:[0, 1/2]. 2 * sin(2 * u) ^ -1')
        res = rules.OnLocation(rules.RewriteTrigonometric('TR0'), (0, 0)).eval(e, ctx)
        self.assertEqual(str(res),
                         'INT u:[0,1/2]. 2 * (sin(u) ^ 2 + cos(u) ^ 2) * sin(2 * u) ^ (-1)')

    def test_rewrite_numerator(self):
        ctx = load_ctx()
        e = parser.parse_expr('INT x:[0, 1]. 1 / (2 * sin(x) * cos(x))')
        res = rules.OnLocation(rules.RewriteTrigonometric('TR0'), (0, 0)).eval(e, ctx)
        self.assertEqual(str(res),
                         'INT x:[0,1]. 1 * (sin(x) ^ 2 + cos(x) ^ 2) / (2 * sin(x) * cos(x))')

    def test_one_shot_does_not_loop(self):
        # The rule output still contains a constant factor matching the lhs,
        # so a fixpoint rewrite would not terminate; one_shot must stop after
        # a single application.
        ctx = load_ctx()
        e = parser.parse_expr('2')
        res = rules.RewriteTrigonometric('TR0').eval(e, ctx)
        self.assertEqual(str(res), '2 * (sin(?x) ^ 2 + cos(?x) ^ 2)')

    def test_const_vars_restrict_to_constants(self):
        # The constant pattern n must match constants only: 2 matches, the
        # non-constant product 2*u does not.
        ctx = load_ctx()
        tr0 = ctx.get_trig_rules('TR0')[0]
        self.assertIsNotNone(parser.parse_expr('2').find_subexpr_pred(
            lambda s: str(s) == '2'))
        m = tr0.lhs.find_subexpr_pred(
            lambda s: s.is_symbol() and s.name == 'n')
        self.assertEqual(len(m), 1)
        # Exercise the loaded rule on a constant and on a non-constant.
        from SAINT.expr import match as expr_match
        self.assertIsNotNone(expr_match(parser.parse_expr('2'), tr0.lhs))
        self.assertIsNone(expr_match(parser.parse_expr('2 * u'), tr0.lhs))


class ApplyStepTest(unittest.TestCase):
    """The step driver: recorded rule + location -> result."""

    def test_TR0_step(self):
        ctx = load_ctx()
        current = parser.parse_expr('INT u:[0, 1/2]. 2 * sin(2 * u) ^ -1')
        step = {'reason': 'Rewrite trigonometric', 'params': {'rule': 'TR0'},
                'location': (0, 0)}
        res = rules.apply_step(current, step, ctx, [])
        self.assertEqual(str(res),
                         'INT u:[0,1/2]. 2 * (sin(u) ^ 2 + cos(u) ^ 2) * sin(2 * u) ^ (-1)')

    def test_TR22_step(self):
        ctx = load_ctx()
        current = parser.parse_expr('INT x:[0,1]. 1 / (1 + tan(x) ^ 2)')
        step = {'reason': 'Rewrite trigonometric', 'params': {'rule': 'TR22'},
                'location': (0, 1)}
        res = rules.apply_step(current, step, ctx, [])
        self.assertEqual(str(res), 'INT x:[0,1]. 1 / sec(x) ^ 2')

    def test_substitution_power(self):
        # Substituting u = x^(1/4): x^(1/4) -> u and x^(3/4) -> u^3.
        ctx = load_ctx()
        current = parser.parse_expr('INT x:[0,1]. exp(x ^ (1/4))')
        step = {'reason': 'Substitution',
                'params': {'var_name': 'u', 'g': 'x ^ (1/4)', 'f': '4 * u ^ 3 * exp(u)'},
                'location': (0,)}
        res = rules.apply_step(current, step, ctx, [])
        self.assertEqual(str(res), 'INT u:[0,1]. 4 * u ^ 3 * exp(u)')

    def test_substitution_linear(self):
        ctx = load_ctx()
        current = parser.parse_expr('INT x:[0,1]. 1 / (2 * x + 1)')
        step = {'reason': 'Substitution',
                'params': {'var_name': 'u', 'g': '2 * x', 'f': '1/2 * (1 / (u + 1))'},
                'location': (0,)}
        res = rules.apply_step(current, step, ctx, [])
        self.assertEqual(str(res), 'INT u:[0,2]. 1/2 * (1 / (u + 1))')

    def test_rewrite_fraction(self):
        ctx = load_ctx()
        current = parser.parse_expr('INT x:[0,1]. 2 * x / 2')
        step = {'reason': 'Rewrite fraction', 'params': {'rhs': 'x'},
                'location': None}
        res = rules.apply_step(current, step, ctx, [])
        self.assertEqual(str(res), 'x')

    def test_step_requires_change(self):
        # A step whose rule leaves the expression unchanged must fail.
        ctx = load_ctx()
        current = parser.parse_expr('INT x:[0,1]. x + 1')
        step = {'reason': 'Rewrite trigonometric', 'params': {'rule': 'TR22'},
                'location': (0,)}
        with self.assertRaises(AssertionError):
            rules.apply_step(current, step, ctx, [])


if __name__ == '__main__':
    unittest.main()

"""State of computation.

Equation-chain model: a Calculation is a chain of steps, each step
stores old_expr = new_expr (an equation justified by a rule).
No Goal, no proof modes -- pure forward computation.
"""

from typing import List, Optional, Union

from SAINT.expr import Expr, Var, Const
from SAINT import rules, expr
from SAINT.rules import Rule
from SAINT.conditions import Conditions
from SAINT.context import Context
from SAINT import latex
from SAINT import parser
from SAINT.poly import normalize


class Label:
    def __init__(self, data):
        self.data = []
        if isinstance(data, str):
            split = data.split(".")
            for n in split:
                if n == '':
                    continue
                assert int(n) >= 1, "Label: non-positive value"
                self.data.append(int(n) - 1)
        elif isinstance(data, list):
            assert all(n >= 0 for n in data), "Label: negative value"
            self.data = list(data)
        else:
            raise AssertionError("Label: unexpected type")

    @property
    def head(self):
        return self.data[0]

    @property
    def tail(self):
        return Label(self.data[1:])

    def empty(self):
        return len(self.data) == 0

    def __str__(self):
        res = ""
        for n in self.data:
            res += str(n+1) + "."
        return res


class StateItem:
    """Items in a state of computation"""
    ctx: Context

    def export(self):
        raise NotImplementedError

    def export_book(self):
        raise NotImplementedError

    def get_by_label(self, label: Label) -> "StateItem":
        raise NotImplementedError

    def get_facts(self):
        return []

    def clear(self):
        pass

    def is_finished(self):
        return True


class FuncDef(StateItem):
    """Introduce a new function definition."""
    def __init__(self, parent: "CompFile", ctx: Context, eq: Expr, conds: Optional[Conditions] = None):
        if not eq.is_equals():
            raise AssertionError("FuncDef: input should be an equation")

        self.parent = parent
        self.ctx = ctx

        self.eq = eq
        if self.eq.lhs.is_fun():
            self.symb = self.eq.lhs.func_name
            self.args = self.eq.lhs.args
        elif self.eq.lhs.is_var():
            self.symb = self.eq.lhs.name
            self.args = []
        else:
            raise AssertionError("FuncDef: left side of equation must be variable or function")
        self.body = self.eq.rhs

        if any(not arg.is_var() for arg in self.args) or len(self.args) != len(set(self.args)):
            raise AssertionError("FuncDef: arguments should be distinct variables")

        if conds is None:
            conds = Conditions()
        self.conds = conds

    def __str__(self):
        res = "Definition\n"
        res += "  %s\n" % self.eq
        return res

    def __eq__(self, other):
        return isinstance(other, FuncDef) and self.eq == other.eq and self.conds == other.conds

    def export(self):
        res = {
            "type": "FuncDef",
            "eq": str(self.eq),
            "latex_lhs": latex.convert_expr(self.eq.lhs),
            "latex_eq": latex.convert_expr(self.eq)
        }
        if self.conds.data:
            res["conds"] = self.conds.export()
        return res

    def export_book(self):
        p = self.parent
        while (not isinstance(p, CompFile)):
            p = p.parent
        res = {
            "type": "definition",
            "expr": str(self.eq),
            "path": p.name
        }
        if self.conds.data:
            res["conds"] = [str(cond) for cond in self.conds.data]
        return res

    def get_by_label(self, label: Label):
        if not label.empty():
            raise AssertionError("get_by_label: invalid label")
        return self

    def get_facts(self):
        return [self.eq]


class CalculationStep(StateItem):
    """A step in the calculation. Stores the equation old_expr = new_expr."""
    def __init__(self, parent: "Calculation", rule: Rule, old_expr: Expr, new_expr: Expr, id: int):
        self.parent = parent
        self.rule = rule
        self.old_expr = old_expr
        self.res = new_expr
        self.id = id
        self.ctx = parent.ctx

    def __str__(self):
        return "%s = %s (%s)" % (self.old_expr, self.res, self.rule)

    def __eq__(self, other):
        return isinstance(other, CalculationStep) and self.rule == other.rule and self.res == other.res

    def export(self):
        return {
            "type": "CalculationStep",
            "rule": self.rule.export(),
            "old_expr": str(self.old_expr),
            "latex_old": latex.convert_expr(self.old_expr),
            "res": str(self.res),
            "latex_res": latex.convert_expr(self.res)
        }

    def clear(self):
        self.parent.clear(id=self.id)

    def perform_rule(self, rule: Rule):
        self.parent.perform_rule(rule, self.id)


class Calculation(StateItem):
    """Calculation starting from an expression.

    A chain of steps where each step transforms the current expression.
    Each step stores old_expr = new_expr (an equation justified by the rule).
    """
    def __init__(self, parent, ctx: Context, start: Expr, *,
                 connection_symbol='=', conds: Optional[Conditions] = None):
        self.parent = parent
        self.start = start
        self.steps: List[CalculationStep] = []
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.connection_symbol = connection_symbol
        if conds is None:
            self.ctx = ctx
        else:
            self.ctx = Context(ctx)
            self.ctx.extend_condition(self.conds)

    def __str__(self):
        res = "  " + str(self.start) + "\n"
        for step in self.steps:
            res += self.connection_symbol + " %s\n" % step
        return res

    def export(self):
        res = {
            "type": "Calculation",
            "start": str(self.start),
            "latex_start": latex.convert_expr(self.start),
            "steps": [step.export() for step in self.steps]
        }
        if self.conds.data:
            res["conds"] = self.conds.export()
        return res

    def export_book(self):
        p = self.parent
        while (not isinstance(p, CompFile)):
            p = p.parent
        res = {
            "type": "calculation",
            "expr": str(self.start),
            "path": p.name
        }
        if self.conds.data:
            res["conds"] = [str(cond) for cond in self.conds.data]
        return res

    def clear(self, id: int = 0):
        self.steps = self.steps[:id]

    def add_step(self, step: CalculationStep):
        self.steps.append(step)

    @property
    def last_expr(self) -> Expr:
        if self.steps:
            return self.steps[-1].res
        else:
            return self.start

    def perform_rule(self, rule: Rule, id: Optional[int] = None):
        """Apply rule to the current expression, creating a new step."""
        if id is not None:
            self.steps = self.steps[:id+1]
        else:
            id = len(self.steps) - 1

        e = self.last_expr
        ctx = Context(self.ctx)
        for step in self.steps:
            ctx.extend_substs(step.rule.get_substs())
        new_e = rule.eval(e, ctx)
        self.add_step(CalculationStep(self, rule, e, new_e, id+1))

    def get_by_label(self, label: Label) -> "StateItem":
        if label.empty():
            return self
        elif label.tail.empty():
            return self.steps[label.head]
        else:
            raise AssertionError("get_by_label: invalid label")

    def get_facts(self):
        return []


class CompFile:
    """A file containing multiple calculation items.

    ctx - initial context (book name or Context).
    name - name of the file.
    """
    def __init__(self, ctx: Union[Context, str], name: str):
        if isinstance(ctx, str):
            self.ctx = Context()
            self.ctx.load_book(ctx, upto=name)
        else:
            self.ctx = ctx
        self.name: str = name
        self.content: List[StateItem] = []

    def __str__(self):
        res = "File %s\n" % self.name
        for st in self.content:
            res += str(st)
        return res

    def get_context(self, index: int = -1) -> Context:
        ctx = Context(self.ctx)
        for item in (self.content if index == -1 else self.content[:index]):
            if isinstance(item, FuncDef):
                ctx.add_definition(item.eq)
                ctx.add_lemma(item.eq)
        return ctx

    def add_definition(self, funcdef: Union[str, Expr], *, conds: List[Union[str, Expr]] = None) -> FuncDef:
        if conds is not None:
            for i in range(len(conds)):
                if isinstance(conds[i], str):
                    conds[i] = parser.parse_expr(conds[i])
        else:
            conds = []

        ctx = self.get_context()
        if isinstance(funcdef, str):
            self.content.append(FuncDef(self, ctx, parser.parse_expr(funcdef), Conditions(conds)))
        elif isinstance(funcdef, Expr):
            self.content.append(FuncDef(self, ctx, funcdef, Conditions(conds)))
        else:
            raise NotImplementedError
        return self.content[-1]

    def add_calculation(self, calc: Union[str, Expr]) -> Calculation:
        ctx = self.get_context()
        if isinstance(calc, str):
            self.content.append(Calculation(self, ctx, parser.parse_expr(calc)))
        elif isinstance(calc, Expr):
            self.content.append(Calculation(self, ctx, calc))
        else:
            raise NotImplementedError
        return self.content[-1]

    def add_item(self, item: StateItem):
        self.content.append(item)

    def export(self):
        return {
            "name": self.name,
            "content": [item.export() for item in self.content]
        }


def parse_rule(item) -> Rule:
    if 'loc' in item:
        if item['loc'] == 'subterms':
            del item['loc']
            return rules.OnSubterm(parse_rule(item))
        else:
            loc = item['loc']
            del item['loc']
            if loc == '' or loc == '.':
                return parse_rule(item)
            else:
                return rules.OnLocation(parse_rule(item), loc)
    elif item['name'] == 'ExpandDefinition':
        func_name = item['func_name']
        return rules.ExpandDefinition(func_name=func_name)
    elif item['name'] == 'FoldDefinition':
        func_name = item['func_name']
        return rules.FoldDefinition(func_name=func_name)
    elif item['name'] == 'DerivIntExchange':
        return rules.DerivIntExchange()
    elif item['name'] == 'FullSimplify':
        return rules.FullSimplify()
    elif item['name'] == 'ElimInfInterval':
        a = Const(0)
        if 'a' in item:
            a = parser.parse_expr(item['a'])
        return rules.ElimInfInterval(a)
    elif item['name'] == 'Substitution':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'])
        return rules.Substitution(var_name, var_subst)
    elif item['name'] == 'SubstitutionInverse':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'])
        return rules.SubstitutionInverse(var_name, var_subst)
    elif item['name'] == 'IntegrationByParts':
        u = parser.parse_expr(item['u'])
        v = parser.parse_expr(item['v'])
        return rules.IntegrationByParts(u, v)
    elif item['name'] == 'Equation':
        new_expr = parser.parse_expr(item['new_expr'])
        old_expr = parser.parse_expr(item['old_expr']) if ('old_expr' in item) else None
        return rules.Equation(old_expr, new_expr)
    elif item['name'] == 'ApplyEquation':
        eq = parser.parse_expr(item['eq'])
        return rules.ApplyEquation(eq)
    elif item['name'] == 'ExpandPolynomial':
        return rules.ExpandPolynomial()
    elif item['name'] == 'SplitRegion':
        c = parser.parse_expr(item['c'])
        return rules.SplitRegion(c)
    elif item['name'] == 'IntegrateByEquation':
        lhs = parser.parse_expr(item['lhs'])
        return rules.IntegrateByEquation(lhs)
    elif item['name'] == 'LHopital':
        return rules.LHopital()
    elif item['name'] == 'ApplyInductHyp':
        return rules.ApplyInductHyp()
    elif item['name'] == 'DerivativeSimplify':
        return rules.DerivativeSimplify()
    elif item['name'] == 'IntegrateBothSide':
        return rules.IntegralEquation()
    elif item['name'] == 'LimitEquation':
        var = item['var']
        lim = parser.parse_expr(item['lim'])
        return rules.LimitEquation(var, lim)
    elif item['name'] == 'IntSumExchange':
        return rules.IntSumExchange()
    elif item['name'] == 'SimplifyPower':
        return rules.SimplifyPower()
    elif item['name'] == 'DerivEquation':
        var = item['var']
        return rules.DerivEquation(var)
    elif item['name'] == 'SolveEquation':
        solve_for = parser.parse_expr(item['solve_for'])
        return rules.SolveEquation(solve_for)
    elif item['name'] == 'VarSubsOfEquation':
        subst = item['subst']
        return rules.VarSubsOfEquation(subst)
    elif item['name'] == 'ApplyIdentity':
        source = parser.parse_expr(item['source'])
        target = parser.parse_expr(item['target'])
        return rules.ApplyIdentity(source, target)
    elif item['name'] == 'IndefiniteIntegralIdentity':
        return rules.IndefiniteIntegralIdentity()
    elif item['name'] == 'DefiniteIntegralIdentity':
        return rules.DefiniteIntegralIdentity()
    elif item['name'] == 'SeriesExpansionIdentity':
        index_var = item['index_var']
        old_expr = None
        if 'old_expr' in item:
            old_expr = parser.parse_expr(item['old_expr'])
        return rules.SeriesExpansionIdentity(old_expr=old_expr, index_var=index_var)
    elif item['name'] == 'SeriesEvaluationIdentity':
        return rules.SeriesEvaluationIdentity()
    elif item['name'] == 'ReplaceSubstitution':
        return rules.ReplaceSubstitution()
    else:
        print(item['name'], flush=True)
        raise NotImplementedError


def parse_step(parent: Calculation, item, id: int) -> CalculationStep:
    if item['type'] != 'CalculationStep':
        raise AssertionError('parse_step')

    rule = parse_rule(item['rule'])
    new_expr = parser.parse_expr(item['res'])
    old_expr = parser.parse_expr(item['old_expr']) if 'old_expr' in item else None
    return CalculationStep(parent, rule, old_expr, new_expr, id)


def parse_conds(item) -> Conditions:
    res = Conditions()
    if 'conds' in item:
        for subitem in item['conds']:
            res.add_condition(parser.parse_expr(subitem['cond']))
    return res


def parse_item(parent, item) -> StateItem:
    if item['type'] == 'FuncDef':
        conds = parse_conds(item)
        eq = parser.parse_expr(item['eq'])
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        return FuncDef(parent, ctx, eq, conds=conds)
    elif item['type'] == 'Calculation':
        start = parser.parse_expr(item['start'])
        ctx = parent.get_context() if isinstance(parent, CompFile) else parent.ctx
        res = Calculation(parent, ctx, start)
        for i, step in enumerate(item['steps']):
            res.add_step(parse_step(res, step, i))
        return res
    else:
        raise NotImplementedError("Unknown item type: %s" % item['type'])


def get_next_step_label(step: Union[Calculation, CalculationStep], label: Label) -> Label:
    if isinstance(step, Calculation):
        return Label(label.data + [0])
    elif isinstance(step, CalculationStep):
        return Label(label.data[:-1] + [label.data[-1] + 1])
    else:
        raise NotImplementedError

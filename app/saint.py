# Author: Runqing Xu

"""API for SAINT interactive integral CAS.

Equation-chain model: each calculation is a chain of steps where
each step stores old_expr = new_expr, justified by a rule.
"""

import os
import json
from flask import request
from flask.json import jsonify

from SAINT import rules, parser, latex, context, compstate
from app.app import app

dirname = os.path.dirname(__file__)
EXAMPLES_DIR = os.path.join(dirname, "../SAINT/examples")


def make_rule(rule_name, params):
    """Construct a Rule from name and params dict."""
    p = params or {}
    if rule_name == 'FullSimplify' or rule_name == 'simplify':
        return rules.FullSimplify()
    if rule_name == 'Substitution' or rule_name == 'substitute':
        return rules.Substitution(p['var_name'], p.get('g') or p.get('var_subst'))
    if rule_name == 'SubstitutionInverse' or rule_name == 'substitute_inverse':
        return rules.SubstitutionInverse(p['var_name'], p.get('g') or p.get('var_subst'))
    if rule_name == 'IntegrationByParts' or rule_name == 'integrate_by_parts':
        u = p.get('parts_u') or p.get('u')
        v = p.get('parts_v') or p.get('v')
        return rules.IntegrationByParts(u, v)
    if rule_name == 'DefiniteIntegralIdentity' or rule_name == 'definite_integral_identity':
        return rules.DefiniteIntegralIdentity()
    if rule_name == 'IndefiniteIntegralIdentity' or rule_name == 'indefinite_integral_identity':
        return rules.IndefiniteIntegralIdentity()
    if rule_name == 'RewriteTrigonometric' or rule_name == 'rewrite_trig':
        return rules.RewriteTrigonometric(p['rule'])
    if rule_name == 'ExpandPolynomial' or rule_name == 'expand_polynomial':
        return rules.ExpandPolynomial()
    if rule_name == 'UnfoldPower' or rule_name == 'unfold_power':
        return rules.UnfoldPower()
    if rule_name == 'ElimAbs' or rule_name == 'elim_abs':
        c = p.get('c')
        return rules.ElimAbs(parser.parse_expr(c)) if c else rules.ElimAbs()
    if rule_name == 'ElimInfInterval' or rule_name == 'elim_inf_interval':
        return rules.ElimInfInterval()
    if rule_name == 'SplitRegion' or rule_name == 'split_region':
        return rules.SplitRegion(p['c'])
    if rule_name == 'IntegrateByEquation' or rule_name == 'integrate_by_equation':
        return rules.IntegrateByEquation(parser.parse_expr(p['lhs']))
    if rule_name == 'Linearity' or rule_name == 'linearity':
        return rules.Linearity()
    if rule_name == 'CommonIntegral' or rule_name == 'common_integral':
        return rules.CommonIntegral()
    if rule_name == 'FunctionTable' or rule_name == 'function_table':
        return rules.FunctionTable()
    if rule_name == 'DerivativeSimplify' or rule_name == 'deriv_simplify':
        return rules.DerivativeSimplify()
    if rule_name == 'ReduceLimit' or rule_name == 'reduce_limit':
        return rules.ReduceLimit()
    if rule_name == 'LHopital' or rule_name == 'lhopital':
        return rules.LHopital()
    if rule_name == 'DerivIntExchange' or rule_name == 'deriv_int_exchange':
        return rules.DerivIntExchange()
    if rule_name == 'IntSumExchange' or rule_name == 'int_sum_exchange':
        return rules.IntSumExchange()
    if rule_name == 'Equation' or rule_name == 'equation':
        return rules.Equation(p.get('old_expr'), p['new_expr'])
    if rule_name == 'ApplyEquation' or rule_name == 'apply_equation':
        return rules.ApplyEquation(parser.parse_expr(p['eq']))
    if rule_name == 'SolveEquation' or rule_name == 'solve_equation':
        return rules.SolveEquation(parser.parse_expr(p['solve_for']))
    if rule_name == 'SeriesExpansionIdentity' or rule_name == 'series_expansion':
        index_var = p.get('index_var', 'n')
        old_expr = parser.parse_expr(p['old_expr']) if 'old_expr' in p else None
        return rules.SeriesExpansionIdentity(old_expr=old_expr, index_var=index_var)
    if rule_name == 'SeriesEvaluationIdentity' or rule_name == 'series_evaluation':
        return rules.SeriesEvaluationIdentity()
    if rule_name == 'MergeSummation' or rule_name == 'merge_summation':
        return rules.MergeSummation()
    if rule_name == 'SummationSimplify' or rule_name == 'summation_simplify':
        return rules.SummationSimplify()
    raise ValueError("Unknown rule: %s" % rule_name)


@app.route("/api/saint/files", methods=['POST'])
def saint_files():
    """List all .calc files."""
    files = []
    for root, dirs, filenames in os.walk(EXAMPLES_DIR):
        for f in filenames:
            if f.endswith('.calc'):
                rel = os.path.relpath(os.path.join(root, f), EXAMPLES_DIR)
                files.append(rel.replace('\\', '/').replace('.calc', ''))
    return jsonify({"files": sorted(files)})


@app.route("/api/saint/load", methods=['POST'])
def saint_load():
    """Load a .calc file and return problems.

    If a goal is an equation A = B, split into goal=A + target=B.
    """
    data = json.loads(request.get_data().decode('utf-8'))
    path = os.path.join(EXAMPLES_DIR, data['filename'] + '.calc')
    if not os.path.exists(path):
        return jsonify({"status": "error", "msg": "File not found"})
    from SAINT.calcfmt import load_calc_file
    d = load_calc_file(path)
    items = []
    for item in d.get('content', []):
        t = item.get('type', '')
        if t in ('header',):
            items.append({'type': 'header', 'name': item.get('name', ''), 'level': item.get('level', 1)})
            continue
        if t == 'table':
            items.append({'type': 'table', 'name': item.get('name', ''), 'table': dict(item.get('table', {}))})
            continue
        if t in ('theorem', 'definition', 'axiom'):
            try:
                e = parser.parse_expr(item.get('expr', ''))
                lx = latex.convert_expr(e)
            except:
                lx = item.get('expr', '')
            items.append({
                'type': t, 'expr': item.get('expr', ''), 'latex': lx,
                'category': item.get('category', ''), 'conds': item.get('conds', []),
            })
            continue
        if t == 'calculation':
            # All calculations are computation tasks (parser always sets goal)
            goal_str = item.get('goal', '')
            target_str = item.get('target')
            if not target_str and goal_str:
                try:
                    e = parser.parse_expr(goal_str)
                    if hasattr(e, 'is_equals') and e.is_equals():
                        goal_str = str(e.args[0])
                        target_str = str(e.args[1])
                except:
                    pass
            items.append({
                'type': 'calculation', 'name': item.get('name', ''),
                'goal': goal_str, 'target': target_str,
            })
            continue
    return jsonify({"items": items})


@app.route("/api/saint/parse", methods=['POST'])
def saint_parse():
    """Parse an expression string and return LaTeX."""
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        e = parser.parse_expr(data['expr'])
        return jsonify({
            "status": "ok",
            "text": str(e),
            "latex": latex.convert_expr(e)
        })
    except Exception as e:
        return jsonify({"status": "error", "msg": str(e)})


@app.route("/api/saint/apply", methods=['POST'])
def saint_apply():
    """Apply a rule, replaying the full calculation.

    Request:
        start: initial expression string
        steps: list of {rule, params} for previous steps
        rule: new rule name
        params: new rule parameters

    Response:
        status: ok/error
        calculation: full exported Calculation (start + all steps with old/new exprs)
    """
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        ctx = context.Context()
        ctx.load_book('base')

        start = parser.parse_expr(data['start'])
        f = compstate.CompFile(ctx, 'temp')
        calc = f.add_calculation(start)

        # Replay previous steps
        for step in data.get('steps', []):
            rule = make_rule(step['rule'], step.get('params', {}))
            calc.perform_rule(rule)

        # Apply new rule
        new_rule = make_rule(data['rule'], data.get('params', {}))
        calc.perform_rule(new_rule)

        return jsonify({
            "status": "ok",
            "calculation": calc.export(),
        })
    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({"status": "error", "msg": str(e)})


@app.route("/api/saint/verify", methods=['POST'])
def saint_verify():
    """Check if two expressions are equal by normalization."""
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        ctx = context.Context()
        ctx.load_book('base')
        e1 = parser.parse_expr(data['expr1'])
        e2 = parser.parse_expr(data['expr2'])
        from SAINT.poly import normalize
        match = normalize(e1, ctx.get_conds()) == normalize(e2, ctx.get_conds())
        return jsonify({"status": "ok", "match": match})
    except Exception as e:
        return jsonify({"status": "error", "msg": str(e)})

@app.route("/api/saint/save", methods=['POST'])
def saint_save():
    """Save items back to a .calc file."""
    data = json.loads(request.get_data().decode('utf-8'))
    path = os.path.join(EXAMPLES_DIR, data['filename'] + '.calc')
    from SAINT.calcfmt import export_calc
    file_data = {
        'name': data.get('name', ''),
        'imports': data.get('imports', []),
        'description': data.get('description', ''),
        'content': data.get('items', []),
    }
    text = export_calc(file_data)
    with open(path, 'w', encoding='utf-8') as f:
        f.write(text)
    return jsonify({"status": "ok"})


@app.route("/api/saint/suggest", methods=['POST'])
def saint_suggest():
    """Suggest applicable rules for the current expression.

    Tries each rule and returns those that produce a change.
    Works for both definite and indefinite integrals.
    Also detects substitution and integration-by-parts candidates.
    """
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        ctx = context.Context()
        ctx.load_book('base')
        e = parser.parse_expr(data['expr'])
        suggestions = []

        # 1. Parameter-free rules: try each, keep if it changes the expression
        param_free = [
            ('simplify', 'Simplify'),
            ('definite_integral_identity', 'Definite Integral ID'),
            ('indefinite_integral_identity', 'Indefinite Integral ID'),
            ('expand_polynomial', 'Expand Polynomial'),
            ('unfold_power', 'Unfold Power'),
            ('elim_inf_interval', 'Elim Infinity'),
            ('int_sum_exchange', 'Exchange Integral/Sum'),
            ('linearity', 'Linearity'),
            ('common_integral', 'Common Integral'),
            ('function_table', 'Function Table'),
        ]
        for rule_name, label in param_free:
            try:
                rule = make_rule(rule_name, {})
                new_e = rule.eval(e, ctx)
                if str(new_e) != str(e):
                    suggestions.append({
                        'rule': rule_name, 'params': {}, 'label': label,
                        'result': str(new_e), 'latex': latex.convert_expr(new_e),
                    })
            except:
                pass

        # 2. Elim abs (might need param c, try without first)
        try:
            rule = make_rule('elim_abs', {})
            new_e = rule.eval(e, ctx)
            if str(new_e) != str(e):
                suggestions.append({
                    'rule': 'elim_abs', 'params': {}, 'label': 'Elim Abs',
                    'result': str(new_e), 'latex': latex.convert_expr(new_e),
                })
        except:
            pass

        # 3. Detect substitution candidates
        # Find integrals in the expression
        from SAINT.expr import Var, Const, Op, Fun, Integral, IndefiniteIntegral, Symbol, collect_spec_expr, OP, FUN, CONST
        integrals = e.separate_integral() if hasattr(e, 'separate_integral') else []
        for integral_expr, loc in integrals:
            if hasattr(integral_expr, 'body') and hasattr(integral_expr, 'var'):
                body = integral_expr.body
                var_name = integral_expr.var

                # Look for linear patterns a*x+b inside functions
                x_sym = Symbol('f', [FUN])
                linear_patterns = [
                    (Symbol('a', [CONST]) * Var(var_name) + Symbol('b', [CONST]), 'a*x+b'),
                    (Symbol('a', [CONST]) * Var(var_name), 'a*x'),
                    (Var(var_name) + Symbol('b', [CONST]), 'x+b'),
                    (Var(var_name) - Symbol('b', [CONST]), 'x-b'),
                ]
                seen_substs = set()
                for pat, desc in linear_patterns:
                    matches = collect_spec_expr(body, pat)
                    for m in matches:
                        subst_str = str(m)
                        if subst_str not in seen_substs:
                            seen_substs.add(subst_str)
                            # Try the substitution
                            try:
                                rule = make_rule('substitute', {'var_name': 'u', 'g': subst_str})
                                new_e = rule.eval(e, ctx)
                                if str(new_e) != str(e):
                                    suggestions.append({
                                        'rule': 'substitute',
                                        'params': {'var_name': 'u', 'g': subst_str},
                                        'label': 'Substitute u = %s' % subst_str,
                                        'result': str(new_e), 'latex': latex.convert_expr(new_e),
                                    })
                            except:
                                pass

                # Look for power patterns x^n
                power_pat = Var(var_name) ** Symbol('n', [CONST])
                matches = collect_spec_expr(body, power_pat)
                for m in matches:
                    subst_str = str(m)
                    if subst_str not in seen_substs and subst_str != var_name:
                        seen_substs.add(subst_str)
                        try:
                            rule = make_rule('substitute', {'var_name': 'u', 'g': subst_str})
                            new_e = rule.eval(e, ctx)
                            if str(new_e) != str(e):
                                suggestions.append({
                                    'rule': 'substitute',
                                    'params': {'var_name': 'u', 'g': subst_str},
                                    'label': 'Substitute u = %s' % subst_str,
                                    'result': str(new_e), 'latex': latex.convert_expr(new_e),
                                })
                        except:
                            pass

                # Look for exp(a*x) patterns
                exp_pat = Fun('exp', Symbol('a', [CONST]) * Var(var_name))
                matches = collect_spec_expr(body, exp_pat)
                for m in matches:
                    subst_str = str(m)
                    if subst_str not in seen_substs:
                        seen_substs.add(subst_str)
                        try:
                            rule = make_rule('substitute', {'var_name': 'u', 'g': subst_str})
                            new_e = rule.eval(e, ctx)
                            if str(new_e) != str(e):
                                suggestions.append({
                                    'rule': 'substitute',
                                    'params': {'var_name': 'u', 'g': subst_str},
                                    'label': 'Substitute u = %s' % subst_str,
                                    'result': str(new_e), 'latex': latex.convert_expr(new_e),
                                })
                        except:
                            pass

                # 4. Integration by parts: if integrand is a product
                if body.ty == OP and body.op == '*':
                    factors = []
                    def collect_factors(e):
                        if e.ty == OP and e.op == '*':
                            collect_factors(e.args[0])
                            collect_factors(e.args[1])
                        else:
                            factors.append(e)
                    collect_factors(body)
                    # Try each factor as u, rest as v'
                    for i, f in enumerate(factors):
                        u = f
                        v_prime = Const(1)
                        for j, g in enumerate(factors):
                            if j != i:
                                v_prime = v_prime * g
                        try:
                            rule = make_rule('integrate_by_parts', {
                                'parts_u': str(u), 'parts_v': str(v_prime)
                            })
                            new_e = rule.eval(e, ctx)
                            if str(new_e) != str(e):
                                suggestions.append({
                                    'rule': 'integrate_by_parts',
                                    'params': {'parts_u': str(u), 'parts_v': str(v_prime)},
                                    'label': 'By Parts: u=%s, v\'=%s' % (str(u), str(v_prime)),
                                    'result': str(new_e), 'latex': latex.convert_expr(new_e),
                                })
                        except:
                            pass

        # 5. Series expansion (for expressions with known series)
        try:
            rule = make_rule('series_expansion', {'index_var': 'n'})
            new_e = rule.eval(e, ctx)
            if str(new_e) != str(e):
                suggestions.append({
                    'rule': 'series_expansion', 'params': {'index_var': 'n'},
                    'label': 'Series Expansion',
                    'result': str(new_e), 'latex': latex.convert_expr(new_e),
                })
        except:
            pass

        return jsonify({"status": "ok", "suggestions": suggestions})
    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({"status": "error", "msg": str(e)})

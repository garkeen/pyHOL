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
    """Load a .calc file and return its problems."""
    data = json.loads(request.get_data().decode('utf-8'))
    path = os.path.join(EXAMPLES_DIR, data['filename'] + '.calc')
    if not os.path.exists(path):
        return jsonify({"status": "error", "msg": "File not found"})
    from SAINT.calcfmt import load_calc_file
    calc_file = load_calc_file(path)
    d = calc_file.as_dict()
    problems = []
    for item in d.get('content', []):
        problems.append({
            'name': item.get('name', ''),
            'goal': item.get('problem', ''),
            'target': item.get('target'),
        })
    return jsonify({"problems": problems})


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

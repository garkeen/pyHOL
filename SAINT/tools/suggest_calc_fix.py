"""Debug a single exercise replay.

Run:  python SAINT/tools/suggest_calc_fix.py "BOOK/Exercise N"
"""
import sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from SAINT import rules, parser
from SAINT.context import Context
from SAINT.calcfmt import load_calc_file
from SAINT.poly import normalize as pnormalize
from SAINT.run_slagle import test_cases

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")


def equiv(a, b, ctx):
    try:
        a = rules.FullSimplify().eval(a, ctx)
        b = rules.FullSimplify().eval(b, ctx)
        return pnormalize(a, ctx.get_conds()) == pnormalize(b, ctx.get_conds())
    except Exception:
        return None


def run(book, name):
    filename = book + '.calc'
    data = load_calc_file(os.path.join(EXAMPLES, filename))
    target_s = test_cases[book][name]
    target = parser.parse_expr(target_s)
    for item in data["content"]:
        if not isinstance(item, dict) or "calc" not in item or item["name"] != name:
            continue
        problem = parser.parse_expr(item['problem'])
        ctx = Context(); ctx.load_book('base')
        current = problem
        print('%s / %s  target=%s' % (book, name, target_s))
        steps = item['calc']
        for i, step in enumerate(steps):
            rule_name = step.get('reason') or step.get('rule')
            try:
                result = rules.apply_step(current, step, ctx, [])
                current = result
            except Exception as ex:
                msg = str(ex).splitlines()[0] if str(ex) else type(ex).__name__
                print('  [%d] %s FAILS: %s' % (i, rule_name, msg))
                if current != target:
                    eq = equiv(current, target, ctx)
                    print('  -> equiv at this point: %s' % eq)
                return
            ok = pnormalize(current, ctx.get_conds()) == pnormalize(target, ctx.get_conds())
            tag = 'MATCH' if ok else ''
            print('  [%d] %s -> %s %s' % (i, rule_name, current, tag))
        eq = equiv(current, target, ctx)
        print('  final equiv: %s  match=%s' % (eq, ok))
        return


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        parts = arg.split('/')
        name = parts[-1]
        book = '/'.join(parts[:-1])
        run(book, name)

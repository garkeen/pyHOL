"""Classify each replay failure: engine-bug vs stale-proof.

Run:  python SAINT/tools/classify_fails.py
"""
import sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from SAINT import rules, parser
from SAINT.context import Context
from SAINT.calcfmt import load_calc_file
from SAINT.poly import normalize

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")

BOOKS = {
    'MIT/2013': ['Exercise 5', 'Exercise 10', 'Exercise 11', 'Exercise 21', 'Exercise 22'],
    'UCDAVIS/usubstitution': ['Exercise 6', 'Exercise 7', 'Exercise 11', 'Exercise 13',
                              'Exercise 14', 'Exercise 15', 'Exercise 16'],
    'UCDAVIS/Exponentials': ['Exercise 5', 'Exercise 7', 'Exercise 8'],
    'UCDAVIS/Trigonometric': ['Exercise 3', 'Exercise 4', 'Exercise 5', 'Exercise 8'],
    'UCDAVIS/Byparts': ['Exercise 8', 'Exercise 9'],
    'UCDAVIS/LogAndArctangent': ['Exercise 5', 'Exercise 8', 'Exercise 14', 'Exercise 15',
                                 'Exercise 16', 'Exercise 20'],
    'UCDAVIS/PartialFraction': ['Exercise 1', 'Exercise 2', 'Exercise 3', 'Exercise 4',
                                'Exercise 5', 'Exercise 6', 'Exercise 7', 'Exercise 8'],
}


def fullsimpl(e, ctx):
    try:
        return normalize(rules.FullSimplify().eval(e, ctx), ctx.get_conds())
    except Exception:
        return None


def classify(book, name):
    data = load_calc_file(os.path.join(EXAMPLES, book + '.calc'))
    item = next(it for it in data['content'] if it.get('name') == name)
    ctx = Context(); ctx.load_book('base')
    current = parser.parse_expr(item['problem'])
    prev = []
    fail_step = None
    fail_msg = None
    for i, step in enumerate(item['calc']):
        try:
            current = rules.apply_step(current, step, ctx, prev)
            prev.append(current)
        except Exception as ex:
            fail_step = i
            fail_msg = str(ex).splitlines()[0] if str(ex) else type(ex).__name__
            break
    if fail_msg is None:
        fail_msg = 'complete'
    recorded = item['calc'][fail_step].get('text') if fail_step is not None and fail_step < len(item['calc']) else None
    rec_expr = parser.parse_expr(recorded) if recorded else None

    if fail_step is None and 'target' in item:
        target = parser.parse_expr(item['target'])
        fs_cur = fullsimpl(current, ctx)
        fs_tgt = fullsimpl(target, ctx)
        if fs_cur is not None and fs_tgt is not None:
            equiv = fs_cur == fs_tgt
            verdict = 'STALE-PROOF' if equiv else 'ENGINE-BUG'
        else:
            equiv, verdict = 'n/a', 'UNKNOWN'
        print("%-24s %-28s [final] %-10s equiv=%s  => %s" % (
            book, name, 'final-answer', equiv, verdict))
        print("    final current: %s" % current)
        print("    target       : %s" % item['target'])
        return

    if rec_expr is not None:
        fs_cur = fullsimpl(current, ctx)
        fs_rec = fullsimpl(rec_expr, ctx)
        if fs_cur is not None and fs_rec is not None:
            equiv = fs_cur == fs_rec
            verdict = 'STALE-PROOF' if equiv else 'ENGINE-BUG'
        else:
            equiv = 'n/a'
            verdict = 'UNKNOWN'
    else:
        equiv = 'n/a'
        verdict = 'UNKNOWN'

    print("%-24s %-28s [%-2s] %-10s equiv=%s  => %s" % (
        book, name, fail_step if fail_step is not None else '-', fail_msg.split(':')[0][:10], equiv, verdict))
    if rec_expr is not None:
        print("    pre-fail current: %s" % current)
        print("    recorded text   : %s" % recorded)
    else:
        print("    pre-fail current: %s" % current)
        if 'target' in item:
            print("    target          : %s" % item['target'])


if __name__ == '__main__':
    for book, names in BOOKS.items():
        for name in names:
            try:
                classify(book, name)
            except Exception as ex:
                print("%-24s %-28s CRASH: %s" % (book, name, ex))

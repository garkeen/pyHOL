# Thm 构造私有化落锁（ARCHITECTURE_AUDIT.md §7.3）。
#
# 信任模型的墙：15 推理原语 + 3 假设规则（sorry / axiom / oracle）是
# 仅有的凭空构造定理的入口。kernel 之外的生产代码不得裸调 Thm(...)：
#
#   - 开洞语句走 tactic.goal.Goal（内部经 Thm.sorry），或语法层
#     前门直接走 Thm.sorry（syntax 低于 tactic，不许 import tactic.goal）；
#   - 公理装载走 core.defcheck.mk_axiom（内部经 Thm.axiom）；
#   - level-0 宏 eval 走 kernel.thm.oracle_thm（具名洞）；
#   - 其余一律经 ProofTerm 推导后取 .th，或引用已有 Thm。
#
# 白名单为空。tests/（断言需要构造期望值）与 kernel/（墙内）除外。

import ast
import io
import os
import unittest

KERNEL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(KERNEL_DIR)

SKIP_DIRS = {'__pycache__', '.cache', '.pytest_cache', '.git', 'build', 'dist'}


def raw_thm_call_lines(path):
    """Line numbers of raw Thm(...) constructor calls in the file.

    Named constructors (Thm.sorry / Thm.axiom / Thm.assume / ...) are
    Attribute calls and pass; only the bare Name call Thm(...) is the
    privatized entry."""
    tree = ast.parse(io.open(path, encoding='utf-8').read())
    lines = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == 'Thm':
            lines.append(node.lineno)
    return lines


class ThmPrivatizationTest(unittest.TestCase):
    def testNoRawThmConstructionOutsideKernel(self):
        """No raw Thm(...) constructor call outside kernel/ production
        code: the rule set is closed at 15 primitives + 3 hole
        constructors, and the lint makes the naming convention a
        construction requirement."""
        offenders = []
        for dirpath, dirnames, filenames in os.walk(ROOT):
            rel_dir = os.path.relpath(dirpath, ROOT).replace(os.sep, '/')
            if rel_dir == 'kernel' or rel_dir.startswith('kernel/'):
                # Inside the wall: skip the whole subtree.
                dirnames[:] = []
                continue
            # tests/ dirs are assertion harnesses, not production logic.
            if rel_dir == 'tests' or rel_dir.endswith('/tests') \
                    or '/tests/' in rel_dir + '/':
                dirnames[:] = []
                continue
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS
                           and not d.startswith('.')]
            for fn in filenames:
                if not fn.endswith('.py'):
                    continue
                path = os.path.join(dirpath, fn)
                lines = raw_thm_call_lines(path)
                if lines:
                    rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
                    offenders.append('%s: lines %s' % (rel, lines))
        self.assertEqual(offenders, [])


if __name__ == "__main__":
    unittest.main()

# util 分家落锁（ARCHITECTURE_AUDIT.md §9.4）。
#
# util/ 的职责是纯工具（name / typecheck / unionfind）——kernel 的合法
# 伙伴，不依赖任何项目模块。项工具（function/list/set/string，语法糖
# 项构造器）已迁 syntax/，多项式（poly，nat/real/integer 的项工具）已
# 迁 theories/poly.py。本测试断住这条界：util/ 任何文件都不得 import
# kernel/syntax/theories/core/method/solvers，否则分家等于白做。
#
# 白名单为空。util/tests 是断言夹具，不在扫描范围。

import ast
import io
import os
import unittest

UTIL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(UTIL_DIR)

FORBIDDEN = ('kernel', 'syntax', 'theories', 'core', 'method', 'solvers')


def imports_of(path):
    tree = ast.parse(io.open(path, encoding='utf-8').read())
    mods = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            mods.update(a.name for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            mods.add(node.module)
    return mods


class UtilPurityTest(unittest.TestCase):
    def testUtilDoesNotImportProjectModules(self):
        """util/ must not import kernel/syntax/theories/core/method/solvers
        (audit §9.4: the 5 term-tool files were sunk out; util is now pure
        structure tools, the kernel's only legal project partner)."""
        offenders = []
        for dirpath, _, filenames in os.walk(UTIL_DIR):
            if os.path.basename(dirpath) in ('tests', '__pycache__'):
                continue
            for fn in filenames:
                if not fn.endswith('.py'):
                    continue
                path = os.path.join(dirpath, fn)
                mods = imports_of(path)
                bad = [m for m in mods
                       if any(m == p or m.startswith(p + '.') for p in FORBIDDEN)]
                if bad:
                    rel = os.path.relpath(path, ROOT).replace(os.sep, '/')
                    offenders.append('%s: %s' % (rel, bad))
        self.assertEqual(offenders, [])


if __name__ == "__main__":
    unittest.main()

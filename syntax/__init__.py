# syntax - Parsing, printing, and term-level sugar.
#
# Importing this package installs the syntax-level sugar on Term:
# numeral/arithmetic methods and operator overloads (syntax.numeral),
# and recognition of the base logical constants (syntax.logicops).
# The constants themselves live in library theories (nat/int/real,
# logic_base); the kernel contains none of this.

from syntax import numeral  # noqa: F401  (installs Term sugar)
from syntax import logicops  # noqa: F401  (installs Term sugar)

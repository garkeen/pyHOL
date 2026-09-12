# syntax - Parsing, printing, and term-level sugar.
#
# Importing this package installs the numeral/arithmetic sugar and
# operator overloads on Term (syntax.numeral). The logic-constant
# recognition predicates live in syntax.logicops as plain functions;
# callers import them explicitly, so there is no import-order side
# effect on Term. The constants themselves live in library theories
# (nat/int/real, logic_base); the kernel contains none of this.

from syntax import numeral  # noqa: F401  (installs Term sugar)

"""SAINT: a self-contained, data-driven symbolic integration engine.

The engine mechanics live in this package; the mathematical facts live as
data (examples/base.calc) rather than as hardcoded behavior.
"""

from SAINT import expr
from SAINT import rules
from SAINT import context
from SAINT import run_slagle

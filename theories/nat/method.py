# theories/nat/method.py - Nat methods, auto-generated from macros.
# Each macro is exposed as an interactive method through the standard
# register_macro_method channel (checked apply_macro entry point).

from core.method import register_macro_method

register_macro_method('nat_norm', limit='nat_nat_power_def_1')
register_macro_method('nat_const_ineq', limit='bit1_neq_one')
register_macro_method('nat_const_less_eq', limit='bit1_neq_one')
register_macro_method('nat_const_less', limit='bit1_neq_one')

# domains/function/__init__.py
# function/conv.py registers fun_upd_eval macro directly (no separate macro file needed),
# but we also have macro.py with additional function macros.
from theories.function import conv  # noqa: F401
from theories.function import macro  # noqa: F401

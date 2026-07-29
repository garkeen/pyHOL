# domains/function/__init__.py
# function/conv.py registers fun_upd_eval macro directly (no separate macro file needed),
# but we also have macro.py with additional function macros.
from domains.function import conv  # noqa: F401
from domains.function import macro  # noqa: F401

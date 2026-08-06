"""Human-readable .calc format for integral calculation tasks.

This is the text representation of an integral proof task.  Following the
spirit of .pyhol files, a .calc file keeps only the *process* (the sequence
of rules and their parameters), not the *results*: the engine re-derives
every intermediate expression from the starting problem.

Grammar (informal)::

    theory  <name>
    imports  <book>[, <book> ...]

    problem  "<name>"
      goal  <expr>                 # required: the problem to prove
      target  <expr>               # optional: expected final value
      cond  <expr>                 # optional: repeated, preconditions
      calc
        <rule>  [key = value, ...] [, at <location>]
        ...
      qed

A step line uses the same shape as .pyhol steps: ``<method> [args]``.
The first step of every calculation (the starting expression) is implicit.
"""

import os
import re
from typing import Dict, List, Optional

from SAINT import parser


REASON_TO_METHOD = {
    "Simplification": "simplify",
    "Substitution": "substitute",
    "Substitution inverse": "substitute_inverse",
    "Integrate by parts": "integrate_by_parts",
    "Rewrite": "rewrite",
    "Rewrite fraction": "rewrite_fraction",
    "Rewrite trigonometric": "rewrite_trigonometric",
    "Unfold power": "unfold_power",
    "Split region": "split_region",
    "Elim abs": "elim_abs",
    "Eliminate infinity": "elim_infinity",
    "Solve equation": "solve_equation",
    "Initial": "initial",
}

METHOD_TO_REASON = {v: k for k, v in REASON_TO_METHOD.items()}


class CalcItem:
    """One problem in a .calc file, mirroring the item shape."""

    def __init__(self, name: str, problem: str, target: Optional[str] = None,
                 conds: Optional[List[str]] = None, calc: Optional[List[dict]] = None):
        self.name = name
        self.problem = problem
        self.target = target
        self.conds = conds or []
        self.calc = calc or []

    def as_dict(self) -> dict:
        """Convert to the item dict consumed by rules.check_item."""
        res = {
            "name": self.name,
            "problem": self.problem,
        }
        if self.target is not None:
            res["target"] = self.target
        if self.conds:
            res["conds"] = list(self.conds)
        res["calc"] = list(self.calc)
        return res


class CalcFile:
    """A .calc file: theory header + list of problems."""

    def __init__(self, name: str = "", imports: Optional[List[str]] = None,
                 description: str = "", content: Optional[List[CalcItem]] = None):
        self.name = name
        self.imports = imports or []
        self.description = description
        self.content = content or []

    def as_dict(self) -> dict:
        return {
            "name": self.name,
            "imports": list(self.imports),
            "description": self.description,
            "content": [item.as_dict() for item in self.content],
        }


def _step_params(step: dict) -> dict:
    """Collect the params (and location) of a step into printable key=value items."""
    parts = []
    for key, value in step.get("params", {}).items():
        parts.append("%s = %s" % (key, value))
    if "location" in step and step["location"] not in ("", "."):
        parts.append("at %s" % step["location"])
    return parts


def _format_step(step: dict) -> str:
    reason = step["reason"]
    method = REASON_TO_METHOD.get(reason, reason)
    args = _step_params(step)
    if args:
        return "    %s  %s" % (method, ", ".join(args))
    return "    %s" % method


def _parse_step_params(param_pairs: List[str]) -> dict:
    """Parse 'key = value' pairs plus an optional trailing 'at loc'."""
    params = {}
    location = ""
    for item in param_pairs:
        item = item.strip()
        if not item:
            continue
        if item.startswith("at "):
            location = item[3:].strip()
            continue
        if "=" in item:
            key, _, value = item.partition("=")
            params[key.strip()] = value.strip()
        else:
            raise ValueError("Invalid step parameter: %r" % item)
    return params, location


def _split_top_level(s: str, sep: str = ",") -> List[str]:
    """Split on sep, ignoring separators inside parentheses."""
    res = []
    depth = 0
    cur = ""
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == sep and depth == 0:
            res.append(cur)
            cur = ""
        else:
            cur += ch
    res.append(cur)
    return res


def _parse_step_line(line: str) -> Optional[dict]:
    line = line.strip()
    if not line or line.startswith("--"):
        return None
    line = line.split("--", 1)[0].rstrip()  # drop trailing in-line comment
    method, _, rest = line.partition(" ")
    method = method.strip()
    reason = METHOD_TO_REASON.get(method, method)
    step = {"reason": reason}
    if rest:
        params, location = _parse_step_params(_split_top_level(rest))
        if params:
            step["params"] = params
        if location:
            step["location"] = location
    return step


def export_calc(file_data: dict) -> str:
    """Export a book dict (item shape) to .calc text."""
    lines = []
    name = file_data.get("name", "")
    if name:
        lines.append("theory  %s" % name)
    imports = file_data.get("imports", [])
    if imports:
        lines.append("imports  %s" % ", ".join(imports))
    desc = file_data.get("description", "")
    if desc:
        lines.append('description  "%s"' % desc)
    lines.append("")

    for item in file_data.get("content", []):
        item_name = item.get("name", "")
        problem = item.get("problem", "")
        lines.append('problem  "%s"' % item_name)
        if "goal" in item and item.get("goal"):
            lines.append("  goal  %s" % item["goal"])
        elif problem:
            lines.append("  goal  %s" % problem)
        if item.get("target"):
            lines.append("  target  %s" % item["target"])
        for cond in item.get("conds", []):
            lines.append("  cond  %s" % cond)
        lines.append("  calc")
        for step in item.get("calc", []):
            if step.get("reason") == "Initial":
                continue
            lines.append(_format_step(step))
        lines.append("  qed")
        lines.append("")

    return "\n".join(lines)


def parse_calc(text: str) -> CalcFile:
    """Parse .calc text into a CalcFile."""
    lines = text.split("\n")
    result = CalcFile()
    cur_item: Optional[CalcItem] = None
    in_calc = False

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i].rstrip()
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            i += 1
            continue

        if in_calc:
            if stripped == "qed":
                in_calc = False
                i += 1
                continue
            step = _parse_step_line(stripped)
            if step is not None:
                cur_item.calc.append(step)
            i += 1
            continue

        if line.startswith("theory "):
            result.name = line[7:].strip()
        elif line.startswith("imports "):
            imports_str = line[8:].strip()
            result.imports = [s.strip() for s in imports_str.split(",") if s.strip()]
        elif line.startswith("imports"):
            result.imports = []
        elif line.startswith("description "):
            desc = line[12:].strip()
            if desc.startswith('"') and desc.endswith('"'):
                desc = desc[1:-1]
            result.description = desc
        elif line.startswith("problem "):
            name = line[8:].strip().strip('"')
            cur_item = CalcItem(name=name, problem="")
            result.content.append(cur_item)
        elif line.startswith("  goal ") and cur_item is not None:
            cur_item.problem = line[7:].strip()
        elif line.startswith("  target ") and cur_item is not None:
            cur_item.target = line[9:].strip()
        elif line.startswith("  cond ") and cur_item is not None:
            cur_item.conds.append(line[7:].strip())
        elif stripped == "calc" and cur_item is not None:
            in_calc = True
        i += 1

    return result


def load_calc_file(path: str) -> CalcFile:
    """Load a .calc file from disk."""
    with open(path, "r", encoding="utf-8") as f:
        return parse_calc(f.read())


# ---------------------------------------------------------------------------
# Theory-book format (.calc for the mathematical fact library, e.g. base.calc)
# ---------------------------------------------------------------------------
#
#     theory  base
#
#     header  "Common integrals"  level = 1
#
#     axiom  "(INT x. c) = c * x + SKOLEM_CONST(C)"
#     axiom  "(INT x. x / (a * x ^ 2 + b)) = ..."  conds = [a != 0]
#     axiom  "exp(a) ^ b = exp(a * b)"  attributes = [simplify]
#     axiom  "n = n * (sin(x)^2 + cos(x)^2)"  attributes = [one_shot]
#                                              category = trigonometric  rule = TR0
#     definition  "cosh(x) = (exp(x) + exp(-x)) / 2"
#
#     table  sin
#       "-(pi / 2)" = "-1"
#       "0" = "0"
#     endtable
#
# List values are written as [v1; v2].  The grammar reuses the loose
# line-oriented style of the exercise-book format.

_THEORY_KEYS = ("conds", "attributes", "category", "rule", "const_vars", "level")


def _format_list(values: List[str]) -> str:
    if not values:
        return "[]"
    return "[" + "; ".join(values) + "]"


def _parse_list(text: str) -> List[str]:
    text = text.strip()
    if text.startswith("[") and text.endswith("]"):
        text = text[1:-1]
    return [s.strip() for s in text.split(";") if s.strip()]


def export_theory(file_data: dict) -> str:
    """Export a theory book dict (item shape) to .calc text."""
    lines = []
    name = file_data.get("name", "")
    if name:
        lines.append("theory  %s" % name)
    imports = file_data.get("imports", [])
    if imports:
        lines.append("imports  %s" % ", ".join(imports))
    lines.append("")

    for item in file_data.get("content", []):
        t = item.get("type")
        if t == "header":
            lines.append('header  "%s"  level = %s' % (item["name"], item.get("level", 1)))
        elif t in ("axiom", "problem", "theorem"):
            parts = ['%s  "%s"' % (t, item["expr"])]
            if item.get("conds"):
                parts.append("conds = %s" % _format_list(item["conds"]))
            if item.get("attributes"):
                parts.append("attributes = %s" % _format_list(item["attributes"]))
            if item.get("category"):
                parts.append("category = %s" % item["category"])
            if item.get("rule"):
                parts.append("rule = %s" % item["rule"])
            if item.get("const_vars"):
                parts.append("const_vars = %s" % _format_list(item["const_vars"]))
            lines.append("  ".join(parts))
        elif t == "definition":
            lines.append('definition  "%s"' % item["expr"])
        elif t == "table":
            lines.append("table  %s" % item["name"])
            for k, v in item.get("table", {}).items():
                lines.append('  "%s" = "%s"' % (k, v))
            lines.append("endtable")
        else:
            raise ValueError("Unknown theory item type: %r" % t)

    return "\n".join(lines)


def parse_theory(text: str) -> dict:
    """Parse .calc theory text into a book dict (item shape).

    Returns {"name": ..., "imports": [...], "content": [items...]}.
    """
    result = {"name": "", "imports": [], "content": []}
    cur_table = None
    for raw in text.split("\n"):
        line = raw.rstrip()
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if cur_table is not None:
            if stripped == "endtable":
                cur_table = None
                continue
            if "=" in stripped:
                k, _, v = stripped.partition("=")
                cur_table[k.strip().strip('"')] = v.strip().strip('"')
            continue
        if line.startswith("theory "):
            result["name"] = line[7:].strip()
        elif line.startswith("imports "):
            result["imports"] = [s.strip() for s in line[8:].strip().split(",") if s.strip()]
        elif line.startswith('header '):
            rest = line[7:].strip()
            item = {"type": "header", "name": "", "level": 1}
            m = re.match(r'"([^"]*)"', rest)
            if m:
                item["name"] = m.group(1)
            lm = re.search(r"level\s*=\s*(\d+)", rest)
            if lm:
                item["level"] = int(lm.group(1))
            result["content"].append(item)
        elif line.startswith("definition "):
            expr = line[11:].strip()
            if expr.startswith('"') and expr.endswith('"'):
                expr = expr[1:-1]
            result["content"].append({"type": "definition", "expr": expr})
        elif line.startswith("table "):
            cur_table = {}
            result["content"].append({"type": "table", "name": line[6:].strip(), "table": cur_table})
        else:
            parts = stripped.split("  ")
            t = parts[0].strip()
            if t not in ("axiom", "problem", "theorem"):
                raise ValueError("Unknown theory line: %r" % stripped)
            body = " ".join(p.strip() for p in parts[1:] if p.strip())
            m = re.match(r'"([^"]*)"', body)
            if not m:
                raise ValueError("Expected quoted expr in: %r" % stripped)
            item = {"type": t, "expr": m.group(1)}
            rest = body[m.end():]
            for km in re.finditer(r"(\w+)\s*=\s*(\[[^\]]*\]|[^\s]+)", rest):
                key, value = km.group(1), km.group(2)
                if key == "conds":
                    item["conds"] = _parse_list(value)
                elif key == "attributes":
                    item["attributes"] = _parse_list(value)
                elif key == "const_vars":
                    item["const_vars"] = _parse_list(value)
                elif key in ("category", "rule"):
                    item[key] = value.strip('"')
            result["content"].append(item)
    return result

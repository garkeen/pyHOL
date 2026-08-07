"""Human-readable .calc format - unified parser.

A .calc file contains any mix of:
  - definition / theorem    (library items, loaded into context)
  - header / table           (organization)
  - calculation              (computation task: has a goal expression to compute)

One parser. One format. No special cases.
"""

import re
import os
from typing import Optional, List


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


def _parse_list(s):
    s = s.strip().strip("[]")
    return [x.strip().strip('"') for x in s.split(";")] if s else []


def _split_top_level(s, sep=","):
    res, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{": depth += 1
        elif ch in ")]}": depth -= 1
        if ch == sep and depth == 0:
            res.append(cur); cur = ""
        else:
            cur += ch
    res.append(cur)
    return res


def _parse_step_line(line):
    line = line.strip()
    if not line or line.startswith("--"):
        return None
    line = line.split("--", 1)[0].rstrip()
    method, _, rest = line.partition(" ")
    reason = METHOD_TO_REASON.get(method.strip(), method.strip())
    step = {"reason": reason}
    if rest:
        params, location = {}, ""
        for item in _split_top_level(rest):
            item = item.strip()
            if not item: continue
            if item.startswith("at "):
                location = item[3:].strip()
            elif "=" in item:
                k, _, v = item.partition("=")
                params[k.strip()] = v.strip()
            else:
                raise ValueError("Bad param: %r" % item)
        if params: step["params"] = params
        if location: step["location"] = location
    return step


def _format_step(step):
    reason = step["reason"]
    method = REASON_TO_METHOD.get(reason, reason)
    parts = ["%s = %s" % (k, v) for k, v in step.get("params", {}).items()]
    loc = step.get("location", "")
    if loc and loc != ".": parts.append("at %s" % loc)
    return "    %s%s" % (method, ("  " + ", ".join(parts)) if parts else "")


def _parse_attrs(rest):
    """Parse conds/category/rule/attributes/const_vars from trailing text."""
    attrs = {}
    for m in re.finditer(r"(\w+)\s*=\s*(\[[^\]]*\]|[^\s]+)", rest):
        key, val = m.group(1), m.group(2)
        if key == "conds": attrs["conds"] = _parse_list(val)
        elif key == "attributes": attrs["attributes"] = _parse_list(val)
        elif key == "const_vars": attrs["const_vars"] = _parse_list(val)
        elif key in ("category", "rule"): attrs[key] = val.strip('"')
    return attrs


def parse_calc_text(text):
    """Parse any .calc file. Returns {"name","imports","description","content":[items]}.

    Item types:
      header, table              - organization
      theorem, definition        - library items (have expr, loaded into context)
      calculation                - computation task (has goal, can compute)
    """
    result = {"name": "", "imports": [], "description": "", "content": []}
    cur_table = None
    cur_calc = None
    in_calc = False

    for raw in text.split("\n"):
        line = raw.rstrip()
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue

        # Inside calc block (steps)
        if in_calc:
            if stripped == "qed":
                in_calc = False; cur_calc = None
            else:
                step = _parse_step_line(stripped)
                if step: cur_calc["calc"].append(step)
            continue

        # Inside table
        if cur_table is not None:
            if stripped == "endtable":
                cur_table = None
            elif "=" in stripped:
                k, _, v = stripped.partition("=")
                cur_table[k.strip().strip('"')] = v.strip().strip('"')
            continue

        # File header
        if line.startswith("theory "):
            result["name"] = line[7:].strip(); continue
        if line.startswith("imports "):
            result["imports"] = [s.strip() for s in line[8:].split(",") if s.strip()]; continue
        if line == "imports":
            result["imports"] = []; continue
        if line.startswith("description "):
            d = line[12:].strip()
            result["description"] = d[1:-1] if d.startswith('"') and d.endswith('"') else d
            continue

        # Section header
        if line.startswith("header "):
            rest = line[7:].strip()
            item = {"type": "header", "name": "", "level": 1}
            m = re.match(r'"([^"]*)"', rest)
            if m: item["name"] = m.group(1)
            lm = re.search(r"level\s*=\s*(\d+)", rest)
            if lm: item["level"] = int(lm.group(1))
            result["content"].append(item)
            cur_calc = None
            continue

        # Table
        if line.startswith("table "):
            cur_table = {}
            result["content"].append({"type": "table", "name": line[6:].strip(), "table": cur_table})
            cur_calc = None
            continue

        # goal/target/cond inside calculation block
        if cur_calc is not None:
            if line.startswith("  goal "):
                cur_calc["goal"] = line[7:].strip(); continue
            if line.startswith("  target "):
                cur_calc["target"] = line[9:].strip(); continue
            if line.startswith("  cond "):
                cur_calc["conds"].append(line[7:].strip()); continue
            if stripped == "calc":
                in_calc = True; continue

        # Single-line items: theorem, definition, calculation
        parts = stripped.split("  ")
        t = parts[0].strip()
        if t in ("theorem", "definition", "calculation", "axiom"):
            body = " ".join(p.strip() for p in parts[1:] if p.strip())
            m = re.match(r'"([^"]*)"', body)
            if not m:
                raise ValueError("Expected quoted string in: %r" % stripped)
            quoted = m.group(1)
            attrs = _parse_attrs(body[m.end():])

            if t in ("theorem", "definition", "axiom"):
                # Library item
                item = {"type": "theorem" if t == "axiom" else t, "expr": quoted}
                item.update(attrs)
                result["content"].append(item)
                cur_calc = None
            elif t == "calculation":
                # Computation task: if no goal line follows, use quoted as goal
                cur_calc = {
                    "type": "calculation",
                    "name": quoted,   # will be overwritten if goal line follows
                    "goal": quoted,   # default: the quoted string IS the goal
                    "target": None,
                    "conds": attrs.get("conds", []),
                    "calc": [],
                }
                cur_calc.update(attrs)
                result["content"].append(cur_calc)
            continue

        raise ValueError("Unknown line: %r" % stripped)

    return result


def load_calc_file(path):
    """Load a .calc file. Returns dict."""
    with open(path, "r", encoding="utf-8") as f:
        return parse_calc_text(f.read())


def export_calc(file_data):
    """Export dict to .calc text."""
    lines = []
    if file_data.get("name"):
        lines.append("theory  %s" % file_data["name"])
    if file_data.get("imports"):
        lines.append("imports  %s" % ", ".join(file_data["imports"]))
    if file_data.get("description"):
        lines.append('description  "%s"' % file_data["description"])
    lines.append("")

    for item in file_data.get("content", []):
        t = item.get("type", "calculation")

        if t == "header":
            lines.append('header  "%s"  level = %d' % (item.get("name", ""), item.get("level", 1)))
        elif t == "table":
            lines.append("table  %s" % item.get("name", ""))
            for k, v in item.get("table", {}).items():
                lines.append('  "%s" = "%s"' % (k, v))
            lines.append("endtable")
        elif t in ("theorem", "definition"):
            parts = ['%s  "%s"' % (t, item.get("expr", ""))]
            if item.get("conds"): parts.append("conds = [%s]" % "; ".join(item["conds"]))
            if item.get("attributes"): parts.append("attributes = [%s]" % "; ".join(item["attributes"]))
            if item.get("category"): parts.append("category = %s" % item["category"])
            if item.get("rule"): parts.append("rule = %s" % item["rule"])
            if item.get("const_vars"): parts.append("const_vars = [%s]" % "; ".join(item["const_vars"]))
            lines.append("  ".join(parts))
        elif t == "calculation":
            if item.get("calc"):
                # Multi-line with steps
                lines.append('calculation  "%s"' % item.get("name", ""))
                if item.get("goal"):
                    lines.append("  goal  %s" % item["goal"])
                if item.get("target"):
                    lines.append("  target  %s" % item["target"])
                for cond in item.get("conds", []):
                    lines.append("  cond  %s" % cond)
                lines.append("  calc")
                for step in item["calc"]:
                    if step.get("reason") != "Initial":
                        lines.append(_format_step(step))
                lines.append("  qed")
            else:
                # Single-line (just goal, no steps)
                lines.append('calculation  "%s"' % item.get("goal", item.get("name", "")))
            lines.append("")
    return "\n".join(lines)

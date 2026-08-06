"""Human-readable .calc format — unified parser.

A .calc file can contain any mix of:
  - definition / theorem  (library items, single-line with attributes)
  - header / table         (organization)
  - calculation            (computation task with goal/steps, or single-line library item)

All parsed by one parser. No distinction at the file level.
"""

import re
import json
import os
from typing import Optional, List, Dict


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


def _parse_list(s: str) -> List[str]:
    s = s.strip().strip("[]")
    if not s:
        return []
    return [x.strip().strip('"') for x in s.split(";")]


def _split_top_level(s: str, sep: str = ",") -> List[str]:
    res, depth, cur = [], 0, ""
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


def _parse_step_params(param_pairs: List[str]):
    params, location = {}, ""
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


def _parse_step_line(line: str) -> Optional[dict]:
    line = line.strip()
    if not line or line.startswith("--"):
        return None
    line = line.split("--", 1)[0].rstrip()
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


def _format_step(step: dict) -> str:
    reason = step["reason"]
    method = REASON_TO_METHOD.get(reason, reason)
    parts = []
    for key, value in step.get("params", {}).items():
        parts.append("%s = %s" % (key, value))
    loc = step.get("location", "")
    if loc and loc != ".":
        parts.append("at %s" % loc)
    if parts:
        return "    %s  %s" % (method, ", ".join(parts))
    return "    %s" % method


# ---- Unified parser ----

def parse_calc_text(text: str) -> dict:
    """Parse any .calc file: library items + calculations, unified.

    Returns {"name": ..., "imports": [...], "description": ..., "content": [items]}.

    Item types in content:
      - header:   {"type": "header", "name": ..., "level": N}
      - theorem/definition: {"type": ..., "expr": ..., "conds": [...], "category": ..., ...}
      - table:    {"type": "table", "name": ..., "table": {k: v}}
      - calculation (library item, single-line): {"type": "calculation", "expr": ...}
      - calculation (computation task): {"type": "calculation", "name": ..., "goal": ..., "target": ..., "conds": [...], "calc": [steps]}
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
                in_calc = False
                cur_calc = None
                continue
            step = _parse_step_line(stripped)
            if step is not None:
                cur_calc["calc"].append(step)
            continue

        # Inside table
        if cur_table is not None:
            if stripped == "endtable":
                cur_table = None
                continue
            if "=" in stripped:
                k, _, v = stripped.partition("=")
                cur_table[k.strip().strip('"')] = v.strip().strip('"')
            continue

        # File header
        if line.startswith("theory "):
            result["name"] = line[7:].strip()
            continue
        if line.startswith("imports "):
            result["imports"] = [s.strip() for s in line[8:].strip().split(",") if s.strip()]
            continue
        if line.startswith("imports"):
            result["imports"] = []
            continue
        if line.startswith("description "):
            desc = line[12:].strip()
            if desc.startswith('"') and desc.endswith('"'):
                desc = desc[1:-1]
            result["description"] = desc
            continue

        # Section header
        if line.startswith("header "):
            rest = line[7:].strip()
            item = {"type": "header", "name": "", "level": 1}
            m = re.match(r'"([^"]*)"', rest)
            if m:
                item["name"] = m.group(1)
            lm = re.search(r"level\s*=\s*(\d+)", rest)
            if lm:
                item["level"] = int(lm.group(1))
            result["content"].append(item)
            cur_calc = None
            continue

        # Table
        if line.startswith("table "):
            cur_table = {}
            result["content"].append({"type": "table", "name": line[6:].strip(), "table": cur_table})
            cur_calc = None
            continue

        # goal / target / cond inside a calculation block
        if cur_calc is not None:
            if line.startswith("  goal "):
                cur_calc["goal"] = line[7:].strip()
                continue
            if line.startswith("  target "):
                cur_calc["target"] = line[9:].strip()
                continue
            if line.startswith("  cond "):
                cur_calc["conds"].append(line[7:].strip())
                continue
            if stripped == "calc":
                in_calc = True
                continue

        # Single-line items: theorem / definition / calculation / problem / axiom
        parts = stripped.split("  ")
        t = parts[0].strip()
        if t in ("axiom", "theorem", "definition", "calculation", "problem"):
            body = " ".join(p.strip() for p in parts[1:] if p.strip())
            m = re.match(r'"([^"]*)"', body)
            if not m:
                raise ValueError("Expected quoted string in: %r" % stripped)
            quoted = m.group(1)

            # Parse attributes
            attrs = {}
            rest = body[m.end():]
            for km in re.finditer(r"(\w+)\s*=\s*(\[[^\]]*\]|[^\s]+)", rest):
                key, value = km.group(1), km.group(2)
                if key == "conds":
                    attrs["conds"] = _parse_list(value)
                elif key == "attributes":
                    attrs["attributes"] = _parse_list(value)
                elif key == "const_vars":
                    attrs["const_vars"] = _parse_list(value)
                elif key in ("category", "rule"):
                    attrs[key] = value.strip('"')

            if t in ("calculation", "problem"):
                # Could be a multi-line block (has goal) or single-line library item
                cur_calc = {
                    "type": "calculation",
                    "name": quoted,
                    "expr": quoted,  # for single-line items, expr is the expression
                    "goal": "",
                    "target": None,
                    "conds": attrs.get("conds", []),
                    "calc": [],
                }
                cur_calc.update(attrs)
                result["content"].append(cur_calc)
            else:
                item = {"type": t, "expr": quoted}
                item.update(attrs)
                result["content"].append(item)
                cur_calc = None
            continue

        raise ValueError("Unknown line: %r" % stripped)

    return result


# ---- Compatibility wrappers ----

def parse_theory(text: str) -> dict:
    """Parse .calc theory text. Delegates to unified parser."""
    return parse_calc_text(text)


def load_calc_file(path: str) -> dict:
    """Load a .calc file from disk. Returns unified dict."""
    with open(path, "r", encoding="utf-8") as f:
        return parse_calc_text(f.read())


def export_calc(file_data: dict) -> str:
    """Export a dict to .calc text."""
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
        t = item.get("type", "calculation")

        if t == "header":
            lines.append('header  "%s"  level = %d' % (item.get("name", ""), item.get("level", 1)))
            continue
        if t == "table":
            lines.append("table  %s" % item.get("name", ""))
            for k, v in item.get("table", {}).items():
                lines.append('  "%s" = "%s"' % (k, v))
            lines.append("endtable")
            continue

        if t in ("theorem", "definition", "axiom"):
            parts = ['%s  "%s"' % (t, item.get("expr", ""))]
            if item.get("conds"):
                parts.append("conds = [%s]" % "; ".join(item["conds"]))
            if item.get("attributes"):
                parts.append("attributes = [%s]" % "; ".join(item["attributes"]))
            if item.get("category"):
                parts.append("category = %s" % item["category"])
            if item.get("rule"):
                parts.append("rule = %s" % item["rule"])
            if item.get("const_vars"):
                parts.append("const_vars = [%s]" % "; ".join(item["const_vars"]))
            lines.append("  ".join(parts))
            continue

        if t == "calculation":
            # Multi-line calculation block (has goal)
            if item.get("goal"):
                lines.append('calculation  "%s"' % item.get("name", ""))
                lines.append("  goal  %s" % item["goal"])
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
            else:
                # Single-line library item
                parts = ['calculation  "%s"' % item.get("expr", "")]
                if item.get("conds"):
                    parts.append("conds = [%s]" % "; ".join(item["conds"]))
                lines.append("  ".join(parts))
            lines.append("")
            continue

    return "\n".join(lines)

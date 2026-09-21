"""Interactive REPL for pyHOL proof development.

Self-contained: depends only on kernel / core / method / syntax.  It does
not import the HTTP backend or the frontend.

Usage
=====
    python -m repl.repl                        # interactive
    python -m repl.repl --script FILE          # run a command file
    python -m repl.repl --theory nat --goal "0 + n = n"

Commands
========
    theory NAME            load a theory and set the parsing context
    var NAME TYPE          declare a context variable (before `goal`)
    goal PROP              start a proof of PROP (stable id #0)
    goals  (or g)          show open goals
    all                    show every stable-ID item (facts and goals)
    methods [SUBSTR]       list methods usable in the current theory
    theorems [-v] [SUBSTR] list theorems in scope (with -v, their props)
    thm NAME               show one theorem's statement + schematic vars
    validate [THEORY]      incrementally re-validate (cache-aware)
    reset                  clear declared variables and the active goal
    <step line>            apply one .pyhol step, e.g.
                             <- rule iffI goal=0
                             -> forward conjD1 goal=4 facts=[3]
                           (paste lines straight out of a .pyhol file)
    undo                   drop the last step
    export                 print the current proof as a .pyhol block
    item NAME              print the whole .pyhol item (header + proof)
    let NAME REF           bind an alias for a stable ID
    check                  report the verification status
    trust NAME,...         admit computation-oracle macros (default: none)
    help / quit

Reference arguments (goal= / facts=)
-------------------------------------
Writing literal stable IDs by hand goes wrong as soon as a proof grows, so a
step line may refer to items *semantically*; the resolved line (with literal
IDs) is echoed, and `export`/`item` always print literal IDs.

    goal=@             first still-open goal opened by the previous step;
                       else the previous step's goal (if still open); else
                       the newest open goal (a note says so)
    goal=@N            same, for the step N steps back (@0 = previous step)
    goal="<prop>"      the open goal whose printed proposition matches
    facts=[@]          the last fact created by the previous step
    facts=[@N]         same, for the step N steps back
    facts=["<prop>"]   the fact whose printed proposition matches
    facts=[NAME]       an alias bound with `let NAME <ref>`
    let NAME 3         bind an alias (references: <sid> | @ | @N | "prop")

Matching is by the printed proposition (whitespace-insensitive): an exact
match wins; otherwise any item containing the text matches, and the largest
stable ID (the most recent derivation) is used, with a note printed.  A
quoted alias is resolved at *use* time, against the branch of the goal it is
used for; fact references are checked against that branch, so a reference
that would fail with `illegal dependence` is reported as such up front.

Design notes (the pain points this REPL exists to fix)
------------------------------------------------------
* Every failure prints the real exception plus the failing step, goals,
  and live stable IDs -- the replay pipeline reports only "replay failed".
* After each step the newly created `#[N]` items are listed, so stable-ID
  bookkeeping is not guesswork.
* `undo` rebuilds from the recorded steps; a bad step leaves no trace.
"""

import argparse
import contextlib
import io
import os
import re
import socket
import sys
import traceback

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from core import basic, context
from kernel.proof import ItemID
from syntax.settings import global_setting
from syntax import parser, pyhol
import method.stable_state as ss

# Bind the z3 backend, exactly as validate_library.py / .cache/validate_one.py
# do: without it a stored `← z3` step fails with "Z3 method: not installed",
# so the oracle-backed theories (real, int, hoare) could not be developed or
# replayed here at all.  Optional: a checkout without z3 still runs.
try:
    import solvers.z3wrapper  # noqa: F401
except ImportError:
    pass


def _short(name):
    return name


class RefError(Exception):
    """A `goal=`/`facts=` reference that does not resolve in this state."""


_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def _split_top_commas(text):
    """Split on commas that are not inside a quoted string."""
    parts, cur, in_quote = [], '', False
    for ch in text:
        if ch == '"':
            in_quote = not in_quote
            cur += ch
        elif ch == ',' and not in_quote:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    parts.append(cur)
    return parts


def _is_quoted(s):
    return len(s) >= 2 and s.startswith('"') and s.endswith('"')


def _scan_goal_ref(line):
    """Find the first `goal=<ref>` token: (start, end, ref) or None.

    Quote-aware, so `goal="some prop"` scans as one reference.
    """
    for m in re.finditer(r'(?<![\w=])goal=', line):
        k = m.end()
        if k < len(line) and line[k] == '"':
            e = line.find('"', k + 1)
            if e < 0:
                return None
            return (m.start(), e + 1, line[k:e + 1])
        e = k
        while e < len(line) and not line[e].isspace():
            e += 1
        return (m.start(), e, line[k:e])
    return None


def _scan_bracket_end(line, start):
    """Index of the `]` matching the `[` at line[start]; -1 if unbalanced.

    Quote-aware, so a quoted proposition containing `]` cannot close it.
    """
    in_quote = False
    for i in range(start, len(line)):
        ch = line[i]
        if ch == '"':
            in_quote = not in_quote
        elif ch == ']' and not in_quote:
            return i
    return -1


# Schematic variables print as `?name`; `rule`/`forward` take them as
# `param_name=...` named arguments.
_SVAR_RE = re.compile(r"\?([A-Za-z_][A-Za-z0-9_']*)")


def _prop_str(th):
    """Print a theorem's proposition, never raising.

    Printing runs type inference; a malformed/ambiguous term must not be
    able to kill the session (or a resident server).
    """
    try:
        with global_setting(unicode=False):
            return str(th.prop)
    except Exception:
        return repr(th.prop)


def _exc_str(e):
    """Format an exception, never raising.

    Some prover exceptions build a lazily-printed mismatch trace whose
    str() can itself raise on ambiguous types.
    """
    try:
        return '%s: %s' % (type(e).__name__, e)
    except Exception:
        return type(e).__name__


class Repl:
    def __init__(self, trust=frozenset()):
        self.theory = None
        self.vars = {}
        self.sps = None
        self.goal_prop = None
        self.goal_raw = None
        self.aliases = {}
        self.history = []      # list of (step_dict, [(sid, prop, is_goal), ...])
        self.trust = frozenset(trust)
        self.failed = False    # a step failed (drives the exit code)

    # -- state helpers ----------------------------------------------------

    def _items_of(self, sps):
        """All trackable items as (sid, prop, is_goal), deduped by sid."""
        pos2sid = sps._build_pos2sid()
        seen = {}
        for item in ss._traverse(sps.state.prf):
            if not ss._trackable(item):
                continue
            sid = pos2sid.get(str(item.id))
            if sid is None or sid in seen:
                continue
            seen[sid] = item
        with global_setting(unicode=False):
            return [(sid, _prop_str(item.th), item.rule == 'sorry')
                    for sid, item in sorted(seen.items())]

    def _items(self):
        return self._items_of(self.sps)

    def _new_items_of(self, sps, before):
        return [(sid, prop, is_goal) for sid, prop, is_goal in self._items_of(sps)
                if sid not in before]

    def show_goals(self):
        goals = [(sid, _prop_str(th)) for sid, th in self.sps.get_open_goals()]
        if not goals:
            print('no open goals -- proof complete')
        for sid, prop in goals:
            print('  #[%d] %s' % (sid, prop))

    def show_all(self):
        for sid, prop, is_goal in self._items():
            print('  #[%d]%s %s' % (sid, ' GOAL' if is_goal else '     ', prop))

    # -- semantic references (goal= / facts=) ------------------------------

    @staticmethod
    def _norm(s):
        return ' '.join(s.split())

    def _open_sids(self):
        if self.sps is None:
            return set()
        return {sid for sid, _ in self.sps.get_open_goals()}

    def _sid2pos(self):
        """Stable ID -> positional ID, exactly as the engine resolves it."""
        if self.sps is None:
            return {}
        pos2sid = self.sps._build_pos2sid()
        return {v: k for k, v in pos2sid.items()}

    def _in_branch_of(self, sid, target_sid):
        """Whether item `sid` is a legal dependency of item `target_sid`.

        This is the engine's own rule (`ItemID.can_depend_on`: same parent
        proof, earlier line), so a reference that resolves here is accepted
        there too.  A match outside the branch is reported as such, instead
        of failing later with `apply_method: illegal dependence`.
        """
        if self.sps is None or target_sid is None:
            return True
        sid2pos = self._sid2pos()
        gpos, fpos = sid2pos.get(target_sid), sid2pos.get(sid)
        if gpos is None:
            return True
        if fpos is None or fpos == gpos:
            return False
        return ItemID(gpos).can_depend_on(ItemID(fpos))

    def _match_prop(self, text, pool):
        """Items in `pool` whose printed proposition matches `text`.

        Whitespace-insensitive exact match wins; otherwise any proposition
        containing the text matches.  Returns (sids, exact).
        """
        norm = self._norm(text)
        exact = [sid for sid, prop, _ in pool if self._norm(prop) == norm]
        if exact:
            return exact, True
        return [sid for sid, prop, _ in pool if norm in self._norm(prop)], False

    def _pick_match(self, text, pool, outside, what, target_sid=None):
        """Best match for a quoted proposition: (sid, note)."""
        sids, exact = self._match_prop(text, pool)
        if not sids:
            if outside:
                raise RefError(
                    '%r matches %d item(s) that goal #[%s] cannot depend on '
                    '(#%s); a fact must be an earlier line of the same subproof'
                    % (text, len(outside), target_sid,
                       ','.join(str(s) for s in sorted(it[0] for it in outside))))
            raise RefError('no %s matches %r' % (what, text))
        sid = max(sids)
        if exact and len(sids) == 1:
            return sid, None
        return sid, ('%d %s(s) match %r; using #[%d]'
                     % (len(sids), what, text, sid))

    def _step_back(self, spec):
        """Parse `@` / `@N` into the history index it refers to."""
        if spec == '@':
            n = 0
        elif spec[1:].isdigit():
            n = int(spec[1:])
        else:
            raise RefError('bad reference %r (use @ or @N)' % spec)
        idx = len(self.history) - 1 - n
        if idx < 0:
            raise RefError('%s: only %d step(s) recorded' % (spec, len(self.history)))
        return idx

    def _alias_value(self, spec):
        """Look up an alias, or explain that it does not exist."""
        val = self.aliases.get(spec)
        if val is None:
            raise RefError("unknown alias %r (bind one with: let %s <ref>)"
                           % (spec, spec))
        return val

    def _open_goal_pool(self):
        open_sids = self._open_sids()
        return [it for it in self._items() if it[2] and it[0] in open_sids]

    def resolve_goal_ref(self, spec):
        """Resolve a `goal=` argument to a stable ID.  Returns (sid, note)."""
        spec = spec.strip()
        if spec.isdigit():
            return int(spec), None
        if spec.startswith('@'):
            open_sids = self._open_sids()
            step, new = self.history[self._step_back(spec)]
            sub = [sid for sid, _, is_goal in new if is_goal and sid in open_sids]
            if sub:
                return min(sub), None
            g = step.get('goal')
            if isinstance(g, int) and g in open_sids:
                return g, None
            # The step closed its own goal without opening subgoals (a
            # rewrite that finished it).  Continue on the newest goal still
            # open; the note keeps the heuristic visible.
            rest = sorted(open_sids)
            if rest:
                return rest[-1], ('%s: the step closed its goal; '
                                  'continuing on the newest open goal #[%d]'
                                  % (spec, rest[-1]))
            raise RefError('%s: no open goal to continue (the proof is closed)' % spec)
        if _is_quoted(spec):
            return self._pick_match(spec[1:-1], self._open_goal_pool(), [],
                                    'open goal')
        if _IDENT_RE.fullmatch(spec):
            val = self._alias_value(spec)
            if isinstance(val, tuple):
                return self._pick_match(val[1], self._open_goal_pool(), [],
                                        'open goal')
            return val, None
        raise RefError('cannot resolve goal reference %r' % spec)

    def resolve_fact_ref(self, spec, target_sid=None):
        """Resolve one `facts=[...]` entry to a stable ID.  (sid, note).

        `target_sid` is the goal the step will be applied to; facts are
        checked against its branch (see `_in_branch_of`).
        """
        spec = spec.strip()
        if spec.isdigit():
            return int(spec), None
        items = self._items()
        pool_all = [it for it in items if not it[2]]
        pool = [it for it in pool_all if self._in_branch_of(it[0], target_sid)]
        outside = [it for it in pool_all if it not in pool]
        if spec.startswith('@'):
            _, new = self.history[self._step_back(spec)]
            sids = [sid for sid, _, is_goal in new if not is_goal]
            if not sids:
                raise RefError(
                    '%s: the previous step created no fact; use a literal id, '
                    'a quoted proposition, or the goal reference' % spec)
            sid = max(sids)
            if not self._in_branch_of(sid, target_sid):
                raise RefError('%s = #[%d] is outside the branch of goal #[%s]'
                               % (spec, sid, target_sid))
            return sid, None
        if _is_quoted(spec):
            text = spec[1:-1]
            try:
                return self._pick_match(text, pool, outside, 'fact', target_sid)
            except RefError:
                goals, _ = self._match_prop(text, [it for it in items if it[2]])
                if goals:
                    raise RefError('%r matches open goal #[%d]; facts= takes facts'
                                   % (text, max(goals)))
                raise
        if _IDENT_RE.fullmatch(spec):
            val = self._alias_value(spec)
            if isinstance(val, tuple):
                return self._pick_match(val[1], pool, outside, 'fact', target_sid)
            if not self._in_branch_of(val, target_sid):
                raise RefError('alias %s = #[%d] is outside the branch of goal #[%s]'
                               % (spec, val, target_sid))
            return val, None
        raise RefError('cannot resolve fact reference %r' % spec)

    def _rewrite_refs(self, line):
        """Replace semantic `goal=`/`facts=` references by literal stable IDs.

        Returns (new_line, notes).  Only references that are not plain IDs
        are touched, so a stored .pyhol line passes through unchanged.  The
        goal is resolved first: it fixes the branch that fact references are
        then checked against.
        """
        goal_ref = _scan_goal_ref(line)
        notes = []
        target = None
        if goal_ref is not None:
            target, note = self.resolve_goal_ref(goal_ref[2])
            if note:
                notes.append(note)
        out, i = [], 0
        while i < len(line):
            at_word = (i == 0 or line[i - 1].isspace())
            if goal_ref is not None and i == goal_ref[0]:
                out.append('goal=%d' % target)
                i = goal_ref[1]
            elif at_word and line.startswith('facts=[', i):
                end = _scan_bracket_end(line, i + 6)
                if end < 0:
                    raise RefError('unbalanced facts=[ ... ] in %r' % line)
                sids = []
                for part in _split_top_commas(line[i + 7:end]):
                    if not part.strip():
                        continue
                    sid, note = self.resolve_fact_ref(part, target)
                    sids.append(sid)
                    if note:
                        notes.append(note)
                out.append('facts=[%s]' % ','.join(str(s) for s in sids))
                i = end + 1
            else:
                out.append(line[i])
                i += 1
        return ''.join(out), notes

    # -- commands ---------------------------------------------------------

    def cmd_theory(self, arg):
        name = arg.strip()
        context.set_context(name, vars=dict(self.vars))
        self.theory = name
        print('theory %s loaded' % name)

    def cmd_var(self, arg):
        # Split on the first run of whitespace only: type strings contain
        # spaces (e.g. `'a => bool`).
        parts = arg.strip().split(None, 1)
        if len(parts) != 2:
            print('usage: var NAME TYPE')
            return
        name, typ = parts
        self.vars[name] = typ
        if self.theory:
            context.set_context(self.theory, vars=dict(self.vars))
        print('variable %s :: %s' % (name, typ))

    def cmd_goal(self, arg):
        if not self.theory:
            print('load a theory first (theory NAME)')
            return
        context.set_context(self.theory, vars=dict(self.vars))
        self.goal_raw = arg.strip()
        self.aliases = {}
        try:
            # `'a::C` sugar, same rule as the item layer (syntax/parser.py):
            # annotations in the declared variables' types (or in the goal
            # itself) become premises, so a proof developed here matches the
            # statement the .pyhol item is stored with.
            prop = parser.with_class_premises(
                self.goal_raw, *self.vars.values())
        except Exception as e:
            print('cannot parse goal: %s' % _exc_str(e))
            self.sps = None
            return
        self.goal_prop = prop
        try:
            self.sps = ss.StableProofState.create(self.goal_prop, dict(self.vars),
                                                  trust=self.trust)
        except Exception as e:
            print('cannot parse goal: %s' % _exc_str(e))
            self.sps = None
            return
        self.history = []
        print('goal accepted:')
        if self._norm(prop) != self._norm(self.goal_raw):
            print('  prop (with class premises): %s' % prop)
        self.show_goals()

    def _rebuild(self, upto):
        """Recreate the proof state by replaying the first `upto` steps."""
        context.set_context(self.theory, vars=dict(self.vars))
        sps = ss.StableProofState.create(self.goal_prop, dict(self.vars),
                                         trust=self.trust)
        new_hist = []
        for step, _ in self.history[:upto]:
            before = {sid for sid, _, _ in self._items_of(sps)}
            sps.apply_method_dict(step, strict=True)
            new_hist.append((step, self._new_items_of(sps, before)))
        self.sps = sps
        self.history = new_hist

    def cmd_step(self, line):
        if self.sps is None:
            print('no active goal (use: goal PROP)')
            return False
        try:
            resolved, notes = self._rewrite_refs(line.strip())
        except RefError as e:
            self.failed = True
            print('CANNOT RESOLVE REFERENCE: %s' % e)
            print('  failing line: %s' % line.strip())
            print('  live stable ids: %s'
                  % sorted({sid for sid, _, _ in self._items()}))
            self.show_goals()
            return False
        for note in notes:
            print('  note: %s' % note)
        if resolved != line.strip():
            print('  resolved: %s' % resolved)
        step = pyhol._parse_step_line(resolved)
        if step is None:
            print('cannot parse step: %r' % line)
            return False
        before = {sid for sid, _, _ in self._items()}
        try:
            self.sps.apply_method_dict(step, strict=True)
        except Exception as e:
            self.failed = True
            print('STEP FAILED: %s' % _exc_str(e))
            if os.environ.get('PYHOL_REPL_TRACE'):
                traceback.print_exc()
            print('  failing line: %s' % resolved)
            print('  live stable ids: %s'
                  % sorted({sid for sid, _, _ in self._items()}))
            self.show_goals()
            return False
        new = self._new_items_of(self.sps, before)
        for sid, prop, is_goal in new:
            print('  + #[%d]%s %s' % (sid, ' GOAL' if is_goal else '     ', prop))
        if not new:
            print('  (no new items; goal closed or rewritten in place)')
        self.history.append((step, new))
        self.show_goals()
        return True

    def cmd_undo(self):
        if not self.history:
            print('nothing to undo')
            return
        self.history.pop()
        self._rebuild(len(self.history))
        print('undone; %d step(s) remain' % len(self.history))
        self.show_goals()

    def cmd_reset(self):
        """Clear declared variables and the active goal.

        `var` declarations live for the whole session, so a variable
        from an earlier goal can collide with a witness name in a later
        one (`elim: duplicate name p`).  `reset` returns to a clean slate
        without reloading the theory.
        """
        self.vars = {}
        self.sps = None
        self.goal_prop = None
        self.goal_raw = None
        self.aliases = {}
        self.history = []
        self.failed = False
        if self.theory:
            context.set_context(self.theory, vars={})
        print('session reset (variables and goal cleared)')

    def _proof_lines(self):
        """The recorded proof as .pyhol lines (with `#[N]` annotations)."""
        lines = ['proof']
        for step, new in self.history:
            step = dict(step)
            step['new_items'] = [{'sid': sid, 'prop': prop}
                                 for sid, prop, _ in new]
            lines.append('  %s' % pyhol._export_step(step))
            for ann in pyhol._export_anns(step):
                lines.append('    %s' % ann)
        lines.append('qed')
        return lines

    def cmd_export(self):
        if not self.history:
            print('no steps to export')
            return
        print('\n'.join(self._proof_lines()))

    def cmd_item(self, arg):
        """Print the whole .pyhol item: header, statement, and proof.

        The statement uses the text given to `goal` (so a `'a::C` annotation
        stays in the file and the item layer re-injects the premise), and the
        committed variables are the session's `var` declarations.  Copy the
        output into a theory file -- do not retype the proposition.
        """
        name = arg.strip()
        if not name:
            print('usage: item NAME   (prints the .pyhol item block)')
            return
        if not self.history:
            print('no steps to export')
            return
        if not _IDENT_RE.fullmatch(name):
            print('bad theorem name: %r' % name)
            return
        lines = ['theorem %s' % name]
        if self.vars:
            lines.append('  fixes ' + ', '.join(
                '%s :: %s' % (k, v) for k, v in self.vars.items()))
        lines.append('  prop %s' % (self.goal_raw or self.goal_prop))
        lines.extend(self._proof_lines())
        print('\n'.join(lines))

    def cmd_let(self, arg):
        """Bind a name to an item, so step lines can read semantically.

        `let h 3`            the item with stable ID 3
        `let h @`            the last fact the previous step created
        `let h "x <= y"`     the fact whose printed proposition matches
        `let g goal=@`       the goal auto-reference (usable as goal=g)
        With no argument, list the current bindings.

        A quoted proposition is bound *by text* and resolved when it is
        used, against the branch of the goal it is used for; stable IDs and
        `@` references are resolved immediately.
        """
        arg = arg.strip()
        if not arg:
            if not self.aliases:
                print('no aliases')
                return
            for name, val in self.aliases.items():
                if isinstance(val, tuple):
                    print('  %-10s "%s" (resolved at use time)' % (name, val[1]))
                else:
                    prop = next((p for s, p, _ in self._items() if s == val), None)
                    print('  %-10s #[%d] %s' % (name, val, prop if prop else '<?>'))
            return
        parts = arg.split(None, 1)
        name = parts[0]
        if len(parts) != 2:
            print('usage: let NAME <sid|@|@N|"prop"|goal=<ref>>')
            return
        if not _IDENT_RE.fullmatch(name):
            print('bad alias name: %r' % name)
            return
        spec = parts[1].strip()
        if _is_quoted(spec):
            # Bound by text: the branch is only known when the alias is
            # used, so resolve (and report) at use time.
            self.aliases[name] = ('prop', spec[1:-1])
            sids, _ = self._match_prop(spec[1:-1], self._items())
            where = ('now matches #[%d] ' % max(sids)) if sids else 'no match yet '
            print('alias %s = "%s" (%s; resolved at use time)'
                  % (name, spec[1:-1], where.strip()))
            return
        try:
            if spec.startswith('goal='):
                sid, _ = self.resolve_goal_ref(spec[len('goal='):])
            else:
                try:
                    sid, _ = self.resolve_fact_ref(spec)
                except RefError as e:
                    # The reference may name an open goal instead of a
                    # fact; a name is useful for both.
                    if 'matches open goal' not in str(e):
                        raise
                    sid, _ = self.resolve_goal_ref(spec)
        except RefError as e:
            print('cannot bind %s: %s' % (name, e))
            return
        self.aliases[name] = sid
        prop = next((p for s, p, g in self._items() if s == sid), None)
        print('alias %s = #[%d] %s' % (name, sid, prop if prop else '<?>'))

    def cmd_check(self):
        if self.sps is None:
            print('no active goal')
            return
        gaps = self.sps.num_gaps
        print('VALID' if gaps == 0 else 'open goals: %d' % gaps)

    def cmd_methods(self, arg):
        """List methods usable in the current theory (optional filter).

        The registry is the same one the checked channel `apply_method`
        uses, so this is exactly what a step line may name -- and it
        already respects each method's `limit` (a theory dependency).
        """
        from core import method as _method
        pat = arg.strip()
        names = sorted(_method.get_all_methods())
        hit = [n for n in names if not pat or pat in n]
        for name in hit:
            m = _method.global_methods[name]
            params = ', '.join(getattr(m, 'sig', None) or []) or '-'
            limit = getattr(m, 'limit', None)
            print('  %-13s params: %-22s%s'
                  % (name, params, '' if limit is None else '[needs %s]' % limit))
        print('(%d of %d method(s)%s)'
              % (len(hit), len(names), '' if not pat else " matching %r" % pat))

    def cmd_theorems(self, arg):
        """List theorems in scope, optionally filtered by substring.

        With `-v`, print each theorem's proposition.  Read the library
        through this (or `thm NAME`) instead of guessing names.
        """
        from kernel import theory as _theory
        parts = arg.split()
        verbose = '-v' in parts
        pat = ' '.join(p for p in parts if p != '-v')
        if _theory.thy is None:
            print('load a theory first (theory NAME)')
            return
        names = sorted(_theory.thy.get_data('theorems'))
        hit = [n for n in names if not pat or pat in n]
        for name in hit:
            if not verbose:
                print('  %s' % name)
                continue
            try:
                th = _theory.thy.get_theorem(name)
                print('  %-28s %s' % (name, _prop_str(th)))
            except Exception as e:
                print('  %-28s <%s>' % (name, _exc_str(e)))
        print('(%d of %d theorem(s)%s)'
              % (len(hit), len(names), '' if not pat else " matching %r" % pat))

    def cmd_thm(self, arg):
        """Show one theorem's statement, hypotheses, and schematic vars."""
        from kernel import theory as _theory
        name = arg.strip()
        if not name:
            print('usage: thm NAME   (list names with: theorems [SUBSTR])')
            return
        if _theory.thy is None:
            print('load a theory first (theory NAME)')
            return
        try:
            th = _theory.thy.get_theorem(name)
        except Exception as e:
            print('no such theorem: %s' % _exc_str(e))
            return
        print('%s:' % name)
        with global_setting(unicode=False):
            print('  prop: %s' % _prop_str(th))
            for h in getattr(th, 'hyps', None) or []:
                print('  hyp:  %s' % h)
            svars = sorted(set(_SVAR_RE.findall(_prop_str(th))))
        if svars:
            print('  schematic vars (rule/forward named args): %s'
                  % ', '.join('param_%s' % v for v in svars))

    def cmd_validate(self, arg):
        """Incrementally re-validate a theory from inside the session.

        Only the affected part is replayed: a file whose source and
        imports are unchanged comes from cache; a locally edited file
        replays from its first changed item; importers of a changed file
        are re-validated.  The resident process therefore keeps its
        parsed theories warm instead of reloading the library.

        Uses the session trust set, so oracle proofs need `trust +...`.
        """
        name = arg.strip() or self.theory
        if not name:
            print('usage: validate [THEORY]')
            return
        from core import incremental
        lines = []

        def report(f, reused, start, changed):
            if f == '__done__':
                return
            if reused:
                lines.append('  %-16s cached' % f)
            else:
                lines.append('  %-16s replayed from item %d%s'
                             % (f, start, '   (verdict changed)' if changed else ''))

        incremental.validate_incremental([name], trust=self.trust, report=report)
        print('\n'.join(lines) if lines else 'nothing to validate')

    def handle_request(self, req):
        """Run one server request; return the reply dict.

        Kept socket-free so it is testable, and so the resident server
        (and any other embedding) share one execution path.
        """
        out = io.StringIO()
        self.failed = False
        with contextlib.redirect_stdout(out):
            try:
                for cmd in req.get('cmds', []):
                    if not self.run_line(cmd):
                        break
            except Exception as e:
                # A request must never kill the resident server.
                self.failed = True
                out.write('REPL INTERNAL ERROR: %s\n' % _exc_str(e))
        return {
            'out': out.getvalue(),
            'gaps': self.sps.num_gaps if self.sps is not None else None,
            'failed': self.failed,
        }

    # -- dispatch ---------------------------------------------------------

    def run_line(self, line):
        line = line.rstrip('\n')
        stripped = line.strip()
        if not stripped or stripped.startswith('--'):
            return True
        if stripped in ('quit', 'exit', 'q'):
            return False
        if stripped in ('help', '?'):
            print(__doc__.split('Commands', 1)[1].split('Design notes')[0])
            return True
        if stripped in ('goals', 'g'):
            self.show_goals() if self.sps else print('no active goal')
            return True
        if stripped == 'all':
            self.show_all() if self.sps else print('no active goal')
            return True
        if stripped == 'undo':
            self.cmd_undo()
            return True
        if stripped == 'reset':
            self.cmd_reset()
            return True
        if stripped == 'export':
            self.cmd_export()
            return True
        if stripped == 'check':
            self.cmd_check()
            return True
        # A step line may begin with a name that is also a command
        # (`var a :: 'a goal=3`).  Step lines carry `goal=`/`facts=` or a
        # direction arrow; give those priority over command prefixes.
        is_step = (stripped.startswith(('←', '→'))
                   or ' goal=' in stripped or ' facts=' in stripped)
        if not is_step:
            for cmd, fn in (('theory ', self.cmd_theory), ('load ', self.cmd_theory),
                            ('var ', self.cmd_var), ('goal ', self.cmd_goal),
                            ('methods', self.cmd_methods),
                            ('theorems', self.cmd_theorems), ('thm ', self.cmd_thm),
                            ('validate', self.cmd_validate),
                            ('item ', self.cmd_item), ('let ', self.cmd_let),
                            ('let', self.cmd_let),
                            ('trust ', lambda a: self._set_trust(a))):
                if stripped.startswith(cmd):
                    fn(stripped[len(cmd):])
                    return True
        self.cmd_step(line)
        return True

    def _set_trust(self, arg):
        """Set or extend the session trust set.

        Trust is always passed explicitly by this shell into the proof
        state; the kernel never loads it on its own.  Explicitly applying
        a level-0 oracle method (e.g. `z3`) authorizes that name for the
        session through the checked macro channel, so `trust` is only
        needed when replaying stored oracle lines.
        """
        arg = arg.strip()
        if not arg:
            print('trust set: %s' % (sorted(self.trust) or 'empty (no oracles)'))
            return
        if arg.startswith('+'):
            names = [x.strip() for x in arg[1:].split(',') if x.strip()]
            self.trust = self.trust | frozenset(names)
        elif arg.startswith('-'):
            names = {x.strip() for x in arg[1:].split(',') if x.strip()}
            self.trust = self.trust - names
        else:
            self.trust = frozenset(x.strip() for x in arg.split(',') if x.strip())
        if self.sps is not None:
            self.sps.set_trust(self.trust)
        print('trust set: %s' % (sorted(self.trust) or 'empty (no oracles)'))


def main():
    ap = argparse.ArgumentParser(description='pyHOL REPL')
    ap.add_argument('--script', help='run commands from a file, then exit')
    ap.add_argument('--theory', help='load this theory at startup')
    ap.add_argument('--goal', help='start a goal at startup')
    ap.add_argument('--trust', default='', help='comma-separated oracle names')
    ap.add_argument('--serve', action='store_true',
                    help='run as a resident server (see repl.client)')
    ap.add_argument('--port', type=int, default=5599,
                    help='server port (with --serve)')
    args = ap.parse_args()

    basic.load_metadata()
    if args.serve:
        serve(args.port, args.theory, [x for x in args.trust.split(',') if x])
        return
    rp = Repl(trust=[x for x in args.trust.split(',') if x])
    if args.theory:
        rp.run_line('theory %s' % args.theory)
    if args.goal:
        rp.run_line('goal %s' % args.goal)

    if args.script:
        with open(args.script, encoding='utf-8') as f:
            for line in f:
                if not rp.run_line(line):
                    break
        sys.exit(1 if rp.failed or (rp.sps is not None and rp.sps.num_gaps) else 0)

    if not sys.stdin.isatty():
        for line in sys.stdin:
            if not rp.run_line(line):
                break
        sys.exit(1 if rp.failed or (rp.sps is not None and rp.sps.num_gaps) else 0)

    print('pyHOL REPL -- type help, quit to exit')
    while True:
        try:
            line = input('pyHOL> ')
        except (EOFError, KeyboardInterrupt):
            print()
            break
        if not rp.run_line(line):
            break


def bind_server(port):
    """Bind the resident server socket to 127.0.0.1:port.

    SO_REUSEADDR is only set on POSIX (where it is needed to rebind after
    TIME_WAIT).  On Windows it does the opposite of what one wants: a second
    server can bind the same port and silently shadow the first, so a
    "restart" appears to work while clients keep talking to the old code.
    Failing loudly here is the point.
    """
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    if os.name != 'nt':
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    try:
        srv.bind(('127.0.0.1', port))
    except OSError as e:
        srv.close()
        raise
    srv.listen(1)
    return srv


def serve(port, theory, trust):
    """Resident REPL: theory stays loaded across client requests.

    Protocol (one JSON request per line, one JSON reply per line):
        request  {"cmds": ["theory nat", "← induct x nat_induct goal=0", ...]}
        reply    {"out": "<captured stdout>", "gaps": int|null,
                  "failed": bool}
    Binds 127.0.0.1 only.  The client is repl/client.py.
    """
    import json

    rp = Repl(trust=trust)
    if theory:
        rp.run_line('theory %s' % theory)

    try:
        srv = bind_server(port)
    except OSError as e:
        print('cannot bind 127.0.0.1:%d: %s -- another server on this port?'
              % (port, e), flush=True)
        sys.exit(2)
    print('repl server on 127.0.0.1:%d (theory=%s)' % (port, theory or '-'),
          flush=True)
    while True:
        conn, _ = srv.accept()
        f = conn.makefile('rwb', buffering=0)
        for raw in f:
            try:
                req = json.loads(raw.decode('utf-8'))
            except ValueError:
                break
            resp = rp.handle_request(req)
            conn.sendall((json.dumps(resp) + '\n').encode('utf-8'))
        conn.close()


if __name__ == '__main__':
    main()

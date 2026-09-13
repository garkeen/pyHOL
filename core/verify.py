"""Verification pipeline: proof-status judgement for theory files.

This is the core half of verify (audit §7.4): the four-state machine
for theorem entries, run by library validation and the IDE.  The
status of a theorem entry is an output of the verification pipeline,
not data of the logical kernel.

States (contract, the last three are all failures):
  VALID       full proof, zero gaps after replay
  DEP_FAILED  proof intact but references a failed-state theorem
  STEP_FAILED proof exists but replay fails or leaves open goals
  UNPROVED    no proof at all (no steps)

Only 'thm' entries participate.  'thm.ax' entries are theory content
admitted by the axiom rule -- recorded as 'AXIOM' for display, not a
state.

The replay itself goes through the method layer's stable-ID pipeline
(injected at load via set_replay_fn -- core must not import the
method layer).  The cache format (.cache/<theory>.json keyed on source
mtime) is unchanged from the monitor-era implementation.
"""

import json
import os

from kernel import theory
from kernel.thm import Thm, InvalidDerivationException
from kernel.term import Var, Inst
from kernel.proof import Proof, ProofItem
from kernel.theory import (CheckProofException, TypeCheckException,
                           has_macro, get_macro, primitive_deriv)
from kernel.replay import ReplayException
from kernel import replay as replay_mod
from core import basic
from core import context
from core import matcher


# ---------------------------------------------------------------------------
# Proof-status tables (audit §7.4): theorem status is output of this
# pipeline, not kernel data.  The tables themselves live in core.basic
# (beside the .json cache read/write); the kernel's thm_status and
# thm_error tables are gone.  Writing goes through the set_status /
# set_error helpers so every mutation of the tables is greppable.
# ---------------------------------------------------------------------------

def axioms():
    """Set of theorem names admitted by the axiom assumption rule.

    This is what the kernel-side replay must be *given* (injected as
    the axioms argument) -- the kernel does not read any status table.
    """
    return frozenset(
        name for name, status in basic.statuses.items()
        if status == 'AXIOM')


# Local alias (the verify() function shadows the name with a parameter).
_current_axioms = axioms


# Computation-oracle macros admitted by default (audit §7.1 "computation
# is oracle" debt).  These name level-0 oracle nodes that appear *inside*
# a macro expansion (norm/auto folding numeric constants through
# *_eval_conv's auto_solve) rather than as explicit method steps, so they
# never pass through the checked apply_macro channel that self-authorizes
# a directly-applied level-0 macro (z3).  Without them, `auto` on
# `(1::real) + 1 = 2` and `norm` on `(1::int) + 1 = 2` hard-fail with
# "oracle macro 'real_eval'/'int_eval' is not trusted".
#
# Single source of truth for both validate_library.py (CLI, full-library)
# and the backend IDE endpoints (interactive default).
COMPUTATION_ORACLES = frozenset({
    'nat_eval', 'int_eval', 'int_const_ineq',
    'real_eval', 'real_norm', 'real_const_eq', 'real_compare',
    'real_const_ineq', 'real_eq_comparison',
    'sympy', 'z3',
})


# ---------------------------------------------------------------------------
# The expander: the core half of proof-level verify (audit §7.1).
#
# Walks a linear Proof once, resolving every line's theorem (writing it
# back onto lines that lack one, as the old checker did -- this is not a
# rewrite of the line's identity, only the cached theorem). Macros are
# expanded IN A TEMPORARY FLATTENED STREAM handed to the kernel replay:
# the proof itself is never rewritten (immutable-line contract: rule,
# args, prevs stay as written). The kernel half (kernel/replay.py) sees
# only primitives, theorem/variable/reference, sorry, and oracle lines.
#
# Macro policy:
#   * auto_close -- level None, expands to a reference line (and a
#     substitution primitive when the cited fact must be specialized).
#     No oracle hole; the citation is re-derived by kernel replay.
#   * level-0 oracle macros -- computation without derivation (z3,
#     sympy, simplex, numeric evaluation). NEVER expanded (expansion
#     is impossible by construction). Evaluating one requires its name
#     in the trust set; the result is emitted as an oracle assumption
#     line in the flattened stream (the original macro line is left
#     untouched, only its theorem is written back).
#   * every other macro -- expanded to primitives, emitted inline.
# ---------------------------------------------------------------------------

def _memo_key(rule, args, prev_ths, stated, thy):
    """Content key for the incremental-verify cache.

    The key is the derivation's FULL input: the rule, its arguments,
    the identity of the previous theorems, the identity of the line's
    own stated theorem (`stated`), and the identity of the global
    theory (`thy`).  `stated` matters because a macro's expansion may
    depend on the line's own statement -- e.g. auto_close specializes
    to the goal it closes -- so two lines with the same premises but
    different statements are different derivations.  `thy` matters
    because the global theory is not always fixed for a whole replay:
    z3 proof reconstruction (`theories/z3rec.py`) calls
    basic.load_theory mid-replay, replacing it.  Keying by the theory
    object is the same defence `core/auto.py::_cache_key` uses.

    The stored value pins the premise theorems, the stated theorem, the
    theory and the result, so an entry can only be taken when those
    objects are literally the same ones (`verify` reuses the theorem
    written back onto each proof item, which keeps identity stable
    across calls).
    """
    try:
        hash(args)
        ak = args
    except TypeError:
        ak = repr(args)
    return (rule, ak, tuple(id(th) for th in prev_ths),
            None if stated is None else id(stated), id(thy))


# Audit switch for the incremental-verify cache.  When True, a memo hit
# is CONFIRMED by re-deriving the line and comparing, which restores the
# original property that every line is re-derived on every pass (at the
# original O(n^2) cost).  Off by default so normal validation keeps the
# speedup; turn it on for an audit run (`validate_library.py --selfcheck`).
memo_selfcheck = False


def _thm_confirmed(fresh, cached):
    """True when a fresh derivation confirms a cached line theorem.

    Exactly the acceptance test the miss path applies (below): a derived
    theorem may be stronger than the line's stated one (fewer hyps), so
    the check is `fresh.can_prove(cached)`, not equality.  In self-check
    mode this re-runs that test on every memo hit, restoring the
    "every line re-derived on every pass" property.
    """
    return fresh is cached or fresh.can_prove(cached)


def verify(prf, rpt=None, *, no_gaps=False, trust=frozenset(), axioms=None,
           compute_only=False, memo=None):
    """Verify the given proof. Returns the final theorem.

    Raises theory.CheckProofException when a line cannot be resolved.

    prf -- linear proof to check. Theorem write-back onto lines that
        lack one is the only mutation (the line identity -- rule,
        args, prevs -- is never rewritten).
    rpt -- optional report (kernel.report.ProofReport).
    no_gaps -- reject sorry lines outright (strict mode).
    trust -- names of computation-oracle macros admitted to evaluate
        (default: none). An untrusted oracle name is a hard failure,
        never a warning.
    axioms -- theorem names admitted by the axiom assumption rule;
        defaults to the current AXIOM set from the status tables.
    compute_only -- incremental mode (method layer after line edits):
        every line is still resolved and derived (cached theorems are
        re-derived and checked), only the final independent replay over
        the flattened stream is skipped. Full verify() runs that replay.
    memo -- optional dict owned by the caller (one theorem replay).
        In compute_only mode a macro line whose derivation inputs are
        unchanged since the previous call reuses its expansion result
        instead of re-expanding.  Keys are content-based (see
        _memo_key), so an edited line -- or a premise whose theorem
        changed -- always misses and is re-derived.  None disables it.
        Only sound while the theory is fixed, i.e. within one replay.
    """
    if axioms is None:
        axioms = _current_axioms()

    # id -> Thm: theorems derived so far (prev resolution + write-back).
    ths = {}
    # The flattened primitive stream handed to the kernel replay.
    flat = []

    def emit(seq):
        """Resolve seq's theorem and append its primitive/data/oracle
        form to the flattened stream. Macros expand recursively here
        (a single walk builds both the th table and the replay stream).
        The proof is never rewritten: only th write-back onto lines
        that lack one, as the old checker did.
        """
        rule = seq.rule
        if rule == "":
            return
        if rule == "sorry":
            assert seq.th is not None, "sorry must have explicit statement."
            if no_gaps:
                raise CheckProofException("gaps are not allowed")
            if rpt is not None and seq.th not in rpt.gaps:
                rpt.add_gap(seq.th)
            ths[seq.id] = seq.th
            flat.append(seq)
            return
        if rule == "theorem":
            try:
                th = theory.thy.get_theorem(seq.args)
            except theory.TheoryException:
                raise CheckProofException("theorem not found")
            if rpt is not None:
                rpt.apply_theorem(seq.args)
            if seq.th is None:
                seq.th = th
            elif not th.can_prove(seq.th):
                raise CheckProofException(
                    "output does not match\n%s\n vs.\n%s" % (seq.th, th))
            ths[seq.id] = seq.th
            flat.append(seq)
            return
        if rule == "variable":
            nm, T = seq.args
            th = Thm.mk_VAR(Var(nm, T))
            if seq.th is None:
                seq.th = th
            ths[seq.id] = th
            flat.append(seq)
            return
        if rule == "reference":
            # Pure reference, emitted by ProofTerm.export for an atom root
            # (auto_close expands to exactly this). It re-cites the
            # referenced item and derives nothing, so it enters the
            # flattened stream as itself. can_depend_on is deliberately
            # not consulted here: export gives a reference line a child id
            # of the line that produced it, so a child citing an earlier
            # sibling would fail that structural test without being wrong.
            if not seq.prevs:
                raise CheckProofException("reference must cite a fact")
            prev_th = ths.get(seq.prevs[0])
            if prev_th is None:
                raise CheckProofException(
                    "reference: fact %s not found" % seq.prevs[0])
            if seq.th is None:
                seq.th = prev_th
            elif not prev_th.can_prove(seq.th):
                raise CheckProofException(
                    "output does not match\n%s\n vs.\n%s" % (seq.th, prev_th))
            ths[seq.id] = seq.th
            flat.append(seq)
            return
        if rule == "oracle":
            if seq.args not in trust:
                raise CheckProofException(
                    "oracle '%s' is not trusted (not in the trust set)"
                    % seq.args)
            if rpt is not None:
                rpt.eval_macro(seq.args)
            ths[seq.id] = seq.th
            flat.append(seq)
            return
        if rule == "subproof":
            # A macro line whose expansion is attached as a subproof
            # (method layer). Flatten its items in place, then bind the
            # line's own id to the expansion's conclusion: later lines cite
            # the subproof line, not its items, so the line must stand in
            # the flattened stream as well.
            if not seq.subproof:
                return
            for s in seq.subproof.items:
                emit(s)
            last = seq.subproof.items[-1]
            if seq.th is None:
                seq.th = last.th
            elif not last.th.can_prove(seq.th):
                raise CheckProofException(
                    "output does not match\n%s\n vs.\n%s" % (seq.th, last.th))
            ths[seq.id] = seq.th
            flat.append(ProofItem(seq.id, "reference", prevs=[last.id],
                                  th=seq.th))
            return

        # Derivation (primitive or macro): resolve prevs first.
        prev_ths = []
        for prev in seq.prevs:
            if not seq.id.can_depend_on(prev):
                raise CheckProofException(
                    "id %s cannot depend on %s" % (seq.id, prev))
            pth = ths.get(prev)
            if pth is None:
                raise CheckProofException("previous item not found")
            prev_ths.append(pth)

        if rule in primitive_deriv:
            rule_fun, _ = primitive_deriv[rule]
            try:
                res_th = (rule_fun(*prev_ths) if seq.args is None
                          else rule_fun(seq.args, *prev_ths))
            except InvalidDerivationException:
                raise CheckProofException("invalid derivation")
            except TypeError:
                raise CheckProofException(
                    "invalid input to derivation " + rule)
            if rpt is not None:
                rpt.apply_primitive_deriv()
            if seq.th is None:
                seq.th = res_th
            elif not res_th.can_prove(seq.th):
                raise CheckProofException(
                    "output does not match\n%s\n vs.\n%s" % (seq.th, res_th))
            ths[seq.id] = seq.th
            flat.append(seq)
            return

        if has_macro(rule):
            macro = get_macro(rule)
            assert macro.level is None or (isinstance(macro.level, int)
                                           and macro.level >= 0), \
                ("verify: invalid macro level " + str(macro.level))
            if macro.level == 0:
                # Computation oracle: expansion is impossible. Only
                # trusted names may evaluate; the result is emitted as
                # an oracle assumption line in the flattened stream
                # (the original macro line is untouched).
                if rule not in trust:
                    raise CheckProofException(
                        "oracle macro '%s' is not trusted (add it to the "
                        "trust set)" % rule)
                res_th = macro.eval(seq.args, prev_ths)
                if rpt is not None:
                    rpt.eval_macro(rule)
                if seq.th is None:
                    seq.th = res_th
                elif not res_th.can_prove(seq.th):
                    raise CheckProofException(
                        "output does not match\n%s\n vs.\n%s"
                        % (seq.th, res_th))
                ths[seq.id] = seq.th
                flat.append(ProofItem(seq.id, "oracle", args=rule,
                                      prevs=[], th=res_th))
                return
            # Closable macro: expand to its primitive stream and emit the
            # expansion's lines inline (flattened). The macro line itself is
            # bound to a reference line at its own id -- later lines cite the
            # macro line, not its expansion items, so the line must stand in
            # the flattened stream as well.
            args = seq.args
            # auto_close closes the current line by citing a fact. When the
            # fact only matches it schematically, specialize it here (the
            # expander owns both theorems, so it is the only place that can
            # compute the instantiation) and record it as visible primitive
            # lines; the auto_close line itself stays argument-free.
            if rule == "auto_close" and seq.th is not None and prev_ths \
                    and prev_ths[0].prop != seq.th.prop:
                try:
                    args = matcher.first_order_match(
                        prev_ths[0].prop, seq.th.prop, Inst())
                except matcher.MatchException:
                    raise CheckProofException(
                        "auto_close: fact %s does not match the goal"
                        % seq.prevs[0])
            mkey = None
            checked = None
            if compute_only and memo is not None:
                # Incremental reuse: identical inputs (rule, args, the
                # very same premise theorems, and the same line
                # statement) means an identical derivation, so the
                # previous expansion result stands.  flat is unused in
                # compute_only, so skipping the expansion's emitted
                # lines is safe here; a changed line or premise changes
                # the key and misses.
                stated = seq.th
                thy = theory.thy
                mkey = _memo_key(rule, args, prev_ths, stated, thy)
                cached = memo.get(mkey)
                if cached is not None and cached[1] is stated \
                        and cached[2] is thy \
                        and len(cached[0]) == len(prev_ths) \
                        and all(a is b for a, b in zip(cached[0], prev_ths)):
                    if not memo_selfcheck:
                        # Same write-back/consistency as the miss path
                        # below, minus the (expensive) re-expansion: a
                        # fresh line that matches an earlier derivation
                        # still needs its own theorem cached onto it.
                        res_th = cached[3]
                        if stated is None:
                            seq.th = res_th
                        elif seq.th is not res_th and not res_th.can_prove(seq.th):
                            raise CheckProofException(
                                "output does not match\n%s\n vs.\n%s"
                                % (seq.th, res_th))
                        ths[seq.id] = seq.th
                        return
                    # Audit mode: fall through and confirm the cached
                    # result against a fresh derivation (below).
                    checked = cached[3]
            expanded = macro.expand(
                seq.id, args, list(zip(seq.prevs, prev_ths)))
            if rpt is not None:
                rpt.expand_macro(rule)
            for s in expanded.items:
                emit(s)
            res_th = expanded.items[-1].th
            if checked is not None and not _thm_confirmed(res_th, checked):
                raise CheckProofException(
                    "incremental verify self-check: cached theorem is not "
                    "confirmed by a fresh derivation\n%s\n vs.\n%s"
                    % (checked, res_th))
            if seq.th is None:
                seq.th = res_th
            elif not res_th.can_prove(seq.th):
                raise CheckProofException(
                    "output does not match\n%s\n vs.\n%s" % (seq.th, res_th))
            ths[seq.id] = seq.th
            if mkey is not None and seq.th is not None:
                # Store under the statement as it now stands.  A line
                # whose statement was not yet known re-derives once
                # more on the next call, then hits from then on.
                memo[_memo_key(rule, args, prev_ths, seq.th, thy)] = (
                    tuple(prev_ths), seq.th, thy, seq.th)
            flat.append(ProofItem(seq.id, "reference",
                                  prevs=[expanded.items[-1].id], th=seq.th))
            return

        raise CheckProofException("proof method not found: " + rule)

    # Walk the proof. Every line is emitted (derived and checked) in
    # both modes -- compute_only only skips the final independent
    # replay. Trusting cached theorems would let an edited line's
    # statement be accepted without derivation (audit §7.1: the kernel
    # primitives are the only source of theorems), so the incremental
    # mode still resolves each line; it just skips the second,
    # independent pass over the flattened stream.
    for seq in prf.items:
        emit(seq)

    if compute_only:
        # No full replay in incremental mode: the method layer only
        # needs the newly-added line to derive. Full verify() runs the
        # independent replay below.
        for seq in reversed(prf.items):
            if seq.rule != "" and seq.th is not None:
                return seq.th
        return None

    # Independent primitive replay of the flattened stream.
    flat_proof = Proof()
    flat_proof.items = list(flat)
    try:
        res_th, holes = replay_mod.replay(flat_proof, axioms=axioms)
    except ReplayException as e:
        raise CheckProofException(e.msg)

    # Trust report (audit §7.2): every non-primitive assumption the
    # proof rests on is recorded -- axiom lines and oracle lines into
    # the report; sorry holes are already in rpt.gaps.
    if rpt is not None:
        for rule, label, _th in holes:
            if rule == 'axiom':
                rpt.add_axiom_hole(label)
            elif rule == 'oracle':
                rpt.add_oracle_hole(label)

    # Final theorem = last non-empty line's statement (can_prove
    # accepts weaker hypotheses; stronger is rejected). Typing checked
    # once at the end.
    last = None
    for seq in reversed(prf.items):
        if seq.rule != "":
            last = seq
            break
    if last is not None:
        if last.th is None:
            last.th = res_th
        elif not res_th.can_prove(last.th):
            raise CheckProofException(
                "output does not match\n%s\n vs.\n%s" % (last.th, res_th))
        try:
            last.th.check_thm_type()
        except TypeCheckException:
            raise CheckProofException("typing error")
        return last.th
    return res_th


# ---------------------------------------------------------------------------
# Replay injection: method.stable_state.StableProofState lives above
# this layer.  The method layer wires it at import time; until then
# validate_theory raises instead of silently skipping proofs.
# ---------------------------------------------------------------------------

_replay_fn = None


def set_replay_fn(fn):
    """Register the proof replay function.

    fn(item, name, trust=frozenset()) must replay item.steps under
    item.vars and return the number of open goals (0 for a complete
    proof), raising on any replay failure.  trust is the caller's
    computation-oracle declaration (audit §7.1).
    """
    global _replay_fn
    _replay_fn = fn


def _replay(item, name, trust=frozenset()):
    assert _replay_fn is not None, (
        "verify: replay function not registered -- "
        "import method.stable_state (the method layer) first")
    return _replay_fn(item, name, trust=trust)


# ---------------------------------------------------------------------------
# Dependency-status resolution (cross-file, along the import DAG).
# ---------------------------------------------------------------------------

_FAILED_STATES = ('STEP_FAILED', 'DEP_FAILED', 'UNPROVED')


def _import_statuses(filename, seen=None):
    """Collect the cached statuses of theorems in the theories that
    filename imports (transitively), for cross-file dependency checks.

    Reads the .json status caches via load_status data; theories whose
    cache does not exist contribute nothing (validation of this file
    will still record their failures once they are validated
    themselves).
    """
    statuses = {}
    if seen is None:
        seen = {filename}
    for imp in basic.theory_cache.get(filename, {}).get('imports', []):
        if imp in seen:
            continue
        seen.add(imp)
        path = basic.status_cache_file(imp)
        if os.path.exists(path):
            try:
                with open(path, encoding='utf-8') as f:
                    data = json.load(f)
                for nm, st in data.get('theorems', {}).items():
                    statuses.setdefault(nm, st)
            except (OSError, ValueError):
                pass
        # transitive imports
        for nm, st in _import_statuses(imp, seen).items():
            statuses.setdefault(nm, st)
    return statuses


# ---------------------------------------------------------------------------
# Four-state judgement.
# ---------------------------------------------------------------------------

def validate_theory(filename, *, force=False, trust=frozenset()):
    """Validate all theorems in a theory file.

    Caching (see validate_theory_info for the precise rules):
    - a file whose source and whose imported theories are unchanged is
      returned from the .json cache without replay;
    - a file whose source changed re-plays only from its FIRST changed
      item onward (later items may depend on the edit, earlier ones are
      reused verbatim);
    - a file any of whose imports changed is re-validated in full;
    - theorems deleted from the source have their verdicts dropped from
      the in-memory tables at once.
    force=True ignores all of that and replays everything.

    trust -- names of computation-oracle macros admitted while
    replaying proofs (audit §7.1).  Empty default rejects every
    oracle; library validation passes the explicit set of the legacy
    computation oracles (audit line 366 debt).

    Returns (statuses, errors) for THIS file's theorem entries:
    statuses maps theorem names to states ('VALID', 'STEP_FAILED',
    'DEP_FAILED', 'AXIOM', 'UNPROVED'); errors maps failed theorems
    to a message.  (The cross-theory tables in core.basic accumulate
    for /api/theory-status; they are not the return value.)
    """
    statuses, errors, _ = validate_theory_info(filename, force=force,
                                               trust=trust)
    return statuses, errors


def validate_theory_info(filename, *, force=False, trust=frozenset()):
    """Incremental core of validate_theory.

    Returns (statuses, errors, info) where info is
    {'reused': bool, 'start': int} -- 'reused' is True when the whole
    file came from cache, 'start' is the index of the first item
    actually replayed.
    """
    basic.load_theory(filename)
    cache = basic.theory_cache[filename]
    content = cache['content']
    names_now = _theorem_names(content)
    cached = basic.load_status_data(filename)
    meta = cached.get('meta', {})
    cached_thms = cached.get('theorems', {})

    # A theorem deleted from the source must lose its verdict right
    # away -- in memory as well as on disk.
    for name in set(cached_thms) - names_now:
        basic.drop_status(name)

    from core import incremental
    imports_epoch = incremental.imports_epoch(filename)
    same_source = meta.get('source_hash') == cache.get('source_hash')
    same_imports = meta.get('imports_epoch') == imports_epoch

    if not force and same_source and same_imports and cached_thms:
        for name, st in cached_thms.items():
            basic.set_status(name, st)
            basic.set_error(name, None)
        return (dict(cached_thms), {n: None for n in cached_thms},
                {'reused': True, 'start': len(content)})

    if not force and same_imports:
        # Same imports: everything before the first changed item still
        # holds, so replay only the suffix.
        start = incremental.first_diff_index(meta.get('item_hashes'),
                                             cache.get('item_hashes'))
    else:
        start = 0

    seed_names = _theorem_names(content[:start])
    seed_statuses = {n: cached_thms[n] for n in seed_names if n in cached_thms}
    seed_errors = {n: None for n in seed_statuses}
    statuses, errors = _validate_items(
        filename, trust=trust, start=start,
        seed_statuses=seed_statuses, seed_errors=seed_errors,
        imports_epoch=imports_epoch)
    return statuses, errors, {'reused': False, 'start': start}


def _theorem_names(content):
    """Names of the theorem entries (theorem/axiom) in a content list."""
    return {item.name for item in content if item.ty in ('thm', 'thm.ax')}


def _validate_items(filename, *, trust=frozenset(), start=0,
                    seed_statuses=None, seed_errors=None,
                    imports_epoch=None):
    """Replay this file's items from index `start` onward.

    seed_statuses/seed_errors reuse the verdicts of items before
    `start`; they are trusted because the incremental verifier only
    calls this with a seed whose source hashes are unchanged and whose
    imported theories have not changed.  Returns (statuses, errors)
    for every theorem in the file.
    """
    content = basic.theory_cache[filename]['content']
    statuses = dict(seed_statuses) if seed_statuses else {}
    errors = dict(seed_errors) if seed_errors else {}
    imported = _import_statuses(filename)

    for item in content[start:]:
        name = item.name

        if item.ty == 'thm.ax':
            statuses[name] = 'AXIOM'
            basic.set_status(name, 'AXIOM')
            basic.set_error(name, None)
            continue

        if item.ty != 'thm':
            continue

        if not item.steps:
            statuses[name] = 'UNPROVED'
            basic.set_status(name, 'UNPROVED')
            basic.set_error(name, None)
            continue

        # Check whether any referenced theorem has a failed state --
        # in this file (already judged) or an imported one (cached).
        # All three failure states count, including UNPROVED: a proof
        # that depends on an unproved theorem is dependency-failed
        # (audit §7.4 deviation 1 -- the monitor version only treated
        # STEP_FAILED/DEP_FAILED as failures).
        dep_failed = False
        for step in item.steps:
            dep = step.get('theorem')
            if not dep:
                continue
            dep_status = statuses.get(dep, imported.get(dep))
            if dep_status in _FAILED_STATES:
                dep_err = errors.get(dep, '')
                errors[name] = ('depends on %s which is %s%s'
                                % (dep, dep_status,
                                   (': ' + dep_err) if dep_err else ''))
                dep_failed = True
                break

        if dep_failed:
            statuses[name] = 'DEP_FAILED'
            basic.set_status(name, 'DEP_FAILED')
            basic.set_error(name, errors[name])
            continue

        # Replay the proof via the injected stable-ID pipeline.
        try:
            with theory.fresh_theory():
                context.set_context(filename, limit=('thm', name),
                                    vars=dict(item.vars) if item.vars else {})
                gaps = _replay(item, name, trust=trust)
            statuses[name] = 'VALID' if gaps == 0 else 'STEP_FAILED'
            errors[name] = None if gaps == 0 else 'proof has %d open goal(s)' % gaps
        except Exception as e:
            statuses[name] = 'STEP_FAILED'
            errors[name] = '%s: %s' % (e.__class__.__name__, str(e))

        basic.set_status(name, statuses[name])
        basic.set_error(name, errors[name])

    basic.save_status(filename, statuses, imports_epoch=imports_epoch)
    return statuses, errors

# Author: AI assistant

"""Translate .imp program files into .pyhol theorem files.

.imp is syntactic sugar for writing Hoare triples.  The translator
desugars it into .pyhol: one theorem per verification condition (VC).
Each VC is an independent proof obligation.

  z3-provable VC  ->  proof with 0: z3
  unprovable VC   ->  proof with 0: sorry  (user proves interactively)

Re-translation preserves existing proofs: VCs whose proposition is
unchanged keep their proof steps; only changed/new VCs are reset.

Semantics: Burstall-Bornat style heap model.  The state is a pair
Pair (reg :: nat => nat) (heap :: nat => nat): program variables live
in the register array (assigned variables get indices in declaration
order), and the heap is an independent array.  !p reads heap st p,
p := new allocates lim + 1 and advances the user variable lim.

Limitations:
* nat/ref only (reg and heap are nat-valued arrays; no int).
* Heap safety is not checked: !p := v is a total function update.
"""

from syntax import logicops
import os
import re
import textwrap

from kernel.type import TFun, TConst
from syntax.numeral import NatType, IntType
from kernel import term
from kernel.term import Term, Var, Lambda, Eq, Const
from syntax.numeral import Number
from syntax.logicops import Not, true, false
from kernel import theory
from framework import basic
from framework.logic import mk_if
from imperative import expr as expr_mod
from imperative import com as com_mod
from imperative import parser2
from imperative import imp
from syntax import printer, settings, pyhol
from solvers import z3wrapper
from domains.nat import util_nat as nat


class CompileError(Exception):
    """Error while parsing or translating an .imp file."""


# Inductive predicates of the imported theories that may appear in
# assertions.  Each entry maps the predicate name used in .imp files to
# the HOL constant name.  Types are resolved from the theory at compile
# time (see _register_predicates).
_assertion_preds = ['ll', 'reached']


def _load_theories(imports):
    """Load the given theories (and their dependencies) into the current
    theory, in dependency order.  Unlike repeated basic.load_theory calls
    (each of which resets the global theory to EmptyTheory), this merges
    all the imported theories into a single context."""
    from framework.basic import load_theory_cache, load_metadata
    load_metadata()
    theory_cache = load_theory_cache.__globals__.get('theory_cache', {})
    closure = []

    def dfs(name):
        if name in closure:
            return
        if name in theory_cache:
            for import_name in theory_cache[name]['imports']:
                dfs(import_name)
        closure.append(name)

    for nm in imports:
        dfs(nm)
    if 'hoare' not in closure:
        closure.append('hoare')
    for nm in closure:
        cache = load_theory_cache(nm)
        for item in cache['content']:
            if item.error is None:
                try:
                    theory.thy.unchecked_extend(item.get_extension())
                except theory.TheoryException:
                    pass  # Skip duplicates


def _register_predicates():
    """Register inductive predicates of the loaded theories for use in
    assertions (e.g. ll(p, s)).  This is safe to call multiple times."""
    from kernel.type import TFun, BoolType
    from syntax.numeral import NatType
    for pred in _assertion_preds:
        if theory.thy.has_term_sig(pred) and pred not in expr_mod.global_fnames:
            T = theory.thy.get_term_sig(pred)
            expr_mod.global_fnames[pred] = (pred, T)
    _register_recursive_preds()


def _register_recursive_preds():
    """Register inductive predicates of the loaded theories for Z3
    recursive functions.

    Recursive function equations are extracted mechanically from the
    theory's own constructor theorems, not hand-written.  For a predicate
    P with base constructor (e.g. ll_null: P null s) and step constructor
    (e.g. ll_step: ~(x = null) --> P (s x) s --> P x s), the equation
    P args = (base | ~(arg = null) & step_prems) is built from the two
    theorem props, with null rewritten via null_def.
    """
    from kernel.term import Var, Forall, Eq, Const
    from syntax.logicops import Or, And
    from syntax.numeral import NatType
    from framework import conv

    def strip_foralls(t):
        """Strip outer !x_1 ... x_n. Stored theorems use free Vars
        (no quantifier prefix), so also collect the head's argument
        variables in argument order."""
        arg_vars = []
        while t.is_forall():
            abs_t = t.arg
            v = Var(abs_t.var_name, abs_t.var_T)
            arg_vars.append(v)
            t = abs_t.subst_bound(v)
        return t, arg_vars

    def base_from_ctor(base_name, step_lhs):
        """Base disjunct of the expansion: either arg = null (null
        constructor) or arg_i = arg_j (reflexive constructor)."""
        th = theory.thy.get_theorem(base_name, svar=False)
        base_lhs, _ = strip_foralls(th.prop)
        args = base_lhs.args
        null_c = Const('null', NatType)
        for a in args:
            if a == null_c:
                return None  # null branch handled via rewrite below
        for i in range(len(args)):
            for j in range(i + 1, len(args)):
                if args[i] == args[j]:
                    return Eq(args[i], args[j])
        raise CompileError("Cannot extract base case from constructor %s" % base_name)

    def unfold_from_ctors(pred_name, base_name, step_name):
        if not theory.thy.has_theorem(step_name):
            return None
        th = theory.thy.get_theorem(step_name, svar=False)
        t, arg_vars = strip_foralls(th.prop)
        assms = []
        while t.is_implies():
            assms.append(t.arg1)
            t = t.arg
        lhs = t
        conj = And(*assms) if len(assms) > 1 else assms[0]
        base = base_from_ctor(base_name, lhs)
        if base is None:
            base = Eq(lhs.args[0], Const('null', NatType))
        rhs = Or(base, conj)
        if theory.thy.has_theorem('null_def'):
            cv = conv.top_conv(conv.try_conv(conv.rewr_conv('null_def')))
            rhs = cv.eval(rhs).rhs
        body = Eq(lhs, rhs)
        if not arg_vars:
            arg_vars = [v for v in lhs.args if isinstance(v, Var)]
        # Quantify in lhs argument order, so that stripping the foralls
        # in register_recursive_defs yields the same order as t.args.
        for v in arg_vars:
            body = Forall(v, body)
        return body

    for pred, base, step in [
            ('ll', 'll_null', 'll_step'),
            ('reached', 'r_self', 'r_step')]:
        eq_term = unfold_from_ctors(pred, base, step)
        if eq_term is not None:
            z3wrapper.register_recursive_pred(pred, eq_term)


class ImpProgram:
    """Intermediate representation of a single program in an .imp file."""

    def __init__(self):
        self.name = None
        self.vars = []      # list of (name, ty)
        self.pre = None
        self.post = None
        self.body = None


class ImpFile:
    """Parsed .imp file: theory header + list of programs."""

    def __init__(self):
        self.theory = None
        self.imports = []
        self.programs = []


def parse_imp(text):
    """Parse .imp text into an ImpFile (theory + multiple programs)."""
    imp_file = ImpFile()
    lines = text.split('\n')
    i = 0
    cur_prog = None

    def finish_prog(prog):
        if prog is not None:
            if prog.name is None or prog.pre is None or prog.post is None or not prog.body:
                raise CompileError("Program missing one of: name, pre, post, body.")
            imp_file.programs.append(prog)

    while i < len(lines):
        raw = lines[i].strip()
        if not raw or raw.startswith('//') or raw.startswith('#'):
            i += 1
            continue
        m = re.match(r'^theory\s+(\S+)\s*$', raw)
        if m:
            imp_file.theory = m.group(1)
            i += 1
            continue
        m = re.match(r'^imports\s+(.+)$', raw)
        if m:
            imp_file.imports = [s.strip() for s in m.group(1).split(',') if s.strip()]
            i += 1
            continue
        m = re.match(r'^program\s+(\S+)\s*$', raw)
        if m:
            finish_prog(cur_prog)
            cur_prog = ImpProgram()
            cur_prog.name = m.group(1)
            i += 1
            continue
        if cur_prog is None:
            raise CompileError("Line %d: expected 'theory' or 'program' section." % (i + 1))
        m = re.match(r'^vars:\s*(.+)$', raw)
        if m:
            for decl in m.group(1).split(','):
                decl = decl.strip()
                if not decl:
                    continue
                nm, _, ty = decl.partition(':')
                nm, ty = nm.strip(), ty.strip()
                if not nm or not ty:
                    raise CompileError("Line %d: bad variable declaration '%s'." % (i + 1, decl))
                cur_prog.vars.append((nm, ty))
            i += 1
            continue
        m = re.match(r'^pre:\s*(.+)$', raw)
        if m:
            cur_prog.pre = m.group(1).strip()
            i += 1
            continue
        m = re.match(r'^post:\s*(.+)$', raw)
        if m:
            cur_prog.post = m.group(1).strip()
            i += 1
            continue
        m = re.match(r'^body:', raw)
        if m:
            body_lines = []
            i += 1
            while i < len(lines):
                line = lines[i].strip()
                # Stop body at next program/keyword
                if re.match(r'^program\s+', line):
                    break
                if not line or line.startswith('//') or line.startswith('#'):
                    i += 1
                    continue
                body_lines.append(line)
                i += 1
            cur_prog.body = '\n'.join(body_lines)
            continue
        raise CompileError("Line %d: unrecognized section '%s'." % (i + 1, raw[:40]))
    finish_prog(cur_prog)
    if not imp_file.programs:
        raise CompileError("No program found in .imp file.")
    return imp_file


def get_assigned_vars(com):
    """Collect names of variables assigned in the command."""
    res = set()
    if isinstance(com, com_mod.Assign):
        assert isinstance(com.v, expr_mod.Var), "Assign target must be a variable"
        res.add(com.v.name)
    elif isinstance(com, com_mod.Seq):
        res |= get_assigned_vars(com.c1)
        res |= get_assigned_vars(com.c2)
    elif isinstance(com, com_mod.Cond):
        res |= get_assigned_vars(com.c1)
        res |= get_assigned_vars(com.c2)
    elif isinstance(com, com_mod.While):
        res |= get_assigned_vars(com.c)
    elif isinstance(com, com_mod.Call):
        res.add(com.result)
    elif isinstance(com, com_mod.Assert):
        pass
    elif isinstance(com, com_mod.ArrayAssign):
        res.add(com.name)
    elif isinstance(com, com_mod.New):
        res.add(com.v)
        res.add('lim')
    elif isinstance(com, com_mod.For):
        res |= get_assigned_vars(com.init)
        res |= get_assigned_vars(com.step)
        res |= get_assigned_vars(com.c)
    return res


def stmt_may_break(com):
    """Whether executing the command may execute a break (in the enclosing loop)."""
    if isinstance(com, com_mod.Break):
        return True
    elif isinstance(com, com_mod.Seq):
        return stmt_may_break(com.c1) or stmt_may_break(com.c2)
    elif isinstance(com, com_mod.Cond):
        return stmt_may_break(com.c1) or stmt_may_break(com.c2)
    elif isinstance(com, com_mod.While):
        return False  # inner loops capture their own breaks
    elif isinstance(com, com_mod.For):
        return False  # inner loops capture their own breaks
    return False


class Translator:
    """Translate an ImpProgram into HOL terms."""

    def __init__(self, prog, prog_table=None):
        self.prog = prog
        self.prog_table = prog_table or {}
        # Check types: nat, nat[N], ref supported (heap model is nat-valued:
        # the state is Pair (reg :: nat => nat) (heap :: nat => nat), both
        # variable store and heap are arrays of naturals).
        for nm, ty in prog.vars:
            if not re.match(r'^(nat)(\[\d+\])?$', ty) and ty != 'ref':
                raise CompileError("Variable '%s': unsupported type %s (heap "
                                   "model supports nat, nat[N], ref only)." % (nm, ty))
        has_ref = any(ty == 'ref' for _, ty in prog.vars)
        self.value_T = NatType
        self.T = TConst('state')
        self.st = Var('st', self.T)
        reg_T = TFun(self.T, TFun(NatType, NatType))
        self._reg_const = Const('reg', reg_T)
        self._heap_const = Const('heap', reg_T)
        # The heap of the current state; 's' in assertions denotes it.
        self.s = self._heap_const(self.st)

        # Parse array declarations: "nat[4]" -> (type, size)
        self.array_info = {}  # name -> (base_index, size)
        parsed_vars = []
        for nm, ty in prog.vars:
            m = re.match(r'^(\w+)\[(\d+)\]$', ty)
            if m:
                parsed_vars.append((nm, m.group(1), int(m.group(2))))
            else:
                parsed_vars.append((nm, ty, None))

        # State variables: those assigned in the body, in declaration order.
        com = parser2.parse_com(prog.body)
        assigned = get_assigned_vars(com)
        self.state_idx = {}   # name -> index (for scalars) or base index (for arrays)
        next_idx = 0
        for nm, ty, sz in parsed_vars:
            if sz is not None:
                # Arrays always go in state, reserving sz consecutive indices.
                self.array_info[nm] = (next_idx, sz)
                self.state_idx[nm] = next_idx
                next_idx += sz
            elif nm in assigned:
                self.state_idx[nm] = next_idx
                next_idx += 1
        self.params = [nm for nm, ty in prog.vars if nm not in self.state_idx]
        self.next_flag = 0   # counter for compiler-generated flag variables

        # Reserved prefix for compiler-generated variables.
        for nm, ty in prog.vars:
            if nm.startswith('__imp_'):
                raise CompileError("Variable '%s': names starting with '__imp_' are reserved." % nm)

        # Stack of enclosing loops, each {'flag': name, 'breaks': [pc...]}.
        self.loop_stack = []
        # Path conditions (as HOL terms over s) for break recording.
        self.pc_stack = []

        self.com = com
        # First pass: translate once to allocate all compiler-generated
        # flag variables, so indices are stable before real translation.
        self.translate_com(com)
        self.com_term = self.translate_com(com)

    def _reg(self, idx):
        """reg st idx: the program variable register at index idx."""
        return self._reg_const(self.st)(idx)

    def new_flag_var(self):
        """Allocate a compiler-generated flag variable (nat 0/1) in the state."""
        name = '__imp_done%d' % self.next_flag
        if name not in self.state_idx:
            self.state_idx[name] = len(self.state_idx)
        return name

    def translate_expr(self, e):
        """Translate an expression to a HOL term (nat semantics)."""
        if isinstance(e, expr_mod.Var):
            if e.name == 's':
                if e.name in self.state_idx or e.name in self.params:
                    raise CompileError("Variable name 's' is reserved for the heap.")
                # The heap, usable in assertions (e.g. ll(p, s)).
                return self.s
            elif e.name in self.state_idx:
                return self._reg(Number(NatType, self.state_idx[e.name]))
            elif e.name in self.params:
                return Var(e.name, self.value_T)
            else:
                raise CompileError("Variable '%s' not declared in vars." % e.name)
        elif isinstance(e, expr_mod.ArrayElt):
            if e.ident.name not in self.array_info:
                raise CompileError("Array access to non-array '%s'." % e.ident.name)
            return self._reg(self._array_index(e.ident.name, e.idx))
        elif isinstance(e, expr_mod.Deref):
            # Heap read: !e = heap st (e).
            addr = self.translate_expr(e.e)
            return self.s(addr)
        elif isinstance(e, expr_mod.Const):
            if isinstance(e.val, bool):
                return true if e.val else false
            else:
                return Number(self.value_T, e.val)
        elif isinstance(e, expr_mod.Op):
            if len(e.args) == 1:
                arg = self.translate_expr(e.args[0])
                if e.op == "-":
                    return -arg
                elif e.op == "~":
                    return ~arg
                raise CompileError("Unknown unary operator '%s'." % e.op)
            else:
                a, b = self.translate_expr(e.args[0]), self.translate_expr(e.args[1])
                if e.op == "+":
                    return a + b
                elif e.op == "-":
                    return a - b
                elif e.op == "*":
                    return a * b
                elif e.op == "==":
                    return Eq(a, b)
                elif e.op == "!=":
                    return Not(Eq(a, b))
                elif e.op == "<=":
                    return a <= b
                elif e.op == "<":
                    return a < b
                elif e.op == ">=":
                    return b <= a
                elif e.op == ">":
                    return b < a
                elif e.op == "&":
                    return logicops.And(a, b)
                elif e.op == "|":
                    return logicops.Or(a, b)
                elif e.op == "-->":
                    return term.Implies(a, b)
                elif e.op == "<-->":
                    return term.Eq(a, b)
                raise CompileError("Unknown operator '%s'." % e.op)
        elif isinstance(e, expr_mod.ITE):
            return mk_if(self.translate_expr(e.cond),
                         self.translate_expr(e.e1),
                         self.translate_expr(e.e2))
        elif isinstance(e, expr_mod.Fun):
            if e.fname not in expr_mod.global_fnames:
                raise CompileError("Unknown function '%s'." % e.fname)
            from kernel.term import Const
            if e.fname == 'll':
                # ll(p, s): heap predicate evaluated on the heap.
                if len(e.args) != 2:
                    raise CompileError("ll takes two arguments: ll(p, s).")
                p = self.translate_expr(e.args[0])
                s_t = self.translate_expr(e.args[1])
                name, T = expr_mod.global_fnames['ll']
                return Const(name, T)(p, s_t)
            name, T = expr_mod.global_fnames[e.fname]
            return Const(name, T)(*[self.translate_expr(a) for a in e.args])
        else:
            raise CompileError("Expression form not supported yet: %s" % e)

    def translate_pred(self, text):
        """Translate a condition text (pre/post/invariant) to a lambda over the state."""
        e = parser2.parse_cond(text)
        return Lambda(self.st, self.translate_expr(e))

    def translate_com(self, com, flag=None):
        """Translate a Com AST to a HOL com term.

        flag: name of the current loop's flag variable (or None outside
        any loop).  break/continue are only meaningful inside a loop.

        """
        if isinstance(com, com_mod.Skip):
            return imp.Skip(self.T)
        elif isinstance(com, com_mod.Assign):
            assert isinstance(com.v, expr_mod.Var), "Assign target must be a variable"
            if com.v.name not in self.state_idx:
                raise CompileError("Assigning to undeclared or non-state variable '%s'." % com.v.name)
            idx = Number(NatType, self.state_idx[com.v.name])
            b = Lambda(self.st, self.translate_expr(com.e))
            return imp.AssignV(self.T)(Lambda(self.st, idx), b)
        elif isinstance(com, com_mod.Seq):
            return self.translate_seq(com.c1, com.c2, flag)
        elif isinstance(com, com_mod.Cond):
            b_term = self.translate_expr(com.b)
            b = Lambda(self.st, b_term)
            self.pc_stack.append(b_term)
            c1 = self.translate_com(com.c1, flag)
            c2 = self.translate_com(com.c2, flag)
            self.pc_stack.pop()
            return imp.Cond(self.T)(b, c1, c2)
        elif isinstance(com, com_mod.While):
            return self.translate_while(com, flag)
        elif isinstance(com, com_mod.For):
            return self.translate_for(com, flag)
        elif isinstance(com, com_mod.ArrayAssign):
            return self.translate_array_assign(com)
        elif isinstance(com, com_mod.DerefAssign):
            return self.translate_deref_assign(com)
        elif isinstance(com, com_mod.New):
            return self.translate_new(com)
        elif isinstance(com, com_mod.Break):
            if not self.loop_stack:
                raise CompileError("break outside of a loop.")
            ctx = self.loop_stack[-1]
            if ctx['flag'] is None:
                raise CompileError("break: internal error (no flag).")
            pc = logicops.And(*self.pc_stack) if self.pc_stack else true
            ctx['breaks'].append(pc)
            return imp.AssignV(self.T)(Lambda(self.st, Number(NatType, self.state_idx[ctx['flag']])),
                                       Lambda(self.st, Number(NatType, 1)))
        elif isinstance(com, com_mod.Assert):
            return self.translate_assert(com)
        elif isinstance(com, com_mod.Call):
            return self.translate_call(com)
        elif isinstance(com, com_mod.Continue):
            if not self.loop_stack:
                raise CompileError("continue outside of a loop.")
            return imp.Skip(self.T)
        raise CompileError("Unknown command form.")

    def translate_seq(self, c1, c2, flag):
        """Translate a sequence, guarding statements after a possible break."""
        # Translate the two halves of a Seq.  c2 is executed after c1; if
        # c1 may execute a break, every statement of c2 must be guarded by
        # (flag == 0).  The same guard applies transitively to c2's tail.
        c1_term = self.translate_com(c1, flag)
        if stmt_may_break(c1):
            c2_term = self.guard_after_break(c2, flag)
        else:
            c2_term = self.translate_com(c2, flag)
        return imp.Seq(self.T)(c1_term, c2_term)

    def guard_after_break(self, com, flag):
        """Translate a command, wrapping it so that it only runs while the
        flag is still 0 (i.e. no break has been executed yet)."""
        if isinstance(com, com_mod.Seq):
            return self.translate_seq(com.c1, com.c2, flag)
        elif isinstance(com, com_mod.Cond):
            b_term = self.translate_expr(com.b)
            b = Lambda(self.st, b_term)
            self.pc_stack.append(b_term)
            c1 = self.guard_after_break(com.c1, flag)
            c2 = self.guard_after_break(com.c2, flag)
            self.pc_stack.pop()
            return imp.Cond(self.T)(b, c1, c2)
        elif isinstance(com, com_mod.While):
            return self.translate_while(com, flag, guard=True)
        elif isinstance(com, com_mod.For):
            return self.translate_for(com, flag, guard=True)
        else:
            flag_zero = Eq(self._reg(Number(NatType, self.state_idx[flag])), Number(NatType, 0))
            return imp.Cond(self.T)(Lambda(self.st, flag_zero),
                                    self.translate_com(com, flag),
                                    imp.Skip(self.T))

    def loop_invariant(self, inv, ctx):
        """Strengthen the user invariant with the break flag constraints:
        inv & flag in {0,1} & (flag == 1 --> OR of the break point path
        conditions).

        flag in {0,1} is written as (flag == 0 | flag == 1) rather than
        flag <= 1, because z3 encodes nat as int without a non-negativity
        constraint on function values, so flag <= 1 would admit flag = -1."""
        zero = Number(NatType, 0)
        one = Number(NatType, 1)
        flag = self._reg(Number(NatType, self.state_idx[ctx['flag']]))
        flag_in_01 = logicops.Or(Eq(flag, zero), Eq(flag, one))
        if not ctx['breaks']:
            return Lambda(self.st, logicops.And(inv, flag_in_01))
        flag_eq_1 = Eq(flag, one)
        return Lambda(self.st, logicops.And(inv, flag_in_01,
                                        term.Implies(flag_eq_1, logicops.Or(*ctx['breaks']))))

    def translate_while(self, com, flag, guard=False):
        """Translate a While.  A fresh break flag is introduced only if the
        loop body may execute a break (otherwise the flag would leak into
        the exit verification condition and make it unprovable)."""
        inv_term = self.translate_expr(com.inv)
        if stmt_may_break(com.c):
            f = self.new_flag_var()
            ctx = {'flag': f, 'breaks': []}
            self.loop_stack.append(ctx)
            body = self.guard_after_break(com.c, flag=f)
            self.loop_stack.pop()
            b = Lambda(self.st, logicops.And(self.translate_expr(com.b),
                                         Eq(self._reg(Number(NatType, self.state_idx[f])), Number(NatType, 0))))
            inv = self.loop_invariant(inv_term, ctx)
            wh = imp.While(self.T)(b, inv, body)
            init = imp.AssignV(self.T)(Lambda(self.st, Number(NatType, self.state_idx[f])),
                                       Lambda(self.st, Number(NatType, 0)))
            res = imp.Seq(self.T)(init, wh)
        else:
            b = Lambda(self.st, self.translate_expr(com.b))
            ctx = {'flag': None, 'breaks': []}
            self.loop_stack.append(ctx)
            body = self.translate_com(com.c, flag)
            self.loop_stack.pop()
            wh = imp.While(self.T)(b, Lambda(self.st, inv_term), body)
            res = wh
        if guard:
            flag_zero = Eq(self._reg(Number(NatType, self.state_idx[flag])), Number(NatType, 0))
            res = imp.Cond(self.T)(Lambda(self.st, flag_zero), res, imp.Skip(self.T))
        return res

    def _array_index(self, name, idx_expr):
        """Compute state index for array access: base + idx."""
        base, size = self.array_info[name]
        idx_term = self.translate_expr(idx_expr)
        return nat.plus(Number(NatType, base), idx_term)

    def translate_array_assign(self, com):
        """a[i] := v -> Cond(0 <= i < size, Assign(base+i, v), stuck).

        Generates bounds check VC + array element update.
        """
        if com.name not in self.array_info:
            raise CompileError("Array assignment to non-array '%s'." % com.name)
        base, size = self.array_info[com.name]
        idx_term = self.translate_expr(com.idx)
        state_idx = self._array_index(com.name, com.idx)
        val_term = self.translate_expr(com.e)

        # Bounds check: 0 <= i AND i < size
        bounds = logicops.And(
            nat.less_eq(Number(NatType, 0), idx_term),
            nat.less(idx_term, Number(NatType, size))
        )

        assign = imp.AssignV(self.T)(Lambda(self.st, state_idx), Lambda(self.st, val_term))
        skip = imp.Skip(self.T)
        b_true = Lambda(self.st, logicops.true)
        stuck = imp.While(self.T)(b_true, Lambda(self.st, false), skip)
        return imp.Cond(self.T)(Lambda(self.st, bounds), assign, stuck)

    def translate_deref_assign(self, com):
        """!p := v -> AssignH p v: write v to heap address p."""
        idx_term = self.translate_expr(com.ptr)
        val_term = self.translate_expr(com.e)
        return imp.AssignH(self.T)(Lambda(self.st, idx_term), Lambda(self.st, val_term))

    def translate_new(self, com):
        """p := new -> p := lim + 1; lim := lim + 1.

        lim is a user-declared nat variable holding the allocation
        frontier.  Fresh addresses are lim + 1 (0 is null); both updates
        are register assignments (variables live in the reg array).
        """
        if com.v not in self.state_idx:
            raise CompileError("new: target variable '%s' is not a state variable." % com.v)
        if 'lim' not in self.state_idx:
            raise CompileError("new: variable 'lim' (nat) must be declared for allocation.")
        v_idx = Number(NatType, self.state_idx[com.v])
        lim_idx = Number(NatType, self.state_idx['lim'])
        lim_val = self._reg(lim_idx)
        a = imp.AssignV(self.T)(Lambda(self.st, v_idx),
                                Lambda(self.st, nat.plus(lim_val, Number(NatType, 1))))
        b = imp.AssignV(self.T)(Lambda(self.st, lim_idx),
                                Lambda(self.st, nat.plus(lim_val, Number(NatType, 1))))
        return imp.Seq(self.T)(a, b)

    def translate_assert(self, com):
        """assert P -> Cond(P, Skip, While(true,true,Skip)).

        VCG generates: P ⟶ WP(rest, Q)  and  true (trivially).
        If P fails, program loops forever (partial correctness).
        """
        P = self.translate_expr(com.cond)
        skip = imp.Skip(self.T)
        b_true = Lambda(self.st, logicops.true)
        # While(true, false, Skip): invariant=false means WP=false.
        # Cond(P, Skip, While(true,false,Skip)) gives WP = P ∧ Q:
        #   true branch: P ⟶ Q
        #   false branch: ¬P ⟶ false = P  (P MUST hold)
        stuck = imp.While(self.T)(b_true, Lambda(self.st, false), skip)
        return imp.Cond(self.T)(Lambda(self.st, P), skip, stuck)

    def translate_call(self, com):
        """y := call f(args) -> Cond(pre_f, Assign(y, post_value), stuck).

        Extracts the result value from f's post (must be r == expr form).
        """
        if com.fname not in self.prog_table:
            raise CompileError("Call to unknown program: %s" % com.fname)
        spec = self.prog_table[com.fname]
        callee_vars = spec['vars']
        out_var = callee_vars[-1][0]

        # Map callee input vars to caller Expr objects
        from imperative.parser2 import parse_cond
        var_map = {}
        for i, arg in enumerate(com.args):
            if i < len(callee_vars) - 1:
                var_map[callee_vars[i][0]] = arg  # Expr object

        # Parse callee pre and substitute
        pre_expr = parse_cond(spec['pre'])
        pre_term = self.translate_expr(pre_expr.subst(var_map))

        # Parse callee post: must be "out_var == <expr>"
        post_expr = parse_cond(spec['post'])
        if not (isinstance(post_expr, expr_mod.Op) and post_expr.op == '=='
                and isinstance(post_expr.args[0], expr_mod.Var)
                and post_expr.args[0].name == out_var):
            raise CompileError("Call: callee post must be '%s == <expr>', got: %s" % (out_var, spec['post']))
        # Extract the value expression and substitute input vars
        value_expr = post_expr.args[1].subst(var_map)
        value_term = self.translate_expr(value_expr)

        # Assign result = value
        result_idx = Number(NatType, self.state_idx[com.result])
        assign = imp.AssignV(self.T)(Lambda(self.st, result_idx), Lambda(self.st, value_term))

        skip = imp.Skip(self.T)
        b_true = Lambda(self.st, logicops.true)
        stuck = imp.While(self.T)(b_true, Lambda(self.st, false), skip)
        return imp.Cond(self.T)(Lambda(self.st, pre_term), assign, stuck)


    def translate_for(self, com, flag, guard=False):
        """Translate a For by desugaring into a while (with a break flag
        only when the body may break)."""
        inv_term = self.translate_expr(com.inv)
        step = self.translate_com(com.step, flag)
        if stmt_may_break(com.c):
            f = self.new_flag_var()
            ctx = {'flag': f, 'breaks': []}
            self.loop_stack.append(ctx)
            body = self.guard_after_break(com.c, flag=f)
            self.loop_stack.pop()
            b = Lambda(self.st, logicops.And(self.translate_expr(com.cond),
                                         Eq(self._reg(Number(NatType, self.state_idx[f])), Number(NatType, 0))))
            inv = self.loop_invariant(inv_term, ctx)
            body = imp.Seq(self.T)(body, step)
            wh = imp.While(self.T)(b, inv, body)
            init = imp.AssignV(self.T)(Lambda(self.st, Number(NatType, self.state_idx[f])),
                                       Lambda(self.st, Number(NatType, 0)))
            res = imp.Seq(self.T)(init, imp.Seq(self.T)(self.translate_com(com.init, flag=f), wh))
        else:
            b = Lambda(self.st, self.translate_expr(com.cond))
            ctx = {'flag': None, 'breaks': []}
            self.loop_stack.append(ctx)
            body = imp.Seq(self.T)(self.translate_com(com.c, flag), step)
            self.loop_stack.pop()
            res = imp.Seq(self.T)(self.translate_com(com.init, flag), imp.While(self.T)(b, Lambda(self.st, inv_term), body))
        if guard:
            flag_zero = Eq(self._reg(Number(NatType, self.state_idx[flag])), Number(NatType, 0))
            res = imp.Cond(self.T)(Lambda(self.st, flag_zero), res, imp.Skip(self.T))
        return res


def _parse_existing_proofs(pyhol_text):
    """Parse an existing .pyhol text, return dict: prop_text -> steps.

    Used to preserve proofs across re-translation.  Prop keys are
    normalized: surrounding quotes stripped, whitespace collapsed.
    """
    if not pyhol_text:
        return {}
    try:
        from syntax import pyhol as pyhol_mod
        data = pyhol_mod.parse_pyhol(pyhol_text)
        result = {}
        for item in data.get('content', []):
            if item.get('ty') == 'thm' and 'steps' in item:
                prop = item.get('prop', '')
                if isinstance(prop, str):
                    # Strip surrounding quotes if present
                    prop = prop.strip()
                    if len(prop) >= 2 and prop[0] == '"' and prop[-1] == '"':
                        prop = prop[1:-1]
                    # Normalize whitespace for matching
                    prop = ' '.join(prop.split())
                    result[prop] = item['steps']
        return result
    except Exception:
        return {}


def compile_programs(imp_file, existing_pyhol_text=None, validate_steps=True):
    """Translate an ImpFile (theory + multiple programs) into .pyhol text.

    Each program's VCs become separate theorems named <prog>_vc_<N>.
    z3-provable VCs get z3; unprovable get sorry.  Existing proofs are
    preserved when the VC proposition is unchanged.

    Returns (pyhol_text, total_vcs, vcs) where vcs is a list of
    {program, index, name, prop, smt, proved} dicts.
    """
    existing = _parse_existing_proofs(existing_pyhol_text)
    all_vcs = []
    content = []
    with theory.fresh_theory():
        _load_theories(imp_file.imports or ['hoare'])
        # Register inductive predicates of the imported theories so they can
        # be used in assertions (e.g. ll(p, s)).
        _register_predicates()
        # Build program table for cross-program calls
        prog_table = {}
        for p in imp_file.programs:
            prog_table[p.name] = {'vars': p.vars, 'pre': p.pre, 'post': p.post}

        for prog in imp_file.programs:
            tr = Translator(prog, prog_table=prog_table)
            pre = tr.translate_pred(prog.pre)
            post = tr.translate_pred(prog.post)
            goal = imp.Valid(tr.T)(pre, tr.com_term, post)
            pt = imp.vcg_norm(tr.T, goal)
            vars_dict = {nm: 'nat' for nm in tr.params}

            prog_vcs = []
            with settings.global_setting(unicode=True):
                for A in pt.assums:
                    prop = ' '.join(printer.print_term(A).split())
                    smt_ok = z3wrapper.solve(A)
                    vc = {
                        'program': prog.name,
                        'index': len(prog_vcs),
                        'name': '%s_vc_%d' % (prog.name, len(prog_vcs)),
                        'prop': prop,
                        'smt': smt_ok,
                        'proved': smt_ok or (prop in existing),
                    }
                    prog_vcs.append(vc)
                    all_vcs.append(vc)

            for vc in prog_vcs:
                if vc['prop'] in existing and existing[vc['prop']]:
                    steps = existing[vc['prop']]
                elif vc['smt']:
                    steps = [{'method_name': 'z3', 'goal': 0}]
                else:
                    steps = [{'method_name': 'sorry', 'goal': 0}]
                content.append({
                    'ty': 'thm',
                    'name': vc['name'],
                    'vars': vars_dict,
                    'prop': vc['prop'],
                    'steps': steps,
                })

            # Main theorem: Valid P c Q, proven from VCs via vcg.
            # Other programs can reference this as the program's spec.
            with settings.global_setting(unicode=True, line_length=None):
                goal_text = ' '.join(printer.print_term(goal).split())
            # vcg produces one subgoal per VC. Assign stable IDs 1, 2, 3, ...
            vc_ids = list(range(1, len(prog_vcs) + 1))
            main_steps = [{'method_name': 'vcg', 'goal': 0, 'new_ids': vc_ids}]
            for i, vc in enumerate(prog_vcs):
                main_steps.append({
                    'method_name': 'rule',
                    'goal': vc_ids[i],
                    'theorem': vc['name'],
                })
            content.append({
                'ty': 'thm',
                'name': prog.name,
                'vars': vars_dict,
                'prop': goal_text,
                'steps': main_steps,
            })

        theory_data = {
            'name': imp_file.theory or imp_file.programs[0].name,
            'imports': imp_file.imports or ['hoare'],
            'description': 'translated from .imp',
            'content': content,
        }
        pyhol_text = pyhol.export_pyhol(theory_data)
    return pyhol_text, len(all_vcs), all_vcs


def compile_file(path, existing_pyhol_text=None):
    """Translate an .imp file on disk.  Returns (pyhol_text, num_vcs, vcs)."""
    with open(path, 'r', encoding='utf-8') as f:
        text = f.read()
    imp_file = parse_imp(text)
    return compile_programs(imp_file, existing_pyhol_text)

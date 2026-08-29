# Author: Bohua Zhan

import importlib
import importlib.util
from fractions import Fraction

if importlib.util.find_spec("z3"):
    import z3
    z3_loaded = True
else:
    z3_loaded = False

# Whether to check using z3.
check_z3 = True

from kernel.type import TFun, BoolType
from syntax.numeral import NatType, IntType, RealType
from kernel import term
from kernel.term import Term, Var, Comb, Abs, Inst, BoolType, Implies
from syntax.logicops import true, false
from kernel.thm import Thm
from kernel.proofterm import ProofTerm
from kernel import theory
from framework import logic

def _mk_int_power(base, exp):
    """Integer-sorted power node.  z3py's ** builds a Real-sorted
    heterogeneous node (operands stay Int) whose Z3 semantics is the
    REAL power, which drags every integer-power proof through ToReal
    congruences; Z3_mk_power keeps the Int sort so the reconstruction
    sees plain integer-power rewrite steps."""
    ctx = base.ctx
    ast = z3.Z3_mk_power(ctx.ref(), base.as_ast(), exp.as_ast())
    return z3.ArithRef(ast, ctx)
from framework import conv
from prover import fologic
from util import name


class Z3Exception(Exception):
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err


def convert_type(T, ctx):
    if T.is_tvar():
        return z3.DeclareSort(T.name, ctx)
    if T == NatType or T == IntType:
        return z3.IntSort(ctx)
    elif T == BoolType:
        return z3.BoolSort(ctx)
    elif T == RealType:
        return z3.RealSort(ctx)
    elif T.is_fun():
        domainT = convert_type(T.domain_type(), ctx)
        rangeT = convert_type(T.range_type(), ctx)
        if isinstance(domainT, tuple):
            raise Z3Exception("convert: unsupported type " + repr(T))
        if isinstance(rangeT, tuple):
            return tuple([domainT] + list(rangeT))
        else:
            return (domainT, rangeT)
    elif T.is_tconst() and T.name == 'set':
        domainT = convert_type(T.args[0], ctx)
        if isinstance(domainT, tuple):
            raise Z3Exception("convert: unsupported type " + repr(T))
        return (domainT, convert_type(BoolType, ctx))
    elif T.is_tconst() and T.name == 'prod':
        return prod_sort(T.args[0], T.args[1], ctx)[0]
    elif T.is_tconst() and T.name == 'state':
        # The program state (Pair (reg :: nat => nat) (heap :: nat => nat))
        # is a Z3 tuple of two arrays: the variable register and the heap.
        return prod_sort(TFun(NatType, NatType), TFun(NatType, NatType), ctx)[0]
    else:
        raise Z3Exception("convert: unsupported type " + repr(T))


_prod_cache = {}

def prod_sort(T1, T2, ctx):
    """Z3 tuple sort for the product type T1 * T2, with its constructor
    and projection functions.  Cached per type pair.  Function-typed
    components (e.g. the state's reg/heap arrays) become Z3 arrays."""
    key = (str(T1), str(T2))
    if key not in _prod_cache:
        def clean(s):
            return ''.join(c for c in s if c.isalnum() or c == '_')
        name = 'prod_%s_%s' % (clean(str(T1)), clean(str(T2)))
        s1 = array_sort(T1, ctx)
        s2 = array_sort(T2, ctx)
        tup, mk, (fst_proj, snd_proj) = z3.TupleSort(name, [s1, s2])
        _prod_cache[key] = (tup, mk, fst_proj, snd_proj)
    return _prod_cache[key]

def array_sort(T, ctx):
    """Sort of a function-typed value, represented as a Z3 array
    (following Boogie's encoding of maps as arrays)."""
    if T.is_fun():
        dom = convert_type(T.domain_type(), ctx)
        if isinstance(dom, tuple):
            raise Z3Exception("convert: cannot array-ify higher-order type " + repr(T))
        return z3.ArraySort(dom, array_sort(T.range_type(), ctx))
    else:
        return convert_type(T, ctx)

def curried_sorts(T, ctx):
    """Flatten a curried function type into the list of sorts of a Z3
    (uninterpreted) function declaration.  Function-typed parameters are
    represented as array sorts."""
    sorts = []
    while T.is_fun():
        dom = T.domain_type()
        if dom.is_fun():
            sorts.append(array_sort(dom, ctx))
        else:
            sorts.append(convert_type(dom, ctx))
        T = T.range_type()
    sorts.append(convert_type(T, ctx))
    return sorts

def convert_const(name, T, ctx):
    if T.is_fun():
        if name in recursive_preds:
            return z3.RecFunction(name, *curried_sorts(T, ctx))
        return z3.Const(name, array_sort(T, ctx))
    z3_T = convert_type(T, ctx)
    if isinstance(z3_T, tuple):
        return z3.Function(name, *z3_T)
    else:
        return z3.Const(name, z3_T)


# Inductive predicates (e.g. the linked-list predicate ll) that should be
# translated to Z3 as recursive functions.  Each entry maps the constant
# name to a closed HOL term of the form !x_1 ... x_n. P x_1 ... x_n = body,
# where P is the predicate and body is the (recursive) expansion.
recursive_preds = {}


def register_recursive_pred(name, eq_term):
    """Register an inductive predicate for translation as a Z3 recursive
    function.

    eq_term is a HOL term: !x_1 ... x_n. P x_1 ... x_n = body.
    """
    recursive_preds[name] = eq_term


# Recursive function declarations registered on each Z3 context.  The
# definitions are global to the context, so registering once per context
# is enough even if multiple solvers share it.
_registered_rec_defs = set()


def register_recursive_defs(ctx):
    """Register all recursive predicates as Z3 recursive functions
    (z3.RecFunction + z3.RecAddDefinition) on the given context.

    The registered equation !x_1 ... x_n. P x_1 ... x_n = body is turned
    into a genuine recursive definition: the recursive calls inside body
    refer to the same function, so Z3 evaluates them by recursion (and by
    simplification on ground arguments) instead of bounded expansion.
    """
    for name, eq_term in recursive_preds.items():
        key = (name, id(ctx))
        if key in _registered_rec_defs:
            continue
        body = eq_term
        arg_vars = []
        while body.is_forall():
            abs_t = body.arg
            v = Var(abs_t.var_name, abs_t.var_T)
            arg_vars.append(v)
            body = abs_t.subst_bound(v)
        lhs, rhs = body.arg1, body.arg
        # The Z3 function's parameters are ordered by the type of the
        # predicate (P :: T_1 => ... => T_n => bool), so the formal
        # parameters must be collected from the lhs arguments in
        # position order.  The forall prefix order is irrelevant (e.g.
        # ll :: nat => (nat => nat) => bool has prefix !s. !p. while its
        # parameters are p, s).
        z3_vars = []
        for a in lhs.args:
            if isinstance(a, Var):
                z3_vars.append(convert_const(a.name, a.T, ctx))
        z3_rhs = convert(rhs, [v.name for v in arg_vars], {}, {}, ctx)
        z3.RecAddDefinition(convert_const(name, lhs.head.get_type(), ctx), z3_vars, z3_rhs)
        _registered_rec_defs.add(key)


def convert(t, var_names, assms, to_real, ctx):
    """Convert term t to Z3 input."""
    cache = {}

    def rec(t):
        """Memoized converter: repeated subterms (e.g. huge state-update
        chains substituted into recursive expansions) are converted once."""
        if t._id in cache:
            return cache[t._id]
        r = rec_inner(t)
        cache[t._id] = r
        return r

    def rec_inner(t):
        if t.is_var():
            z3_t = convert_const(t.name, t.T, ctx)
            if t.T == NatType and t.name not in assms:
                assms[t.name] = z3_t >= 0
            return z3_t
        elif t.is_forall():
            nm = name.get_variant_name(t.arg.var_name, var_names)
            var_names.append(nm)
            v = Var(nm, t.arg.var_T)
            z3_v = convert_const(nm, t.arg.var_T, ctx)
            return z3.ForAll(z3_v, rec(t.arg.subst_bound(v)))
        elif t.is_exists():
            nm = name.get_variant_name(t.arg.var_name, var_names)
            var_names.append(nm)
            v = Var(nm, t.arg.var_T)
            z3_v = convert_const(nm, t.arg.var_T, ctx)
            return z3.Exists(z3_v, rec(t.arg.subst_bound(v)))
        elif t.is_number():
            # Return a Z3 numeral (in the current context), not a Python
            # number: otherwise `rec(a) == rec(b)` yields a Python bool
            # instead of a BoolRef and crashes downstream z3 calls.
            n = t.dest_number()
            if t.get_type() == RealType:
                if isinstance(n, Fraction):
                    return z3.RealVal('%d/%d' % (n.numerator, n.denominator), ctx)
                return z3.RealVal(n, ctx)
            else:
                return z3.IntVal(n, ctx)
        elif t.is_implies():
            return z3.Implies(rec(t.arg1), rec(t.arg))
        elif t.is_equals():
            return rec(t.arg1) == rec(t.arg)
        elif t.is_conj():
            return z3.And(rec(t.arg1), rec(t.arg)) if ctx is None else z3.And(rec(t.arg1), rec(t.arg), ctx)
        elif t.is_disj():
            return z3.Or(rec(t.arg1), rec(t.arg)) if ctx is None else z3.Or(rec(t.arg1), rec(t.arg), ctx)
        elif logic.is_if(t):
            b, t1, t2 = t.args
            return z3.If(rec(b), rec(t1), rec(t2), ctx)
        elif logic.is_xor(t):
            t1, t2 = t.args
            return z3.Or(z3.And(rec(t1), z3.Not(rec(t2))), z3.And(z3.Not(rec(t1)), rec(t2)), ctx)
        elif t.is_not():
            return z3.Not(rec(t.arg), ctx)
        elif t.is_plus():
            return rec(t.arg1) + rec(t.arg)
        elif t.is_minus():
            m, n = rec(t.arg1), rec(t.arg)
            if t.arg1.get_type() == NatType:
                return z3.If(m >= n, m - n, 0, ctx)
            return m - n
        elif t.is_uminus():
            return -rec(t.arg)
        elif t.is_times():
            return rec(t.arg1) * rec(t.arg)
        elif t.is_less_eq():
            return rec(t.arg1) <= rec(t.arg)
        elif t.is_less():
            return rec(t.arg1) < rec(t.arg)
        elif t.is_greater_eq():
            return rec(t.arg1) >= rec(t.arg)
        elif t.is_greater():
            return rec(t.arg1) > rec(t.arg)
        elif t.is_divides():
            return rec(t.arg1) / rec(t.arg)
        elif t.is_nat_power():
            # power :: T => nat => T; z3 power on the Int sort for
            # nat/int bases, and on the Real sort (with a ToReal
            # exponent) for real bases.
            base, exp = rec(t.arg1), rec(t.arg)
            if t.arg1.get_type() == RealType:
                return base ** z3.ToReal(exp)
            return _mk_int_power(base, exp)
        elif t.is_real_power():
            return rec(t.arg1) ** rec(t.arg)
        elif t.is_comb('power', 2) and t.arg.get_type() == IntType:
            # int.pyhol's power with an int exponent (int_power_1 &c).
            return _mk_int_power(rec(t.arg1), rec(t.arg))
        elif t.is_comb('nat_divide', 2):
            # nat DIV: z3's integer division agrees with the nat
            # semantics on nonnegative operands (assms enforce x >= 0).
            # Division by zero is unspecified in SMT-LIB; pin each
            # instance to the holpy semantics (y DIV 0 = 0) with a
            # ground implication, which is true in the holpy model and
            # ignored by proofrec's assertion preprocessing.
            a, b = rec(t.arg1), rec(t.arg)
            zero = z3.IntVal(0, ctx)
            assms['_divax%d' % len(assms)] = z3.Implies(b == zero, a / zero == zero)
            return a / b
        elif t.is_comb('nat_modulus', 2):
            a, b = rec(t.arg1), rec(t.arg)
            zero = z3.IntVal(0, ctx)
            assms['_modax%d' % len(assms)] = z3.Implies(b == zero, a % zero == a)
            return a % b
        elif t.is_comb('of_int', 1):
            if t.get_type() == RealType:
                return z3.ToReal(rec(t.arg))
            raise Z3Exception("convert: unsupported of_int " + repr(t))
        elif t.is_comb('of_nat', 1):
            if t.get_type() == RealType:
                if t.arg.is_var():
                    if t.arg.name not in to_real:
                        nm = name.get_variant_name("r" + t.arg.name, var_names)
                        var_names.append(nm)
                        to_real[t.arg.name] = nm
                        z3_t = convert_const(nm, RealType, ctx)
                        assms[nm] = z3_t >= 0
                        return z3_t
                    else:
                        return convert_const(to_real[t.arg.name], RealType, ctx)
                return z3.ToReal(rec(t.arg))
            else:
                raise Z3Exception("convert: unsupported of_nat " + repr(t))
        elif t.is_comb('max', 2):
            a, b = rec(t.arg1), rec(t.arg)
            return z3.If(a >= b, a, b, ctx)
        elif t.is_comb('min', 2):
            a, b = rec(t.arg1), rec(t.arg)
            return z3.If(a <= b, a, b, ctx)
        elif t.is_comb('abs', 1):
            a = rec(t.arg)
            return z3.If(a >= 0, a, -a, ctx)
        elif t.is_comb('member', 2):
            a, S = rec(t.arg1), rec(t.arg)
            if z3.is_array(S):
                return z3.Select(S, a)
            return S(a)
        elif t.is_comb('Pair', 2):
            a, b = t.args
            _, mk, _, _ = prod_sort(TFun(NatType, NatType), TFun(NatType, NatType), ctx)
            return mk(rec(a), rec(b))
        elif t.is_comb('reg', 1):
            _, _, fst_proj, _ = prod_sort(TFun(NatType, NatType), TFun(NatType, NatType), ctx)
            return fst_proj(rec(t.arg))
        elif t.is_comb('heap', 1):
            _, _, _, snd_proj = prod_sort(TFun(NatType, NatType), TFun(NatType, NatType), ctx)
            return snd_proj(rec(t.arg))
        elif t.is_comb('pair', 2):
            a, b = t.args
            _, mk, _, _ = prod_sort(a.get_type(), b.get_type(), ctx)
            return mk(rec(a), rec(b))
        elif t.is_comb('fst', 1):
            T1, T2 = t.arg.get_type().args
            _, _, fst_proj, _ = prod_sort(T1, T2, ctx)
            return fst_proj(rec(t.arg))
        elif t.is_comb('snd', 1):
            T1, T2 = t.arg.get_type().args
            _, _, _, snd_proj = prod_sort(T1, T2, ctx)
            return snd_proj(rec(t.arg))
        elif t.is_comb('fun_upd', 3):
            # fun_upd s a b as a value: store into the array.
            func, a, b = t.args
            rf = rec(func)
            if z3.is_array(rf):
                return z3.Store(rf, rec(a), rec(b))
            return rf(rec(a), rec(b))
        elif t.is_comb('fun_upd', 4):
            # (f)(a := b)(x) = Select(f[a := b], x).  In the array
            # model f is an array, so the update is a Store and the
            # application a Select; Z3's array theory simplifies
            # Select(Store(...)) directly.
            func, a, b, x = t.args
            rf = rec(func)
            if z3.is_array(rf):
                return z3.Select(z3.Store(rf, rec(a), rec(b)), rec(x))
            return rf(rec(x))
        elif t.is_comb() and t.head.is_const() and t.head.name in recursive_preds:
            f = convert_const(t.head.name, t.head.T, ctx)
            return f(*[rec(arg) for arg in t.args])
        elif t.is_comb():
            f = rec(t.fun)
            a = rec(t.arg)
            if z3.is_array(f):
                return z3.Select(f, a)
            return f(a)
        elif t.is_const():
            if t == true:
                return z3.BoolVal(True, ctx)
            elif t == false:
                return z3.BoolVal(False, ctx)
            elif t.T.is_fun():
                return convert_const(t.name, t.T, ctx)
            else:
                raise Z3Exception("convert: unsupported constant " + repr(t))
        else:
            raise Z3Exception("convert: unsupported operation " + repr(t))

    return rec(t)


norm_thms = [
    'member_empty_simp',
    'member_insert',
    'member_univ_simp',
    'member_collect',
    'member_union_iff',
    'member_inter_iff',
    'set_equal_iff',
    'subset_def',
    'diff_def',
    ('real_zero_def', True),
    ('real_one_def', True),
    ('real_of_nat_add', True),
    ('real_of_nat_mul', True),
    'real_of_nat_minus',
    'real_inverse_divide',
    'real_open_interval_def',
    'real_closed_interval_def',
]

def norm_term(t):
    # Collect list of theorems that can be used.
    cvs = []
    for th_name in norm_thms:
        if isinstance(th_name, str) and theory.thy.has_theorem(th_name):
            cvs.append(conv.try_conv(conv.rewr_conv(th_name)))
        elif theory.thy.has_theorem(th_name[0]):
            cvs.append(conv.try_conv(conv.rewr_conv(th_name[0], sym=True)))
    cvs.append(conv.try_conv(conv.beta_conv()))
    cv = conv.top_conv(conv.every_conv(*cvs))
    while True:
        rhs = cv.eval(t).rhs
        if rhs == t:
            break
        else:
            t = rhs
    return fologic.simplify(t)

def solve_core(s, t, debug=False):
    # First strip foralls from t.
    t = norm_term(t)
    new_names = logic.get_forall_names(t, svar=False)
    _, As, C = logic.strip_all_implies(t, new_names, svar=False)

    def print_debug(*args):
        if debug:
            print(*args)

    register_recursive_defs(s.ctx)
    var_names = [v.name for v in term.get_vars(As + [C])]
    assms = dict()
    to_real = dict()
    for A in As:
        try:
            z3_A = convert(A, var_names, assms, to_real, s.ctx)
            print_debug('A', z3_A)
            s.add(z3_A)
        except Z3Exception as e:
            print_debug(e)
    try:
        z3_C = convert(C, var_names, assms, to_real, s.ctx)
        print_debug('C', z3_C)
        s.add(z3.Not(z3_C))
    except Z3Exception as e:
        print_debug(e)

    for nm, A in assms.items():
        print_debug('A', A)
        s.add(A)

    return s

Z3_TIMEOUT = 5000  # milliseconds

def solve_and_reconstruct(t, debug=False):
    """Prove the holpy statement t with z3 and reconstruct a kernel
    proof of t ITSELF (the raw reconstruction only yields ⊢ false under
    the stripped sequent's hypotheses).  Returns the ProofTerm of t up
    to the statement level: close_sequent proves the stripped sequent
    A1 ⟹ … ⟹ An ⟹ C, which is then bridged back to t's own shape
    (norm_term may normalize the statement) through their canonical
    forms."""
    import prover.proofrec as proofrec
    proof, assertions = solve_and_proof(t, debug)
    pt_false = proofrec.proofrec(proof, assertions=assertions)
    t_norm = norm_term(t)
    names = logic.get_forall_names(t_norm, svar=False)
    _, As, C = logic.strip_all_implies(t_norm, names, svar=False)
    pt = proofrec.close_sequent(pt_false, As, C)
    if pt is pt_false or pt.prop == t:
        return pt
    try:
        convs = proofrec._canon_conv()
        pt_A = proofrec.refl(pt.prop).on_rhs(*convs)
        pt_B = proofrec.refl(t).on_rhs(*convs)
        if pt_A.rhs != pt_B.rhs:
            return pt
        iff = pt_A.transitive(pt_B.symmetric())      # ⊢ pt.prop ⟷ t
        return iff.equal_elim(pt)                    # ⊢ t
    except Exception:
        return pt

def solve(t, debug=False):
    """Solve the given goal using Z3. Returns True if unsatisfiable (goal proved)."""
    s = z3.Solver()
    s.set("timeout", Z3_TIMEOUT)
    s = solve_core(s, t, debug)
    result = str(s.check())
    return result == 'unsat'


def solve_and_proof(t, debug=False):
    """Solve the given goal using Z3 and get proof."""
    z3.set_param(proof=True)
    try:
        s = z3.Solver(ctx=z3.Context())
        s.set("timeout", Z3_TIMEOUT)
        s = solve_core(s, t, debug)
        result = s.check()
        assert str(result) == 'unsat', "Z3: not solved (result=%s)" % result
        return s.proof(), s.assertions()
    finally:
        z3.set_param(proof=False)

def apply_z3(t):
    return ProofTerm('z3', args=t)


# Z3Macro and Z3Method moved to logic/macros/z3.py and server/methods/z3.py

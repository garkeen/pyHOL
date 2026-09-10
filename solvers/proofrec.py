"""
Z3 proof reconstruction.
Reference: Fast LCF-Style Proof Reconstruction for Z3
by Sascha Böhme and Tjark Weber.
"""

import z3
from z3.z3consts import *
from theories.integer import conv as integer
from theories.integer import macro as integer_macro
from theories.logic import conv as proplogic
from theories.real.conv import norm_neg_real_ineq_conv, real_const_eq_conv, real_eval_conv, real_norm_comparison
from kernel.type import TFun, BoolType, STVar, TVar
from syntax.numeral import NatType, IntType, RealType
from kernel.term import *
from syntax.numeral import *  # noqa: F401,F403  (numeral sugar moved out of kernel)
from syntax.logicops import *  # noqa: F401,F403  (logic sugar moved out of kernel)
from kernel.proofterm import ProofTerm, refl, eval_macro
from kernel.macro import Macro
from kernel.theory import verify, register_macro
from kernel import theory
from kernel.report import ProofReport
from core import basic, matcher
from core import context
from tactic.goal import Goal
from core.logic import apply_theorem
from theories.logic.logic import imp_disj_iff, disj_norm, resolution
from theories.logic.macro import imp_conj_macro
from tactic.steps import rewrite_goal_with_prev
from core.conv import rewr_conv, try_conv, top_conv, top_sweep_conv, bottom_conv, arg_conv, ConvException, Conv, arg1_conv, binop_conv, replace_conv
from core import auto
from solvers import sat, tseitin, simplex, simplex_strict
from syntax.settings import settings
from syntax import parser
from solvers import omega
from collections import deque
import functools
import operator
import json
import time
import sys
import multiprocessing
# from z3 import Context, Solver, parse_smt2_file, set_param
import z3
z3.set_param(proof=True)
sys.setrecursionlimit(10000000)

basic.load_theory('smt')

def mk_int_const_ineq_pt(value):
    """Proof term for the sign fact of an integer constant, via the
    int_const_ineq oracle macro (level 0): |- c > 0 or |- c < 0.

    Emission lives at the prover layer; the conv layer receives the
    fact as a parameter (audit iron law: conv 不得出现宏名).

    """
    if value > 0:
        return eval_macro('int_const_ineq', greater(IntType)(Int(value), Int(0)))
    else:
        return eval_macro('int_const_ineq', less(IntType)(Int(value), Int(0)))


conj_expr = dict()
disj_expr = dict()

# Z3 proof method name.
method = ('mp', 'mp~', 'asserted', 'trans', 'trans*', 'monotonicity', 'rewrite', 'and-elim', 'not-or-elim',
            'iff-true', 'iff-false', 'unit-resolution', 'commutativity', 'def-intro', 'apply-def',
            'def-axiom', 'iff~', 'nnf-pos', 'nnf-neg', 'sk', 'proof-bind', 'quant-inst', 'quant-intro',
            'lemma', 'hypothesis', 'symm', 'refl', 'apply-def', 'intro-def', 'th-lemma', 'elim-unused',
            'true-axiom')

# Rewriting theorems from the general library (int/real/function/logic
# theories, all within the 'smt' theory's import closure) consulted by
# schematic_rules_rewr in addition to the r-theorems of smt.pyhol.  These
# cover many of Z3's non-decidable rewrite rules (multiplication by 0/1,
# commutativity/associativity, fun_upd i.e. z3 select/store, ite rules).
# A name that fails to match only costs one try, so the list is additive.
SCHEMATIC_EXTRA = [
    # int (library/int.pyhol)
    'int_add_0_left', 'int_add_0_right', 'int_mul_0_l', 'int_mul_0_r',
    'int_mul_1_l', 'int_mul_1_r', 'int_add_comm', 'int_add_assoc',
    'int_mult_comm', 'int_mult_assoc', 'int_leq', 'int_geq',
    'int_eq_move_left', 'int_geq_shift',
    'int_mul_add_distr_r', 'int_mul_add_distr_l', 'int_power_1',
    # nat div/mod (library/nat.pyhol; z3 idiv/mod agree on nonneg operands)
    'div_zero', 'mod_zero',
    # real (library/real.pyhol)
    'real_add_lid', 'real_add_rid', 'real_mul_lzero', 'real_mul_rzero',
    'real_mul_lid', 'real_mul_rid', 'real_add_comm', 'real_add_assoc',
    'real_mult_comm', 'real_mult_assoc', 'real_neg_neg',
    'real_inverse_divide', 'real_ge_le_same_num', 'real_add_ldistrib',
    'real_of_int_leq', 'real_of_int_lt', 'real_of_int_gt',
    'real_of_int_geq', 'real_of_int_add', 'real_of_int_mul',
    # function / array (library/function.pyhol; z3 select/store = fun_upd)
    'fun_upd_same', 'fun_upd_other', 'fun_upd_triv', 'fun_upd_upd', 'fun_upd_twist',
    # logic (library/logic.pyhol)
    'conj_assoc', 'disj_assoc_eq', 'conj_comm', 'disj_comm',
    'double_neg', 'de_morgan_thm1', 'de_morgan_thm2', 'neg_iff_both_sides',
    'eq_true', 'eq_false', 'not_true', 'not_false', 'if_true', 'if_false',
    'cond_id', 'cond_swap', 'ite_to_disj', 'not_all', 'not_exists',
]


class Z3Term:
    def __init__(self, t):
        assert isinstance(t, z3.AstRef), "%s is not z3 term!" % str(t)
        self.t = t

    def __eq__(self, value):
        return self.t.sort() == value.t.sort() and self.t == value.t

    def __hash__(self):
        return z3.AstRef.__hash__(self.t)

    def __str__(self):
        return str(self.t)

def index_and_relation(proof):
    """Index all terms in z3 proof and get the relation between the terms."""
    s = dict()
    id = 0
    def rec(term, parent=None):
        nonlocal id
        if term in s.keys() and parent is not None:
            s[parent][1].append(s[term][0])
        else:
            s[term] = [id, []]
            if parent is not None:
                s[parent][1].append(id)
            id += 1
            if not z3.is_quantifier(term.t):
                for child in term.t.children():
                    rec(Z3Term(child), term)
    rec(Z3Term(proof))
    return {value[0]: key.t for key, value in s.items()}, {value[0]: value[1] for key, value in s.items()}

def DepthFirstOrder(G):
    """Traverse graph in reversed DFS order."""
    reversePost = deque()
    marked = [False for i in range(len(G))]
    
    def dfs(G, v):
        marked[v] = True
        for w in G[v]:
            if not marked[w]:
                dfs(G, w)
        reversePost.append(v)

    for v in G.keys():
        if not marked[v]:
            dfs(G, v)
    
    return reversePost

def arity(l):
    """
    Give a lambda term %x1 x2 ... xn. body
    return n
    """
    return 1 + arity(l.body) if l.is_abs() else 0

def translate_type(sort):
    """Translate z3 type into holpy type."""
    T = sort.kind()
    if T == Z3_BOOL_SORT:
        return BoolType
    elif T == Z3_INT_SORT:
        return IntType
    elif T == Z3_REAL_SORT:
        return RealType
    elif T == Z3_UNINTERPRETED_SORT:
        return TVar(sort.name())
    elif T == Z3_ARRAY_SORT:
        # z3 arrays encode HOL function types (see z3wrapper.array_sort).
        return TFun(translate_type(sort.domain()), translate_type(sort.range()))
    else:
        raise NotImplementedError

def solve_cnf(F):
    encode_pt = tseitin.encode(Not(F))
    cnf = tseitin.convert_cnf(encode_pt.prop)
    res, proof = sat.solve_cnf(cnf)
    assert res == 'unsatisfiable', 'solve_cnf: statement is not provable'
    
    # Perform the resolution steps
    clause_pts = [ProofTerm.assume(clause) for clause in encode_pt.prop.strip_conj()]
    for new_id in sorted(proof.keys()):
        steps = proof[new_id]
        pt = clause_pts[steps[0]]
        for step in steps[1:]:
            pt = resolution(pt, clause_pts[step])
        clause_pts.append(pt)

    contra_pt = clause_pts[-1]
    assert contra_pt.prop == false
    
    # Show contradiction from ~F and definitions of new variables
    pt1, pt2 = encode_pt, contra_pt
    while pt1.prop.is_conj():
        pt_left = apply_theorem('conjD1', pt1)
        pt2 = pt2.implies_intr(pt_left.prop).implies_elim(pt_left)  # remove one clause from assumption
        pt1 = apply_theorem('conjD2', pt1)
    pt2 = pt2.implies_intr(pt1.prop).implies_elim(pt1)  # remove last clause from assumption

    # Clear definition of new variables from antecedent
    eqs = [t for t in pt2.hyps if t.is_equals()]
    eqs = list(reversed(sorted(eqs, key=lambda t: int(t.lhs().name[1:]))))

    for eq in eqs:
        pt2 = pt2.implies_intr(eq).forall_intr(eq.lhs).forall_elim(eq.rhs) \
                 .implies_elim(ProofTerm.reflexive(eq.rhs))

    return apply_theorem('negI', pt2.implies_intr(pt2.hyps[0])).on_prop(rewr_conv('double_neg'))

def translate(term, bounds=deque(), subterms=[]):
    """Transalte z3 term into holpy term.
       bounds represents bounded variables, key is de-Bruijn index of the var, value is the bounded variable already in holpy.
    """
    if z3.is_func_decl(term): # z3 function, including name, sort of each arguments, constant is function with 0 arg.
        arity = term.arity()
        rangeT = translate_type(term.range())
        domainT = [translate_type(term.domain(i)) for i in range(arity)]
        types = domainT + [rangeT]
        return Var(term.name(), TFun(*types))
    elif z3.is_quantifier(term): 
        body = term.body()
        var = tuple(Var(term.var_name(i), translate_type(term.var_sort(i))) for i in range(term.num_vars()))
        for v in var:
            bounds.appendleft(v)
        # patterns = tuple(term.patterns(i) for i in range(term.num_patterns()))
        if term.is_lambda():
            if body.decl().name() == 'refl':
                lhs = translate(body.arg(0).arg(0), bounds)
                return ProofTerm.reflexive(Lambda(*var, lhs))
            elif body.decl().name() in method:
                subst_var = [z3.Const(term.var_name(term.num_vars()-1-i), term.var_sort(term.num_vars()-1-i)) for i in range(term.num_vars())]
                prf = proofrec(z3.substitute_vars(body, *subst_var), bounds=bounds, assertions=[])
                bounds.clear()
                for v in reversed(var):
                    prf = prf.abstraction(v)
                return prf
            else:
                raise NotImplementedError
            l = Lambda(*var, translate(body, bounds))
            bounds.clear()
            return l
        elif term.is_exists():
            e = Exists(*var, translate(body, bounds))
            for i in range(len(var)):
                bounds.popleft()
            return e
        elif term.is_forall():
            f = Forall(*var, translate(body, bounds))
            for i in range(len(var)):
                bounds.popleft()
            return f
        else:
            raise NotImplementedError
    elif z3.is_expr(term):
        if z3.is_var(term):
            return bounds[z3.get_var_index(term)]
        kind = term.decl().kind() # term function application
        sort = translate_type(term.sort()) # term sort
        args = subterms
        if len(subterms) == 0 and term.num_args() != 0:
            args = tuple(translate(term.arg(i), bounds) for i in range(term.num_args()))
        if z3.is_int_value(term): # int number
            return Int(term.as_long())
        elif z3.is_rational_value(term): # Return `True` if term is rational value of sort Real
            return Real(term.as_fraction())
        elif z3.is_algebraic_value(term): # a number
            return Real(term.as_fraction())
        elif z3.is_true(term):
            return true
        elif z3.is_false(term):
            return false
        elif z3.is_const(term): 
            # incomplete, is_const(Int(1)) == true, but Int(1) have already been
            # translated above
            if term.decl().name() in local.keys():
                return local[term.decl().name()]
            return Var(term.decl().name(), sort)
        elif z3.is_add(term):
            return functools.reduce(lambda x, y: x + y, args)
        elif term.decl().kind() == Z3_OP_UMINUS:
            return uminus(sort)(*args)
        elif z3.is_sub(term):
            return functools.reduce(lambda x, y: x - y, args)
        elif z3.is_mul(term):
            return functools.reduce(lambda x, y: x * y, args)
        elif z3.is_idiv(term):
            # integer (nat) division: nat_divide at int types (nat is
            # erased to int throughout the roundtrip, as with all other
            # operators).  This branch must come before the real-division
            # test below, whose z3.is_div also accepts idiv nodes.
            return Const('nat_divide', TFun(IntType, IntType, IntType))(*args)
        elif z3.is_div(term):
            return divides(sort)(*args)
        elif z3.is_eq(term):
            return Eq(args[0], args[1])
        elif z3.is_and(term):
            return And(*args)
        elif z3.is_or(term):
            return Or(*args)
        elif z3.is_implies(term):
            return Implies(*args)
        elif z3.is_not(term):
            return Not(args[0])
        elif z3.is_lt(term):
            return less(args[0].get_type())(*args)
        elif z3.is_le(term):
            return less_eq(args[0].get_type())(*args)
        elif z3.is_gt(term):
            return greater(args[0].get_type())(*args)
        elif z3.is_ge(term):
            return greater_eq(args[0].get_type())(*args)
        elif z3.is_distinct(term):
            ineq = [Not(Eq(args[i], args[j])) for i in range(len(args)) for j in range(i+1, len(args))]
            return And(*ineq)
        elif kind == Z3_OP_SELECT:
            # z3 encodes function application f a as Select(f, a).
            return args[0](args[1])
        elif kind == Z3_OP_STORE:
            # z3 encodes function update (f)(a := b) as Store(f, a, b).
            f, a, b = args
            T_dom, T_rng = f.get_type().domain_type(), f.get_type().range_type()
            return Const('fun_upd', TFun(TFun(T_dom, T_rng), T_dom, T_rng, TFun(T_dom, T_rng)))(f, a, b)
        elif kind == Z3_OP_MOD:
            return Const('nat_modulus', TFun(IntType, IntType, IntType))(*args)
        elif kind == Z3_OP_POWER:
            base, exp = args
            T = base.get_type()
            if exp.get_type() == RealType:
                return real_power(T)(base, exp)
            # z3 exponents are int; int.pyhol defines this power and
            # provides theorems (int_power_1, int_power_add).
            return Const('power', TFun(T, IntType, T))(base, exp)
        elif kind == Z3_OP_TO_REAL:
            return of_int(RealType)(args[0])
        elif kind == Z3_OP_ITE:
            cond, stat1, stat2 = translate(term.arg(0)), translate(term.arg(1)), translate(term.arg(2))
            T = stat1.get_type() # stat1 and stat2 must have same type
            return Const('IF', TFun(BoolType, T, T, T))(cond, stat1, stat2)
        elif kind == Z3_OP_UNINTERPRETED: # s(0)
            uf = translate(term.decl(), bounds)
            args = [translate(term.arg(i), bounds) for i in range(term.num_args())]
            return uf(*args)
        elif z3.is_bool(term) and kind == Z3_OP_OEQ: # "~"" operator in z3 is ambiguous
            return Eq(translate(term.arg(0)), translate(term.arg(1)))
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

def and_elim(arg1, concl):
    global conj_expr
    if arg1.prop not in conj_expr:
        conj_expr.update({arg1.prop: dict()})
    
    for key, value in conj_expr[arg1.prop].items():
        if key == concl:
            # print("!!")
            return value    

    pt = arg1
    while pt.prop.is_conj():
        left, right = pt.prop.arg1, pt.prop.arg
        pt_l, pt_r = apply_theorem('conjD1', pt), apply_theorem('conjD2', pt)
        conj_expr[arg1.prop].update({left: pt_l, right: pt_r})
        pt = pt_r
    # assert pt.prop == concl # I will implement proofrec exception later
    return conj_expr[arg1.prop][concl]

def monotonicity(pts, concl):
    """
    f = f, x1 = y1, x2 = y2, ..., xn = yn
    =====================================
        f(x1,...,xn) = f(y1,...,yn)

    Note: In HOL, disj and conj are both binary right-associative operators,
    but in z3, they are polyadic, so if f and g are disj/conj, the
    first thing is to abstract over the bool var in them to get the real 
    f and g. If f and g are not disj and conj, we can easily get the fun
    by calling specific method(*.fun). 

    After getting f and g, the next thing is to find x1...xn and y1...yn, although
    z3 has provided some equality instances like above, but when xk = yk, it will 
    ignore the equality(even when f=g), so we need to find out them. This can be done by ranging
    over the last argument f(x1,...,xn). If f and g are disj or conj, we can easily 
    get them by "strip_disj()/strip_conj()" method. Or else we can use "strip_comb()"
    method to get them.

    As soon as we've collected all necessary stuff, we can reconstrcut the proof by
    recursively using combination rule.

    There is a special case for conj and disj, for example: the provided equality is
    B∨C = C∨B, and we want to prove A∨B∨C = A∨C∨B, it is inappropriate to use strip_disj(),
    because disj is right-associate, we have no chance to get complete B∨C term. So we need
    to implemented custom strip_disj()/strip_conj() method.

    The translate process have bugs(∧,∨ are polyadic), that's why disj and conj are special.

    When f is +/-/*, there is another pitfall: in HOL, while ∧ or ∨ is right associative, +/-/*
    is left associative when construct terms.
    """

    def strip_fun(fun, tm, tl):
        """
        tm is a function term, fun is its function name, tl is a term list, 
        in which are arguments occured in tm(but not all). strip_fun will strip
        tm's arguments based on tl.
        
        For example, fun is plus, tm is v1 * 2 - s_0 * 16 + v0, tl is [v1 * 2 - s_0 * 16],
        then the return list is [v1 * 2 - s_0 * 16, v0]
        """
        if tm.is_comb(fun, None):
            if tm.arg1 in tl:
                return tm.args
            else:
                return strip_fun(fun, tm.arg1, tl) + [tm.arg]
        else:
            return [tm]

    def get_argument(f, left_assoc=False):
        """
        Suppose f is f x1 x2 x3, return [x1, x2, x3]
        When assoc_direction is true, we can't use strip_comb.
        """
        if not left_assoc:
            _, fx = f.strip_comb()
            return fx
        else:
            args = deque()
            while f.is_plus():
                args.appendleft(f.args[1])
                f = f.args[0]
            return [f] + list(args)

    def arith_eq(fun_eq, pts):
        """
        fun is ⊢+ = +/- = -/* = *,
        pts is a list of equality proof terms: [a = a', b = b', c = c', ...]
        return a proofterm: ⊢ a + b + c + ⋯ = a' + b' + c' + ⋯
        """
        if len(pts) == 1:
            return pts[0]
        else:
            return fun_eq.combination(arith_eq(fun_eq, pts[:-1])).combination(pts[-1])

    # First get f, g.
    f_expr, g_expr = concl.lhs, concl.rhs
    if not f_expr.is_disj() and not f_expr.is_conj():
        f, g = f_expr.head, g_expr.head

        # Next collect arguments: x1...xn/y1...yn
        # We can't split the term in pts into subterms.
        # if not f_expr.is_plus():
        #     fx, gy = get_argument(f_expr), get_argument(g_expr)
        # else:
        #     fx, gy = get_argument(f_expr, True), get_argument(g_expr, True)
        # fx = get_argument(f_expr) if not (f_expr.is_plus() or f_expr().is_minus()) else get_argument(f_expr, True)
        # gy = get_argument(g_expr) if not (g_expr.is_plus() or g_expr().is_minus()) else get_argument(g_expr, True)
        # Then put all useful equalities proofterm in equalities.
        if f_expr.is_plus() or f_expr.is_minus() or f_expr.is_times():
            pts_lhs, pts_rhs = [pt.lhs for pt in pts], [pt.rhs for pt in pts]
            fx, gy = strip_fun(f.name, f_expr, pts_lhs), strip_fun(g.name, g_expr, pts_rhs)
        else:
            fx, gy = get_argument(f_expr), get_argument(g_expr)
        equalities = []
        if f == g:
            equalities.append(ProofTerm.reflexive(f))
            index = 0
        else:
            index = 1

        for x, y in zip(fx, gy):
            if x == y: # z3 not provide it
                equalities.append(ProofTerm.reflexive(x))
            else:
                equalities.append(pts[index])
                index += 1

        # use combination get final proof
        if not f_expr.is_plus():
            return functools.reduce(lambda f, x : f.combination(x), equalities)
        else:
            return arith_eq(ProofTerm.reflexive(f_expr.head), equalities[1:])
    else:
        eq_prop = concl # f x1 x2 ... xk ~ f y1 y2 ... yk
        eq_hyps = pts
        assert eq_prop.lhs.head == eq_prop.rhs.head
        head = eq_prop.lhs.head
        if head.name == "disj":
            head_arity = len(concl.lhs.strip_disj())
        elif head.name == "conj":
            head_arity = len(concl.lhs.strip_conj())
        # collect xi ~ yi
        lhs_param, rhs_param = [], []
        eq_assms_lhs = [p.prop.lhs for p in eq_hyps]
        eq_assms_rhs = [p.prop.rhs for p in eq_hyps]

        def rec(p, param, known_eq):
            if p in known_eq:
                param.append(p)
            elif p.head == head:
                param.append(p.args[0])
                if len(p.args) > 1:
                    rec(p.args[1], param, known_eq)
            elif p.head != head:
                param.append(p)

        rec(eq_prop.lhs, lhs_param, eq_assms_lhs)
        rec(eq_prop.rhs, rhs_param, eq_assms_rhs)

        pt_concl = ProofTerm.reflexive(head)
        index = 0
        
        eq_pts = deque()
        
        for l, r in zip(lhs_param, rhs_param):
            if l != r:
                eq_pts.appendleft(eq_hyps[index])
                index += 1
            else:
                eq_pts.appendleft(ProofTerm.reflexive(l))
                if l in eq_assms_lhs:
                    index += 1
        pt1 = eq_pts[0]
        if len(eq_pts) == 1:
            return pt_concl.combination(eq_pts[0])
        for i in range(len(eq_pts) - 1):
            pt1 = pt_concl.combination(eq_pts[i+1]).combination(pt1)

        return pt1

def distinct_monotonicity(pts, concl, z3terms):
    """
    If we want to prove distinct[x, y, z] <--> distinct[a, b, c]
    with premises: [x = a, y = b, z = c], because HOL doesn't have distinct 
    operator, we need to implement one.
    For example, we can use monotonicity to get 
    "x = a, y = b ⊢ x = y <--> a = b", and use combination we can get 
    "x = a, y = b ⊢ Not(x = y) <--> Not(a = b)". If we have n premises, we
    can get n(n-1)/2 similarly proofterms. These proofterms are
    enough to call a monotonicity rule, in which function is conjunction.
    """

    def equal_mono(pt1, pt2):
        """
        Due to bugs in monotonicity method(not use z3terms as argument indicator), 
        we temporarily implement a little equal monotonicity rule here.
        pt1: ⊢ a = b
        pt2: ⊢ c = d
        concl: a = c <--> b = d
        """
        eq = equals(pt1.prop.lhs.get_type())
        eq_refl = ProofTerm.reflexive(eq)
        pt1 = ProofTerm.combination(eq_refl, pt1)
        pt2 = ProofTerm.combination(pt1, pt2)
        return pt2

    arg_num = z3terms[-1].arg(0).num_args()
    lhs_arguments = [translate(z3terms[-1].arg(0).arg(i)) for i in range(arg_num)]
    rhs_arguments = [translate(z3terms[-1].arg(1).arg(i)) for i in range(arg_num)]
    new_equals = []
    index = 0
    for l, r in zip(lhs_arguments, rhs_arguments):
        if l == r:
            new_equals.append(ProofTerm.reflexive(l))
        else:
            new_equals.append(pts[index])
            index += 1
    new_pts = [(new_equals[i], new_equals[j], \
        Eq(Eq(new_equals[i].prop.lhs, new_equals[j].prop.lhs), Eq(new_equals[i].prop.rhs, new_equals[j].prop.rhs))) \
        for i in range(len(new_equals)) for j in range(i+1, len(new_equals))]

    new_pts1 = [equal_mono(p[0], p[1]) for p in new_pts]
    neg_refl = ProofTerm.reflexive(neg)
    new_pts2 = [ProofTerm.combination(neg_refl, p) for p in new_pts1]
    conj_refl = ProofTerm.reflexive(conj)
    pt_conj = new_pts2[-1]
    for i in reversed(range(len(new_pts2) - 1)):
        pt = ProofTerm.combination(conj_refl, new_pts2[i]).combination(pt_conj)
        pt_conj = pt
    return pt_conj

def schematic_rules_rewr(thms, lhs, rhs):
    """Rewrite by instantiating schematic theorems."""
    for thm in thms:
        try:
            pt = ProofTerm.theorem(thm)
            inst1 = matcher.first_order_match(pt.prop.lhs, lhs)
            inst2 = matcher.first_order_match(pt.prop.rhs, rhs, inst=inst1)
            return pt.substitution(inst2)
        except Exception:
            # MatchException is the expected failure; TheoryException
            # (theorem not in the current theory) must not abort the sweep.
            continue
    return Goal(Eq(lhs, rhs)).sorry()

def is_ineq(t):
    """determine whether t is an inequality"""
    return t.is_less() or t.is_less_eq() or t.is_greater() or t.is_greater_eq()

class flat_left_assoc_conj_conv(Conv):
    """convert the left-associative conjunction to right-associative conjunction."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_conj():
            if t.arg1.is_conj():
                return pt.on_rhs(
                    rewr_conv('conj_assoc', sym=True),
                    self
                )
            else:
                return pt
        else:
            return pt

class flat_left_assoc_disj_conv(Conv):
    """convert the left-associative disjunction to right-associative disjunction."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_disj():
            if t.arg1.is_disj():
                return pt.on_rhs(
                    rewr_conv('disj_assoc_eq', sym=True),
                    self
                )
            else:
                return pt
        else:
            return pt

def compare_lhs_rhs(tm, cvs):
    """
    tm is an equality term, first try use conversions in cvs iteratively to normalize left-hand side
    to match tm's right-hand side. If failed, then use conversions to normalize right-hand side similarly.
    If they still can't match, we can only return sorry.
    """
    norm_lhs_pt = refl(tm.lhs)
    for cv in cvs:
        norm_lhs_pt = norm_lhs_pt.on_rhs(cv)
        if norm_lhs_pt.rhs == tm.rhs:
            return norm_lhs_pt
    norm_rhs_pt = refl(tm.rhs)
    for cv in cvs:
        norm_rhs_pt = norm_rhs_pt.on_rhs(cv)
        if norm_rhs_pt.rhs == norm_lhs_pt.rhs:
            return norm_lhs_pt.transitive(norm_rhs_pt.symmetric())
        
    return Goal(tm).sorry()

def match_pattern(pat, tm):
    """If the schematic pattern can match with term tm, return true, else false"""
    if isinstance(pat, str):
        pat = parser.parse_term(pat).convert_svar()
    try:
        matcher.first_order_match(pat, tm)
        return True
    except matcher.MatchException:
        return False

def try_tran_pt(pt1, pt2):
    """Try to do transition with pt1 and pt2, """
    if pt1.rhs == pt2.lhs:
        return pt1.transitive(pt2)
    else:
        return Goal(Eq(pt1.lhs, pt2.rhs)).sorry()

def analyze_type(tm):
    """
    Infer the theory which term tm most likely belongs to.
    """
    if tm.is_number():
        return tm.get_type()
    else:
        types = [v.T for v in tm.get_vars()] + [v.T for v in tm.get_consts()]
        range_types = [T.strip_type()[-1] for T in types]
        if not types: # only have true or false
            return set([BoolType])
        else:
            return set(range_types)

def rewrite_bool(tm):
    pt1 = compare_lhs_rhs(tm, [proplogic.norm_full()])
    if pt1.rule == 'sorry':
        return compare_lhs_rhs(tm, [
            proplogic.norm_full(),
            top_conv(rewr_conv('neg_iff_both_sides')),
            proplogic.norm_full()
        ])
    else:
        return pt1

def rewrite_int(tm, has_bool=False):
    """
    Patterns:
    1) a ⋈ b <--> c ⋈ d
    2) a = b <--> c = d
    3) a = b
    4) ¬(a = b) <--> ¬(c = d)
    5) (a = b) <--> (a ≤ b) & (a ≥ b)
    6) a ⋈ b <--> ¬(c ⋈ d)
    7) ¬(a ⋈ b) <--> ¬(c ⋈ d)
    8) a | b = c <--> a | b ≤ c & b ≥ c
    9) ¬(a ⋈ b) <--> ¬(c ⋈ d) (k * a = c, k * b = d)
    10) (a = b) <--> false

    If all above patterns cannot match tm, we have to apply a more general strategy:
    1) normalize the logic term;
    2) normalize all comparison;
    3) convert all equality term to less_eq /\ greater_eq

    """
    if tm.lhs.is_compares() and tm.rhs.is_compares():
        """
        Two cases:
        1. prove equality by moving terms
        2. simplified one side by dividing GCD to match with the other
        """
        try:
            return integer_macro.int_eq_comparison_macro().get_proof_term(tm)
        except:
            return compare_lhs_rhs(tm, [top_conv(integer.int_gcd_compares(mk_int_const_ineq_pt)), integer.omega_form_conv()])
    elif match_pattern('(a::int) = (b::int) <--> (c::int) = (d::int)', tm):
        return compare_lhs_rhs(tm, [integer.int_norm_eq()])
    elif tm.lhs.get_type() == IntType and tm.rhs.get_type() == IntType:
        pt1 = refl(tm.lhs).on_rhs(integer.simp_full())
        pt2 = refl(tm.rhs).on_rhs(integer.simp_full())
        res = try_tran_pt(pt1, pt2.symmetric())
        if res.rule != 'sorry':
            return res
    elif tm.lhs.is_not() and tm.rhs.is_not() and tm.lhs.arg.is_equals() and tm.rhs.arg.is_equals():
        pt_internal = compare_lhs_rhs(Eq(tm.lhs.arg, tm.rhs.arg), [integer.int_norm_eq()])
        if pt_internal.rule != 'sorry':
            return refl(neg).combination(compare_lhs_rhs(Eq(tm.lhs.arg, tm.rhs.arg), [integer.int_norm_eq()]))        
    elif tm.lhs.is_equals() and tm.rhs.is_conj() and tm.rhs.arg1.is_less_eq() and tm.rhs.arg.is_greater_eq():
        pt = refl(tm.lhs).on_rhs(rewr_conv('int_eq_leq_geq'))
        if pt.rhs == tm.rhs:
            return pt
        else:
            return Goal(tm).sorry()
    elif tm.lhs.is_compares() and tm.rhs.is_not() and tm.rhs.arg.is_compares():
        pt_elim_neg_sym = refl(tm.rhs).on_rhs(integer.int_norm_neg_compares(), integer.omega_form_conv()).symmetric()
        pt_eq = integer_macro.int_eq_comparison_macro().get_proof_term(Eq(tm.lhs, pt_elim_neg_sym.lhs))
        return try_tran_pt(pt_eq, pt_elim_neg_sym)
    elif tm.lhs.is_not() and tm.lhs.arg.is_compares() and tm.rhs.is_not() and tm.rhs.arg.is_compares():
        """
        Two cases:
        1. normalize the comparisons can prove they are equal.
        2. use gcd, ¬(a ⋈ b) <--> ¬(m * c ⋈ m * d)
        """
        pt_lhs_elim_neg = refl(tm.lhs).on_rhs(integer.int_norm_neg_compares(), integer.omega_form_conv())
        pt_rhs_elim_neg_sym = refl(tm.rhs).on_rhs(integer.int_norm_neg_compares(), integer.omega_form_conv()).symmetric()
        pt1 = try_tran_pt(pt_lhs_elim_neg, pt_rhs_elim_neg_sym)
        if pt1.rule != 'sorry':
            return pt1
        return compare_lhs_rhs(tm, [top_conv(integer.int_gcd_compares(mk_int_const_ineq_pt)), integer.int_norm_neg_compares(), integer.omega_form_conv()])
    elif match_pattern('(a::bool) | (b::int) = c <--> (a::bool) | ~(~((b::int) <= c) | ~((b::int) >=c))', tm):
        pt_lhs = refl(tm.lhs).on_rhs(arg_conv(rewr_conv('int_eq_leq_geq')), arg_conv(proplogic.norm_full()))
        pt_rhs_sym = refl(tm.rhs).on_rhs(arg_conv(proplogic.norm_full())).symmetric()        
        return try_tran_pt(pt_lhs, pt_rhs_sym)
    elif match_pattern('((a :: int) = (b :: int)) <--> false', tm):
        return refl(tm.lhs).on_rhs(integer.int_norm_eq(), integer.int_neq_false_conv(mk_int_const_ineq_pt))
    elif match_pattern("(a :: int) * 0 = 0", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('int_mul_0_r'))
    
    return rewrite_int_second_level(tm)

def rewrite_int_second_level(tm):
    """Use single rewrite conversion"""
    armony = [
        (proplogic.norm_full(), ),
        (try_conv(rewr_conv('pos_eq_neg')), ),
        (try_conv(rewr_conv('neg_eq_pos')), ),
        (bottom_conv(integer.int_norm_conv()), ),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_geq_leq_conj'))),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_leq_geq'))),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_leq_geq')), proplogic.norm_full()),
        # (proplogic.norm_full(), try_conv(bottom_conv(integer.int_norm_eq())), top_conv(rewr_conv('int_eq_geq_leq_conj'))),
        # (proplogic.norm_full(), try_conv(bottom_conv(integer.int_norm_eq())), bottom_conv(integer.omega_form_conv())),
        # (proplogic.norm_full(),try_conv(top_conv(integer.int_norm_eq())), try_conv(bottom_conv(integer.simp_full())), top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        # (proplogic.norm_full(), top_conv(integer.int_gcd_compares(mk_int_const_ineq_pt)), top_conv(integer.int_norm_neg_compares()), top_conv(integer.omega_form_conv())),
        (top_conv(rewr_conv('neg_iff_both_sides')), top_conv(rewr_conv('double_neg'))),
        (try_conv(bottom_conv(integer.omega_form_conv())),
        try_conv(bottom_conv(integer.int_norm_neg_compares())), try_conv(bottom_conv(integer.omega_form_conv())),
        bottom_conv(integer.int_norm_eq()),
        top_conv(rewr_conv('eq_mean_true')),
        try_conv(proplogic.norm_full()),
        top_conv(rewr_conv('neg_iff_both_sides')), 
        try_conv(proplogic.norm_full()))
    ]

    for arm in armony:
        try:
            pt = compare_lhs_rhs(tm, arm)
        except:
            continue
        if pt.rule != 'sorry':
            return pt

    armony_with_norm = [
        (top_conv(rewr_conv('int_eq_geq_leq_conj')), ),
        (top_conv(rewr_conv('int_eq_geq_leq_conj')), ),
        (top_conv(rewr_conv('int_eq_leq_geq')), ),
        (top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        (top_conv(rewr_conv('int_eq_leq_geq')), proplogic.norm_full()),
        (try_conv(bottom_conv(integer.int_norm_eq())), top_conv(rewr_conv('int_eq_geq_leq_conj'))),
        (try_conv(bottom_conv(integer.int_norm_eq())), bottom_conv(integer.omega_form_conv())),
        (proplogic.norm_full(),try_conv(top_conv(integer.int_norm_eq())), try_conv(bottom_conv(integer.simp_full())), top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        (top_conv(integer.int_gcd_compares(mk_int_const_ineq_pt)), top_conv(integer.int_norm_neg_compares()), top_conv(integer.omega_form_conv())),
    ]

    pt_norm_full = refl(tm).on_rhs(binop_conv(proplogic.norm_full()))
    tm_norm_full = pt_norm_full.rhs
    for arm in armony_with_norm:
        try:
            pt = compare_lhs_rhs(tm_norm_full, arm)
        except:
            continue
        if pt.rule != 'sorry':
            return pt_norm_full.symmetric().equal_elim(pt)

    return Goal(tm).sorry()

def rewrite_by_assertion(tm):
    """
    Rewrite the tm by assertions. Currently we only rewrite the absolute boolean variables.
    """
    global atoms
    pt = refl(tm)
    # boolvars = [v for v in tm.get_vars()] + [v for v in tm.get_consts()]
    return pt.on_rhs(*[top_conv(replace_conv(v)) for _, v in atoms.items()]).on_rhs(*[top_conv(replace_conv(v)) for _, v in atoms.items()])

def rewrite_real(tm, has_bool=False):
    if match_pattern("(x::real) = y <--> (x::real) <= y & x >= y", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('real_ge_le_same_num'))
    elif match_pattern("((x::real) = y) <--> false", tm) or match_pattern("((x::real) = y) <--> true", tm):
        t = real_const_eq_conv().get_proof_term(tm.lhs)
        return t
    elif match_pattern("(if P then (t :: 'a) else t) = t", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('cond_id'))
    elif match_pattern("(if P then (x::'a) else if (Q::bool) then (x::'a) else (y::'a)) = (if P ∨ Q then (x::'a) else y)", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('ite_elim_else_if'))
    return rewrite_real_second_level(tm)

def rewrite_real_second_level(tm):
    global atoms
    cvs = [value for _, value in atoms.items()]
    armony = [
        # (auto.norm_conv(), top_conv(rewr_conv('ite_to_disj')), bottom_conv(norm_neg_real_ineq_conv()), bottom_conv(real_norm_comparison()), proplogic.norm_full()),
        (bottom_conv(rewr_conv("if_true")), bottom_conv(rewr_conv("if_false"))),
        (bottom_conv(norm_neg_real_ineq_conv()),
        bottom_conv(real_norm_comparison()),
        *[top_conv(replace_conv(cv)) for cv in cvs],
        auto.norm_conv(), 
        bottom_conv(rewr_conv('not_true')),
        bottom_conv(rewr_conv('not_false')),
        bottom_conv(real_const_eq_conv()),
        bottom_conv(proplogic.norm_full()),
        bottom_conv(rewr_conv('if_true')),
        bottom_conv(rewr_conv('if_false')), 
        bottom_conv(rewr_conv('ite_to_disj')),
        bottom_conv(rewr_conv('ite_cond_disj_to_conj')),
        bottom_conv(rewr_conv('eq_false', sym=True)),
        top_conv(rewr_conv('real_ge_le_same_num')),
        bottom_conv(rewr_conv('norm_neg_equality')),
        bottom_conv(proplogic.norm_full()),
        bottom_conv(norm_neg_real_ineq_conv()),
        bottom_conv(real_norm_comparison()),
        bottom_conv(rewr_conv('cond_swap')), 
        bottom_conv(proplogic.norm_full()),),

        (bottom_conv(norm_neg_real_ineq_conv()),
        bottom_conv(real_norm_comparison()),
        auto.norm_conv(), 
        bottom_conv(rewr_conv('not_true')),
        bottom_conv(rewr_conv('not_false')),
        bottom_conv(real_const_eq_conv()),
        bottom_conv(proplogic.norm_full()),
        bottom_conv(rewr_conv('if_true')),
        bottom_conv(rewr_conv('if_false')), 
        bottom_conv(rewr_conv('ite_to_disj')),
        bottom_conv(rewr_conv('ite_cond_disj_to_conj')),
        bottom_conv(rewr_conv('eq_false', sym=True)),
        top_conv(rewr_conv('real_ge_le_same_num')),
        bottom_conv(rewr_conv('norm_neg_equality')),
        bottom_conv(proplogic.norm_full()),
        bottom_conv(norm_neg_real_ineq_conv()),
        bottom_conv(real_norm_comparison()),
        bottom_conv(rewr_conv('cond_swap')), 
        bottom_conv(proplogic.norm_full()),),

        (bottom_conv(rewr_conv('ite_eq_value')), bottom_conv(real_const_eq_conv()), proplogic.norm_full()),

        (proplogic.norm_full(), real_eval_conv(), ),
    
        (proplogic.norm_full(), top_conv(rewr_conv('cond_swap')), )
    ]

    # pt_norm_full = refl(tm).on_rhs(binop_conv(proplogic.norm_full()))
    # tm_norm_full = pt_norm_full.rhs
    for arm in armony:
        pt = compare_lhs_rhs(tm, arm)
        if pt.rule != 'sorry':
            return pt
    return Goal(tm).sorry()

# Cache of theorem names in library/smt.pyhol, keyed by prefix ('r' for
# rewrite schematic rules, 'd' for def-axiom schematic rules).  A Z3 proof
# can contain thousands of rewrite steps; re-parsing the file on each call
# is prohibitively slow.
_SMT_THM_NAMES = dict()

def _smt_theorem_names(prefix):
    """Names of theorems in library/smt.pyhol whose name starts with prefix,
    sorted.  The file is parsed lazily once and cached."""
    if prefix not in _SMT_THM_NAMES:
        from syntax import pyhol
        with open('library/smt.pyhol', 'r', encoding='utf-8') as f:
            f_data = pyhol.parse_pyhol(f.read())
        _SMT_THM_NAMES[prefix] = sorted(c['name'] for c in f_data['content']
                                        if c['name'].startswith(prefix))
    return _SMT_THM_NAMES[prefix]

def _sat_net(lhs, rhs):
    """Propositional decision net: prove ⊢ lhs = rhs by refuting ¬(lhs = rhs)
    with Tseitin + SAT + resolution (solve_cnf).  Non-logical subterms are
    treated as atoms, so this is complete for the full propositional
    fragment (all of bool_rewriter's rules).  Return None on failure."""
    try:
        return solve_cnf(Eq(lhs, rhs))
    except Exception:
        return None

def _arith_norm_net(lhs, rhs):
    """Linear arithmetic net for int/real equalities: normalize both sides
    with the same canonicalizing conversion; equal normal forms close the
    goal.  Complete for linear integer arithmetic (poly_rewriter and the
    linear part of arith_rewriter).  Return None on failure."""
    T = lhs.get_type()
    if T == IntType:
        cv = bottom_conv(integer.omega_simp_full_conv())
    elif T == RealType:
        # No proof-producing polynomial normalizer for real (real_norm
        # macro has no proof term); constant folding is the safe subset.
        cv = bottom_conv(real_eval_conv())
    else:
        return None
    try:
        pt_l = refl(lhs).on_rhs(cv)
        pt_r = refl(rhs).on_rhs(cv)
    except Exception:
        return None
    if pt_l.rhs == pt_r.rhs:
        return pt_l.transitive(pt_r.symmetric())
    return None

def _prove_atom(atom):
    """Prove ⊢ atom for an arithmetic equality atom, using the decision
    net and schematic rules on the atom itself.  Return None on failure."""
    if not atom.is_equals():
        return None
    try:
        pt = rewrite_decision_net(atom)
        if pt is not None and pt.rule != 'sorry':
            return pt
    except Exception:
        pass
    pt = schematic_rules_rewr(_smt_theorem_names('r') + SCHEMATIC_EXTRA,
                              atom.lhs, atom.rhs)
    return None if pt.rule == 'sorry' else pt

def _refute_atom(atom):
    """Prove ⊢ ¬atom for an arithmetic comparison/equality atom, by
    refuting atom with the omega (int) or simplex (real) backends.
    None on failure."""
    try:
        if not (atom.is_compares() or atom.is_equals()):
            return None
        T = atom.arg1.get_type()
        if T == IntType:
            try:
                return int_th_lemma_1_omega(Not(atom))
            except Exception:
                pass
            if atom.is_equals():
                # omega cannot parse the negation of an equality; a
                # ground equation is decided by evaluation instead:
                # ⊢ atom ⟷ false (int_neq_false_conv) lifts to ⊢ ¬atom.
                try:
                    pt1 = refl(atom).on_rhs(integer.int_norm_eq(),
                                            integer.int_neq_false_conv(mk_int_const_ineq_pt))
                    pt_c = refl(Not(atom).fun).combination(pt1)
                    pt_t = pt_c.on_prop(top_conv(rewr_conv('not_false')))
                    return pt_t.symmetric().equal_elim(apply_theorem('trueI'))
                except Exception:
                    return None
            # omega mishandles some constant-cancelling inequalities
            # (e.g. 1 + x <= x); the simplex backend covers them.
            return int_th_lemma_1_simplex(Not(atom))
        elif T == RealType:
            return real_th_lemma([Not(atom)])
    except Exception:
        return None
    return None

def _prove_comp(comp):
    """Prove ⊢ comp for a (linear) comparison atom by refuting its
    negation with omega / simplex and removing the double negation.
    Nonlinear atoms are correctly refuted by nobody, so None is
    returned and the caller falls through to the schematic stage."""
    if not comp.is_compares():
        return None
    try:
        T = comp.arg1.get_type()
        if T == IntType:
            try:
                pt = int_th_lemma_1_omega(Not(comp))
            except Exception:
                pt = int_th_lemma_1_simplex(Not(comp))
        elif T == RealType:
            pt = real_th_lemma([Not(comp)])
        else:
            return None
        if pt is None or pt.rule == 'sorry' or len(pt.gaps) != 0:
            return None
        return pt.on_prop(rewr_conv('double_neg'))
    except Exception:
        return None

def _norm_bool_side(side):
    """Normalize a negated boolean literal / negated comparison to a form
    the atom nets understand.  Returns (proof of ⊢ side = atom, atom);
    (None, side) when no normalization applies."""
    if not side.is_not():
        return None, side
    if side.arg == true:
        return refl(side).on_rhs(rewr_conv('not_true')), false
    if side.arg == false:
        return refl(side).on_rhs(rewr_conv('not_false')), true
    if side.arg.is_compares():
        try:
            T = side.arg.arg1.get_type()
            if T == IntType:
                pt = refl(side).on_rhs(integer.int_norm_neg_compares())
            elif T == RealType:
                pt = refl(side).on_rhs(norm_neg_real_ineq_conv())
            else:
                return None, side
            return pt, pt.rhs
        except Exception:
            return None, side
    return None, side

def _atom_bool_net(tm):
    """Rewrite goals of the form atom ⟷ true / atom ⟷ false (in either
    order, also under a negation wrapper on either side): prove or
    refute the atom with the existing machinery, then connect with
    eq_true / eq_false.  Covers the arith_rewriter family that reduces
    comparisons and equations to true/false; the pure SAT net cannot
    close these because it treats arithmetic atoms opaquely."""
    if not tm.is_equals():
        return None
    if tm.lhs.is_not() and tm.rhs.is_not():
        # Z3 rewrites atoms inside a negation context, emitting steps
        # like ¬atom ⟷ ¬true: close the inner equality and lift it
        # through the Not congruence (Not = Not combined with the inner
        # proof gives ⊢ ¬P ⟷ ¬Q).
        try:
            inner = Eq(tm.lhs.arg, tm.rhs.arg)
            pt_inner = rewrite_decision_net(inner)
            if pt_inner is None or pt_inner.rule == 'sorry' or len(pt_inner.gaps) != 0:
                pt_inner = schematic_rules_rewr(
                    _smt_theorem_names('r') + SCHEMATIC_EXTRA,
                    tm.lhs.arg, tm.rhs.arg)
                if pt_inner.rule == 'sorry' or len(pt_inner.gaps) != 0:
                    pt_inner = None
        except Exception:
            pt_inner = None
        if pt_inner is not None:
            return refl(tm.lhs.fun).combination(pt_inner)
    lhs_pt, lhs_a = _norm_bool_side(tm.lhs)
    rhs_pt, rhs_a = _norm_bool_side(tm.rhs)

    def _core(a1, a2):
        if a1.is_not() and (a1.arg.is_equals() or a1.arg.is_compares()):
            # Negated atom: ⟷ true means the atom is refutable,
            # ⟷ false means the atom is provable.
            inner = a1.arg
            if a2 == true:
                pt = _refute_atom(inner)
                return iff_true(pt, None) if pt is not None else None
            if a2 == false:
                pt = _prove_atom(inner) if inner.is_equals() else _prove_comp(inner)
                if pt is not None:
                    pt_c = refl(a1.fun).combination(iff_true(pt, None))
                    pt_nt = refl(false).on_rhs(rewr_conv('not_true', sym=True))
                    return pt_c.transitive(pt_nt.symmetric())
                return None
        if a2 == true:
            if a1.is_equals():
                pt = _prove_atom(a1)
            elif a1.is_compares():
                pt = _prove_comp(a1)
            else:
                pt = None
            return iff_true(pt, None) if pt is not None else None
        if a2 == false:
            pt = _refute_atom(a1)
            return iff_false(pt, None) if pt is not None else None
        return None

    core = _core(lhs_a, rhs_a)
    if core is None:
        core = _core(rhs_a, lhs_a)
        if core is not None:
            core = core.symmetric()
    if core is None:
        return None
    if lhs_pt is None and rhs_pt is None:
        return core
    pt = core
    if lhs_pt is not None:
        pt = lhs_pt.transitive(pt)
    if rhs_pt is not None:
        pt = pt.transitive(rhs_pt.symmetric())
    return pt

def rewrite_decision_net(tm):
    """Decision-procedure safety net for rewrite goals tm of the form
    lhs = rhs.  Covers the decidable fragment of the rewriter's rules
    (~177 of 278): propositional structure by SAT, linear arithmetic by
    normalization.  Return a ProofTerm of ⊢ tm, or None if the net cannot
    close the goal (the caller then falls back to the existing routes)."""
    if not tm.is_equals():
        return None
    lhs, rhs = tm.lhs, tm.rhs
    Ts = analyze_type(tm)
    try:
        if IntType not in Ts and RealType not in Ts:
            return _sat_net(lhs, rhs)
        pt = _arith_norm_net(lhs, rhs)
        if pt is not None and pt.rule != 'sorry':
            return pt
        pt_atom = _atom_bool_net(tm)
        if pt_atom is not None and pt_atom.rule != 'sorry':
            return pt_atom
        # Mixed: boolean structure over arithmetic atoms.  Normalize the
        # arithmetic atoms, then hand the propositional structure to SAT.
        pt_norm = refl(tm).on_rhs(
            bottom_conv(try_conv(integer.int_norm_neg_compares())),
            bottom_conv(try_conv(integer.omega_form_conv())),
            bottom_conv(try_conv(norm_neg_real_ineq_conv())),
            bottom_conv(try_conv(real_norm_comparison())),
            proplogic.norm_full(),
        )
        if pt_norm.rhs == true:
            # Normalization alone collapsed the goal to true.
            return pt_norm.symmetric().equal_elim(apply_theorem('trueI'))
        if pt_norm.rhs.is_equals() and pt_norm.rhs != tm:
            pt2 = _sat_net(pt_norm.rhs.lhs, pt_norm.rhs.rhs)
            if pt2 is not None and pt2.rule != 'sorry':
                return pt_norm.symmetric().equal_elim(pt2)
        return None
    except Exception:
        return None

def _guarded(fn, tm, *args):
    """Run a rewrite heuristic; a crashing heuristic must not abort the
    remaining stages (net / assertion / schematic), so return None."""
    try:
        return fn(tm, *args)
    except Exception:
        return None

def _ground_eval(tm):
    """Close a rewrite equation whose both sides are ground arithmetic
    terms by numeral evaluation (the trusted nat_eval / int_eval macros,
    extended to power / DIV / MOD).  Returns None unless both sides
    evaluate to the same numeral."""
    from theories.nat.conv import nat_eval_conv
    T = tm.lhs.get_type()
    if T == IntType:
        cv = integer.int_eval_conv()
    elif T == NatType:
        cv = nat_eval_conv()
    else:
        return None
    try:
        pt1 = cv.get_proof_term(tm.lhs)
        pt2 = cv.get_proof_term(tm.rhs)
    except Exception:
        return None
    if pt1.rhs == pt2.rhs:
        return pt1.transitive(pt2.symmetric())
    return None

def schematic_rules_rewr_cond(thms, lhs, rhs):
    """Like schematic_rules_rewr, but also uses conditional theorems
    (implications whose conclusion is the equation lhs = rhs): each
    hypothesis is discharged by the decision nets, so the result is
    gap-free or the theorem is skipped.  Returns a ProofTerm."""
    for thm in thms:
        try:
            pt = ProofTerm.theorem(thm)
            if not pt.prop.is_implies():
                continue
            preds, concl = pt.prop.strip_implies()
            if not concl.is_equals():
                continue
            inst1 = matcher.first_order_match(concl.lhs, lhs)
            inst = matcher.first_order_match(concl.rhs, rhs, inst=inst1)
            pt = pt.substitution(inst)
            preds, concl = pt.prop.strip_implies()
            discharged = []
            for p in preds:
                pt_h = rewrite_decision_net(Eq(p, true))
                if pt_h is None or pt_h.rule == 'sorry' or len(pt_h.gaps) != 0:
                    discharged = None
                    break
                discharged.append(pt_h.symmetric().equal_elim(apply_theorem('trueI')))
            if discharged is None:
                continue
            for pt_h in discharged:
                pt = pt.implies_elim(pt_h)
            return pt
        except Exception:
            continue
    return Goal(Eq(lhs, rhs)).sorry()

def _rewrite(tm):
    th_name = _smt_theorem_names('r')
    if tm.lhs == tm.rhs:
        return refl(tm.lhs)
    Ts = analyze_type(tm)
    heuristic, heuristic_name = None, None
    if IntType in Ts:
        heuristic = rewrite_int
        heuristic_name = 'int'
    elif RealType in list(Ts):
        heuristic = rewrite_real
        heuristic_name = 'real'
    elif IntType not in Ts and RealType not in Ts: # only have bool type variables
        heuristic = rewrite_bool
        heuristic_name = 'bool'
    else:
        return Goal(tm).sorry()

    args1 = (tm, True) if (BoolType in Ts and heuristic_name != 'bool') else (tm,)
    pt1 = _guarded(heuristic, *args1)
    if pt1 is not None and pt1.rule != 'sorry':
        return pt1
    pt_net = rewrite_decision_net(tm)
    if pt_net is not None and pt_net.rule != 'sorry':
        return pt_net
    try:
        pt_asst_lhs = rewrite_by_assertion(tm.lhs)
        pt_asst_rhs = rewrite_by_assertion(tm.rhs)
        tm_asst = Eq(pt_asst_lhs.rhs, pt_asst_rhs.rhs)
    except Exception:
        tm_asst = None
    if tm_asst is not None:
        pt2 = _guarded(heuristic, tm_asst)
        if pt2 is not None and pt2.rule != 'sorry':
            return pt_asst_lhs.transitive(pt2).transitive(pt_asst_rhs.symmetric())
        pt_net2 = rewrite_decision_net(tm_asst)
        if pt_net2 is not None and pt_net2.rule != 'sorry':
            return pt_asst_lhs.transitive(pt_net2).transitive(pt_asst_rhs.symmetric())
    if heuristic_name == 'bool':
        thms = th_name[:60] + SCHEMATIC_EXTRA
    else:
        thms = th_name + SCHEMATIC_EXTRA
    pt_eval = _guarded(_ground_eval, tm)
    if pt_eval is not None:
        return pt_eval
    pt = schematic_rules_rewr(thms, tm.lhs, tm.rhs)
    if pt.rule != 'sorry':
        return pt
    return schematic_rules_rewr_cond(thms, tm.lhs, tm.rhs)

# def rewrite(t, z3terms, assertions=[]):
def rewrite(t):
    """
    Multiple strategies for rewrite rule:
    a) if we want to rewrite distinct[a,...,z] to false, we can check whether there are
    same terms in args.
    """
    try:
        return _rewrite(t)
    except ConvException:
        return Goal(t).sorry()

def quant_inst(p):
    """
    A proof of (or (not (forall (x) (P x))) (P a))
    Note: because "a" maybe not equal to "x", so we need to
    replace "x" by "a" when necessary.
    """
    pat = ProofTerm.theorem('forall_elim')
    f = Implies(p.arg1.arg, p.arg)
    inst = matcher.first_order_match(pat.prop, f)
    pt1 = apply_theorem('forall_elim', inst=inst)
    
    old_var = Var("x", pt1.prop.arg1.arg.var_T)
    new_var = Var(p.arg1.arg.arg.var_name, p.arg1.arg.arg.var_T)

    if old_var != new_var: 
        # we must subsitute old_var by new var
        # example: |- (!x. s x = 0) --> s 2 = 0) to |- (!n. s n = 0) --> s 2 = 0)
        ptn1 = ProofTerm.assume(pt1.prop.arg1) # !x. s x = 0 |- !x. s x = 0
        ptn2 = ptn1.forall_elim(new_var) # !x. s x = 0 |- s n = 0 
        ptn3 = ptn2.forall_intr(new_var) # !x. s x = 0 |- !n. s n = 0
        ptn4 = ProofTerm.assume(ptn3.prop) # !n. s n = 0 |- !n. s n = 0
        ptn5 = ptn4.forall_elim(old_var) # !n. s n = 0 |- s x = 0
        ptn6 = ptn5.forall_intr(old_var) # !n. s n = 0 |- !x. s x = 0
        ptn7 = pt1.implies_elim(ptn6) # !n. s n = 0 |- s 2 = 0
        pt1 = ptn7.implies_intr(ptn7.hyps[0]) # |- (!n. s n = 0) --> s 2 = 0

    pt2 = apply_theorem('disj_conv_imp', inst=Inst(A=pt1.prop.arg1, B=pt1.prop.arg)).symmetric()
    pt3 = pt2.equal_elim(pt1)
    return pt3

def quant_intro(p, q):
    def helper(l):
        if l.is_abs():
            return [Var(l.var_name, l.var_T)] + helper(l.body)
        else:
            return []
    
    l, r = p.prop.lhs, p.prop.rhs
    var = helper(l)
    is_forall = q.lhs.is_forall()
    pt = p
    for v in var:
        pf_refl = ProofTerm.reflexive(v)
        pt = ProofTerm.combination(pt, pf_refl)
        pt_l = ProofTerm.beta_conv(l(v)).symmetric()
        pt_r = ProofTerm.beta_conv(r(v))
        pt_l_beta_norm = pt_l.transitive(pt)
        pt = pt_l_beta_norm.transitive(pt_r)
        l, r = pt.prop.lhs, pt.prop.rhs

    for v in reversed(var):
        pf_quant = ProofTerm.reflexive(forall(v.get_type())) if is_forall else ProofTerm.reflexive(exists(v.get_type()))
        pt = pt.abstraction(v)
        pt = ProofTerm.combination(pf_quant, pt)

    return pt

def mp(arg1, arg2):
    """modus ponens:
    
    arg1: ⊢ p
    arg2: ⊢ p <--> q
    then have: ⊢ q
    """
    try:
        pt = ProofTerm.equal_elim(arg2, arg1)
    except:
        pt = Goal(arg2.prop, arg2.th.hyps, arg1.th.hyps).sorry()
    return pt

def iff_true(arg1, arg2):
    """
    arg1: ⊢ p
    return: ⊢ p <--> true
    """
    pt1 = apply_theorem('eq_true', inst=Inst(A=arg1.prop))
    return ProofTerm.equal_elim(pt1, arg1)

def iff_false(arg1, arg2):
    """
    arg1: ⊢ ¬p
    return: ⊢ ¬p <--> false
    """
    pt1 = apply_theorem('eq_false', inst=Inst(A=arg1.prop.arg))
    return ProofTerm.equal_elim(pt1, arg1)

def not_or_elim(arg1, arg2):
    """
    For the reason that z3 elimates double neg term implicitly, so arg2 may be negative or positive.  
    There are two cases:
    1) arg2 is a negative term: ¬t: we need to check if there exists a disjunct in arg1
    proposition which is equal to t;
    2) arg2 is a positive term t: we need to check if there exists a disjunct in arg1's proposition
    which is equal to ¬t;
    """
    global disj_expr
    if arg1.prop not in disj_expr:
        disj_expr.update({arg1.prop: dict()})
    
    for key, value in disj_expr[arg1.prop].items():
        if key == arg2:
            # print("!!!")
            return value        

    disj = arg2.arg if arg2.is_not() else Not(arg2)

    pt = arg1
    while pt.prop.arg.is_disj():
        disj1, disj2 = pt.prop.arg.arg1, pt.prop.arg.arg
        pt_l, pt_r = apply_theorem('not_or_elim1', pt).on_prop(try_conv(rewr_conv('double_neg'))),\
            apply_theorem('not_or_elim2', pt).on_prop(try_conv(rewr_conv('double_neg')))
        disj_expr[arg1.prop].update({disj1: pt_l, disj2: pt_r})
        if disj1 == disj:
            return pt_l.on_prop(try_conv(rewr_conv('double_neg')))
        elif disj2 == disj:
            return pt_r.on_prop(try_conv(rewr_conv('double_neg')))
        else:
            pt = pt_r
    assert pt.prop == disj
    return pt.on_prop(try_conv(rewr_conv('double_neg')))

def double_neg(pt):
    """
    If pt prop is in double neg form, try to simplify it.
    """
    cv = top_conv(try_conv(rewr_conv('double_neg')))
    return pt.on_prop(cv)

def nnf(pt):
    """
    Sometimes z3 get a proof which propositions is not in nnf-form.
    And z3 directly use it to operate unit-resolution, so we implemented a rule here
    to use de Morgan law when the propositions is not in nnf form.
    """
    cv_de_morgan_and = top_conv(try_conv(rewr_conv('de_morgan_thm1')))
    cv_de_morgan_or = top_conv(try_conv(rewr_conv('de_morgan_thm2')))
    
    if pt != pt.on_prop(cv_de_morgan_and):
        return nnf(pt.on_prop(cv_de_morgan_and))
    elif pt != pt.on_prop(cv_de_morgan_or):
        return nnf(pt.on_prop(cv_de_morgan_or))
    else:
        return pt

def beta_norm_lambda_eq(pt):
    """
    Suppose pt is: ⊢ (λx. p)(x) <--> (λy. q)(y)
    return a proofterm: ⊢ p x <--> q y
    """
    assert isinstance(pt, ProofTerm) and pt.prop.is_equals() and\
        pt.prop.lhs.head.is_abs() and pt.prop.rhs.head.is_abs(), \
        "Invalid ProofTerm: %s" % str(pt)
    lhs, rhs = pt.prop.lhs, pt.prop.rhs
    pt_lhs = ProofTerm.beta_conv(lhs).symmetric()
    pt_rhs = ProofTerm.beta_conv(rhs)
    return pt_lhs.transitive(pt).transitive(pt_rhs)

def schematic_rules_def_axiom(axiom):
    """Rewrite by instantiating def_axiom schematic theorems."""
    thms = _smt_theorem_names('d')
    for thm in thms:
        pt = ProofTerm.theorem(thm)
        try:
            inst1 = matcher.first_order_match(pt.prop, axiom)
            return pt.substitution(inst1)
        except matcher.MatchException:
            continue
    return None
    

def def_axiom(arg1):
    """
    def-axiom rule prove propositional tautologies axioms.
    for reason that prove need propositional logic decision procedure,
    currently use proofterm.sorry
    """
    Ts = analyze_type(arg1)
    if IntType in Ts:
        pt = refl(arg1).on_rhs(
            top_conv(rewr_conv('int_ite01')),
            bottom_conv(rewr_conv('eq_mean_true')),
            bottom_conv(integer.int_norm_eq()),
            bottom_conv(integer.int_neq_false_conv(mk_int_const_ineq_pt)),
            proplogic.norm_full()
        )
        pt = pt.symmetric()
        try:
            basic.load_theory('sat')
            pt_cnf = solve_cnf(pt.lhs)
            basic.load_theory('smt')
            return pt.equal_elim(pt_cnf)
        except:
            pass
    try:
        return solve_cnf(arg1)
    except:
        return Goal(arg1).sorry()

def intro_def(concl):
    """
    Introduce a name for a formula/term e.
    There are several cases according to different type of e:
    
    a) e is of boolean type:
    return n = e ⊢ (n ∨ ¬e) ∧ (¬n ∨ e)
    b) e is of form "ite cond th e1":
    return n = e ⊢ (¬cond ∨ n = th) ∧ (cond ∨ n = e1)
    c) otherwise:
    return n = e ⊢ n = e
    
    But z3 only provide the right hands of proofterm instead of n,
    so we need to find n at first. After find n, we need to prove
    n = e ⊢ concl. 
    """
    case = ""
    if concl.is_conj(): # a), b) cases
        if concl.arg1.arg.is_equals():
            n = concl.arg1.arg.lhs
            case = "b"
        else:
            n = concl.arg1.arg1
            case = "a"
    else:
        n = concl.lhs
        case = "c"
    
    #prove.
    if case == "c":
        return ProofTerm.assume(concl)
    elif case == "a":
        e = concl.arg.arg
        pt = apply_theorem('iff_conv_conj_disj', inst = Inst(A=n, B=e))
        pt_assume = ProofTerm.assume(Eq(n, e))
        return ProofTerm.equal_elim(pt, pt_assume)
    else: # case == "b"
        cond = concl.arg.arg1
        th = concl.arg1.arg.rhs
        e1 = concl.arg.arg.rhs
        T = th.get_type()
        ite = Const("IF", TFun(BoolType, T, T, T))(cond, th, e1)
        redundant.append(Eq(n, ite)) # we need to delete the equalities after reconstruction.
        # First prove ⊢ (¬cond ∨ n = th)
        pt = apply_theorem('if_P', inst=Inst(P=cond, x=th, y=e1))
        pt_cond_assm = ProofTerm.assume(cond)
        pt1 = pt.implies_elim(pt_cond_assm) # cond ⊢ ite = th
        pt_eq = ProofTerm.assume(Eq(n, ite)) # n = ite ⊢ n = ite
        pt2 = pt_eq.transitive(pt1) # n = ite, cond ⊢ n = th
        pt3 = pt2.implies_intr(cond) # n = ite ⊢ cond -> n = th
        cv = rewr_conv('disj_conv_imp', sym=True)
        pt4 = cv.get_proof_term(pt3.prop) # ⊢ cond -> n = th <--> ¬cond ∨ n = th
        pt5 = ProofTerm.equal_elim(pt4, pt3) # n = ite ⊢ ¬cond ∨ n = th
        # then prove ⊢ (cond ∨ n = e1)
        pt6 = apply_theorem('if_not_P', inst=Inst(P=cond, x=th, y=e1)) # ⊢ ¬cond --> (if cond then th else e1) = e1
        pt_not_con_assm = ProofTerm.assume(Not(cond)) # ¬cond ⊢ ¬cond
        pt7 = pt6.implies_elim(pt_not_con_assm) # ¬cond ⊢ (if cond then th else e1) = e1
        pt8 = pt_eq.transitive(pt7) # n = ite, ¬cond ⊢ n = e1
        pt9 = pt8.implies_intr(Not(cond)) # n = ite ⊢ ¬cond --> n = e1
        pt10 = cv.get_proof_term(pt9.prop) # ⊢ ¬cond --> n = e1 <--> ¬¬cond ∨ n = e1
        pt11 = ProofTerm.equal_elim(pt10, pt9)
        pt12 = double_neg(pt11) # n = ite ⊢ cond ∨ n = e1
        pt13 = apply_theorem('conjI', pt5, pt12)
        return pt13


def apply_def(arg1):
    return ProofTerm.reflexive(arg1.lhs)

def unit_resolution(pt1, pts, concl, z3terms):
    """
    T1: (or l_1 ... l_n l_1' ... l_m')
    T2: (not l_1)
    ...
    T(n+1): (not l_n)
    [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')

    parameters: pt1 is T1 in HOL, pts is [T2,...,Tn+1] in HOL, concl is the prop in HOL 
    which we want to prove, z3terms are the original T1,...,Tn+1, with unit-resolution ...

    a) get n, n = len(z3terms) - 2
    b) use a set to record T1's disjunction structure, every time resolution
    with Ti, the set delete corresponding li.
    c) call resolution method to resolve each Ti.
    """
    n = len(z3terms) - 2
    original_disj = z3terms[0].arg(z3terms[0].num_args() - 1)
    if z3.is_or(original_disj):
        literals = [translate(original_disj.arg(i)) for i in range(original_disj.num_args())]
    else:
        literals = [translate(original_disj)]
    resolved_literal = None
    disj1 = literals
    pt_resolved = pt1

    for i in range(n):
        if resolved_literal is not None:
            disj1.remove(resolved_literal)

        disj2 = [translate(z3terms[i+1].arg(z3terms[i+1].num_args() - 1))]
        side = None
        for j, t1 in enumerate(disj1):
            if t1 == Not(disj2[0]):
                side = 'right'
                break
            elif Not(t1) == disj2[0]:
                side = 'left'
                break
        
        assert side is not None, 'literal not found'

        resolved_literal = disj1[j]

        
        disj1 = [disj1[j]] + disj1[:j] + disj1[j+1:]
        eq_pt1 = imp_disj_iff(Eq(pt_resolved.prop, Or(*disj1)))
        new_pt1 = ProofTerm.equal_elim(eq_pt1, pt_resolved)
        new_pt2 = pts[i]
        if side == 'left': 
            if len(disj1) > 1:
                pt_resolved = apply_theorem('resolution_left', new_pt1, new_pt2)
            else: # len(disj1) == 1 and len(disj2) == 1
                pt_resolved = apply_theorem('negE', new_pt2, new_pt1)
        else: # side == 'right'
            if len(disj1) > 1:
                pt_resolved = apply_theorem('resolution_right', new_pt2, new_pt1)
            else:
                pt_resolved = apply_theorem('negE', new_pt1, new_pt2)

    return pt_resolved


def lemma(arg1, arg2, subterm):
    """
    arg1 is proof: Γ ∪ {L1, L2, ..., Ln} ⊢ ⟂
    return proof: Γ ⊢ ¬L1 ∨ ... ∨ ¬Ln

    L1,...,Ln are propositions stored in the set when use hypothesis rule. 

    the implementation stategy is match arg1's hyps with the set, and use implies_intr()
    move them to props, then
    recursively using theorem "A->B --> ¬A ∨ B"

    And because L1, L2, ..., Ln have an order, so we need the original z3 term.
    """
    subterm = subterm[-1]
    if z3.is_or(subterm):
        subs = [subterm.arg(i) for i in range(subterm.num_args())]
    else:
        subs = [subterm]
    literal = []
    for s in subs:
        if z3.is_not(s):
            literal.append(translate(s.arg(0)))
        else:
            literal.append(Not(translate(s)))
    # hyps = [p for p in arg1.th.hyps if p in hypos] # store hyps
    pt1 = arg1
    for h in reversed(literal):
        pt1 = pt1.implies_intr(h)
    # now we have Γ ⊢ L1 --> L2 --> ...--> Ln --> ⟂
    cv1 = top_conv(rewr_conv('disj_conv_imp', sym=True))
    cv2 = top_sweep_conv(rewr_conv('disj_false_right'))
    cv3 = top_conv(rewr_conv('double_neg'))
    return pt1.on_prop(cv1, cv2, cv3)


def _sk_exists_eq(P_body):
    """Prove ⊢ exists P_body = P_body (Some P_body), i.e.
    ⊢ (∃x. Q x) = (λx. Q x) (SOME x. Q x), from exists_thm
    (⊢ exists = λP. P (Some P), library/logic_base.pyhol)."""
    inst = Inst()
    inst.tyinst['a'] = P_body.get_type().domain_type()
    pt1 = ProofTerm.theorem('exists_thm').substitution(inst)
    pt_comb = pt1.combination(ProofTerm.reflexive(P_body))
    pt_beta = ProofTerm.beta_conv(pt_comb.rhs)
    return pt_comb.transitive(pt_beta)

def sk(concl):
    """Skolemization rule: no antecedents; the conclusion is
    (∃x. P x) = P c  or  ¬(∀x. P x) = ¬(P c), where c is the Skolem term.
    Following Isabelle (z3_replay.ML sk_rules), c is treated as
    SOME x. ... : we assume c = Some (λx. ...), prove the conclusion with
    exists_thm, and register the assumption in `redundant` so that it is
    discharged at the very end by delete_redundant."""
    orig_concl = concl
    try:
        is_neg = False
        if concl.lhs.is_not() and concl.lhs.arg.is_forall() and concl.rhs.is_not():
            is_neg = True
            pt_not_all = refl(concl.lhs).on_rhs(rewr_conv('not_all'))
            # After not_all: lhs becomes ∃x. ¬(P x), an exists-shape formula.
            lhs = pt_not_all.rhs
            rhs = concl.rhs
        else:
            lhs, rhs = concl.lhs, concl.rhs
        if not lhs.is_exists() or not rhs.is_comb() or (is_neg and not rhs.arg.is_comb()):
            return Goal(orig_concl).sorry()
        P_body = lhs.arg            # λx. P x  (λx. ¬(P x) in the ¬∀ case)
        # the application P c: rhs itself, or rhs.arg under the negation
        pt_app_target = rhs.arg if is_neg else rhs
        c = pt_app_target.arg       # Skolem term
        # ⊢ (∃x. P x) = (λx. P x) (Some P_body) = P (Some P_body)
        pt_main = _sk_exists_eq(P_body)
        pt_right = ProofTerm.beta_conv(pt_main.rhs)
        # assumption c = Some P_body; congruence rewrites P (Some P_body)
        # into P c (under the negation in the ¬∀ case).
        some = Const('Some', TFun(P_body.get_type(), c.get_type()))
        pt_assume = ProofTerm.assume(Eq(c, some(P_body)))
        pt_app = ProofTerm.reflexive(pt_app_target.head).combination(pt_assume)
        if is_neg:
            pt_cong = ProofTerm.reflexive(neg).combination(pt_app)
        else:
            pt_cong = pt_app
        pt_chain = pt_main.transitive(pt_right).transitive(pt_cong.symmetric())
        if is_neg:
            pt_chain = pt_not_all.transitive(pt_chain)
        redundant.append(pt_assume.prop)
        return pt_chain
    except Exception:
        return Goal(orig_concl).sorry()


def real_th_lemma(args):
    """handle real th-lemma."""
    def traverse_A(pt):
        if pt.prop.is_conj():
            return traverse_A(apply_theorem('conjD1', pt)) + traverse_A(apply_theorem('conjD2', pt))
        else:
            return [pt]
    if len(args) == 1: 
        # case1: single term. e.g. Or(Not(x_4 <= 0), Not(x_4 >= 60))
        # In this case, we need to prove its negation is false.
        
        # First step, negate it and use de morgan to simplify it: And(x_4 <= 0, x_4 >= 60)
        pt1 = ProofTerm.assume(Not(args[0])).on_prop(
            top_conv(rewr_conv('de_morgan_thm2')),
            top_conv(rewr_conv('double_neg')),
            bottom_conv(norm_neg_real_ineq_conv()),
            proplogic.norm_full()
        )

        # Second step, send the inequalies in conjunction to simplex, get
        # |- x_4 <= 0 --> x_4 >= 60 --> false
        # pt_norm_prop = pt1.on_prop(bottom_conv(rewr_conv('real_mul_lid', sym=True)), bottom_conv(real_eval_conv()))
        conjs = pt1.prop.strip_conj()
        if any(conj.is_greater() or conj.is_less() for conj in conjs):
            pt2 = simplex_strict.StrictSimplexMacro().get_proof_term(args=conjs)
        else:
            pt2 = simplex.SimplexMacro().get_proof_term(args=conjs) # 1 * x_4 <= 0, 1 * x_4 >= 60 |- false

        for h in reversed(conjs): # |- 1 * x_4 <= 0 --> 1 * x_4 >= 60 --> false
            pt2 = pt2.implies_intr(h)
        pt2 = pt2.on_prop(bottom_conv(rewr_conv('real_mul_lid'))) # |- x_4 <= 0 --> x_4 >= 60 --> false
        
        # Third step, construct the proof for each conjunct from the conjunction assumption, e.g.
        # 1 * x_4 <= 0, 1 * x_4 >= 60 |- 1 * x_4 <= 0
        # 1 * x_4 <= 0, 1 * x_4 >= 60 |- 1 * x_4 >= 60

        pts_A = traverse_A(ProofTerm.assume(pt1.prop))

        # Fourth step, use the conjunct proofs to do implies_elim, finally got 
        # |- 1 * x_4 <= 0 & 1 * x_4 >= 60 --> false
        pt3 = functools.reduce(lambda x, y: x.implies_elim(y), [pt2] + pts_A)
        pt4 = pt3.implies_intr(pt3.hyps[0])
        
        # Last step, prove the original formula is true
        pt5 = refl(Not(args[0])).on_rhs(
            top_conv(rewr_conv('de_morgan_thm2')),
            top_conv(rewr_conv('double_neg')),
            bottom_conv(norm_neg_real_ineq_conv()),
            proplogic.norm_full()
        ) # |- Not(Or(Not(x_4 <= 0), Not(x_4 >= 60))) <--> And(x_4 <= 0, x_4 >= 60)
        pt6 = pt4.on_prop(top_conv(replace_conv(pt5.symmetric()))) # |- Not(Or(Not(x_4 <= 0), Not(x_4 >= 60))) --> false
        pt7 = apply_theorem('negI', pt6).on_prop(rewr_conv('double_neg'))
        return pt7

    else:
        # case2, there are several proofterms in args, and the last arg is false, e.g.
        # |- x_4 ≥ 60
        # |- x_2 ≤ 1
        # |- x_2 + -1 * x_4 ≥ 0
        # false
        
        # First step, send these inequalies to simplex, get
        # |- x_4 ≥ 60 --> x_2 ≤ 1 --> x_2 + -1 * x_4 ≥ 0 --> false
        norm_pts = []
        input_ineq = []
        for pt in args[:-1]:
            if pt.prop.is_not():
                norm_pt = refl(pt.prop).on_rhs(norm_neg_real_ineq_conv()).symmetric()
                norm_pts.append(norm_pt)
                input_ineq.append(norm_pt.lhs)
            else:
                input_ineq.append(pt.prop)

        
        # ineqs = [pt.prop for pt in args[:-1]]

        if any(ineq.is_greater() or ineq.is_less() for ineq in input_ineq):
            pt1 = simplex_strict.StrictSimplexMacro().get_proof_term(args=input_ineq)
        else:     
            pt1 = simplex.solve_hol_ineqs(input_ineq)
        for h in reversed(input_ineq): # |- 1 * x_4 <= 0 --> 1 * x_4 >= 60 --> false
            pt1 = pt1.implies_intr(h)
        pt1 = pt1.on_prop(*[top_conv(replace_conv(pt)) for pt in norm_pts])
        pt2 = pt1.on_prop(bottom_conv(rewr_conv('real_mul_lid')))
        
        # Second step, implies elim each given proof term's proposition with the simplex's proof term
        pt_final = functools.reduce(lambda x, y: x.implies_elim(y), [pt1] + list(args[:-1]))

        return pt_final

def int_th_lemma_1_omega(tm):
    def traverse_A(pt):
            if pt.prop.is_conj():
                return traverse_A(apply_theorem('conjD1', pt)) + traverse_A(apply_theorem('conjD2', pt))
            else:
                return [pt]
    pt_refl = refl(Not(tm))
    pt_norm = pt_refl.on_rhs(
        top_conv(proplogic.norm_full()),
        top_conv(integer.int_norm_neg_compares()), top_conv(integer.omega_form_conv()),
        top_conv(integer.omega_form_conv())
    )
    conjs = pt_norm.rhs.strip_conj()
    solver = omega.OmegaHOL(conjs)

    pt = solver.solve()
    
    # reconstruction, get proof ⊢ P
    # for now, we have a proof of e_1, ..., e_n ⊢ false
    # the proof is as following:
    # a) get ⊢ e_1 → ... → e_n -> false
    # b) get e_1 ∧ ... ∧ e_n ⊢ e_1, ..., e_1 ∧ ... ∧ e_n ⊢ e_n
    # c) get e_1 ∧ ... ∧ e_n ⊢ false QED
    # a)  
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), reversed(conjs), pt)
    # b)
    conj_pts = [p.on_prop(integer.omega_form_conv()) for p in traverse_A(ProofTerm.assume(pt_norm.rhs))]
    # c)
    pt_conj_false = functools.reduce(lambda x, y: x.implies_elim(y), conj_pts, pt_implies_false)

    # final step, we already have ⊢ ¬P ⟷ e_1 ∧ ... ∧ e_n and ⊢ e_1 ∧ ... ∧ e_n → false
    # so we could derive ⊢ P
    pt_neg_prop_implies_false = pt_conj_false.implies_intr(pt_norm.rhs).on_prop(top_conv(replace_conv(pt_norm.symmetric())))
    return apply_theorem('negI', pt_neg_prop_implies_false).on_prop(rewr_conv('double_neg'))

def int_th_lemma_n_omega(tms):
    pts = tms[:-1]
    pt_norm_eq = [refl(pt.prop).on_rhs(try_conv(integer.int_norm_neg_compares()), try_conv(integer.omega_form_conv())).symmetric() for pt in pts]
    solver = omega.OmegaHOL([pt.lhs for pt in pt_norm_eq])
    pt_unsat = solver.solve()
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), pt_unsat.hyps, pt_unsat)
    pt_implies_false_initial = pt_implies_false
    for pt in pt_norm_eq:
       pt_implies_false_initial = pt_implies_false_initial.on_prop(top_conv(replace_conv(pt)))
    imps, _ = pt_implies_false_initial.prop.strip_implies()
    pt_final = pt_implies_false_initial
    for imp in imps:
        pt_final = pt_final.implies_elim(ProofTerm.assume(imp))
    return pt_final 

def int_th_lemma_1_simplex(tm):
    def traverse_A(pt):
            if pt.prop.is_conj():
                return traverse_A(apply_theorem('conjD1', pt)) + traverse_A(apply_theorem('conjD2', pt))
            else:
                return [pt]
    pt_refl = refl(Not(tm))
    pt_norm = pt_refl.on_rhs(
        top_conv(rewr_conv('int_neg_equal')),
        top_conv(proplogic.norm_full()),
        top_conv(integer.int_norm_neg_compares()),
        top_conv(integer.int_simplex_form())
    )
    conjs = pt_norm.rhs.strip_conj()
    # pt = simplex.unsat_integer_simplex(conjs)
    pt = simplex.IntegerSimplexMacro().get_proof_term(args=conjs)
    # pt = solver.solve()
    
    # reconstruction, get proof ⊢ P
    # for now, we have a proof of e_1, ..., e_n ⊢ false
    # the proof is as following:
    # a) get ⊢ e_1 → ... → e_n -> false
    # b) get e_1 ∧ ... ∧ e_n ⊢ e_1, ..., e_1 ∧ ... ∧ e_n ⊢ e_n
    # c) get e_1 ∧ ... ∧ e_n ⊢ false QED
    # a)  
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), reversed(conjs), pt)
    # b)
    conj_pts = [p.on_prop(integer.int_simplex_form()) for p in traverse_A(ProofTerm.assume(pt_norm.rhs))]
    # c)
    pt_conj_false = functools.reduce(lambda x, y: x.implies_elim(y), conj_pts, pt_implies_false)

    # final step, we already have ⊢ ¬P ⟷ e_1 ∧ ... ∧ e_n and ⊢ e_1 ∧ ... ∧ e_n → false
    # so we could derive ⊢ P
    pt_neg_prop_implies_false = pt_conj_false.implies_intr(pt_norm.rhs).on_prop(top_conv(replace_conv(pt_norm.symmetric())))
    return apply_theorem('negI', pt_neg_prop_implies_false).on_prop(rewr_conv('double_neg'))

def int_th_lemma_n_simplex(tms):
    """Two cases, 
        1) ... ⊢ false
        2) ... ⊢   
    """
    pts = tms[:-1]
    pt_norm_eq = [refl(pt.prop).on_rhs(try_conv(integer.int_norm_neg_compares()), try_conv(integer.int_simplex_form())).symmetric() for pt in pts]
    # solver = omega.OmegaHOL([pt.lhs for pt in pt_norm_eq])
    # pt_unsat = solver.solve()
    # pt_unsat = simplex.unsat_integer_simplex([pt.lhs for pt in pt_norm_eq])
    pt_unsat = simplex.IntegerSimplexMacro().get_proof_term(args=[pt.lhs for pt in pt_norm_eq])
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), pt_unsat.hyps, pt_unsat)
    pt_implies_false_initial = pt_implies_false
    for pt in pt_norm_eq:
       pt_implies_false_initial = pt_implies_false_initial.on_prop(top_conv(replace_conv(pt)))
    imps, _ = pt_implies_false_initial.prop.strip_implies()
    pt_final = pt_implies_false_initial
    for imp in imps:
        pt_final = pt_final.implies_elim(ProofTerm.assume(imp))
    return pt_final

def int_th_lemma_equation(args):
    """
    args[-1] is an equation, args[:-1] can derive the only possible value for variable
    occurs in args[-1].
    For example, ¬(y ≤ 3), y ≤ 4 ⊢ 0 = -4 + y
    The proving strategy is first get the conjunction of the two hyps, eliminate the negation,
    then get the conclusion of the possible value for the varibale, finally use conversion.
    1) ¬(y ≤ 3), y ≤ 4 ⊢ ¬(y ≤ 3) ∧ y ≤ 4
    2) ¬(y ≤ 3), y ≤ 4 ⊢ y ≥ 4 ∧ y ≤ 4
    3) ¬(y ≤ 3), y ≤ 4 ⊢ y = 4
    4) ⊢ 0 = -4 + y ⟷ y = 4
    5) ⊢ ¬(y ≤ 3), y ≤ 4 ⊢ 0 = -4 + y
    """
    # if len(args) != 3 or not args[-1].prop.is_equals():
    #     return None
    
    pt1 = apply_theorem('conjI', args[0], args[1])
    pt2 = pt1.on_prop(
        top_conv(rewr_conv('int_not_less_eq')),
        top_conv(rewr_conv('int_not_greater_eq')),
        top_conv(rewr_conv('int_less_to_leq')),
        top_conv(rewr_conv('int_gt_to_geq')),
        top_conv(integer.int_eval_conv()),
    )
    if pt2.prop.arg1.is_less_eq():
        pt2 = pt2.on_prop(rewr_conv('conj_comm'))

    pt3 = pt2.on_prop(rewr_conv('int_eq_geq_leq_conj', sym=True))
    
    pt4 = refl(args[-1]).on_rhs(rewr_conv('int_eq_move_left'), arg1_conv(integer.omega_simp_full_conv()))
    if pt4.rhs.arg1.is_plus() and integer.int_eval(pt4.rhs.arg1.arg1.arg1) == -1:
        pt4 = pt4.on_rhs(rewr_conv('int_pos_neg_eq_0'), arg1_conv(integer.omega_simp_full_conv()))
    elif pt4.rhs.arg1.is_times() and integer.int_eval(pt4.rhs.arg1.arg1) == -1:
        pt4 = pt4.on_rhs(rewr_conv('int_pos_neg_eq_0'), arg1_conv(integer.omega_simp_full_conv()))
    if pt4.rhs.arg1.arg.is_number():
        pt4 = pt4.on_rhs(rewr_conv('add_move_0_r'), arg_conv(integer.int_eval_conv()))
    pt5 = pt4.on_rhs(arg1_conv(rewr_conv('int_mul_1_l')))
    return pt5.symmetric().equal_elim(pt3)
    

def match_and_apply(tm, th_name):
    """Match tm with the theorem, if successful, instantiate it."""
    for name in th_name:
        try:
            pt = ProofTerm.theorem(name)
            inst = matcher.first_order_match(pt.prop, tm)
            return pt.substitution(inst)
        except:
            continue
    return None

def int_th_lemma(args):
    if len(args) == 1:
        th_name = ['int_ite_tau', 't036', 't037']
        res = match_and_apply(args[0], th_name)
        if res:
            return res
    if len(args) == 3 and args[-1].is_equals():
        res = int_th_lemma_equation(args)
        if res:
            return res
    if len(args) == 1:        
        return int_th_lemma_1_simplex(args[0])
    else:
        return int_th_lemma_n_simplex(args)


def th_lemma(args):
    """
    th-lemma: Generic proof for theory lemmas.
    """
    if len(args) == 1:
        th_name = ['int_ite_tau', 't036', 't037', 't099', 't100']
        res = match_and_apply(args[0], th_name)
        if res:
            return res
    # tms = [p.prop if isinstance(p, ProofTerm) else p for p in args]
    # Ts = set(sum([list(analyze_type(tm)) for tm in tms], []))
    # try:
    # Nonlinear or otherwise unreplayable th-lemma steps (e.g. over
    # s 0 * B with a free B) can be satisfiable for the simplex/omega
    # backends, which then fail; fall back to a gap instead of crashing.
    # The type sniffing also lives inside the try: non-arithmetic theory
    # lemmas (e.g. over fun_upd) do not have the assumed shape.
    concl = args[-1].prop if isinstance(args[-1], ProofTerm) else args[-1]
    try:
        t1 = args[0]
        if not isinstance(t1, ProofTerm):
            t2 = t1.arg1
            if t2.is_not():
                T = t2.arg.arg.get_type()
            else:
                T = t2.arg.get_type()
        else:
            if t1.prop.is_not():
                T = t1.prop.arg.arg.get_type()
            else:
                T = t1.prop.arg.get_type()
        if RealType == T:
            return real_th_lemma(args)
        elif IntType == T:
            return int_th_lemma(args)
        else:
            raise NotImplementedError
    except Exception:
        return Goal(concl).sorry()

def hypothesis(prop):
    """
    any proposition asserted by hyp rule must be explicitly discharged
    later on in the proof using lemma rule.

    In order to find them quickly when apply lemma rule, we should store them
    in a set.
    """
    hypos.add(prop)
    return ProofTerm.assume(prop)

def asserted(prop):
    """
    asserted rule is used to get assertions refutation proof.
    
    There is a special case: asserted true
    """
    if prop == true:
        return apply_theorem('trueI')
    else:
        return ProofTerm.assume(prop)


def nnf_pos(pts, concl, z3terms):
    """nnf-pos are used in following cases:

    a) creating a quantifier: q = q_new ⊢ forall (x T) q = forall (x T) q_new
    b) elimating implies: p -> q ⊢ ¬p ∨ q
    iff: p <--> q ⊢ (¬p ∨ q) ∧ (p ∨ ¬q)

    We need to check the concl is whether a quantifier formula.
    """
    if concl.lhs.is_forall():
        pt_forall = ProofTerm.reflexive(forall(concl.lhs.arg.var_T))
        return ProofTerm.combination(pt_forall, pts[0])
    elif concl.lhs.is_exists():
        pt_exists = ProofTerm.reflexive(exists(concl.lhs.arg.var_T))
        return ProofTerm.combination(pt_exists, pts[0])
    # Remaining cases (imp/iff elimination) are purely propositional.
    pt = rewrite_decision_net(concl)
    if pt is not None and pt.rule != 'sorry':
        return pt
    return Goal(concl).sorry()

def nnf_neg(pts, concl, z3terms):
    """nnf-neg: NNF transformation with flipped polarity.  The conclusion
    is propositional in most cases (handled by the decision net); the
    quantifier duality cases go through not_all / not_exists, which the
    net cannot prove (it treats quantifiers as atoms)."""
    if concl.is_equals():
        pt = rewrite_decision_net(concl)
        if pt is not None and pt.rule != 'sorry':
            return pt
        try:
            return compare_lhs_rhs(concl, [
                top_conv(try_conv(rewr_conv('not_all'))),
                top_conv(try_conv(rewr_conv('not_exists'))),
            ])
        except Exception:
            pass
    return Goal(concl).sorry()

def elim_unused(eq):
    """
    Given an formula ?X. p, p doesn't have X, return ?X.p ⟷ p.
    """
    lhs, rhs = eq.lhs, eq.rhs
    pt_lhs_assume = ProofTerm.assume(lhs)
    pt_rhs_assume = ProofTerm.assume(rhs)
    var = Var(lhs.arg.var_name, lhs.arg.var_T)
    # first prove ?X.p ⟶ p
    pt_lhs_elim_var = pt_lhs_assume.forall_elim(var).implies_intr(lhs)
    # second prove p ⟶ ?X.p
    pt_rhs_intro_var = pt_rhs_assume.forall_intr(var).implies_intr(rhs)
    return ProofTerm.equal_intr(pt_lhs_elim_var, pt_rhs_intro_var)

def trans(args):
    return functools.reduce(lambda x, y: x.transitive(y), args[:-1])


def convert_method(term, *args, subterms=None, assertions=[]):
    name = term.decl().name()
    if name == 'asserted' or name == 'true-axiom': # {P} ⊢ {P}; true-axiom concludes true
        return asserted(args[0])
    elif name == 'hypothesis':
        return hypothesis(args[0])
    elif name == 'and-elim':
        arg1, arg2 = args
        return and_elim(arg1, arg2)
    elif name == 'not-or-elim':
        arg1, arg2, = args
        return not_or_elim(arg1, arg2)
    elif name == 'monotonicity':
        *equals, concl = args
        if subterms[-1].arg(0).decl().name() == 'distinct':
            return distinct_monotonicity(equals, concl, subterms)
        try:
            return monotonicity(equals, concl)
        except Exception:
            # monotonicity's argument collection has known blind spots
            # (polyadic connectives, newly supported operators); a gap
            # beats aborting the whole reconstruction.
            return Goal(concl).sorry()
    elif name in ('trans', 'trans*'):
        return trans(args)
    elif name in ('mp', 'mp~'):
        arg1, arg2, _ = args
        return mp(arg1, arg2)
    elif name in ('rewrite', 'commutativity'):
        arg1, = args
        # return rewrite(arg1, subterms=subterms, assertions=assertions)
        return rewrite(arg1)
    elif name == 'unit-resolution':
        return unit_resolution(args[0], args[1:-1], args[-1], subterms)
    elif name == 'nnf-pos':
        return nnf_pos(args[:-1], args[-1], subterms)
    elif name == 'nnf-neg':
        return nnf_neg(args[:-1], args[-1], subterms)
    elif name == 'proof-bind':
        return args[0]
    elif name == 'quant-inst':
        arg1, = args
        return quant_inst(arg1)
    elif name == 'quant-intro':
        arg1, arg2, = args
        return quant_intro(arg1, arg2)
    elif name == 'iff-true':
        arg1, arg2, = args
        return iff_true(arg1, arg2)
    elif name == 'iff-false':
        arg1, arg2, = args
        return iff_false(arg1, arg2)
    elif name == 'symm':
        return args[0].symmetric()
    elif name == 'refl':
        return ProofTerm.reflexive(args[0])
    elif name == 'def-axiom':
        arg1, = args
        return def_axiom(arg1)
    elif name == 'intro-def':
        arg1, = args
        return intro_def(arg1)
    elif name == 'apply-def':
        arg1, arg2, = args
        return apply_def(arg2)
    elif name == 'lemma':
        arg1, arg2 = args
        return lemma(arg1, arg2, subterms)
    elif name == 'sk':
        arg1, = args
        return sk(arg1)
    elif name == 'th-lemma':
        return th_lemma(args)
    elif name == 'elim-unused':
        return elim_unused(args[0])
    else:
        raise NotImplementedError
    
local = dict()
redundant = []
hypos = set()
# store boolvars' true value in assertion which maybe implicitly used in rewrite rules.
assert_atom = set()

def delete_redundant(pt, redundant):
    """
    Because we introduce abbreviations for formula during def-intro,
    after reconstruction complete, we can delete these formulas use 
    theorem "(?t = ?t ⟹ False) ⟹ False"
    """
    new_pt = pt
    for r in redundant:
        new_pt = new_pt.implies_intr(r).forall_intr(r.lhs).forall_elim(r.rhs) \
             .implies_elim(ProofTerm.reflexive(r.rhs))
    
    return new_pt

def is_prop_fm(f):
    """Determine an assertion is whether a propositional formula."""
    if f.is_var() or f.is_const():
        return f.T == BoolType
    elif f.is_comb():
        head, args = f.head, f.args
        head_ty = head.get_type()
        head_range_ty = head_ty.strip_type()[-1]
        return head_range_ty == BoolType and all(is_prop_fm(arg) for arg in args)
    else:
        return False

atoms = dict()

def _occurs(t, u):
    """Whether term t occurs as a subterm of u."""
    if t == u:
        return True
    if u.is_comb():
        return _occurs(t, u.fun) or _occurs(t, u.arg)
    if u.is_abs():
        return _occurs(t, u.body)
    return False

def handle_assertion(ast):
    """
    Two cases:
    1) If the assertion is a conjunction, find all boolean variables or negative boolean variables
    in assertion, convert them to proofterm like "⊢ x ⟷ true" or "⊢ x ⟷ false"
    Note, the assertion conjunction may not have already been flatten, we need to preprocess it.

    This is a iterative process, every time we get an atom is true or false, we can also use it to get
    more information by rewriting the assertion, until no more new information we can get.
    2) If there are more than one assertion Γ_1, ..., Γ_n, we need to first get the set of proof terms:
                                Γ_1, ..., Γ_n ⊢ Γ_1 ∧ ... ∧ Γ_n
    then do the same things as above
    """
    global atoms

    def traverse(pt):
        """Note that we assume pt is right-associative"""
        while pt.prop.is_conj():
            lhs, rhs = pt.prop.arg1, pt.prop.arg
            if not lhs.is_conj():
                d[lhs] = apply_theorem('conjD1', pt)
            if not rhs.is_conj():
                d[rhs] = apply_theorem('conjD2', pt)
                break
            else:
                pt = apply_theorem('conjD2', pt)
    
    if len(ast) == 1:
        hol_ast = translate(ast[0])
        pt_ast = ProofTerm.assume(hol_ast).on_prop(proplogic.norm_full())
    else:
        hol_asts = [translate(a) for a in ast]
        pt_ast = functools.reduce(lambda x, y: apply_theorem('conjI', x, ProofTerm.assume(y)),\
                                hol_asts[1:], ProofTerm.assume(hol_asts[0])).on_prop(proplogic.norm_full())
    flag = True
    # Termination guard: the fixpoint loop can diverge when an atom
    # replacement keeps generating new successor nestings (e.g.
    # 0 = s 1 replaced, then s 1 = s (s 1), then s (s 1) = s (s (s 1)), ...).
    # Working goals converge in 1-2 rounds; 20 is a generous bound.
    rounds = 0
    while rounds < 20:
        rounds += 1
        if not pt_ast.prop.is_conj():
            break
        new_conv = []
        d = dict()
        traverse(pt_ast)
        for key, value in d.items():
            if key.is_var() and (key not in atoms or value != atoms[key]):
                atoms[key] = value.on_prop(rewr_conv('eq_true'))
                new_conv.append(atoms[key])
                flag = True
            elif key.is_not() and (key.arg not in atoms or value != atoms[key.arg]):
                atoms[key.arg] = value.on_prop(rewr_conv('eq_false'))    
                flag = True
                new_conv.append(atoms[key.arg])
            elif key.is_equals():
                lhs, rhs = key.lhs, key.rhs
                if lhs in (true, false):
                    atoms[rhs] = value.symmetric()
                    new_conv.append(atoms[rhs])
                elif rhs in (true, false):
                    atoms[lhs] = value
                    new_conv.append(atoms[lhs])
                elif not (lhs.head.is_const("IF") or rhs.head.is_const("IF")) \
                        and not _occurs(lhs, rhs):
                    # Replacing lhs by rhs must not be self-nesting (e.g.
                    # s 1 = s (s 1)): such a replacement diverges inside
                    # top_conv, rewriting its own output forever.
                    atoms[lhs] = value
                    new_conv.append(atoms[lhs])

        if flag:
            flag = False
            pt_ast = pt_ast.on_prop(
                *[top_conv(replace_conv(cv)) for cv in new_conv],
                bottom_conv(rewr_conv('not_true')),
                bottom_conv(rewr_conv('not_false')),
                bottom_conv(rewr_conv('if_true')),
                bottom_conv(rewr_conv('if_false')), 
                proplogic.norm_full(),)
                # bottom_conv(proplogic.norm_full()))
        else:
            break
    # normalize atoms key, for example, a pair in atoms maybe "x_9 ≤ x_3: x_9 ≤ x_3 ⟷ false",
    # we need to add a new pair: "x_3 + -1 * x_9 < 0: x_3 + -1 * x_9 < 0 ⟷ false"
    for key in list(atoms.keys()):
        if (key.is_equals() or key.is_compares()) and key.arg1.get_type() == RealType:
            norm_key = refl(key).on_rhs(
                bottom_conv(real_norm_comparison())
            )
            atoms[norm_key.rhs] = atoms[key].on_prop(top_conv(replace_conv(norm_key)))
            ori = atoms[key]
            if ori.rhs == false:
                pt_true = ori.on_prop(
                    rewr_conv('eq_false', sym=True),
                    try_conv(norm_neg_real_ineq_conv()),
                    real_norm_comparison(),
                    rewr_conv('eq_true')
                )
                atoms[pt_true.lhs] = pt_true

class eq_num_swap_conv(Conv):
    """z3 canonically moves numerals to the LEFT of an equation
    (0 = x * y) while library statements state them numeral-last, and
    may flip iff orientation (true ⟷ A).  Canonicalize to the z3
    orientation (via the symmetry schematic r001) so that refutation
    hypotheses match sequent pieces."""
    def get_proof_term(self, t):
        numeric = t.is_equals() and t.arg.is_number() and not t.arg1.is_number()
        boolean = t.is_equals() and (t.arg == true or t.arg == false) \
            and not (t.arg1 == true or t.arg1 == false)
        if numeric or boolean:
            th = ProofTerm.theorem('r001')
            inst = matcher.first_order_match(th.prop.lhs, t)
            return th.substitution(inst)
        raise ConvException('eq_num_swap_conv')

def _canon_conv():
    """Canonical form shared by the sequent pieces and the refutation
    hypotheses.  Stage order matters: boolean literal folding (r155/r156)
    exposes new comparisons, so comparison normalization must come after
    it; norm_full runs last.  The whole pipeline is applied twice to
    reach the fixpoint (a child rewrite can re-expose an earlier
    stage's redex)."""
    rounds = (bottom_conv(try_conv(rewr_conv('r155'))),
              bottom_conv(try_conv(rewr_conv('r156'))),
              bottom_conv(try_conv(eq_num_swap_conv())),
              bottom_conv(try_conv(rewr_conv('r153'))),
              bottom_conv(try_conv(rewr_conv('r154'))),
              bottom_conv(try_conv(integer.int_norm_neg_compares())),
              bottom_conv(try_conv(norm_neg_real_ineq_conv())),
              proplogic.norm_full())
    return rounds + rounds

def close_sequent(pt_false, As, C):
    """Turn the raw z3-refutation reconstruction ⊢ false -- whose
    hypotheses are the canonically normalized assertions A1..An and ¬C
    -- into a kernel proof of ⊢ A1 ⟹ … ⟹ An ⟹ C.  Returns pt_false
    unchanged when the hypotheses cannot be matched to the sequent."""
    if pt_false.prop != false or not pt_false.hyps:
        return pt_false
    convs = _canon_conv()

    def canon_pt(p):
        return refl(p).on_rhs(*convs)

    def canon(p):
        try:
            return canon_pt(p).rhs
        except Exception:
            return None

    pieces = list(As) + [Not(C)]
    hyps = list(pt_false.hyps)
    pc = [canon(p) for p in pieces]
    hc = [canon(h) for h in hyps]
    if any(c is None for c in pc + hc):
        return pt_false
    # bipartite match: each hypothesis to a unique sequent piece
    order = [None] * len(pieces)
    used = set()
    for j, c in enumerate(hc):
        for i, cp in enumerate(pc):
            if i not in used and cp == c:
                order[i] = hyps[j]
                used.add(i)
                break
    if not all(i is not None for i in order) or len(used) != len(pieces):
        return pt_false
    try:
        # Build the closure in the RAW (z3-normalized) forms: flip the
        # refuted conclusion, then discharge the assumptions outward.
        pt = pt_false.implies_intr(order[-1])
        pt = pt.on_prop(rewr_conv('imp_false_iff'), rewr_conv('double_neg'))
        for h in reversed(order[:-1]):
            pt = pt.implies_intr(h)
        # Bridge the raw statement to the original one through their
        # (equal) canonical forms.  A direct replace_conv rewrite is not
        # an option: canon -> original rules can be expanding.
        P = pt.prop
        st = C
        for a in reversed(As):
            st = Implies(a, st)
        pt_P = refl(P).on_rhs(*convs)
        pt_S = refl(st).on_rhs(*convs)
        if pt_P.rhs != pt_S.rhs:
            return pt_false
        iff = pt_P.transitive(pt_S.symmetric())          # ⊢ P ⟷ st
        return iff.equal_elim(pt)                        # ⊢ st
    except Exception:
        return pt_false

def proofrec(proof, bounds=deque(), trace=False, debug=False, assertions=None):
    """
    If trace is true, print reconstruction trace.
    """
    global conj_expr, disj_expr
    term, net = index_and_relation(proof)
    order = DepthFirstOrder(net)
    r = dict()
    conj_expr.clear()
    disj_expr.clear()
    assert_atom.clear()
    atoms.clear()
    redundant.clear()
    gaps = set()
    time1 = time.perf_counter()
    if assertions:
        # print("start process assertion!")
        handle_assertion(assertions)
    # with open('int_prf1.txt', 'a', encoding='utf-8') as f:
    #     f.seek(0)
    #     f.truncate()
    # print("done")
    for i in order:
        args = tuple(r[j] for j in net[i])
        # if trace:
        #     print('term['+str(i)+']', term[i])
        if z3.is_quantifier(term[i]) or term[i].decl().name() not in method:
            r[i] = translate(term[i], bounds=bounds, subterms=args)
        else:
            method_name = term[i].decl().name()
            subterms = [term[j] for j in net[i]]
            t1 = time.perf_counter()
            r[i] = convert_method(term[i], *args, subterms=subterms)
            t2 = time.perf_counter()
            # with open('int_prf1.txt', 'a', encoding='utf-8') as f:
            #     if r[i].rule == 'sorry' and method_name != 'def-axiom':
            #         gaps |= set(r[i].gaps)
            #         print('term['+str(i)+']', term[i], file=f)
            #         print('r['+str(i)+']', r[i], t2 - t1, file=f)
            #     if trace:
            #         print('r['+str(i)+']', term[i].decl().name(), t2 - t1, file=f)
    conclusion = delete_redundant(r[0], redundant)
    redundant.clear()
    time2 = time.perf_counter()
    # print("total time: ", time2 - time1)
    # rpt = ProofReport()
    # theory.verify(r[0].export(), rpt)
    # print(rpt)
    # print(r[0].export())
    return conclusion
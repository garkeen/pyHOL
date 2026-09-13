# Author: Bohua Zhan

from typing import Tuple, List, Union
import copy
import re
from lark import Lark, Transformer, v_args, exceptions

from syntax.lark_error import LarkParseError, translate_lark_error
import syntax
from kernel import type as hol_type
from kernel.type import Type, STVar, TVar, TConst, TFun, BoolType, TyInst
from syntax.numeral import NatType
from kernel.term import SVar, Var, Const, Comb, Abs, Bound, Term, Implies, Inst
from syntax.numeral import Binary
from syntax.logicops import Not, And, Or
from kernel import macro
from kernel import term
from kernel.thm import Thm
from kernel.proof import ProofItem
from kernel import theory
from kernel import extension
from syntax import infertype


class ParserException(Exception):
    """Exceptions during parsing."""
    def __init__(self, str):
        self.str = str


ParserError = LarkParseError


grammar = r"""
    ?type: typ_fun

    ?typ_fun: typ_prod ("=>"|"⇒") typ_fun -> funtype   // Function types
        | typ_prod

    ?typ_prod: typ_atom "×" typ_prod -> prodtype       // Product type, right assoc
        | typ_atom

    ?typ_atom: "'" CNAME ("::" CNAME)? -> tvar  // Type variable, optional class
        | "?'" CNAME  -> stvar             // Schematic type variable
        | CNAME -> type                   // Type constants
        | typ_atom CNAME -> typeapp       // Type constructor with one argument
        | "(" type ("," type)* ")" CNAME -> type  // Type constructor with multiple arguments
        | "(" type ")"                    // Parenthesis

    ?atom: CNAME -> vname                 // Constant, variable, or bound variable
        | "?" CNAME -> sname              // Schematic variable
        | INT -> number                   // Numbers
        | ("%"|"λ") CNAME "::" type ". " term -> abs     // Abstraction
        | ("%"|"λ") CNAME ". " term           -> abs_notype
        | ("!"|"∀") CNAME "::" type ". " term -> all     // Forall quantification
        | ("!"|"∀") CNAME ". " term           -> all_notype
        | ("?"|"∃") CNAME "::" type ". " term -> exists  // Exists quantification
        | ("?"|"∃") CNAME ". " term           -> exists_notype
        | ("?!"|"∃!") CNAME "::" type ". " term -> exists1   // Exists unique
        | ("?!"|"∃!") CNAME ". " term         -> exists1_notype
        | "THE" CNAME "::" type ". " term -> the         // THE operator
        | "THE" CNAME ". " term -> the_notype
        | "SOME" CNAME "::" type ". " term -> some         // SOME operator
        | "SOME" CNAME ". " term -> some_notype
        | "[]"                     -> literal_list  // Empty list
        | "[" term ("," term)* "]" -> literal_list  // List
        | ("{}"|"∅")               -> literal_set   // Empty set
        | "{" term ("," term)* "}" -> literal_set   // Set
        | "{" CNAME "::" type ". " term "}" -> collect_set
        | "{" CNAME ". " term "}"          -> collect_set_notype
        | "'" ("_"|LETTER|DIGIT) "'"  -> char
        | "\"" CNAME "\""               -> string
        | "if" term "then" term "else" term  -> if_expr // if expression
        | "(" term ")(" term ":=" term ("," term ":=" term)* ")"   -> fun_upd // function update
        | "{" term ".." term "}"   -> nat_interval
        | "(" term "," term ("," term)* ")" -> tuple   // Pair / tuple
        | "(" term ")"                    // Parenthesis
        | "(" term "::" type ")"   -> typed_term    // Term with specified type

    ?comb: comb atom | atom

    ?big_inter: ("INT"|"⋂") big_inter -> big_inter | comb         // Intersection: priority 90

    ?big_union: ("UN"|"⋃") big_union -> big_union | big_inter     // Union: priority 90

    ?uminus: "-" uminus -> uminus | big_union   // Unary minus: priority 80

    ?power: power "^" uminus | uminus   // Power: priority 81

    ?times_expr: times_expr "*" power -> times     // Multiplication: priority 70
        | times_expr "/" power -> real_divide      // Division: priority 70
        | times_expr "DIV" power -> nat_divide     // Division: priority 70
        | times_expr "MOD" power -> nat_modulus    // Modulus: priority 70
        | power

    ?inter: inter ("Int"|"∩") times_expr | times_expr     // Intersection: priority 70

    ?plus_expr: plus_expr "+" inter  -> plus     // Addition: priority 65
        | plus_expr "-" inter -> minus           // Subtraction: priority 65
        | inter                   

    ?append: plus_expr "@" append | plus_expr    // Append: priority 65

    ?cons: append "#" cons | append     // Cons: priority 65

    ?union: union ("Un"|"∪") cons | cons        // Union: priority 65

    ?comp_fun: union ("O"|"∘") comp_fun | union // Function composition: priority 60

    ?eq: eq "=" comp_fun | comp_fun             // Equality: priority 50

    ?mem: mem ("Mem"|"∈") mem | eq              // Membership: priority 50

    ?subset: subset ("Sub"|"⊆") subset | mem    // Subset: priority 50

    ?less_eq: less_eq ("<="|"≤") less_eq | subset  // Less-equal: priority 50

    ?less: less "<" less | less_eq      // Less: priority 50

    ?greater_eq: greater_eq (">="|"≥") greater_eq | less   // greater-equal: priority 50

    ?greater: greater ">" greater | greater_eq     // greater: priority 50

    ?neg: ("~"|"¬") neg -> neg | greater   // Negation: priority 40

    ?conj: neg ("&"|"∧") conj | neg     // Conjunction: priority 35

    ?disj: conj ("|"|"∨") disj | conj   // Disjunction: priority 30

    ?iff: disj ("<-->"|"⟷") iff | disj // Iff: priority 25

    ?imp: iff ("-->"|"⟶") imp | iff    // Implies: priority 20

    ?term: imp

    thm: ("|-"|"⊢") term
        | term ("," term)* ("|-"|"⊢") term

    term_pair: CNAME ":" term

    inst: "{}"
        | "{" term_pair ("," term_pair)* "}"

    type_pair: CNAME ":" type

    tyinst: "{}"
        | "{" type_pair ("," type_pair)* "}"

    var_decl: CNAME "::" type  // variable declaration

    ind_constr: CNAME ("(" CNAME "::" type ")")*  // constructor for inductive types

    named_thm: CNAME ":" term | term  // named theorem

    term_list: term ("," term)*   // list of terms

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.LETTER
    %import common.DIGIT

    %ignore WS
"""


@v_args(inline=True)
class HOLTransformer(Transformer):
    def __init__(self, ctxt=None):
        # Pure-data name->type tables (interface inversion, audit §9.5):
        # the parser does not read core.context's global singleton;
        # callers above syntax pass their context explicitly.
        self.ctxt = ctxt if ctxt is not None else infertype.EMPTY_CTXT

    def tvar(self, *args):
        # `'a::C` carries a class annotation.  The type is just `'a`: the
        # class is sugar for a premise on the statement that mentions it
        # (see CLASSES / with_class_premises below), so the type level is
        # free of constraints.
        return TVar(str(args[0]))

    def stvar(self, s):
        return STVar(str(s))

    def type(self, *args):
        # A type written in a term (the `::` annotation) goes through the
        # same abbreviation expansion as parser.parse_type, so an
        # abbreviated type name never reaches the kernel.
        return expand_type_abbrevs(TConst(str(args[-1]), *args[:-1]))

    def funtype(self, t1, t2):
        return TFun(t1, t2)

    def typeapp(self, T, name):
        return expand_type_abbrevs(TConst(str(name), T))

    def prodtype(self, t1, t2):
        return TConst('prod', t1, t2)

    def tuple(self, *args):
        # Right-nested pairs: (a, b, c) is Pair a (Pair b c).  Types are
        # left to infertype, as with the other term transformers.
        res = args[-1]
        for a in reversed(args[:-1]):
            res = Const('Pair', None)(a, res)
        return res

    def sname(self, s):
        s = str(s)
        return SVar(s, None)

    def vname(self, s):
        s = str(s)
        if theory.thy.has_term_sig(s) or s in self.ctxt.defs:
            # s is the name of a constant in the theory
            return Const(s, None)
        else:
            # s not found, either bound or free variable
            return Var(s, None)

    def typed_term(self, t, T):
        if t.is_comb('of_nat', 1) and t.arg.is_binary() and t.arg.dest_binary() >= 2:
            t.fun.T = TFun(NatType, T)
        else:
            t.T = T
        return t

    def number(self, n):
        if int(n) == 0:
            return Const("zero", None)
        elif int(n) == 1:
            return Const("one", None)
        else:
            return Const("of_nat", None)(Binary(int(n)))

    def literal_list(self, *args):
        from syntax import list_tools as list
        return list.mk_literal_list(args, None)

    def char(self, c):
        from syntax import string_tools as string
        return string.mk_char(str(c))

    def string(self, s):
        from syntax import string_tools as string
        return string.mk_string(str(s))

    def if_expr(self, P, x, y):
        return Const("IF", None)(P, x, y)

    def fun_upd(self, *args):
        def helper(*args):
            if len(args) == 3:
                f, a, b = args
                return Const("fun_upd", None)(f, a, b)
            elif len(args) > 3:
                return helper(helper(*args[:3]), *args[3:])
            else:
                raise TypeError
        return helper(*args)

    def comb(self, fun, arg):
        return Comb(fun, arg)

    def abs(self, var_name, T, body):
        return Abs(str(var_name), T, body.abstract_over(Var(var_name, None)))

    def abs_notype(self, var_name, body):
        return Abs(str(var_name), None, body.abstract_over(Var(var_name, None)))

    def all(self, var_name, T, body):
        all_t = Const("all", None)
        return all_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def all_notype(self, var_name, body):
        all_t = Const("all", None)
        return all_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def exists(self, var_name, T, body):
        exists_t = Const("exists", None)
        return exists_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def exists_notype(self, var_name, body):
        exists_t = Const("exists", None)
        return exists_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def exists1(self, var_name, T, body):
        exists1_t = Const("exists1", None)
        return exists1_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def exists1_notype(self, var_name, body):
        exists1_t = Const("exists1", None)
        return exists1_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def the(self, var_name, T, body):
        the_t = Const("The", None)
        return the_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def the_notype(self, var_name, body):
        the_t = Const("The", None)
        return the_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def some(self, var_name, T, body):
        some_t = Const("Some", None)
        return some_t(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def some_notype(self, var_name, body):
        some_t = Const("Some", None)
        return some_t(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def collect_set(self, var_name, T, body):
        from syntax import set_tools as set
        return set.collect(T)(Abs(str(var_name), T, body.abstract_over(Var(var_name, None))))

    def collect_set_notype(self, var_name, body):
        from syntax import set_tools as set
        return set.collect(None)(Abs(str(var_name), None, body.abstract_over(Var(var_name, None))))

    def power(self, lhs, rhs):
        return Const("power", None)(lhs, rhs)

    def times(self, lhs, rhs):
        return Const("times", None)(lhs, rhs)

    def real_divide(self, lhs, rhs):
        return Const("real_divide", None)(lhs, rhs)

    def nat_divide(self, lhs, rhs):
        return Const("nat_divide", None)(lhs, rhs)

    def nat_modulus(self, lhs, rhs):
        return Const("nat_modulus", None)(lhs, rhs)

    def plus(self, lhs, rhs):
        return Const("plus", None)(lhs, rhs)

    def minus(self, lhs, rhs):
        return Const("minus", None)(lhs, rhs)

    def uminus(self, x):
        return Const("uminus", None)(x)

    def less_eq(self, lhs, rhs):
        return Const("less_eq", None)(lhs, rhs)

    def less(self, lhs, rhs):
        return Const("less", None)(lhs, rhs)

    def greater_eq(self, lhs, rhs):
        return Const("greater_eq", None)(lhs, rhs)

    def greater(self, lhs, rhs):
        return Const("greater", None)(lhs, rhs)

    def append(self, lhs, rhs):
        return Const("append", None)(lhs, rhs)

    def cons(self, lhs, rhs):
        return Const("cons", None)(lhs, rhs)

    def eq(self, lhs, rhs):
        return Const("equals", None)(lhs, rhs)

    def neg(self, t):
        return Not(t)

    def conj(self, s, t):
        return And(s, t)

    def disj(self, s, t):
        return Or(s, t)

    def imp(self, s, t):
        return Implies(s, t)

    def iff(self, s, t):
        return Const("equals", None)(s, t)

    def literal_set(self, *args):
        from syntax import set_tools as set
        return set.mk_literal_set(args, None)

    def mem(self, x, A):
        return Const("member", None)(x, A)

    def subset(self, A, B):
        return Const("subset", None)(A, B)

    def inter(self, A, B):
        return Const("inter", None)(A, B)

    def union(self, A, B):
        return Const("union", None)(A, B)

    def big_inter(self, t):
        return Const("Inter", None)(t)

    def big_union(self, t):
        return Const("Union", None)(t)

    def comp_fun(self, f, g):
        return Const("comp_fun", None)(f, g)

    def nat_interval(self, m, n):
        from kernel.type import TFun
        # `{m..n}` is notation for the library constant `nat_interval`,
        # whose third argument is a set, i.e. a predicate (see
        # syntax/set_tools.setT).
        return Const("nat_interval",
                     TFun(NatType, NatType,
                          TFun(NatType, BoolType)))(m, n)

    def thm(self, *args):
        # Script front door: the user states a goal (assums ..., concl).
        # The statement is minted through the kernel's sorry constructor
        # (syntax layer is below tactic; same mint, kernel channel).
        return Thm.sorry(args[-1], tuple(args[:-1]))

    def term_pair(self, name, T):
        return (str(name), T)

    def type_pair(self, name, T):
        return (str(name), T)

    def inst(self, *args):
        return dict(args)

    def tyinst(self, *args):
        return dict(args)

    def ind_constr(self, *args):
        constrs = {}
        constrs['name'] = str(args[0])
        constrs['args'] = []
        constrs['type'] = []
        for id in range(1, len(args), 2):
            constrs['args'].append(str(args[id]))
            constrs['type'].append(args[id+1])
        return constrs

    def var_decl(self, name, T):
        return (str(name), T)

    def named_thm(self, *args):
        return tuple(args)

    def term_list(self, *args):
        return list(args)


# One shared transformer: the Lark grammar is compiled once per start
# symbol (module-level, below); switching context only swaps the
# transformer's ctxt reference (O(1)), never rebuilds a parser.
_shared_transformer = HOLTransformer()

def get_parser_for(start):
    return Lark(grammar, start=start, parser="lalr",
                transformer=_shared_transformer)

type_parser = get_parser_for("type")
term_parser = get_parser_for("term")
thm_parser = get_parser_for("thm")
inst_parser = get_parser_for("inst")
tyinst_parser = get_parser_for("tyinst")
named_thm_parser = get_parser_for("named_thm")
var_decl_parser = get_parser_for("var_decl")
ind_constr_parser = get_parser_for("ind_constr")
term_list_parser = get_parser_for("term_list")


def _bind_ctxt(ctxt):
    """Point the shared transformer at ctxt for the next parse."""
    _shared_transformer.ctxt = ctxt if ctxt is not None else infertype.EMPTY_CTXT

# ---------------------------------------------------------------------------
# Type abbreviations (type synonyms).
#
# The table is scoped to the currently loaded theory: `typeabbrev` items
# register their definition here, and core.basic clears it whenever the
# theory is reset.  parse_type expands abbreviations, so the kernel never
# sees an abbreviated type constant.
# ---------------------------------------------------------------------------

type_abbrevs = {}


def add_type_abbrev(name, args, body):
    """Register a type abbreviation.

    name -- name of the abbreviated type constant.
    args -- parameter type variable names.
    body -- definition, with any earlier abbreviations already expanded.

    """
    type_abbrevs[name] = {'args': list(args), 'body': body}


def clear_type_abbrevs():
    """Drop all abbreviations.  Called when the theory is reset."""
    type_abbrevs.clear()


# ---------------------------------------------------------------------------
# Type-class sugar: `'a::C` annotations
# ---------------------------------------------------------------------------
#
# A class annotation on a *type variable* is sugar for a premise.  The type
# stays `'a`; a statement item that carries the annotation gains the class
# predicate applied to the class operation(s) as an assumption:
#
#     theorem foo
#       fixes x :: 'a::linorder
#       prop x <= x
#
# is proved, stored and displayed as
#
#     fixes x :: 'a
#     prop linorder (less_eq::'a ⇒ 'a ⇒ bool) ⟶ x <= x
#
# The premise is discharged at the *use* site by the class's instance theorem
# (e.g. `nat_linorder`, proved in library/order.pyhol), so nothing below the
# item layer -- proof replay, the checked channels, the kernel -- has to know
# about classes.  Definitions (`def`/`fun`/`inductive`) keep the annotation as
# a marker only: their equations are uniform in the instance (the operation is
# the generic, overloaded constant), so nothing is injected for them.
#
# CLASSES is the syntax-side registry: class name -> (predicate name, ops),
# where an op is (constant name, type template) and %s in the template stands
# for the annotated type variable.  The predicate itself is library content.
CLASSES = {
    'preorder': ('preorder', (('less_eq', "'%s ⇒ '%s ⇒ bool"),)),
    'order': ('order', (('less_eq', "'%s ⇒ '%s ⇒ bool"),)),
    'linorder': ('linorder', (('less_eq', "'%s ⇒ '%s ⇒ bool"),)),
}


def add_class(name, predicate, ops):
    """Register a class for the `'a::NAME` sugar.

    name -- class name as written after `::`.
    predicate -- library predicate that the class stands for.
    ops -- the class's operations, as (constant name, type template) pairs;
           `%s` in the template is replaced by the annotated type variable.

    """
    CLASSES[name] = (predicate, tuple(ops))


_class_annot_re = re.compile(r"'([A-Za-z_][A-Za-z0-9_']*)::([A-Za-z_][A-Za-z0-9_']*)")


def class_constraints(*texts, strict=True):
    """Collect `(var, class)` annotations from type texts, in first-seen order.

    strict -- also reject a `::` annotation that does not sit on a type
    variable (e.g. `nat::linorder`).  Type texts use strict=True; a prop text
    is scanned leniently, since it may legitimately contain term-level type
    annotations such as `(less_eq :: nat ⇒ nat ⇒ bool)`.

    Raises ParserError for an unknown class (and, when strict, for a `::`
    annotation that is not on a type variable).

    """
    found = []
    for text in texts:
        if not text or '::' not in text:
            continue
        if strict and '::' in _class_annot_re.sub('', text):
            raise ParserError(
                "class annotation must be on a type variable ('a::C): %s" % text)
        for m in _class_annot_re.finditer(text):
            var, cls = m.group(1), m.group(2)
            if cls not in CLASSES:
                raise ParserError(
                    "class %r is not registered (known: %s) in %s"
                    % (cls, ', '.join(sorted(CLASSES)), text))
            if (var, cls) not in found:
                found.append((var, cls))
    return found


def class_premises(constraints):
    """Premise texts for `(var, class)` constraints, in the given order."""
    res = []
    for var, cls in constraints:
        predicate, ops = CLASSES[cls]
        for op_name, op_ty in ops:
            res.append('%s (%s::%s)' % (predicate, op_name, op_ty % (var, var)))
    return res


def with_class_premises(prop_text, *type_texts):
    """Prepend the class premises implied by the annotations in `type_texts`.

    Used by the item layer for statements (theorem/axiom): the annotations in
    the fixes' types and in the prop itself become premises of the prop.  The
    fixes' types are checked strictly; the prop is only scanned for
    annotations (its `::` also appears in term-level type annotations).
    Returns prop_text unchanged when there is no annotation.

    """
    constraints = class_constraints(*type_texts)
    prems = class_premises(class_constraints(prop_text, strict=False))
    prems = class_premises(constraints) + prems
    if not prems:
        return prop_text
    return ' ⟶ '.join(prems + [prop_text])


def _subst_type(T, subst):
    """Substitute type variables by name (both TVar and STVar), so that an
    abbreviation's parameters can be replaced by the actual arguments."""
    if T.is_stvar() or T.is_tvar():
        return subst.get(T.name, T)
    if T.is_tconst():
        return TConst(T.name, *(_subst_type(arg, subst) for arg in T.args))
    return T


def expand_type_abbrevs(T):
    """Recursively expand type abbreviations in T."""
    if not T.is_tconst():
        return T
    args = [expand_type_abbrevs(arg) for arg in T.args]
    ab = type_abbrevs.get(T.name)
    if ab is not None and len(args) == len(ab['args']):
        return _subst_type(ab['body'], dict(zip(ab['args'], args)))
    return TConst(T.name, *args)


def parse_type(s: str, *, check_type: bool = True) -> Type:
    """Parse a type, expanding type abbreviations."""
    try:
        T = type_parser.parse(s)
    except exceptions.UnexpectedToken as e:
        raise translate_lark_error(type_parser, s, e)
    T = expand_type_abbrevs(T)
    if check_type:
        theory.thy.check_type(T)
    return T

def parse_term(s: Union[str, List[str]], *, ctxt=None) -> Term:
    """Parse a term.

    ctxt is a pure-data object with svars, vars, defs (name->type
    tables) consulted during parsing and type inference; callers above
    syntax pass their context explicitly (interface inversion,
    audit §9.5).
    """
    # Permit parsing a list of strings by concatenating them.
    if isinstance(s, list):
        s = " ".join(s)
    _bind_ctxt(ctxt)
    try:
        t = term_parser.parse(s)
        return infertype.type_infer(t, ctxt=ctxt)
    except exceptions.UnexpectedToken as e:
        raise translate_lark_error(term_parser, s, e)
    except exceptions.UnexpectedCharacters as e:
        raise translate_lark_error(term_parser, s, e)
    except exceptions.UnexpectedEOF as e:
        raise translate_lark_error(term_parser, s, e)
    except infertype.TypeInferenceException as e:
        raise ParserError(e.err)
    except term.TermException as e:
        raise ParserError(str(e))

def parse_thm(s: str, *, ctxt=None) -> Thm:
    """Parse a theorem (sequent)."""
    _bind_ctxt(ctxt)
    try:
        th = thm_parser.parse(s)
        th.hyps = tuple(infertype.type_infer(hyp, ctxt=ctxt) for hyp in th.hyps)
        th.prop = infertype.type_infer(th.prop, ctxt=ctxt)
    except exceptions.UnexpectedToken as e:
        raise translate_lark_error(thm_parser, s, e)
    except exceptions.UnexpectedCharacters as e:
        raise translate_lark_error(thm_parser, s, e)
    except exceptions.UnexpectedEOF as e:
        raise translate_lark_error(thm_parser, s, e)
    except infertype.TypeInferenceException as e:
        raise ParserError(e.err)
    return th

def parse_inst(s, *, ctxt=None):
    """Parse a term instantiation."""
    _bind_ctxt(ctxt)
    inst = inst_parser.parse(s)
    for k in inst:
        inst[k] = infertype.type_infer(inst[k], ctxt=ctxt)
    return Inst(inst)

def parse_tyinst(s):
    """Parse a type instantiation."""
    tyinst = tyinst_parser.parse(s)
    return TyInst(tyinst)

def parse_named_thm(s, *, ctxt=None):
    """Parse a named theorem."""
    _bind_ctxt(ctxt)
    res = named_thm_parser.parse(s)
    if len(res) == 1:
        return (None, infertype.type_infer(res[0], ctxt=ctxt))
    else:
        return (str(res[0]), infertype.type_infer(res[1], ctxt=ctxt))

def parse_ind_constr(s):
    """Parse a constructor for an inductive type definition."""
    return ind_constr_parser.parse(s)

def parse_var_decl(s):
    """Parse a variable declaration."""
    return var_decl_parser.parse(s)

def parse_term_list(s, *, ctxt=None):
    """Parse a list of terms."""
    if s == "":
        return []

    _bind_ctxt(ctxt)
    ts = term_list_parser.parse(s)
    for i in range(len(ts)):
        ts[i] = infertype.type_infer(ts[i], ctxt=ctxt)
    return ts

def parse_args(sig, args, *, ctxt=None):
    """Parse the argument according to the signature."""
    try:
        if sig == None:
            assert args == "", "rule expects no argument."
            return None
        elif sig == str:
            return args
        elif sig == Term:
            return parse_term(args, ctxt=ctxt)
        elif sig == Inst:
            return parse_inst(args, ctxt=ctxt)
        elif sig == TyInst:
            return parse_tyinst(args)
        elif sig == Tuple[str, Type]:
            s1, s2 = args.split(",", 1)
            return s1, parse_type(s2)
        elif sig == Tuple[str, Term]:
            s1, s2 = args.split(",", 1)
            return s1, parse_term(s2, ctxt=ctxt)
        elif sig == Tuple[str, Inst]:
            s1, s2 = args.split(",", 1)
            inst = parse_inst(s2, ctxt=ctxt)
            return s1, inst
        elif sig == List[Term]:
            return parse_term_list(args, ctxt=ctxt)
        else:
            raise TypeError
    except exceptions.UnexpectedToken as e:
        raise ParserException("When parsing %s, unexpected token %r at column %s.\n"
                              % (args, e.token, e.column))

def parse_proof_rule(data, *, ctxt=None):
    """Parse a proof rule.

    data is a dictionary containing id, rule, args, prevs, and th.
    The result is a ProofItem object.

    This need to be written by hand because different proof rules
    require different parsing of the arguments.

    """
    id, rule = data['id'], data['rule']

    if rule == "":
        return ProofItem(id, "")

    if data['th'] == "":
        th = None
    else:
        th = parse_thm(data['th'], ctxt=ctxt)


    sig = theory.thy.get_proof_rule_sig(rule)
    args = parse_args(sig, data['args'], ctxt=ctxt)
    return ProofItem(id, rule, args=args, prevs=data['prevs'], th=th)


hol_type.type_parser = parse_type
term.term_parser = parse_term  # rebound to context-aware parsing below

# The kernel's Term(s-from-string) constructor goes through this hook.
# Binding it to context-aware parsing would make syntax depend on
# core, so the rebinding lives in core/context.py instead
# (core already depends on syntax). Do NOT rebind here.

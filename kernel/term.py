# Author: Bohua Zhan

from __future__ import annotations
from collections import UserDict
from copy import copy
from typing import List

from kernel.type import Type, TFun, BoolType, TyInst, TypeMatchException
from util import typecheck
from util import name


class TermException(Exception):
    """Indicates error in processing terms."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class TypeCheckException(Exception):
    """Indicates error in type checking of terms."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class Inst(UserDict):
    """Instantiation of schematic variables."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.tyinst = TyInst()
        self.var_inst = dict()
        self.abs_name_inst = dict()

    def __str__(self):
        res = ''
        if self.tyinst:
            res = str(self.tyinst) + ', '
        res += ', '.join('?%s := %s' % (nm, t) for nm, t in self.items())
        res += ', '.join('%s := %s' % (nm, t) for nm, t in self.var_inst.items())
        res += ', '.join('%s -> %s' % (nm, nm2) for nm, nm2 in self.abs_name_inst.items())
        return res

    def __copy__(self):
        res = Inst(self)
        res.tyinst = copy(self.tyinst)
        res.var_inst = copy(self.var_inst)
        res.abs_name_inst = copy(self.abs_name_inst)
        return res

    def __bool__(self):
        return bool(self.tyinst) or bool(self.keys()) or bool(self.var_inst) or bool(self.abs_name_inst)


"""Default parser for terms. If None, Term() is unable to parse string."""
term_parser = None

"""Default printer for terms. If None, Term.print_basic is used."""
term_printer = None


class Term:
    """Represents a term in higher-order logic.
    
    There are six term constructors:
    
    SVar(name, T): schematic variable with given name and type.

    Var(name, T): variable with given name and type.

    Const(name, T): constant with given name and type.

    Comb(f, a): the function f applied to a, written as f a (or f(a)).

    Abs(x, T, body): abstraction. x is the suggested name of the bound
    variable, and T is the type of the bound variable. body is the body of
    the abstraction. This is written as %x::T. body, where the type T is
    usually omitted.

    Bound(n): bound variable with de Bruijn index n.

    Examples:

    Var("a", nat) is a variable of type nat.

    Const("zero", nat) is constant zero.

    Comb(Const("Suc", nat => nat), Const("zero", nat)) is the successor function
    applied to zero, or the constant 1.

    Comb(Comb(Const("plus", nat => nat => nat), Var("a", nat)), Var("b", nat))
    is the term a + b.
    
    Bound variables in the lambda calculus are represented using de Bruijn
    indices, where Bound(i) represents the bound variable that is i
    abstractions away.

    Examples:
    
    Abs("x", T, P(Bound(0))) is %x::T. P x.

    Abs("x", S, Abs("y", T, Q(Bound(1), Bound(0)))) is %x::S. %y::T. Q x y.

    """
    # ty values for distinguishing between Term objects.
    SVAR, VAR, CONST, COMB, ABS, BOUND = range(6)

    def __init__(self, arg):
        if not isinstance(arg, Term):
            if term_parser is not None:
                t = term_parser(arg)
            else:
                raise TermException('Term: parser not found.')
        else:
            t = arg
        
        # Now copy the content of t onto self
        self.__dict__.update(t.__dict__)

    def is_svar(self) -> bool:
        return self.ty == Term.SVAR

    def is_var(self) -> bool:
        """Return whether the term is a variable."""
        return self.ty == Term.VAR

    def is_const(self, name=None) -> bool:
        """Return whether the term is a constant.

        name : optional str
            If given, test whether the term has that name.

        """
        if self.ty != Term.CONST:
            return False
        else:
            return name is None or self.name == name

    def is_comb(self, name=None, nargs=None) -> bool:
        """Return whether the term is a combination.

        name : optional str
            If given, test whether the head of the term has that name.

        nargs : optional int
            Must be given together with name. If given, test whether the
            head is applied to exactly that many arguments.

        """
        if self.ty != Term.COMB:
            return False
        if name is not None:
            t = self.fun
            count = 1
            while t.ty == Term.COMB:
                t = t.fun
                count += 1
            return t.ty == Term.CONST and t.name == name and (nargs is None or count == nargs)
        else:
            return True

    def is_abs(self) -> bool:
        """Return whether the term is an abstraction."""
        return self.ty == Term.ABS

    def is_bound(self) -> bool:
        """Return whether the term is a bound variable."""
        return self.ty == Term.BOUND

    def print_basic(self) -> str:
        """Basic printing function for terms. Note we do not yet handle collision
        in lambda terms.

        """
        def helper(t: Term, bd_vars):
            """bd_vars is the list of names of bound variables."""
            if t.is_svar():
                return "?" + t.name
            elif t.is_var() or t.is_const():
                return t.name
            elif t.is_comb():
                # a b c associates to the left. So parenthesis is needed to express
                # a (b c). Parenthesis is also needed for lambda terms.
                if t.fun.is_abs():
                    str_fun = "(" + helper(t.fun, bd_vars) + ")"
                else:
                    str_fun = helper(t.fun, bd_vars)
                if t.arg.is_comb() or t.arg.is_abs():
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                else:
                    str_arg = helper(t.arg, bd_vars)
                return str_fun + " " + str_arg
            elif t.is_abs():
                body_repr = helper(t.body, [t.var_name] + bd_vars)
                return "%" + t.var_name + ". " + body_repr
            elif t.is_bound():
                if t.n >= len(bd_vars):
                    return ":B" + str(t.n)
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError

        return helper(self, [])

    def __str__(self):
        if term_printer is None:
            return self.print_basic()
        else:
            return term_printer(self)

    def __repr__(self):
        if self.is_svar():
            return "SVar(%s, %s)" % (self.name, self.T)
        elif self.is_var():
            return "Var(%s, %s)" % (self.name, self.T)
        elif self.is_const():
            return "Const(%s, %s)" % (self.name, self.T)
        elif self.is_comb():
            return "Comb(%s, %s)" % (repr(self.fun), repr(self.arg))
        elif self.is_abs():
            return "Abs(%s, %s, %s)" % (self.var_name, self.var_T, repr(self.body))
        elif self.is_bound():
            return "Bound(%s)" % self.n
        else:
            raise TypeError

    def __hash__(self):
        if not hasattr(self, "_hash_val"):
            if self.is_svar():
                self._hash_val = hash(("SVAR", self.name, self.T))
            elif self.is_var():
                self._hash_val = hash(("VAR", self.name, self.T))
            elif self.is_const():
                self._hash_val = hash(("CONST", self.name, self.T))
            elif self.is_comb():
                self._hash_val = hash(("COMB", self.fun, self.arg))
            elif self.is_abs():
                self._hash_val = hash(("ABS", self.var_T, self.body))
            elif self.is_bound():
                self._hash_val = hash(("BOUND", self.n))
            else:
                raise TypeError
        return self._hash_val

    def __eq__(self, other):
        """Equality on terms is defined by alpha-conversion. This ignores
        suggested names in lambda terms.

        """
        assert isinstance(other, Term), "cannot compare Term with %s" % str(type(other))

        if self._id == other._id:
            return True

        if self.ty != other.ty:
            return False
        elif self.ty == Term.SVAR or self.ty == Term.VAR or self.ty == Term.CONST:
            return self.name == other.name and self.T == other.T
        elif self.ty == Term.COMB:
            return self.fun == other.fun and self.arg == other.arg
        elif self.ty == Term.ABS:
            # Note the suggested variable name is not important
            return self.var_T == other.var_T and self.body == other.body
        elif self.ty == Term.BOUND:
            return self.n == other.n
        else:
            raise TypeError

    def __copy__(self):
        """Returns a copy of self. Types are shared, the rest of
        the information are copied.

        """
        if self.is_svar():
            return SVar(self.name, self.T)
        elif self.is_var():
            return Var(self.name, self.T)
        elif self.is_const():
            return Const(self.name, self.T)
        elif self.is_comb():
            return Comb(copy(self.fun), copy(self.arg))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, copy(self.body))
        elif self.is_bound():
            return Bound(self.n)
        else:
            raise TypeError

    def __call__(self, *args):
        """Apply self (as a function) to a list of arguments."""
        res = self
        for arg in args:
            res = Comb(res, arg)
        return res

    def size(self) -> int:
        """Return the size of the term."""
        if self.is_svar() or self.is_var() or self.is_const():
            return 1
        elif self.is_comb():
            return 1 + self.fun.size() + self.arg.size()
        elif self.is_abs():
            return 1 + self.body.size()
        elif self.is_bound():
            return 1
        else:
            raise TypeError

    def get_absBindVar(self) -> list:
        res = []
        def f(t:Term):
            if t.is_abs():
                res.append(t.var_name)
                return
            elif t.is_comb():
                f(t.fun)
                f(t.arg)
            else:
                return
        f(self)
        return res





    def get_type(self) -> Type:
        """Returns type of the term with minimal type checking."""
        def rec(t: Term, bd_vars):
            """Helper function. bd_vars is the list of types of the bound variables."""
            if t.is_svar() or t.is_var() or t.is_const():
                return t.T
            elif t.is_comb():
                type_fun = rec(t.fun, bd_vars)
                if type_fun.is_fun():
                    return type_fun.range_type()
                else:
                    raise TypeCheckException('function type expected in application')
            elif t.is_abs():
                return TFun(t.var_T, rec(t.body, [t.var_T] + bd_vars))
            elif t.is_bound():
                if t.n >= len(bd_vars):
                    raise TypeCheckException("open term")
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError

        return rec(self, [])

    def is_open(self) -> bool:
        """Whether t is an open term."""
        def rec(t, n):
            if t.is_svar() or t.is_var() or t.is_const():
                return False
            elif t.is_comb():
                return rec(t.fun, n) or rec(t.arg, n)
            elif t.is_abs():
                return rec(t.body, n+1)
            elif t.is_bound():
                return t.n >= n
            else:
                raise TypeError
        return rec(self, 0)

    def subst_type(self, tyinst=None, **kwargs) -> Term:
        """Perform substitution on type variables.
        
        Parameters
        ==========
        tyinst : TyInst
            Type instantiation to be substituted.

        """
        if tyinst is None:
            tyinst = TyInst(**kwargs)
        if self.is_svar():
            return SVar(self.name, self.T.subst(tyinst))
        elif self.is_var():
            return Var(self.name, self.T.subst(tyinst))
        elif self.is_const():
            return Const(self.name, self.T.subst(tyinst))
        elif self.is_comb():
            return Comb(self.fun.subst_type(tyinst), self.arg.subst_type(tyinst))
        elif self.is_abs():
            return Abs(self.var_name, self.var_T.subst(tyinst), self.body.subst_type(tyinst))
        elif self.is_bound():
            return self
        else:
            raise TypeError

    def subst_type_inplace(self, tyinst) -> Term:
        """Perform substitution on type variables."""
        typecheck.checkinstance('subst_type_inplace', tyinst, TyInst)
        if hasattr(self, "_hash_val"):
            del self._hash_val
        if self.is_svar() or self.is_var() or self.is_const():
            self.T = self.T.subst(tyinst)
        elif self.is_comb():
            self.fun.subst_type_inplace(tyinst)
            self.arg.subst_type_inplace(tyinst)
        elif self.is_abs():
            self.var_T = self.var_T.subst(tyinst)
            self.body.subst_type_inplace(tyinst)
        elif self.is_bound():
            pass
        else:
            raise TypeError

    def subst(self, inst=None, **kwargs) -> Term:
        """Perform substitution on term variables.

        Parameters
        ==========
        inst : Inst
            Instantiation to be substituted.

        """
        if inst is None:
            inst = Inst(**kwargs)

        # First match type variables.
        svars = self.get_svars()
        for v in svars:
            if v.name in inst:
                try:
                    inst_T = inst[v.name].get_type()
                    v.T.match_incr(inst_T, inst.tyinst)
                except TypeMatchException:
                    raise TermException("subst: type " + str(v.T) + " cannot match " + str(inst_T))

        # Cache for rec function
        cache = dict()

        # Now apply substitution recursively.
        def rec(t):
            if t.is_svar():
                if t.name in inst:
                    return inst[t.name]
                else:
                    return t
            elif t.is_var():
                if t.name in inst.var_inst:
                    return inst.var_inst[t.name]
                else:
                    return t
            elif t.is_const():
                return t
            elif t.is_bound():
                return t
            elif t._id in cache:
                return cache[t._id]
            elif t.is_comb():
                fun_t = rec(t.fun)
                arg_t = rec(t.arg)
                if fun_t._id == t.fun._id and arg_t._id == t.arg._id:
                    res = t
                else:
                    res = Comb(fun_t, arg_t)
                cache[t._id] = res
                return res
            elif t.is_abs():
                if t.var_name in inst.abs_name_inst:
                    var_name = inst.abs_name_inst[t.var_name]
                else:
                    var_name = t.var_name
                body_t = rec(t.body)
                if body_t._id == t.body._id and var_name == t.var_name:
                    res = t
                else:
                    res = Abs(var_name, t.var_T, body_t)
                cache[t._id] = res
                return res
            else:
                raise TypeError

        t = self
        if inst.tyinst:
            t = self.subst_type(inst.tyinst)
        return rec(t)

    def strip_comb(self):
        """Given a term f t1 t2 ... tn, returns (f, [t1, t2, ..., tn])."""
        t = self
        args = []
        while t.is_comb():
            args.append(t.arg)
            t = t.fun
        return (t, list(reversed(args)))

    def strip_forall(self, *, num=None):
        """Given a term !x1 x2 ... xn. body, returns ([x1, x2, ..., xn], body)"""
        args = []
        t = self
        while t.is_forall() and (num is None or num > 0):
            body = t.arg
            v = Var(body.var_name, body.var_T)
            args.append(v)
            t = body.subst_bound(v)
            if num is not None:
                num -= 1
        return args, t

    @property
    def head(self) -> Term:
        """Given a term f t1 t2 ... tn, returns f."""
        t = self
        while t.is_comb():
            t = t.fun
        return t

    @property
    def args(self):
        """Given a term f t1 t2 ... tn, return the list [t1, ..., tn]."""
        return self.strip_comb()[1]

    def is_binop(self) -> bool:
        """Whether self is of the form f t1 t2."""
        return len(self.args) == 2

    @property
    def arg1(self) -> Term:
        """Given a term f a b, return a."""
        return self.fun.arg

    def is_implies(self) -> bool:
        """Whether self is of the form A --> B."""
        return self.is_comb('implies', 2)

    def strip_implies(self):
        """Given s1 --> ... --> sn --> t, return ([s1, ..., sn], t)."""
        if self.is_implies():
            rest, c = self.arg.strip_implies()
            return ([self.arg1] + rest, c)
        else:
            return ([], self)

    def is_forall(self) -> bool:
        """Whether self is of the form !x. P x."""
        return self.is_comb('all', 1)

    def is_equals(self) -> bool:
        """Whether self is of the form A = B."""
        return self.is_comb('equals', 2)

    def is_reflexive(self) -> bool:
        """Whether self is of the form A = A."""
        return self.is_equals() and self.arg1 == self.arg

    def is_VAR(self) -> bool:
        """Whether self is of the form _VAR v."""
        return self.is_comb('_VAR', 1) and self.arg.is_var()

    @property
    def lhs(self) -> Term:
        assert self.is_equals(), "lhs: not an equality."
        return self.arg1

    @property
    def rhs(self) -> Term:
        assert self.is_equals(), "rhs: not an equality."
        return self.arg

    def incr_boundvars(self, inc):
        """Increase loose bound variables in self by inc."""
        def rec(t, lev):
            if t.is_svar() or t.is_var() or t.is_const():
                return t
            elif t.is_comb():
                fun_t = rec(t.fun, lev)
                arg_t = rec(t.arg, lev)
                if fun_t._id == t.fun._id and arg_t._id == t.arg._id:
                    return t
                else:
                    return Comb(fun_t, arg_t)
            elif t.is_abs():
                body_t = rec(t.body, lev+1)
                if body_t._id == t.body._id:
                    return t
                else:
                    return Abs(t.var_name, t.var_T, body_t)
            elif t.is_bound():
                if t.n >= lev:
                    return Bound(t.n + inc)
                else:
                    return t
            else:
                raise TypeError

        return rec(self, 0)

    def subst_bound(self, t: Term) -> Term:
        """Given an Abs(x,T,body), substitute x for t in the body. t should
        have type T.

        """
        is_open = t.is_open()
        cache = dict()
        def rec(s, n):
            if s.is_svar() or s.is_var() or s.is_const():
                return s
            if s.is_bound():
                if s.n == n:
                    if is_open:
                        return t.incr_boundvars(n)
                    else:
                        return t
                elif s.n > n:  # Bound outside
                    return Bound(s.n - 1)
                else:  # Locally bound
                    return s
            id_s = s._id
            if (id_s, n) in cache:
                return cache[(id_s, n)]
            if s.is_comb():
                fun_s = rec(s.fun, n)
                arg_s = rec(s.arg, n)
                if fun_s._id == s.fun._id and arg_s._id == s.arg._id:
                    res = s
                else:
                    res = Comb(fun_s, arg_s)
                cache[(id_s, n)] = res
                return res
            elif s.is_abs():
                body_s = rec(s.body, n+1)
                if body_s._id == s.body._id:
                    res = s
                else:
                    res = Abs(s.var_name, s.var_T, body_s)
                cache[(id_s, n)] = res
                return res
            else:
                raise TypeError

        if self.is_abs():
            # Perform the substitution. Note t may be a bound variable itself.
            return rec(self.body, 0)
        else:
            raise TermException("subst_bound: input is not an abstraction.")

    def beta_conv(self) -> Term:
        """Beta-conversion: given a term of the form (%x. t1) t2, return the
        term t1[t2/x] which is beta-equivalent.

        """
        if self.is_comb() and self.fun.is_abs():
            return self.fun.subst_bound(self.arg)
        else:
            raise TermException("beta_conv: input is not in the form (%x. t1) t2.")

    def beta_norm(self) -> Term:
        """Normalize self using beta-conversion."""
        if self.is_svar() or self.is_var() or self.is_const() or self.is_bound():
            return self
        elif self.is_comb():
            f = self.fun.beta_norm()
            x = self.arg.beta_norm()
            if f.is_abs():
                return f(x).beta_conv().beta_norm()
            else:
                return f(x)
        elif self.is_abs():
            return Abs(self.var_name, self.var_T, self.body.beta_norm())
        else:
            raise TypeError

    def subst_norm(self, inst=None, **kwargs) -> Term:
        """Substitute using the given instantiation, then normalize with
        respect to beta-conversion.

        """
        if inst is None:
            inst = Inst(**kwargs)
        return self.subst(inst).beta_norm()

    def occurs_var(self, t: Term) -> Term:
        """Whether the variable t occurs in self."""
        if self.is_svar():
            return False
        if self.is_var():
            return self == t
        elif self.is_const():
            return False
        elif self.is_comb():
            return self.fun.occurs_var(t) or self.arg.occurs_var(t)
        elif self.is_abs():
            return self.body.occurs_var(t)
        elif self.is_bound():
            return False
        else:
            raise TypeError    

    def abstract_over(self, t: Term) -> Term:
        """Abstract over the variable t. The result is ready to become
        the body of an Abs term.
        
        """
        def rec(s, n):
            if s.is_svar():
                if t.is_svar() and s.name == t.name:
                    if s.T != t.T:
                        raise TermException("abstract_over: wrong type.")
                    else:
                        return Bound(n)
                else:
                    return s
            elif s.is_var():
                if t.is_var() and s.name == t.name:
                    if s.T != t.T:
                        raise TermException("abstract_over: wrong type.")
                    else:
                        return Bound(n)
                else:
                    return s
            elif s.is_const():
                return s
            elif s.is_comb():
                fun_s = rec(s.fun, n)
                arg_s = rec(s.arg, n)
                if fun_s._id == s.fun._id and arg_s._id == s.arg._id:
                    return s
                else:
                    return Comb(fun_s, arg_s)
            elif s.is_abs():
                body_s = rec(s.body, n+1)
                if body_s._id == s.body._id:
                    return s
                else:
                    return Abs(s.var_name, s.var_T, body_s)
            elif s.is_bound():
                return s
            else:
                raise TypeError

        if t.is_var() or t.is_svar():
            return rec(self, 0)
        else:
            raise TermException("abstract_over: t is not a variable.")

    def checked_get_type(self) -> Type:
        """Perform type-checking and return the type of self."""
        def rec(t, bd_vars):
            if t.is_svar() or t.is_var() or t.is_const():
                return t.T
            elif t.is_comb():
                funT = rec(t.fun, bd_vars)
                argT = rec(t.arg, bd_vars)
                if not funT.is_fun():
                    raise TypeCheckException('function type expected in application')
                elif funT.domain_type() != argT:
                    raise TypeCheckException(
                        'type mismatch in application. Expected %s. Got %s' % (funT.domain_type(), argT))
                else:
                    return funT.range_type()
            elif t.is_abs():
                bodyT = rec(t.body, [t.var_T] + bd_vars)
                return TFun(t.var_T, bodyT)
            elif t.is_bound():
                if t.n >= len(bd_vars):
                    raise TypeCheckException("open term")
                else:
                    return bd_vars[t.n]
            else:
                raise TypeError
        return rec(self, [])

    def convert_svar(self) -> Term:
        if self.is_svar():
            raise TermException("convert_svar: term already contains SVar.")
        elif self.is_var():
            return SVar(self.name, self.T.convert_stvar())
        elif self.is_const():
            return Const(self.name, self.T.convert_stvar())
        elif self.is_comb():
            return self.fun.convert_svar()(self.arg.convert_svar())
        elif self.is_abs():
            return Abs(self.var_name, self.var_T.convert_stvar(), self.body.convert_svar())
        elif self.is_bound():
            return self
        else:
            raise TypeError

    def dest_abs(self, var_name=None):
        """Given self of form %x. body, return pair (x, body).

        If var_name is None, the name recorded in the abstraction is used
        as the suggested name. Otherwise var_name is used as suggested name.

        It is guaranteed that v does not repeat names with any variables
        in the body.

        """
        assert self.is_abs(), 'dest_abs'
        var_names = [v.name for v in self.body.get_vars()]
        if var_name is None:
            var_name = self.var_name
        nm = name.get_variant_name(var_name, var_names)
        v = Var(nm, self.var_T)
        body = self.subst_bound(v)

        return v, body


    def get_svars(self):
        res = []
        found = set()
        def rec(t):
            if t.is_svar():
                if t not in found:
                    res.append(t)
                    found.add(t)
            elif t.is_comb():
                rec(t.fun)
                rec(t.arg)
            elif t.is_abs():
                rec(t.body)
        rec(self)
        return res

    def get_vars(self) -> List[Var]:
        res = []
        found = set()
        def rec(t):
            if t.is_var():
                if t not in found:
                    res.append(t)
                    found.add(t)
            elif t.is_comb():
                rec(t.fun)
                rec(t.arg)
            elif t.is_abs():
                rec(t.body)
        rec(self)
        return res

    def get_consts(self):
        res = []
        found = set()
        def rec(t):
            if t.is_const():
                if t not in found:
                    res.append(t)
                    found.add(t)
            elif t.is_comb():
                rec(t.fun)
                rec(t.arg)
            elif t.is_abs():
                rec(t.body)
        rec(self)
        return res        

    def has_var(self):
        if self.is_var():
            return True
        elif self.is_comb():
            return self.fun.has_var() or self.arg.has_var()
        elif self.is_abs():
            return self.body.has_var()
        else:
            return False

    def has_vars(self, vs):
        """Return whether self contains any of the variables in vs."""
        if self.is_var():
            return self in vs
        elif self.is_comb():
            return self.fun.has_vars(vs) or self.arg.has_vars(vs)
        elif self.is_abs():
            return self.body.has_vars(vs)
        else:
            return False

    def get_stvars(self):
        res = []
        def rec(t):
            if t.is_var() or t.is_const():
                for stvar in t.T.get_stvars():
                    if stvar not in res:
                        res.append(stvar)
            elif t.is_comb():
                rec(t.fun)
                rec(t.arg)
            elif t.is_abs():
                for stvar in t.var_T.get_stvars():
                    if stvar not in res:
                        res.append(stvar)
                rec(t.body)
        rec(self)
        return res


class SVar(Term):
    """Schematic variable, specified by name and type."""
    def __init__(self, name, T):
        self.ty = Term.SVAR
        self.name = name
        self.T = T
        self._id = id(self)

class Var(Term):
    """Variable, specified by name and type."""
    def __init__(self, name, T):
        self.ty = Term.VAR
        self.name = name
        self.T = T
        self._id = id(self)

class Const(Term):
    """Constant, specified by name and type."""
    def __init__(self, name, T):
        self.ty = Term.CONST
        self.name = name
        self.T = T
        self._id = id(self)

class Comb(Term):
    """Combination."""
    def __init__(self, fun, arg):
        self.ty = Term.COMB
        self.fun = fun
        self.arg = arg
        self._id = id(self)

class Abs(Term):
    """Abstraction. The input to Abs is the list x1, T1, ..., xn, Tn, body.
    
    The result is %x1 : T1. ... %xn : Tn. body.
    """
    def __init__(self, *args):
        if len(args) < 3:
            raise TypeError
        else:
            self.ty = Term.ABS
            self.var_name = args[0]
            self.var_T = args[1]
            if len(args) == 3:
                self.body = args[2]
            else:
                self.body = Abs(*args[2:])
            self._id = id(self)

class Bound(Term):
    """Bound variable, with de Bruijn index n."""
    def __init__(self, n):
        self.ty = Term.BOUND
        self.n = n
        self._size = 1
        self._id = id(self)

def get_svars(t):
    """Returns list of schematic variables in a term or a list of terms."""
    if isinstance(t, Term):
        return t.get_svars()
    elif isinstance(t, list):
        found = set()
        res = []
        for s in t:
            for svar in s.get_svars():
                if svar not in found:
                    res.append(svar)
                    found.add(svar)
        return res
    else:
        raise TypeError

def get_vars(t):
    """Returns list of variables in a term or a list of terms."""
    if isinstance(t, Term):
        return t.get_vars()
    elif isinstance(t, list):
        found = set()
        res = []
        for s in t:
            for var in s.get_vars():
                if var not in found:
                    res.append(var)
                    found.add(var)
        return res
    else:
        raise TypeError

def get_stvars(t):
    """Get the list of type variables for a term."""
    if isinstance(t, Term):
        return t.get_stvars()
    elif isinstance(t, list):
        found = set()
        res = []
        for s in t:
            for stvar in s.get_stvars():
                if stvar not in found:
                    res.append(stvar)
                    found.add(stvar)
        return res
    else:
        raise TypeError


implies = Const("implies", TFun(BoolType, BoolType, BoolType))

def equals(T):
    """Returns the equals constant for the given type."""
    return Const("equals", TFun(T, T, BoolType))

def Eq(s, t):
    """Construct the term s = t."""
    return equals(s.get_type())(s, t)


def Implies(*args):
    """Construct the term s1 --> ... --> sn --> t."""
    typecheck.checkinstance('Implies', args, [Term])
    if not args:
        raise TermException("Implies: input must have at least one term.")
    res = args[-1]
    for s in reversed(args[:-1]):
        res = implies(s, res)
    return res

def Lambda(*args):
    """Construct the term %x_1 ... x_n. body.
    
    The arguments are x_1, ..., x_n, body.

    Here x_1, ..., x_n must be variables (or schematic variable) and
    body is a term possibly depending on x_1, ..., x_n.
    
    """
    typecheck.checkinstance('Lambda', args, [Term])
    if len(args) < 2:
        raise TermException("Lambda: must provide two terms.")
    body = args[-1]
    for x in reversed(args[:-1]):
        if not (x.is_var() or x.is_svar()):
            raise TermException("Lambda: x must be a variable. Got %s" % str(x))
        body = Abs(x.name, x.T, body.abstract_over(x))
    return body

def forall(T):
    return Const("all", TFun(TFun(T, BoolType), BoolType))
 
def Forall(*args):
    """Construct the term !x_1 ... x_n. body.
    
    The arguments are x_1, ..., x_n, body.

    Here x_1, ..., x_n must be variables (or schematic variable) and
    body is a term possibly depending on x_1, ..., x_n.

    """
    typecheck.checkinstance('Forall', args, [Term])
    if len(args) < 1:
        raise TermException("Forall: must provide one term.")
    body = args[-1]
    for x in reversed(args[:-1]):
        if not (x.is_var() or x.is_svar()):
            raise TermException("Forall: x must be a variable. Got %s" % str(x))
        body = forall(x.T)(Lambda(x, body))
    return body

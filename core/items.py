"""Abstraction for parsing and processing of different types of items."""

import traceback

from kernel.type import TVar, TConst, TFun, BoolType
from kernel.term import Const
from kernel import theory
from kernel import extension
from core import context
from core import defcheck
from syntax import parser
from syntax import printer
from syntax import pprint
from syntax.settings import settings, global_setting
from core.defcheck import check_fun_recursion
from core.defcheck import check_datatype_positivity


class ItemException(Exception):
    """Exception when checking an item."""
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err


class Item:
    """Base class for different types of items."""
    def __init__(self, data):
        self.error = None

    def parse(self, data):
        """Parse an item from data in JSON format."""
        raise NotImplementedError

    def get_extension(self):
        """Obtain the extension corresponding to the item.

        Call only when self.error is None.

        """
        raise NotImplementedError

    def get_display(self):
        """Obtain data for display or edit.
        
        Normally, use highlight=False, unicode=True for edit, and
        highlight=True, unicode=True for display.

        """
        raise NotImplementedError

    def parse_edit(self, edit_data):
        """Parse the given edit_data to the object."""
        raise NotImplementedError

    def export_json(self):
        """Export the object to JSON format."""
        raise NotImplementedError

    def export_web(self):
        res = self.export_json()
        with global_setting(highlight=True, unicode=True):
            res['display'] = self.get_display()
        with global_setting(highlight=False, unicode=True):
            res['edit'] = self.get_display()
        if self.error is None:
            with global_setting(highlight=False, unicode=True, line_length=None):
                res['ext'] = printer.print_extensions(self.get_extension())
        else:
            res['error'] = {
                "err_type": self.error.__class__.__name__,
                "err_str": str(self.error),
                "trace": self.trace
            }
        return res


def export_term(t):
    """Function for printing a term for export to json."""
    try:
        with global_setting(unicode=True, line_length=80):
            res = printer.print_term(t)
        if len(res) == 1:
            res = res[0]
        return res
    except Exception:
        # Fallback: return raw repr
        return repr(t)

def display_raw(s):
    """Display unparsed type or term."""
    if isinstance(s, str):
        return [pprint.N(s)]
    else:
        return [pprint.N(line) for line in s]

def display_term(t):
    """Display parsed term."""
    res = printer.print_term(t)
    if not settings.highlight and settings.line_length is not None:
        return '\n'.join(res)
    else:
        return res


class Constant(Item):
    """Axiomatic constant."""
    def __init__(self):
        self.ty = 'def.ax'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.overloaded = False  # whether the constant is overloadable
        self.cname = None  # expanded name of the constant (for linking)
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.overloaded == other.overloaded and self.cname == other.cname and self.error == other.error

    def parse(self, data):
        self.name = data['name']
        if 'overloaded' in data and data['overloaded']:
            self.overloaded = True

        try:
            self.type = parser.parse_type(data['type'])
            if self.overloaded:
                self.cname = self.name
            else:
                self.cname = theory.thy.get_overload_const_name(self.name, self.type)
        except Exception as error:
            self.type = data['type']
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))
        if self.overloaded:
            res.append(extension.Overload(self.name))
        return res

    def get_display(self):
        return {
            'ty': 'def.ax',
            'name': self.name,
            'type': display_raw(self.type) if self.error else printer.print_type(self.type),
            'overloaded': self.overloaded
        }

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            res = {
                'ty': 'def.ax',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type)
            }
        if self.overloaded:
            res['overloaded'] = True
        return res

class Axiom(Item):
    """Axiom."""
    def __init__(self):
        self.ty = 'thm.ax'
        self.name = None  # name of the axiom
        self.vars = dict()  # variable declarations
        self.prop = None  # proposition
        self.attributes = list()  # list of attributes
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.vars == other.vars and \
            self.prop == other.prop and self.attributes == other.attributes and self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            # `'a::C` is sugar for a premise on the statement (syntax/parser.py):
            # the annotation lives in the source text (and so round-trips), the
            # kernel item sees only the ordinary implication.
            prop_text = parser.with_class_premises(
                data['prop'], *data.get('vars', {}).values())

            with context.fresh_context(vars=data['vars']):
                self.vars = context.ctxt.vars
                self.prop = context.parse_term(prop_text)

            # theorem does not already exist
            if theory.thy.has_theorem(self.name):
                raise ItemException("Theorem %s: theorem already exists" % self.name)

            # prop should not contain extra variables
            self_vars = set(self.vars.keys())
            prop_vars = set(v.name for v in self.prop.get_vars())
            if not prop_vars.issubset(self_vars):
                raise ItemException(
                    "Theorem %s: extra variables in prop: %s" % (
                        self.name, ", ".join(v for v in prop_vars - self_vars)))

        except Exception as error:
            self.vars = data['vars']
            self.prop = data['prop']
            self.error = error
            self.trace = traceback.format_exc()
        
        if 'attributes' in data:
            self.attributes = data['attributes']
        
    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Theorem(self.name, defcheck.mk_axiom(self.prop)))
        for attr in self.attributes:
            res.append(extension.Attribute(self.name, attr))
        return res

    def get_display(self):
        if self.error:
            disp_vars = [pprint.N(nm + ' :: ' + T) for nm, T in self.vars.items()]
            disp_prop = display_raw(self.prop)
        else:
            disp_vars = [pprint.N(nm + ' :: ') + printer.print_type(T) for nm, T in self.vars.items()]
            disp_prop = display_term(self.prop)

        return {
            'ty': 'thm.ax',
            'name': self.name,
            'vars': disp_vars if settings.highlight else '\n'.join(disp_vars),
            'prop': disp_prop,
            'attributes': self.attributes
        }

    def parse_edit(self, edit_data):
        raw_vars = edit_data.get('vars', {})
        if isinstance(raw_vars, dict):
            # Already in dict format (from export_json round-trip)
            vars = {nm: T for nm, T in raw_vars.items() if nm}
        else:
            # String format: "P :: bool\nQ :: nat"
            vars = dict()
            for var_decl in raw_vars.split('\n'):
                if var_decl.strip():
                    nm, T = [s.strip() for s in var_decl.split('::')]
                    vars[nm] = T
        edit_data['vars'] = vars
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            res = {
                'ty': 'thm.ax',
                'name': self.name,
                'vars': self.vars if self.error else \
                    dict((nm, printer.print_type(T)) for nm, T in self.vars.items()),
                'prop': self.prop if self.error else export_term(self.prop)
            }
        if self.attributes:
            res['attributes'] = self.attributes
        return res

class Theorem(Axiom):
    """Theorem"""
    def __init__(self):
        super().__init__()
        self.ty = 'thm'
        self.steps = None

    def __eq__(self, other):
        return super().__eq__(other) and self.steps == other.steps

    def parse(self, data):
        super().parse(data)

        if 'steps' in data:
            self.steps = data['steps']

    def get_extension(self):
        return super().get_extension()

    def get_display(self):
        res = super().get_display()
        res['ty'] = 'thm'
        return res

    def get_proof(self):
        res = dict()
        if self.steps:
            res['steps'] = self.steps
        return res

    def parse_edit(self, edit_data):
        super().parse_edit(edit_data)

    def export_json(self):
        res = super().export_json()
        res['ty'] = 'thm'
        if self.steps:
            res['steps'] = self.steps
        return res

class Definition(Item):
    """Definition"""
    def __init__(self):
        self.ty = 'def'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.prop = None  # defining proposition
        self.cname = None  # expanded name of the constant (for linking)
        self.attributes = []
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.prop == other.prop and self.cname == other.cname and self.attributes == other.attributes and \
            self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            self.type = parser.parse_type(data['type'])
            self.cname = theory.thy.get_overload_const_name(self.name, self.type)

            with context.fresh_context(defs={self.name: self.type}):
                self.prop = context.parse_term(data['prop'])

            # prop should be an equality
            if not self.prop.is_equals():
                raise ItemException("Definition %s: prop is not an equality" % self.name)
            
            f, args = self.prop.lhs.strip_comb()
            if f != Const(self.name, self.type):
                raise ItemException("Definition %s: wrong head of lhs" % self.name)
            lhs_vars = set(v.name for v in args)
            rhs_vars = set(v.name for v in self.prop.rhs.get_vars())
            if len(lhs_vars) != len(args):
                raise ItemException("Definition %s: variables on lhs must be distinct" % self.name)
            if not rhs_vars.issubset(lhs_vars):
                raise ItemException(
                    "Definition %s: extra variables in rhs: %s" % (
                        self.name, ", ".join(v for v in rhs_vars - lhs_vars)))

        except Exception as error:
            self.type = data['type']
            self.prop = data['prop']
            self.error = error
            self.trace = traceback.format_exc()

        if 'attributes' in data:
            self.attributes = data['attributes']

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))
        res.append(extension.Theorem(self.cname + "_def", defcheck.mk_axiom(self.prop)))
        for attr in self.attributes:
            res.append(extension.Attribute(self.cname + "_def", attr))
        return res

    def get_display(self):
        if self.error:
            disp_type = display_raw(self.type)
            disp_prop = display_raw(self.prop)
        else:
            disp_type = printer.print_type(self.type)
            disp_prop = display_term(self.prop)
        
        return {
            'ty': 'def',
            'name': self.name,
            'type': disp_type,
            'prop': disp_prop,
            'attributes': self.attributes
        }
    
    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            res = {
                'ty': 'def',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type),
                'prop': self.prop if self.error else export_term(self.prop)
            }
        if self.attributes:
            res['attributes'] = self.attributes
        return res

class Fun(Item):
    """Inductively defined functions.
    
    An inductively defined function is specified by its name, type, and
    a list of equations. Each equation specifies a rewriting rule for the
    defined constant. The rules may be recursive, but must be clearly
    terminating.

    For example, addition on natural numbers is specified by:
    fun plus :: nat => nat => nat
      plus 0 n = n
      plus (Suc m) n = Suc (plus m n)

    and multiplication on natural numbers is specified by:
    fun times :: nat => nat => nat
      times 0 n = 0
      times (Suc m) n = plus n (times m n)

    """
    def __init__(self):
        self.ty = 'def.ind'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.rules = []  # list of equality rules
        self.cname = None  # expanded name of the constant (for linking)
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.rules == other.rules and self.cname == other.cname and self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            self.type = parser.parse_type(data['type'])
            self.cname = theory.thy.get_overload_const_name(self.name, self.type)

            for rule in data['rules']:
                with context.fresh_context(defs={self.name: self.type}):
                    prop = context.parse_term(rule['prop'])

                # prop should be an equality
                if not prop.is_equals():
                    raise ItemException("Fun %s: rule is not an equality" % self.name)

                f, args = prop.lhs.strip_comb()
                if f != Const(self.name, self.type):
                    raise ItemException("Fun %s: wrong head of lhs" % self.name)
                lhs_vars = set(v.name for v in prop.lhs.get_vars())
                rhs_vars = set(v.name for v in prop.rhs.get_vars())
                if not rhs_vars.issubset(lhs_vars):
                    raise ItemException(
                        "Fun %s: extra variables in rhs: %s" % (
                            self.name, ", ".join(v for v in rhs_vars - lhs_vars)))

                self.rules.append({'prop': prop})

            # Check that the equations are structural recursion.
            check_fun_recursion(self.name, self.type, self.rules)
            
        except Exception as error:
            self.type = data['type']
            self.rules = data['rules']
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))
        for i, rule in enumerate(self.rules):
            th_name = self.cname + "_def_" + str(i + 1)
            res.append(extension.Theorem(th_name, defcheck.mk_axiom(rule['prop'])))
            res.append(extension.Attribute(th_name, "hint_rewrite"))
        return res

    def get_display(self):
        if self.error:
            disp_type = display_raw(self.type)
            disp_rules = [rule['prop'] for rule in self.rules]
        else:
            disp_type = printer.print_type(self.type)
            with global_setting(line_length=None):
                disp_rules = [printer.print_term(rule['prop']) for rule in self.rules]
        
        return {
            'ty': 'def.ind',
            'name': self.name,
            'type': disp_type,
            'rules': disp_rules if settings.highlight else '\n'.join(disp_rules)
        }

    def parse_edit(self, edit_data):
        rules = []
        for prop in edit_data['rules'].split('\n'):
            rules.append({'prop': prop})
        edit_data['rules'] = rules
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            return {
                'ty': 'def.ind',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type),
                'rules': [{'prop': rule['prop'] if self.error else export_term(rule['prop'])}
                          for rule in self.rules]
            }

class Inductive(Item):
    """Inductively defined predicate.

    An inductive predicate is specified by its name and type, and a list
    of introduction rules. We require each introduction rule be named.
    The conclusion of each introduction rule must correspond to the defined
    constant.

    """
    def __init__(self):
        self.ty = 'def.pred'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.rules = []  # list of introduction rules
        self.cname = None  # expected name of the constant (for linking)
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.rules == other.rules and self.cname == other.cname and self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            self.type = parser.parse_type(data['type'])
            self.cname = theory.thy.get_overload_const_name(self.name, self.type)

            for rule in data['rules']:
                with context.fresh_context(defs={self.name: self.type}):
                    prop = context.parse_term(rule['prop'])

                # Test conclusion of the prop
                _, concl = prop.strip_implies()
                f, _ = concl.strip_comb()
                if f != Const(self.name, self.type):
                    raise ItemException("Inductive %s: wrong head of conclusion" % self.name)

                self.rules.append({'name': rule['name'], 'prop': prop})

        except Exception as error:
            self.type = data['type']
            self.rules = data['rules']
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))

        for rule in self.rules:
            res.append(extension.Theorem(rule['name'], defcheck.mk_axiom(rule['prop'])))
            res.append(extension.Attribute(rule['name'], 'hint_backward'))

        res.extend(defcheck.inductive_case_induct_axioms(
            self.name, self.type, self.cname, self.rules))

        return res

    def get_display(self):
        if self.error:
            disp_type = display_raw(self.type)
            disp_rules = [pprint.N(rule['name'] + ": " + rule['prop']) for rule in self.rules]
        else:
            disp_type = printer.print_type(self.type)
            with global_setting(line_length=None):
                disp_rules = [pprint.N(rule['name'] + ": ") + printer.print_term(rule['prop'])
                            for rule in self.rules]
        
        return {
            'ty': 'def.pred',
            'name': self.name,
            'type': disp_type,
            'rules': disp_rules if settings.highlight else '\n'.join(disp_rules)
        }

    def parse_edit(self, edit_data):
        rules = []
        for rule in edit_data['rules'].split('\n'):
            name, prop = [s.strip() for s in rule.split(':', 1)]
            rules.append({'name': name, 'prop': prop})
        edit_data['rules'] = rules
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            return {
                'ty': 'def.pred',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type),
                'rules': [{'name': rule['name'],
                           'prop': rule['prop'] if self.error else export_term(rule['prop'])}
                          for rule in self.rules]
            }

class AxType(Item):
    """Axiomatic types."""
    def __init__(self):
        self.ty = 'type.ax'
        self.name = None  # name of the type
        self.args = list()  # list of type arguments
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.args == other.args and \
            self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.args = data['args']

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.TConst(self.name, len(self.args)))
        return res

    def get_display(self):
        Targs = [TVar(arg) for arg in self.args]
        T = TConst(self.name, *Targs)
        return {
            'ty': 'type.ax',
            'type': printer.print_type(T)
        }

    def parse_edit(self, edit_data):
        T = parser.parse_type(edit_data['type'], check_type=False)
        data = {
            'ty': 'type.ax',
            'name': T.name,
            'args': [argT.name for argT in T.args]
        }
        self.parse(data)

    def export_json(self):
        return {
            'ty': 'type.ax',
            'name': self.name,
            'args': self.args
        }

class Datatype(Item):
    """Inductive datatypes.
    
    An inductive datatype is specified by its name, its arity (as a list
    of default names of type arguments), and a list of constructors.

    For example, the natural numbers is defined by:
    datatype nat =
      zero
      Suc (n :: nat)

    and the type of lists is defined by:
    datatype 'a list =
      nil
      cons (x :: 'a) (xs :: 'a list)
    
    """
    def __init__(self):
        self.ty = 'type.ind'
        self.name = None  # name of the type
        self.args = list()  # list of type arguments
        self.constrs = list()  # list of type constructors
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.args == other.args and \
            self.constrs == other.constrs and self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.args = data['args']
        theory.thy.add_type_sig(self.name, len(self.args))

        try:
            for constr in data['constrs']:
                constr_type = parser.parse_type(constr['type'])
                self.constrs.append({
                    'name': constr['name'],
                    'type': constr_type,
                    'cname': theory.thy.get_overload_const_name(constr['name'], constr_type),
                    'args': constr['args']
                })

            # Check that the datatype occurs strictly positive in the
            # arguments of its constructors.
            check_datatype_positivity(self.name, self.constrs)
        except Exception as error:
            self.constrs = data['constrs']
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []

        # Add to type and term signature.
        res.append(extension.TConst(self.name, len(self.args)))
        # Register the constructors for the structural-recursion check
        # of fun definitions.
        theory.thy.add_datatype_constrs(
            self.name, [Const(c['name'], c['type']) for c in self.constrs])
        for constr in self.constrs:
            res.append(extension.Constant(constr['name'], constr['type'], ref_name=constr['cname']))

        res.extend(defcheck.datatype_axioms(self.name, self.args, self.constrs))

        return res

    def get_display(self):
        Targs = [TVar(arg) for arg in self.args]
        T = TConst(self.name, *Targs)
        constrs = []
        for constr in self.constrs:
            argsT, _ = constr['type'].strip_type()
            res = pprint.N(constr['name'])
            for i, arg in enumerate(constr['args']):
                res += pprint.N(' (' + arg + ' :: ') + printer.print_type(argsT[i]) + pprint.N(')')
            constrs.append(res)

        return {
            'ty': 'type.ind',
            'type': printer.print_type(T),
            'constrs': constrs if settings.highlight else '\n'.join(constrs)
        }

    def parse_edit(self, edit_data):
        T = parser.parse_type(edit_data['type'])
        constrs = []
        for constr_decl in edit_data['constrs'].split('\n'):
            constr = parser.parse_ind_constr(constr_decl)
            constr['type'] = str(TFun(*(constr['type'] + [T])))
            constrs.append(constr)

        data = {
            'ty': 'type.ind',
            'name': T.name,
            'args': [argT.name for argT in T.args],
            'constrs': constrs
        }

        self.parse(data)

    def export_json(self):
        constrs = []
        for constr in self.constrs:
            constrs.append({
                'name': constr['name'],
                'args': constr['args'],
                'type': constr['type'] if self.error else printer.print_type(constr['type'])
            })
        return {
            'ty': 'type.ind',
            'name': self.name,
            'args': self.args,
            'constrs': constrs
        }

def _has_schematic_tvar(T):
    """Whether the type contains an undetermined (schematic) type
    variable.  Used by quotient items, whose arity is read off the
    relation's type variables: a schematic variable would leave the
    arity undetermined."""
    if T.is_stvar():
        return True
    if T.is_tconst():
        return any(_has_schematic_tvar(arg) for arg in T.args)
    return False


class Quotient(Item):
    """Quotient types.

    A quotient type is specified by its name, the names of its
    abstraction and representation constants, and the relation being
    quotiented by.  The relation, of type A => A => bool, fixes the
    representation type (its domain A) and the arity of the new type
    (its type variables), and therefore the types of the two constants:
    both map between the quotient type and the predicate type
    A => bool.

    For example, the real numbers as a quotient of the sequences of
    integers, using the relation treal_eq:

    quotient real (mk_real, dest_real) treal_eq

    """
    def __init__(self):
        self.ty = 'type.quot'
        self.name = None
        self.args = list()
        self.abs_name = None
        self.rep_name = None
        self.rel = None
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and \
            self.args == other.args and self.abs_name == other.abs_name and \
            self.rep_name == other.rep_name and self.rel == other.rel and \
            self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.abs_name = data['abs']
        self.rep_name = data['rep']

        try:
            self.rel = context.parse_term(data['rel'])
            rel_T = self.rel.get_type()
            if not (rel_T.is_fun() and rel_T.range_type().is_fun() and
                    rel_T.domain_type() == rel_T.range_type().domain_type() and
                    rel_T.range_type().range_type() == BoolType):
                raise ItemException(
                    "Quotient %s: relation must have type A => A => bool, "
                    "got %s" % (self.name, printer.print_type(rel_T)))
            # The arity is the relation's type variables, as in HOL Light's
            # define_quotient_type and HOL Zero's new_tyconst_definition.
            if _has_schematic_tvar(rel_T):
                raise ItemException(
                    "Quotient %s: the relation's type has undetermined "
                    "variables; annotate it, e.g. (rel :: 'a => 'a => bool)"
                    % self.name)
            self.args = sorted(T.name for T in rel_T.get_tvars())
            theory.thy.add_type_sig(self.name, len(self.args))
        except Exception as error:
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.TConst(self.name, len(self.args)))

        T = TConst(self.name, *[TVar(arg) for arg in self.args])
        A = self.rel.get_type().domain_type()
        P = TFun(A, BoolType)
        res.append(extension.Constant(self.abs_name, TFun(P, T)))
        res.append(extension.Constant(self.rep_name, TFun(T, P)))
        res.extend(defcheck.quotient_axioms(
            self.name, self.args, self.rel, self.abs_name, self.rep_name))
        return res

    def get_display(self):
        Targs = [TVar(arg) for arg in self.args]
        T = TConst(self.name, *Targs)
        res = {
            'ty': 'type.quot',
            'type': printer.print_type(T),
            'abs': self.abs_name,
            'rep': self.rep_name
        }
        if self.rel is not None:
            res['rel'] = display_term(self.rel)
        return res

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        return {
            'ty': 'type.quot',
            'name': self.name,
            'args': self.args,
            'abs': self.abs_name,
            'rep': self.rep_name,
            'rel': self.rel if self.error else export_term(self.rel)
        }

class TypeAbbrev(Item):
    """Type abbreviations (type synonyms).

    An abbreviation names an existing type expression, so unlike `type`
    (an axiomatic type constant) it introduces no new type and no
    axioms: the kernel never sees the abbreviated name, and parse_type
    expands it away.

    For example, sets as predicates:

    typeabbrev set 'a = 'a => bool

    """
    def __init__(self):
        self.ty = 'type.abbrev'
        self.name = None
        self.args = list()
        self.defn = None
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and \
            self.args == other.args and self.defn == other.defn and \
            self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.args = data['args']

        try:
            self.defn = parser.parse_type(data['def'])
            extra = set(T.name for T in self.defn.get_tvars()) - set(self.args)
            if extra:
                raise ItemException(
                    "Type abbreviation %s: type variables %s are not "
                    "parameters" % (self.name, ", ".join(sorted(extra))))
            parser.add_type_abbrev(self.name, self.args, self.defn)
        except Exception as error:
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        # Parser-side state, not a theory extension: see
        # core.basic._apply_item, which re-registers it on replay.
        return []

    def get_display(self):
        return {
            'ty': 'type.abbrev',
            'name': self.name,
            'args': self.args,
            'def': self.defn if self.error else printer.print_type(self.defn)
        }

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        return {
            'ty': 'type.abbrev',
            'name': self.name,
            'args': self.args,
            'def': self.defn if self.error else printer.print_type(self.defn)
        }

class Class(Item):
    """A class declaration for the `'a::C` type-class sugar.

    The class and its laws belong to the library that defines the predicates,
    so the library declares them:

        class linorder = linorder (less_eq :: 'a ⇒ 'a ⇒ bool),
                         linorder_lt (less :: 'a ⇒ 'a ⇒ bool)

    The statement `fixes x :: 'a::linorder` then has one premise per entry
    (syntax/parser.py: with_class_premises).  Like `typeabbrev` this item
    carries no theory extension -- it registers parser-side state, which
    core.basic re-registers when a theory is replayed.

    """
    def __init__(self):
        self.ty = 'class'
        self.name = None
        self.body = None      # declaration text after `=`
        self.entries = []     # [(predicate, [(op, type template)])]
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and \
            self.body == other.body and self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.body = data.get('body', '')

        try:
            self.entries = parser.parse_class_body(self.body)
            for predicate, ops in self.entries:
                for op_name, op_ty in ops:
                    parser.parse_type(op_ty, check_type=False)
            parser.add_class(self.name, *self.entries)
        except Exception as error:
            self.error = error
            self.trace = traceback.format_exc()

    def get_extension(self):
        # Parser-side state, not a theory extension: see
        # core.basic._apply_item, which re-registers it on replay.
        return []

    def get_display(self):
        return {
            'ty': 'class',
            'name': self.name,
            'body': self.body,
            'entries': [[pred, [[op, ty] for op, ty in ops]]
                        for pred, ops in self.entries]
        }

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        return {
            'ty': 'class',
            'name': self.name,
            'body': self.body,
            'entries': [[pred, [[op, ty] for op, ty in ops]]
                        for pred, ops in self.entries]
        }


class Header(Item):
    """Header"""
    def __init__(self):
        self.ty = 'header'
        self.depth = None
        self.name = None
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.depth == other.depth and self.name == other.name and \
            self.error == other.error

    def parse(self, data):
        self.depth = data['depth']
        self.name = data['name']

    def get_extension(self):
        return []

    def get_display(self):
        return {
            'ty': 'header',
            'depth': self.depth,
            'name': self.name
        }

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        return {
            'ty': 'header',
            'depth': self.depth,
            'name': self.name
        }


item_table = {
    'def.ax': Constant,
    'thm.ax': Axiom,
    'thm': Theorem,
    'def': Definition,
    'def.ind': Fun,
    'def.pred': Inductive,
    'type.ax': AxType,
    'type.abbrev': TypeAbbrev,
    'type.ind': Datatype,
    'type.quot': Quotient,
    'class': Class,
    'header': Header
}

def parse_item(data):
    obj = item_table[data['ty']]()
    obj.parse(data)
    return obj

def parse_edit(edit_data):
    obj = item_table[edit_data['ty']]()
    obj.parse_edit(edit_data)
    return obj

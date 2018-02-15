#!/usr/bin/env python
##############################################################################
##                                                                          ##
##                                PyMPF                                     ##
##                                                                          ##
##              Copyright (C) 2017-2018, Altran UK Limited                  ##
##                                                                          ##
##  This file is part of PySMT.                                             ##
##                                                                          ##
##  PySMT is free software: you can redistribute it and/or modify           ##
##  it under the terms of the GNU General Public License as published by    ##
##  the Free Software Foundation, either version 3 of the License, or       ##
##  (at your option) any later version.                                     ##
##                                                                          ##
##  PySMT is distributed in the hope that it will be useful,                ##
##  but WITHOUT ANY WARRANTY; without even the implied warranty of          ##
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           ##
##  GNU General Public License for more details.                            ##
##                                                                          ##
##  You should have received a copy of the GNU General Public License       ##
##  along with PySMT. If not, see <http://www.gnu.org/licenses/>.           ##
##                                                                          ##
##############################################################################

##############################################################################
# Structure
##############################################################################

class SMT_Context(object):
    def __init__(self):
        self.use_declare_const = True
        self.use_define_const = True

class Tree_Node(object):
    def __init__(self):
        pass

    def to_smt(self, context):
        raise NotImplementedError("%s does not override method" %
                                  self.__class__.__name__)

class Node_Set_Logic(Tree_Node):
    def __init__(self, logic):
        self.logic = logic

    def to_smt(self, context):
        return "(set-logic %s)" % self.logic

class Node_Set_Info(Tree_Node):
    def __init__(self, key, value):
        assert type(key) is str
        assert type(value) is str
        self.key = key
        self.value = value

    def to_smt(self, context):
        return "(set-info :%s %s)" % (self.key, self.value)

class Node_Set_Option(Tree_Node):
    def __init__(self, key, value):
        assert type(key) is str
        assert type(value) is str
        self.key = key
        self.value = value

    def to_smt(self, context):
        return "(set-option :%s %s)" % (self.key, self.value)

class Node_Declare_Sort(Tree_Node):
    def __init__(self, kind):
        self.kind = kind

    def to_smt(self, context):
        return "(declare-sort %s %u)" % (self.kind.name, self.kind.arity)

class Node_Define_Sort(Tree_Node):
    def __init__(self, kind):
        assert kind.__class__ == Kind_Alias
        self.kind = kind

    def to_smt(self, context):
        if self.kind.parent.is_indexed():
            sdef = ["_", self.kind.parent.name] + map(str, self.kind.parameters)
        else:
            sdef = [self.kind.parent.name] + map(lambda x: x.to_smt(context),
                                                 self.kind.parameters)
        return "(define-sort %s (%s) (%s))" % (
            self.kind.name,
            " ".join(map(lambda x: x.to_smt(context),
                         self.kind.type_parameters)),
            " ".join(sdef))

class Node_Declare_Fun(Tree_Node):
    def __init__(self, sym):
        self.sym = sym

    def to_smt(self, context):
        rv = []
        is_const = context.use_declare_const and self.sym.param_count() == 0
        if is_const:
            rv.append("declare-const")
        else:
            rv.append("declare-fun")
        rv.append(self.sym.name)
        if not is_const:
            rv.append("(%s)" % " ".join(map(lambda x: x.to_smt(context),
                                            self.sym.param_sort)))
        rv.append(self.sym.sort.to_smt(context))
        return "(" + " ".join(rv) + ")"

class Node_Assert(Tree_Node):
    def __init__(self, term):
        self.term = term

    def to_smt(self, context):
        return "(assert %s)" % self.term.to_smt(context)

class Node_Literal_Numeral(Tree_Node):
    def __init__(self, n):
        self.n = int(n)

class Node_Literal_Decimal(Tree_Node):
    def __init__(self, string):
        self.n = string

class Node_Literal_Bitvector(Tree_Node):
    def __init__(self, string):
        if string.startswith("#x"):
            self.width = 4 * (len(string) - 2)
            self.value = int(string[2:], 16)
        elif string.startswith("#b"):
            self.width = len(string) - 2
            self.value = int(string[2:], 2)
        else:
            assert False

class Node_Literal_String(Tree_Node):
    def __init__(self, string):
        self.string = string

# class Node_Identifier(Tree_Node):
#     def __init__(self, entity):
#         self.entity = entity
#         self.sort   = None # TODO

class Node_Quantification(Tree_Node):
    def __init__(self, kind, binding, body):
        assert kind in ("forall", "exists")
        assert type(binding) is list

        self.kind    = kind
        self.binding = binding
        self.body    = body

class Node_Function_Application(Tree_Node):
    def __init__(self, function, parameters, function_index=[]):
        assert len(function_index) == function.arity
        assert ((function.attribute is None and
                 len(parameters) == len(function.param_sort)) or
                (function.attribute is not None and
                 len(parameters) >= len(function.param_sort)))
        self.function       = function
        self.function_index = function_index
        self.parameters     = parameters

    def to_smt(self, context):
        rv = []
        if len(self.function_index):
            rv.append("(_ %s %s)" % (self.function.name,
                                     " ".join(map(str, self.function_index))))
        else:
            rv.append(self.function.name)
        rv += map(lambda x: x.to_smt(context), self.parameters)
        if len(self.parameters) > 0:
            return "(" + " ".join(rv) + ")"
        else:
            assert len(rv) == 1
            return rv[0]

class Node_Check_Sat(Tree_Node):
    def __init__(self):
        pass

    def to_smt(self, context):
        return "(check-sat)"

class Node_Exit(Tree_Node):
    def __init__(self):
        pass

    def to_smt(self, context):
        return "(exit)"


##############################################################################
# Identifiers (simple and indexed)
##############################################################################

class Identifier(object):
    def __init__(self, name):
        self.name  = name
        self.index = []

    def __eq__(self, other):
        if self.__class__ == other.__class__:
            return self.name == other.name
        return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Identifier(%s)" % self.name

    def __hash__(self):
        return hash(str(self))

class Indexed_Identifier(Identifier):
    def __init__(self, name, index):
        assert type(index) is list
        assert len(index) > 0
        self.name  = name
        self.index = index

    def __eq__(self, other):
        if self.__class__ == other.__class__:
            if self.name == other.name and len(self.index) == len(other.index):
                for a, b in zip(self.index, other.index):
                    if a != b:
                        return False
                return True
        return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __str__(self):
        return "(_ %s %s)" % (self.name, " ".join(map(str, self.index)))

    def __repr__(self):
        return "Indexed_Identifier(%s, [%s])" % (self.name,
                                                 " ".join(map(str, self.index)))

##############################################################################
# Kinds and Sorts
##############################################################################

# Sorts are actual types of variables. Kinds are the un-instantiated sorts
# or aliases.

class Kind(object):
    def __init__(self, name):
        assert type(name) is str
        self.name  = name
        self.arity = 0

    def is_indexed(self):
        return False

    def to_smt(self, context):
        return self.name

# Mainly used for define-sort
class Kind_Type_Parameter(Kind):
    def __init__(self, name):
        self.name  = name
        self.arity = 0

class Kind_Parametric(Kind):
    def __init__(self, name, arity, indexed=False):
        super(Kind_Parametric, self).__init__(name)
        assert type(arity) is int and arity > 0
        assert type(indexed) is bool
        self.arity   = arity
        self.indexed = indexed

    def is_indexed(self):
        return self.indexed

class Kind_Datatype(Kind):
    def __init__(self, name, arity):
        super(Kind_Datatype, self).__init__(name, arity)
        assert type(arity) is int and arity >= 0
        self.arity = arity

class Kind_Alias(Kind):
    def __init__(self, name, kind, type_parameters, parameters):
        assert type(type_parameters) is list
        assert type(parameters) is list
        super(Kind_Alias, self).__init__(name)
        self.parent = kind
        self.arity = len(type_parameters)
        self.type_parameters = type_parameters
        self.parameters = parameters

class Sort(object):
    def __init__(self, kind, parameters=[]):
        assert type(parameters) is list and len(parameters) == kind.arity
        assert kind is not None
        self.kind       = kind
        self.parameters = parameters

    def to_smt(self, context):
        if len(self.parameters) == 0:
            return self.kind.name
        elif self.kind.is_indexed():
            return "(_ %s %s)" % (self.kind.name,
                                  " ".join(map(str, self.parameters)))
        else:
            return "(%s %s)" % (self.kind.name,
                                " ".join(map(lambda x: x.to_smt(context),
                                             self.parameters)))


# Polymorphic sort. Either anything (kind=None) or of some class of
# sort (e.g. BitVec). Can never be the sort of a user-defined symbol,
# and special type-checking rules are applied by the various builtin
# function symbols.
class Polymorphic_Sort(Sort):
    def __init__(self, kind=None):
        self.kind       = kind
        self.parameters = None

##############################################################################
# Symbols
##############################################################################

# Basic user-defined function
class Function(object):
    def __init__(self,
                 name,
                 sort,
                 param_sort=[],
                 param_names=None):
        self.name        = name
        self.sort        = sort
        self.param_sort  = param_sort
        self.param_names = param_names
        self.arity       = 0
        self.attribute   = None

    def param_count(self):
        return len(self.param_sort)

# Like a function, but can be chainable, etc. and does not require a sort
class Builtin_Function(Function):
    ATTRIBUTE_KINDS = ("left-assoc",
                       "right-assoc",
                       "chainable",
                       "pairwise")

    def __init__(self,
                 name,
                 sort=None,
                 param_sort=[],
                 attribute=None,
                 arity=0):
        assert attribute is None or \
            attribute in Builtin_Function.ATTRIBUTE_KINDS
        super(Builtin_Function, self).__init__(name, sort, param_sort, None)
        self.attribute = attribute
        self.arity = arity

class Builtin_Function_ITE(Builtin_Function):
    def __init__(self, sort_bool):
        t = Polymorphic_Sort()
        super(Builtin_Function_ITE, self).__init__("ite",
                                                   sort=t,
                                                   param_sort=[sort_bool,
                                                               t, t])

class Builtin_Function_Equality(Builtin_Function):
    def __init__(self, name, sort_bool):
        assert name in ("=", "distinct")
        t = Polymorphic_Sort()
        super(Builtin_Function_Equality, self).__init__(
            name,
            sort=t,
            param_sort=[t, t],
            attribute={"="        : "chainable",
                       "distinct" : "pairwise"}[name])

#class Builtin_Function_FP(Builtin_Function)



class Sorted_Var(object):
    def __init__(self, symbol, sort):
        self.symbol = symbol
        self.sort   = sort

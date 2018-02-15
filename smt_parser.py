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

import traceback

from pprint import pprint

from smt_lexer import SMT_Lexer
from smt_tree import *

class MatchError(Exception):
    # MatchError(token_kind, token)
    # MatchError([token_kind, ...], token)
    def __init__(self, expected_token_type, actual_token):
        assert type(expected_token_type) in (str, list)

        self.expected_token_type = expected_token_type
        self.loc                 = actual_token

    def __str__(self):
        msg = "Expected "
        if self.expected_token_type is None:
            msg += "EOF"
        elif type(self.expected_token_type) is str:
            msg += self.expected_token_type
        else:
            msg += " or ".join(sorted(self.expected_token_type))
        msg +=", got "
        if self.loc is None:
            msg += "EOF"
        else:
            msg += self.loc.type + " '" + self.loc.value + "'"
        msg += " instead"
        return msg

class ParseError(Exception):
    def __init__(self, error, actual_token):
        self.error         = error
        self.loc           = actual_token

    def __str__(self):
        return self.error

class SMT_Parser(object):
    SPEC_CONSTANT_TYPES = ("NUMERAL", "DECIMAL", "HEX", "BINARY", "STRING")

    def __init__(self, filename):
        self.filename = filename

        with open(self.filename, "rU") as fd:
            self.data = fd.read().rstrip()

        self.line_data = self.data.splitlines()
        self.lexer     = SMT_Lexer().tokenize(self.data)

        self.ct       = None
        self.nt       = self.lexer.next()

        self.code    = []

        self.names = []

        # Add builtin stuff
        self.push_scope()
        self.init_core()
        self.init_intreal()
        self.init_bv()
        self.init_float()

        # Create new scope for user-defined stuff
        self.push_scope()

    #######################################################################
    # Name table (sorts and symbols)
    #######################################################################

    def push_scope(self):
        self.names.append({"kind"   : {},  # str -> Kind
                           "symbol" : {}}) # str -> Function

    def pop_scope(self):
        assert len(self.names) > 1
        del self.names[-1]

    def register(self, kind, identifier, entity):
        assert kind in ("kind", "symbol")
        assert type(identifier) is str
        assert identifier not in self.names[-1][kind]
        self.names[-1][kind][identifier] = entity

    def lookup(self, kind, identifier):
        assert kind in ("kind", "symbol")
        assert type(identifier) is str
        for i in xrange(1, len(self.names) + 1):
            if identifier in self.names[-i][kind]:
                return self.names[-i][kind][identifier]
        return None

    #######################################################################
    # Parting utility
    #######################################################################

    def pp_error(self, error):
        if error.loc.lineno < len(self.line_data):
            print self.line_data[error.loc.lineno - 1]
            col = error.loc.lexpos
            for line in self.line_data[:error.loc.lineno - 1]:
                col -= (len(line) + 1)
            print (" " * col) + "^"

        msg = self.filename + "("
        if error.loc is None:
            msg += "EOF"
        else:
            msg += str(error.loc.lineno)
        msg += "): "

        msg += str(error)

        print msg

    def next(self):
        try:
            self.ct = self.nt
            self.nt = self.lexer.next()
        except StopIteration:
            self.nt = None

    def match(self, token_kind):
        self.next()
        if self.ct is None and token_kind is not None:
            return
        elif (self.ct is not None and
              token_kind is not None and
              self.ct.type == token_kind):
            return
        else:
            raise MatchError(token_kind, self.ct)

    def match_set(self, *token_kinds):
        self.next()
        if self.ct is not None and self.ct.type in token_kinds:
            return
        else:
            raise MatchError(token_kinds, self.ct)

    #######################################################################
    # Logics and Theories
    #######################################################################

    def init_core(self):
        assert len(self.names) == 1

        kind_bool = Kind("Bool")

        self.register("kind", "Bool", kind_bool)

        sort_bool = Sort(kind_bool)

        self.register("symbol", "true",
                      Function("true", sort=sort_bool))
        self.register("symbol", "false",
                      Function("false", sort=sort_bool))

        self.register("symbol", "not",
                      Function("not", sort=sort_bool, param_sort=[sort_bool]))

        self.register("symbol", "=>",
                      Builtin_Function("=>",
                                       sort=sort_bool,
                                       param_sort=[sort_bool, sort_bool],
                                       attribute="right-assoc"))
        self.register("symbol", "and",
                      Builtin_Function("and",
                                       sort=sort_bool,
                                       param_sort=[sort_bool, sort_bool],
                                       attribute="left-assoc"))
        self.register("symbol", "or",
                      Builtin_Function("or",
                                       sort=sort_bool,
                                       param_sort=[sort_bool, sort_bool],
                                       attribute="left-assoc"))
        self.register("symbol", "xor",
                      Builtin_Function("xor",
                                       sort=sort_bool,
                                       param_sort=[sort_bool, sort_bool],
                                       attribute="left-assoc"))

        self.register("symbol", "=",
                      Builtin_Function_Equality("=", sort_bool))

        self.register("symbol", "distinct",
                      Builtin_Function_Equality("distinct", sort_bool))

        self.register("symbol", "ite",
                      Builtin_Function_ITE(sort_bool))

    def init_intreal(self):
        assert len(self.names) == 1

        kind_int = Kind("Int")
        self.register("kind", "Int", kind_int)

        kind_real = Kind("Real")
        self.register("kind", "Real", kind_real)

    def init_bv(self):
        assert len(self.names) == 1

        kind_bv = Kind_Parametric("BitVec", 1, indexed=True)
        self.register("kind", "BitVec", kind_bv)

    def init_float(self):
        assert len(self.names) == 1

        kind_float = Kind_Parametric("FloatingPoint", 2, True)
        self.register("kind", "FloatingPoint", kind_float)

        self.register("kind",
                      "Float16",
                      Kind_Alias("Float16", kind_float, [], [5, 11]))

        self.register("kind",
                      "Float32",
                      Kind_Alias("Float32", kind_float, [], [8, 24]))

        self.register("kind",
                      "Float64",
                      Kind_Alias("Float16", kind_float, [], [11, 53]))

        self.register("kind",
                      "Float128",
                      Kind_Alias("Float128", kind_float, [], [15, 113]))

        kind_rm = Kind("RoundingMode")
        self.register("kind", "RoundingMode", kind_rm)

        sort_rm    = Sort(kind_rm)
        sort_float = Polymorphic_Sort(kind_float)

        self.register("symbol", "fp.abs",
                      Builtin_Function("fp.abs",
                                       sort=sort_float,
                                       param_sort=[sort_float]))
        self.register("symbol", "fp.neg",
                      Builtin_Function("fp.neg",
                                       sort=sort_float,
                                       param_sort=[sort_float]))
        self.register("symbol", "fp.nextUp",
                      Builtin_Function("fp.nextUp",
                                       sort=sort_float,
                                       param_sort=[sort_float]))
        self.register("symbol", "fp.nextDown",
                      Builtin_Function("fp.nextDown",
                                       sort=sort_float,
                                       param_sort=[sort_float]))

        self.register("symbol", "fp.add",
                      Builtin_Function("fp.add",
                                       sort=sort_float,
                                       param_sort=[sort_rm,
                                                   sort_float, sort_float]))
        self.register("symbol", "fp.sub",
                      Builtin_Function("fp.sub",
                                       sort=sort_float,
                                       param_sort=[sort_rm,
                                                   sort_float, sort_float]))

    #######################################################################
    # Parsing
    #######################################################################

    def parse_attribute_value(self):
        self.next()
        if self.ct.type == "SYMBOL":
            return self.ct.value
        elif self.ct.type in SMT_Parser.SPEC_CONSTANT_TYPES:
            return self.ct.value
        else:
            raise ParseError("non-symbol attributes not supported yet",
                             self.ct)

    def parse_sort(self):
        self.match_set("SYMBOL", "BRA")

        def get_kind():
            name = self.ct.value
            kind = self.lookup("kind", name)
            if kind is None:
                raise ParseError("%s is not a valid sort" % name,
                                 self.ct)
            return name, kind

        if self.ct.type == "SYMBOL":
            name, kind = get_kind()
            if kind.arity > 0:
                raise ParseError("sort %s has arity %u, no parameters "
                                 "are supplied here" % (name,
                                                        kind.arity),
                                 self.ct)
            return Sort(kind, [])

        elif self.ct.type == "BRA":
            if self.nt.type == "RESERVED_WORD" and self.nt.value == "_":
                # actually just an indexed identifier
                self.match("RESERVED_WORD")
                self.match("SYMBOL")
                name, kind = get_kind()
                if not kind.is_indexed():
                    raise ParseError("%s is not indexed" % name, self.ct)
                index = []
                while self.nt.type != "KET":
                    self.match_set("SYMBOL", "NUMERAL")
                    if self.ct.type == "SYMBOL":
                        index.append(self.ct.value)
                    else:
                        index.append(int(self.ct.value))
                self.match("KET")
                if len(index) != kind.arity:
                    raise ParseError("expected %u indices for %s" % (kind.arity,
                                                                     name),
                                     self.ct)
                return Sort(kind, index)

            else:
                # a parametric sort
                self.match("SYMBOL")
                err_loc = self.ct
                name, kind = get_kind()
                if kind.is_indexed():
                    raise ParseError("%s is indexed" % name, err_loc)

                parm = []
                while self.nt.type != "KET":
                    parm.append(self.parse_sort())
                self.match("KET")

                if len(parm) != kind.arity:
                    raise ParseError("expected %u parameters for %s" %
                                     (kind.arity, name),
                                     self.ct)

                return Sort(kind, parm)

        raise ParseError("simple or parametric sort", self.ct)

    def parse_identifier(self):
        self.match_set("SYMBOL", "BRA")

        if self.ct.type == "SYMBOL":
            return Identifier(self.ct.value)

        elif self.ct.type == "BRA":
            self.match("RESERVED_WORD")
            if self.ct.value == "_":
                self.match("SYMBOL")
                name = self.ct.value
                index = []
                while self.nt.type != "KET":
                    self.match_set("SYMBOL", "NUMERAL")
                    if self.ct.type == "SYMBOL":
                        index.append(self.ct.value)
                    else:
                        index.append(int(self.ct.value))
                self.match("KET")
                return Indexed_Identifier(name, index)
            elif self.ct.value == "as":
                raise ParseError("qualified ident not supported yet", self.ct)
            else:
                raise ParseError("expected indexed or qualified identifier",
                                 self.ct)


    def parse_sorted_var(self):
        self.match("BRA")
        self.match("SYMBOL")
        symbol = Identifier(self.ct.value)
        sort   = self.parse_sort()
        self.match("KET")
        return Sorted_Var(symbol, sort)

    def parse_term(self):
        term = None
        if self.nt.type == "BRA":
            self.match("BRA")

            if self.nt.type == "RESERVED_WORD" and self.nt.value == "as":
                # qual_identifier
                self.next()
                ident = self.parse_identifier()
                sort = self.parse_sort()
                raise ParseError("qual_identifier not supported yet", self.ct)

            elif self.nt.type == "RESERVED_WORD" and self.nt.value == "let":
                raise ParseError("let binder not supported yet", self.nt)

            elif self.nt.type == "RESERVED_WORD" and \
                 self.nt.value in ("forall", "exists"):
                # quantification
                self.match("RESERVED_WORD")
                kind = self.ct.value

                self.push_scope()

                # sorted_var
                binding = []
                self.match("BRA")
                while self.nt.type != "KET":
                    binding.append(self.parse_sorted_var())
                self.match("KET")

                # body
                body = self.parse_term()

                self.pop_scope()

                term = Node_Quantification(kind, binding, body)

            elif self.nt.type == "RESERVED_WORD" and self.nt.value == "match":
                raise ParseError("match binder not supported yet", self.nt)

            elif self.nt.type == "RESERVED_WORD" and self.nt.value == "!":
                raise ParseError("term attribute not supported yet", self.nt)

            else:
                # function application
                fn_id = self.parse_identifier()
                fn = self.lookup("symbol", fn_id.name)
                if fn is None:
                    raise ParseError("unknown function symbol %s" % fn.name,
                                     self.ct)
                elif fn.arity != len(fn_id.index):
                    raise ParseError("indexed function %s needs %u indices" %
                                     (fn_id.name, fn.arity),
                                     self.ct)

                param = []
                while self.nt.type != "KET":
                    param.append(self.parse_term())

                if fn.attribute is None and len(param) != len(fn.param_sort):
                    raise ParseError("function %s needs %u parameters" %
                                     (fn_id.name, len(fn.param_sort)),
                                     self.ct)
                elif fn.attribute is not None and len(param) < len(fn.param_sort):
                    raise ParseError("function %s needs at least %u parameters" %
                                     (fn_id.name, len(fn.param_sort)),
                                     self.ct)

                term = Node_Function_Application(fn, param, fn_id.index)

            self.match("KET")

        elif self.nt.type == "NUMERAL":
            self.match("NUMERAL")
            term = Node_Literal_Numeral(self.ct.value)

        elif self.nt.type == "DECIMAL":
            self.match("DECIMAL")
            term = Node_Literal_Decimal(self.ct.value)

        elif self.nt.type in ("HEX", "BINARY"):
            self.match_set("HEX", "BINARY")
            term = Node_Literal_Bitvector(self.ct.value)

        elif self.nt.type == "STRING":
            self.match("STRING")
            term = Node_Literal_String(self.ct.value)

        elif self.nt.type == "SYMBOL":
            fn_id = self.parse_identifier()
            fn = self.lookup("symbol", fn_id.name)
            if fn is None:
                raise ParseError("unknown function symbol %s" % fn.name,
                                 self.ct)
            elif fn.arity != len(fn_id.index):
                raise ParseError("indexed function %s needs %u indices" %
                                 (fn_id.name, fn.arity),
                                 self.ct)
            elif fn.attribute is None and 0 != len(fn.param_sort):
                raise ParseError("function %s needs %u parameters" %
                                 (fn_id.name, len(fn.param_sort)),
                                 self.ct)
            elif fn.attribute is not None and 0 < len(fn.param_sort):
                raise ParseError("function %s needs at least %u parameters" %
                                 (fn_id.name, len(fn.param_sort)),
                                 self.ct)

            term = Node_Function_Application(fn, [], fn_id.index)

        else:
            raise ParseError("expected term", self.ct)

        return term


    def parse_command(self):
        n = None

        self.match("BRA")

        self.match("RESERVED_WORD")
        cmd = self.ct.value

        if cmd == "set-logic":
            self.match("SYMBOL")
            n = Node_Set_Logic(self.ct.value)

        elif cmd == "set-info":
            self.match("KEY_WORD")
            key = self.ct.value
            if self.nt.type != "KET":
                value = self.parse_attribute_value()
            else:
                value = None
            n = Node_Set_Info(key, value)

        elif cmd == "set-option":
            self.match("KEY_WORD")
            key = self.ct.value
            if self.nt.type != "KET":
                value = self.parse_attribute_value()
            else:
                value = None
            n = Node_Set_Option(key, value)

        elif cmd == "assert":
            term = self.parse_term()
            n = Node_Assert(term)

        elif cmd == "declare-sort":
            self.match("SYMBOL")
            name = self.ct.value
            self.match("NUMERAL")
            arity = int(self.ct.value)
            if arity > 0:
                kind = Kind_Parametric(name, arity)
            else:
                kind = Kind(name)
            self.register("kind", name, kind)
            n = Node_Declare_Sort(kind)

        elif cmd == "define-sort":
            # ( define-sort symbol ( symbol* ) sort )
            self.match("SYMBOL")
            name = self.ct.value
            self.push_scope()
            self.match("BRA")
            par = []
            while self.nt.type != "KET":
                self.match("SYMBOL")
                tp = Kind_Type_Parameter(self.ct.value)
                par.append(tp)
                self.register("kind", tp.name, tp)
            self.match("KET")
            sort = self.parse_sort()
            self.pop_scope()
            kind = Kind_Alias(name, sort.kind, par, sort.parameters)
            self.register("kind", name, kind)
            n = Node_Define_Sort(kind)

        elif cmd == "declare-fun":
            self.match("SYMBOL")
            name = self.ct.value
            self.match("BRA")
            params = []
            while self.nt.type != "KET":
                params.append(self.parse_sort())
            self.match("KET")
            sort = self.parse_sort()
            sym = Function(name, sort, params)
            self.register("symbol", name, sym)
            n = Node_Declare_Fun(sym)

        elif cmd == "declare-const":
            # ( declare-const symbol sort )
            self.match("SYMBOL")
            name = self.ct.value
            sort = self.parse_sort()
            sym = Function(name, sort)
            self.register("symbol", name, sym)
            n = Node_Declare_Fun(sym)

        elif cmd == "check-sat":
            n = Node_Check_Sat()

        elif cmd == "exit":
            n = Node_Exit()

        else:
            raise ParseError("unknown command `%s'" % cmd, self.ct)

        self.match("KET")

        return n

    def parse(self):
        self.code = []
        try:
            while self.nt is not None:
                e = self.parse_command()
                self.code.append(e)
        except MatchError, e:
            self.pp_error(e)
            print "=" * 80
            traceback.print_exc()
        except ParseError, e:
            self.pp_error(e)
            print "=" * 80
            traceback.print_exc()

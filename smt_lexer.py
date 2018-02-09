#!/usr/bin/env python
##############################################################################
##                                                                          ##
##                                PyMPF                                     ##
##                                                                          ##
##              Copyright (C) 2015-2018, Altran UK Limited                  ##
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

import ply.lex as lex

reserved_words = frozenset([
    # Language defined reserved words
    "_",
    "!",
    "as",
    "let",
    "exists",
    "forall",
    "match",
    "par",

    # Reserved words from the scripting language
    "assert",
    "check-sat",
    "check-sat-assuming",
    "declare-const",
    "declare-datatype",
    "declare-datatypes",
    "declare-fun",
    "declare-sort",
    "define-const", # a popular extension
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "echo",
    "exit",
    "get-assertions",
    "get-assignment",
    "get-info",
    "get-model",
    "get-option",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "get-value",
    "pop",
    "push",
    "reset",
    "reset-assertions",
    "set-info",
    "set-logic",
    "set-option",
])

class SMT_Lexer(object):
    tokens = (
        "BRA", "KET",
        "DECIMAL",
        "NUMERAL",
        "HEX",
        "BINARY",
        "STRING",
        "RESERVED_WORD",
        "KEY_WORD",
        "SYMBOL",
    )

    t_BRA     = r"\("
    t_KET     = r"\)"
    t_RESERVED_WORD = "|".join(map(lambda x: "(%s)" % x, reserved_words))

    t_ignore = " \t"

    def t_COMMENT(self, t):
        r";.*"

    def t_DECIMAL(self, t):
        r"(0|([1-9][0-9]*))\.[0-9]+"
        return t

    def t_NUMERAL(self, t):
        r"0|([1-9][0-9]*)"
        return t

    def t_HEX(self, t):
        r"\#x[0-9a-fA-F]+"
        return t

    def t_BINARY(self, t):
        r"\#b[01]+"
        return t

    def t_SYMBOL(self, t):
        r"([a-zA-Z0-9~!@$%&**_+=<>.?/^-][a-zA-Z0-9~!@$%&**_+=<>.?/^-]*)|(\|[^|]+\|)"
        if t.value in reserved_words:
            t.type = "RESERVED_WORD"
        elif t.value[0] == '|':
            t.value = t.value[1:-1]
        return t

    def t_KEY_WORD(self, t):
        r":[a-zA-Z0-9~!@$%&**_+=<>.?/^-][a-zA-Z0-9~!@$%&**_+=<>.?/^-]*"
        t.value = t.value[1:]
        return t

    def t_STRING(self, t):
        r'\"[^"]*\"' # TODO: Quoting

        # Chop the quotes
        t.value = t.value[1:-1]

        return t

    def t_newline(self, t):
        r"\n+"
        t.lexer.lineno += len(t.value)

    def t_error(self, t):
        print "Illegal character: '%s'" % t.value[0]
        t.lexer.skip(1)

    def tokenize(self, data):
        self.lexer.input(data)
        while True:
            tok = self.lexer.token()
            if tok is None:
                break
            yield tok

    def build(self, **kwargs):
        self.lexer = lex.lex(object=self, **kwargs)

    def __init__(self):
        self.build()

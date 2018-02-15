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

from pprint import pprint

from smt_lexer import SMT_Lexer
from smt_parser import SMT_Parser
from smt_tree import SMT_Context

p = SMT_Parser("test7.smt2")
p.parse()
for e in p.code:
    print e.to_smt(SMT_Context())
pprint(p.names)

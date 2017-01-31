#! /usr/bin/env python3

import sys

from parser.smtparser import SMTParser, SMTParseException

KIND_CONST     = "<const bool>"
KIND_CONSTB    = "<const bin>"
KIND_CONSTD    = "<const dec>"
KIND_CONSTN    = "<const num>"
KIND_CONSTH    = "<const hex>"
KIND_CONSTS    = "<const string>"

KIND_ANNOTN    = "!"
KIND_EXISTS    = "exists"
KIND_FORALL    = "forall"
KIND_LET       = "let"

KIND_AND       = "and"
KIND_IMPL      = "=>"
KIND_ITE       = "ite"
KIND_NOT       = "not"
KIND_OR        = "or"
KIND_XOR       = "xor"

KIND_EQ        = "="
KIND_DIST      = "distinct"
KIND_LE        = "<="
KIND_LT        = "<"
KIND_GE        = ">="
KIND_GT        = ">"

KIND_ABS       = "abs"
KIND_ADD       = "+"
KIND_DIV       = "div"
KIND_MOD       = "mod"
KIND_MUL       = "*"
KIND_NEG       = "neg"
KIND_SUB       = "-"
KIND_RDIV      = "/"

KIND_ISI       = "is_int"
KIND_TOI       = "to_int"
KIND_TOR       = "to_real"

KIND_CONC      = "concat"
KIND_EXTR      = "extract"
KIND_REP       = "repeat"
KIND_ROL       = "rotate_left"
KIND_ROR       = "rotate_right"
KIND_SEXT      = "sign_extend"
KIND_ZEXT      = "zero_extend"

KIND_BVADD     = "bvadd"
KIND_BVAND     = "bvand"
KIND_BVASHR    = "bvashr"
KIND_BVCOMP    = "bvcomp"
KIND_BVLSHR    = "bvlshr"
KIND_BVMUL     = "bvmul"
KIND_BVNAND    = "bvnand"
KIND_BVNEG     = "bvneg"
KIND_BVNOR     = "bvnor"
KIND_BVNOT     = "bvnot"
KIND_BVOR      = "bvor"
KIND_BVSDIV    = "bvsdiv"
KIND_BVSGE     = "bvsge"
KIND_BVSGT     = "bvsgt"
KIND_BVSHL     = "bvshl"
KIND_BVSLE     = "bvsle"
KIND_BVSLT     = "bvslt"
KIND_BVSMOD    = "bvsmod"
KIND_BVSREM    = "bvsrem"
KIND_BVSUB     = "bvsub"
KIND_BVUGE     = "bvuge"
KIND_BVUGT     = "bvugt"
KIND_BVUDIV    = "bvudiv"
KIND_BVULE     = "bvule"
KIND_BVULT     = "bvult"
KIND_BVUREM    = "bvurem"
KIND_BVXNOR    = "bvxnor"
KIND_BVXOR     = "bvxor"

KIND_SELECT    = "select"
KIND_STORE     = "store"

KIND_ASSERT    = "assert"
KIND_CHECKSAT  = "check-sat"
KIND_DECLFUN   = "declare-fun"
KIND_DEFFUN    = "define-fun"
KIND_DECLSORT  = "declare-sort"
KIND_DEFSORT   = "define-sort"
KIND_GETASSERT = "get-assertions"
KIND_GETASSIGN = "get-assignment"
KIND_GETPROOF  = "get-proof"
KIND_GETUCORE  = "get-unsat-core"
KIND_GETVALUE  = "get-value"
KIND_GETOPT    = "get-option"
KIND_GETINFO   = "get-info"
KIND_EXIT      = "exit"
KIND_PUSH      = "push"
KIND_POP       = "pop"
KIND_SETLOGIC  = "set-logic"
KIND_SETINFO   = "set-info"
KIND_SETOPT    = "set-option"


g_const_kinds = \
    [ KIND_CONST, KIND_CONSTB, KIND_CONSTD, KIND_CONSTN, KIND_CONSTH, 
      KIND_CONSTS ]

g_fun_kinds   = \
    [ KIND_ABS,    KIND_ADD,    KIND_AND,    KIND_BVADD,  KIND_BVAND,
      KIND_BVASHR, KIND_BVCOMP, KIND_BVLSHR, KIND_BVMUL,  KIND_BVNAND, 
      KIND_BVNEG,  KIND_BVNOR,  KIND_BVNOT,  KIND_BVOR,   KIND_BVSDIV,
      KIND_BVSGE,  KIND_BVSGT,  KIND_BVSHL,  KIND_BVSLE,  KIND_BVSLT, 
      KIND_BVSMOD, KIND_BVSREM, KIND_BVSUB,  KIND_BVUGE,  KIND_BVUGT,
      KIND_BVUDIV, KIND_BVULE,  KIND_BVULT,  KIND_BVUREM, KIND_BVXNOR, 
      KIND_BVXOR,  KIND_CONC,   KIND_DIST,   KIND_DIV,    KIND_EQ,
      KIND_EXTR,   KIND_GE,     KIND_GT,     KIND_IMPL,   KIND_ISI,
      KIND_ITE,    KIND_LE,     KIND_LT,     KIND_MOD,    KIND_MUL,
      KIND_NEG,    KIND_NOT,    KIND_OR,     KIND_RDIV,   KIND_REP,
      KIND_ROL,    KIND_ROR,    KIND_SELECT, KIND_SEXT,   KIND_STORE,
      KIND_SUB,    KIND_TOI,    KIND_TOR,    KIND_XOR,    KIND_ZEXT]

g_cmd_kinds   = \
    [ KIND_ASSERT,   KIND_CHECKSAT, KIND_DECLFUN,   KIND_DEFFUN, 
      KIND_DECLSORT, KIND_DEFSORT,  KIND_GETASSERT, KIND_GETASSIGN, 
      KIND_GETPROOF, KIND_GETUCORE, KIND_GETVALUE,  KIND_GETOPT,
      KIND_GETINFO,  KIND_EXIT,     KIND_PUSH,      KIND_POP,
      KIND_SETLOGIC, KIND_SETINFO,  KIND_SETOPT ]

class SMTAnalyzeParser(SMTParser):

    def __init__ (self):
        super().__init__()
        self.__set_parse_actions()
        self.consts = set() 
        self.symbols = set() 
        self.sorts = set()
        self.funs = {}
        self.nasserts = 0
        self.ndeclfuns = 0

    def __symbol(self, t):
        if t[0] in g_fun_kinds:
            if not t[0] in self.funs:
                self.funs[t[0]] = 0
            self.funs[t[0]] += 1
        return t

    def __sort (self, t):
        return t

    def __sort_expr (self, t):
        return t

    def __print(self, t, cnt = 1):
        print(t)
        return t

    def __command(self, t):
        k = t[0]
        if k == KIND_ASSERT:
            self.nasserts += 1
        elif k == KIND_DECLFUN:
            self.ndeclfuns += 1
        return t

    def __set_parse_actions (self):
        try:
            self.numeral.set_parse_action (lambda t: int(t[0]))
            self.decimal.set_parse_action (lambda t: float(t[0]))
            self.hexadecimal.set_parse_action (lambda t: hex(t[2:]))
            self.binary.set_parse_action (lambda t: bin(t[2:]))
            self.string.set_parse_action (lambda t: str(t))
            self.b_value.set_parse_action (lambda t: str(t))
            self.symbol.set_parse_action (self.__symbol)#lambda t: str(t))
            self.keyword.set_parse_action (lambda t: str(t))
            self.spec_constant.set_parse_action (lambda t: t[0])
#            self.s_expr.set_parse_action (self.__print)
#            self.ident.set_parse_action (lambda t: t)
#            self.sort.set_parse_action (self.__sort)
#            self.sort_expr.set_parse_action (self.__sort_expr)
#            self.attr_value.set_parse_action (self.__print)
#            self.attribute.set_parse_action (self.__print)
#            self.qual_ident.set_parse_action (self.__print)
#            self.var_binding.set_parse_action (self.__print)
#            self.sorted_var.set_parse_action (self.__print)
#            self.sorted_qvar.set_parse_action (self.__print)
#            self.var_bindings.set_parse_action (self.__print)
#            self.sorted_qvars.set_parse_action (self.__print)
#            self.term.set_parse_action (self.__term)
#            self.option.set_parse_action (self.__print)
            self.command.set_parse_action (self.__command)

        except DDSMTParseCheckException as e:
            raise DDSMTParseException (e.msg, e.parser)



if __name__ == "__main__":

    if len(sys.argv) != 2:
        sys.exit("no SMT input file given")

    parser = SMTAnalyzeParser() 

    parser.parse(sys.argv[1])

    print("assertions: {}".format(parser.nasserts))
    print("declfuns: {}".format(parser.ndeclfuns))
    
    print("operations:")
    for v, k in sorted([(v, k) for k,v in parser.funs.items()]):
        print("  {0:7s}: {1:d}".format(k, v))

    sys.exit(0)

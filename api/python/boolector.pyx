# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2013-2014 Mathias Preiner.
#
# All rights reserved.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

cimport btorapi
from libc.stdlib cimport malloc, free
from libc.stdio cimport stdout, FILE, fopen, fclose
import math, os

g_tunable_options = {"rewrite_level", "rewrite_level_pbr",
                     "beta_reduce_all", "probe_beta_reduce_all",
                     "pbra_lod_limit", "pbra_sat_limit", "pbra_ops_factor",
                     "dual_prop", "just", "ucopt", }

class BoolectorException(Exception):
    
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "[pybtor] {}".format(self.msg)

cdef class BoolectorOpt:
    cdef Boolector btor
    cdef const btorapi.BtorOpt* _c_opt

    def __init__(self, Boolector boolector):
        self.btor = boolector

    property internal:
        def __get__(self):
            return self._c_opt.internal == 1

    property shrt:
        def __get__(self):
            cdef bytes py_str = self._c_opt.shrt
            return py_str.decode()

    property lng:
        def __get__(self):
            cdef bytes py_str = self._c_opt.lng
            return py_str.decode()

    property desc:
        def __get__(self):
            cdef bytes py_str = self._c_opt.desc
            return py_str.decode()

    property val:
        def __get__(self):
            return self._c_opt.val

    property dflt:
        def __get__(self):
            return self._c_opt.dflt

    property min:
        def __get__(self):
            return self._c_opt.min

    property max:
        def __get__(self):
            return self._c_opt.max

    property tunable:
        def __get__(self):
            return self.lng in g_tunable_options

    def __str__(self):
        return "{}, {}, [{}, {}], default: {}".format(self.lng, self.tunable,
                                                      self.min, self.max,
                                                      self.dflt)

cdef class BoolectorSort:
    cdef Boolector btor
    cdef btorapi.Btor* _c_btor
    cdef btorapi.BoolectorSort* _c_sort

    def __init__(self, Boolector boolector):
        self.btor = boolector

    def __dealloc__(self):
        btorapi.boolector_release_sort(self.btor._c_btor, self._c_sort)


cdef class BoolectorNode:
    cdef Boolector btor
    cdef btorapi.Btor* _c_btor
    cdef btorapi.BoolectorNode* _c_node

    def __init__(self, Boolector boolector):
        self.btor = boolector

    def __dealloc__(self):
        btorapi.boolector_release(self.btor._c_btor, self._c_node)

    def __richcmp__(BoolectorNode x, BoolectorNode y, opcode):
        if opcode == 2:
            return x.btor.Eq(x, y)
        elif opcode == 3:
            return x.btor.Ne(x, y)
        else:
            raise BoolectorException("opcode '{}' not implemented for "\
                                     "__richcmp__".format(opcode))

    def dump(self, format="btor", outfile = ""):
        if format.lower() == "btor":
            btorapi.boolector_dump_btor_node(self.btor._c_btor, stdout,
                                             self._c_node)
        elif format.lower() == "smt1":
            btorapi.boolector_dump_smt1_node(self.btor._c_btor, stdout,
                                             self._c_node)
        elif format.lower() == "smt2":
            btorapi.boolector_dump_smt2_node(self.btor._c_btor, stdout,
                                             self._c_node)
        else:
            raise BoolectorException("invalid dump format '{}'".format(format)) 

    def symbol(self):
        cdef bytes py_str = btorapi.boolector_get_symbol_of_var(
                                self.btor._c_btor, self._c_node)
        return py_str.decode()

    def assignment(self):
        cdef char** c_str_i
        cdef char** c_str_v
        cdef int size
        cdef const char* c_str
        cdef bytes py_str

        if isinstance(self, BoolectorFunNode) or \
           isinstance(self, BoolectorArrayNode):
            btorapi.boolector_array_assignment(self.btor._c_btor,
                                               self._c_node,
                                               &c_str_i, &c_str_v, &size) 
            model = []
            if size > 0:
                for i in range(size):
                    py_str = c_str_i[i]
                    index = py_str.decode()
                    py_str = c_str_v[i]
                    value = py_str.decode()
                    model.append((index, value))
                btorapi.boolector_free_array_assignment(self.btor._c_btor,
                                                        c_str_i, c_str_v, size) 
            return model
        else:
            c_str = \
                btorapi.boolector_bv_assignment(self.btor._c_btor,
                                                   self._c_node)
            py_str = c_str
            btorapi.boolector_free_bv_assignment(self.btor._c_btor, c_str)
            return py_str.decode()

    def width(self):
        return btorapi.boolector_get_width(self.btor._c_btor, self._c_node)


cdef class BoolectorBVNode(BoolectorNode):

    def __richcmp__(x, y, opcode):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x

        b = (<BoolectorBVNode> x).btor
        if isinstance(y, int):
            y = b.Int(y, (<BoolectorBVNode> x).width())

        if opcode == 0:
            return b.Ult(x, y)
        elif opcode == 1:
            return b.Ulte(x, y)
        elif opcode == 2:
            return b.Eq(x, y)
        elif opcode == 3:
            return b.Ne(x, y)
        elif opcode == 4:
            return b.Ugt(x, y)
        elif opcode == 5:
            return b.Ugte(x, y)
        else:
            raise BoolectorException("opcode '{}' not implemented for "\
                                     "__richcmp__".format(opcode))

    def __neg__(self):
        return self.btor.Neg(self)

    def __invert__(self):
        return self.btor.Not(self)

    def __add__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Add(x, y)

    def __sub__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Sub(x, y)

    def __mul__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Mul(x, y)

    def __div__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Sdiv(x, y)

    def __mod__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Srem(x, y)

    def __lshift__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x = (<BoolectorBVNode> y).btor.Int(x,
                    2**(<BoolectorBVNode> y).width())
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y,
                    math.log((<BoolectorBVNode> x).width(), 2))
        return (<BoolectorBVNode> x).btor.Sll(x, y)

    def __rshift__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Srl(x, y)

    def __and__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.And(x, y)

    def __or__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Or(x, y)

    def __xor__(x, y):
        assert(isinstance(x, BoolectorBVNode) or isinstance(y, BoolectorBVNode))
        if isinstance(x, int):
            x, y = y, x
        if isinstance(y, int):
            y = (<BoolectorBVNode> x).btor.Int(y, (<BoolectorBVNode> x).width())
        return (<BoolectorBVNode> x).btor.Xor(x, y)


cdef class BoolectorArrayNode(BoolectorNode):

    def __getitem__(self, index):
        return self.btor.Read(self, index)

    def index_width(self):
        return btorapi.boolector_get_index_width(self.btor._c_btor,
                   self._c_node)


cdef class BoolectorFunNode(BoolectorNode):

    def __call__(self, *args):
        return self.btor.Apply(list(args), self)

    def arity(self):
        return \
            btorapi.boolector_get_fun_arity(self.btor._c_btor, self._c_node)


cdef class Boolector:
    cdef btorapi.Btor* _c_btor
    UNKNOWN = 0
    SAT = 10
    UNSAT = 20

    def __init__(self, Boolector parent = None):
        if parent is None:
            self._c_btor = btorapi.boolector_new()
        else:
            self._c_btor = btorapi.boolector_clone(parent._c_btor)
            btorapi.boolector_set_opt(self._c_btor,
                                      "force_internal_cleanup", 1);
        if self._c_btor is NULL:
            raise MemoryError()

    def __dealloc__(self):
        if self._c_btor is not NULL:
            btorapi.boolector_delete(self._c_btor)

    # Boolector API functions (general)

    def Assert(self, BoolectorNode n):
        btorapi.boolector_assert(self._c_btor, n._c_node)

    def Assume(self, BoolectorNode n):
        btorapi.boolector_assume(self._c_btor, n._c_node)

    def Failed(self, BoolectorNode n):
        return btorapi.boolector_failed(self._c_btor, n._c_node) == 1

    def Simplify(self):
        return btorapi.boolector_simplify(self._c_btor)

    def Sat(self, lod_limit = -1, sat_limit = -1):
        if lod_limit > 0 or sat_limit > 0:
            return btorapi.boolector_limited_sat(self._c_btor, lod_limit,
                                                 sat_limit)
        return btorapi.boolector_sat(self._c_btor)

    def Clone(self):
        return Boolector(self)

#    def Find(self, BoolectorNode node):
#        if isinstance(node, BoolectorBVNode):
#            r = BoolectorBVNode(self)
#        elif isinstance(node, BoolectorArrayNode):
#            r = BoolectorArrayNode(self)
#        elif isinstance(node, BoolectorFunNode):
#            r = BoolectorFunNode(self)
#        r._c_node = btorapi.boolector_copy(self._c_btor,
#                        btorapi.boolector_find_node(self._c_btor, node._c_node))
#        return r

    # Boolector options
    def Set_opt(self, str opt, int value):
        cdef bytes b_str = opt.encode()
        cdef const char* c_str = b_str
        btorapi.boolector_set_opt(self._c_btor, c_str, value)

    def Get_opt(self, str opt):
        cdef bytes b_str = opt.encode()
        cdef const char* c_str = b_str
        r = BoolectorOpt(self)
        r._c_opt = btorapi.boolector_get_opt(self._c_btor, c_str)
        return r

    def Options(self):
        opts = []
        cdef const btorapi.BtorOpt* c_opt
        cdef const btorapi.BtorOpt* c_last_opt
        c_opt = btorapi.boolector_first_opt(self._c_btor)
        c_last_opt = btorapi.boolector_last_opt(self._c_btor)
        while c_opt != c_last_opt:
            o = BoolectorOpt(self)
            o._c_opt = c_opt
            if not o.internal:
                opts.append(o)
            c_opt = btorapi.boolector_next_opt(self._c_btor, c_opt)
        return opts

    def Set_sat_solver(self, str solver, str optstr="", int nofork=0):
        cdef bytes b_str = solver.encode()
        cdef char* c_str = b_str
        cdef bytes b_optstr = optstr.encode()
        cdef const char* c_optstr = b_optstr
        if optstr == "":
            c_optstr = NULL
        btorapi.boolector_set_sat_solver(self._c_btor, c_str, c_optstr, nofork)

    def Set_msg_prefix(self, str prefix):
        cdef bytes b_str = prefix.encode()
        cdef char* c_str = b_str
        btorapi.boolector_set_msg_prefix(self._c_btor, c_str)

    def Print_model(self, outfile=""):
        cdef FILE* c_file
        cdef bytes b_str = outfile.encode()
        cdef char* c_str = b_str

        if outfile == "":
            c_file = stdout
        else:
            if os.path.isfile(outfile):
                raise BoolectorException(
                        "Outfile '{}' already exists".format(outfile)) 
            elif os.path.isdir(outfile):
                raise BoolectorException(
                        "Outfile '{}' is a directory".format(outfile)) 
            c_file = fopen(c_str, "w")

        btorapi.boolector_print_model(self._c_btor, c_file)

        if outfile != "":
            fclose(c_file)

    def Parse(self, str file):
        cdef FILE* c_file
        cdef bytes b_str = file.encode()
        cdef char* c_str = b_str
        cdef int res
        cdef char* err_msg
        cdef int status

        if not os.path.isfile(file):
            raise BoolectorException("File '{}' does not exist".format(file))

        c_file = fopen(c_str, "r")
        res = btorapi.boolector_parse(self._c_btor, c_file, c_str, &err_msg,
                                      &status)
        fclose(c_file)
        cdef bytes b_err_msg = err_msg
        return (res, status, b_err_msg.decode())

    def Dump(self, format = "btor", outfile = ""):
        cdef FILE* c_file
        cdef bytes b_str = outfile.encode()
        cdef char* c_str = b_str 

        if outfile == "":
            c_file = stdout
        else:
            if os.path.isfile(outfile):
                raise BoolectorException(
                        "Outfile '{}' already exists".format(outfile)) 
            elif os.path.isdir(outfile):
                raise BoolectorException(
                        "Outfile '{}' is a directory".format(outfile)) 
            c_file = fopen(c_str, "w")

        if format.lower() == "btor":
            btorapi.boolector_dump_btor(self._c_btor, c_file)
        elif format.lower() == "smt1":
            btorapi.boolector_dump_smt1(self._c_btor, c_file)
        elif format.lower() == "smt2":
            btorapi.boolector_dump_smt2(self._c_btor, c_file)
        else:
            raise BoolectorException("invalid dump format '{}'".format(format)) 
        if outfile != "":
            fclose(c_file)

    # Boolector nodes

    def Const(self, str bits):
        cdef bytes b_str = bits.encode()
        cdef char* c_str = b_str
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_const(self._c_btor, c_str)
        return r

    def Zero(self, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_zero(self._c_btor, width)
        return r

    def Ones(self, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ones(self._c_btor, width)
        return r

    def TRUE(self):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_true(self._c_btor)
        return r

    def FALSE(self):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_false(self._c_btor)
        return r

    def One(self, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_one(self._c_btor, width)
        return r

    def Uint(self, unsigned int i, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_unsigned_int(self._c_btor, i, width)
        return r

    def Int(self, int i, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_int(self._c_btor, i, width)
        return r

    def Var(self, int width, str symbol = ""):
        cdef bytes b_str = symbol.encode()
        cdef char* c_str = b_str
        if symbol == "":
            c_str = NULL 
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_var(self._c_btor, width, c_str)
        return r

    def Param(self, int width, str symbol = ""):
        cdef bytes b_str = symbol.encode()
        cdef char* c_str = b_str
        if symbol == "":
            c_str = NULL 
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_param(self._c_btor, width, c_str)
        return r

    def Array(self, int elem_width, int index_width, str symbol = ""):
        cdef bytes b_str = symbol.encode()
        cdef char* c_str = b_str
        if symbol == "":
            c_str = NULL 
        r = BoolectorArrayNode(self)
        r._c_node = btorapi.boolector_array(self._c_btor, elem_width,
                                                 index_width, c_str)
        return r

    # Unary operators

    def Not(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_not(self._c_btor, n._c_node)
        return r

    def Neg(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_neg(self._c_btor, n._c_node)
        return r

    def Redor(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_redor(self._c_btor, n._c_node)
        return r

    def Redxor(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_redxor(self._c_btor, n._c_node)
        return r

    def Redand(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_redand(self._c_btor, n._c_node)
        return r

    def Slice(self, BoolectorBVNode n, int upper, int lower):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_slice(self._c_btor, n._c_node,
                                                 upper, lower)
        return r
                                                                
    def Uext(self, BoolectorBVNode n, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_uext(self._c_btor, n._c_node, width)
        return r

    def Sext(self, BoolectorBVNode n, int width):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sext(self._c_btor, n._c_node, width)
        return r

    def Inc(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_inc(self._c_btor, n._c_node)
        return r

    def Dec(self, BoolectorBVNode n):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_dec(self._c_btor, n._c_node)
        return r

    # Binary operators

    def Implies(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_implies(self._c_btor, a._c_node, b._c_node)
        return r

    def Iff(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_iff(self._c_btor, a._c_node, b._c_node)
        return r

    def Xor(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_xor(self._c_btor, a._c_node, b._c_node)
        return r

    def Xnor(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_xnor(self._c_btor, a._c_node, b._c_node)
        return r

    def And(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_and(self._c_btor, a._c_node, b._c_node)
        return r

    def Nand(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_nand(self._c_btor, a._c_node, b._c_node)
        return r

    def Or(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_or(self._c_btor, a._c_node, b._c_node)
        return r

    def Nor(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_nor(self._c_btor, a._c_node, b._c_node)
        return r

    def Eq(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_eq(self._c_btor, a._c_node, b._c_node)
        return r

    def Ne(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ne(self._c_btor, a._c_node, b._c_node)
        return r

    def Add(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_add(self._c_btor, a._c_node, b._c_node)
        return r

    def Uaddo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_uaddo(self._c_btor, a._c_node, b._c_node)
        return r

    def Saddo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_saddo(self._c_btor, a._c_node, b._c_node)
        return r

    def Mul(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_mul(self._c_btor, a._c_node, b._c_node)
        return r

    def Umulo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_umulo(self._c_btor, a._c_node, b._c_node)
        return r

    def Smulo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_smulo(self._c_btor, a._c_node, b._c_node)
        return r

    def Ult(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ult(self._c_btor, a._c_node, b._c_node)
        return r

    def Slt(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_slt(self._c_btor, a._c_node, b._c_node)
        return r

    def Ulte(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_ulte(self._c_btor, a._c_node, b._c_node)
        return r

    def Slte(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_slte(self._c_btor, a._c_node, b._c_node)
        return r

    def Ugt(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ugt(self._c_btor, a._c_node, b._c_node)
        return r

    def Sgt(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sgt(self._c_btor, a._c_node, b._c_node)
        return r

    def Ugte(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_ugte(self._c_btor, a._c_node, b._c_node)
        return r

    def Sgte(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_sgte(self._c_btor, a._c_node, b._c_node)
        return r

    def Sll(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sll(self._c_btor, a._c_node, b._c_node)
        return r

    def Srl(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_srl(self._c_btor, a._c_node, b._c_node)
        return r

    def Sra(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sra(self._c_btor, a._c_node, b._c_node)
        return r

    def Rol(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_rol(self._c_btor, a._c_node, b._c_node)
        return r

    def Ror(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ror(self._c_btor, a._c_node, b._c_node)
        return r

    def Sub(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sub(self._c_btor, a._c_node, b._c_node)
        return r

    def Usubo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_usubo(self._c_btor, a._c_node, b._c_node)
        return r

    def Ssubo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_ssubo(self._c_btor, a._c_node, b._c_node)
        return r

    def Udiv(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_udiv(self._c_btor, a._c_node, b._c_node)
        return r

    def Sdiv(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_sdiv(self._c_btor, a._c_node, b._c_node)
        return r

    def Sdivo(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_sdivo(self._c_btor, a._c_node, b._c_node)
        return r

    def Urem(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_urem(self._c_btor, a._c_node, b._c_node)
        return r

    def Srem(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_srem(self._c_btor, a._c_node, b._c_node)
        return r

    def Smod(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_smod(self._c_btor, a._c_node, b._c_node)
        return r

    def Concat(self, BoolectorBVNode a, BoolectorBVNode b):
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_concat(self._c_btor, a._c_node, b._c_node)
        return r

    def Read(self, BoolectorArrayNode a, b):
        if isinstance(b, int):
            b = self.Int(b, a.index_width())
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_read(self._c_btor, a._c_node,
                                   (<BoolectorBVNode> b)._c_node)
        return r

    # Ternary operators

    def Write(self, BoolectorArrayNode array, index, value):
        if isinstance(index, int):
            index = self.Int(index, array.index_width())

        if isinstance(value, int):
            value = self.Int(value, array.width())

        r = BoolectorArrayNode(self)
        r._c_node = \
            btorapi.boolector_write(self._c_btor, array._c_node,
                                    (<BoolectorBVNode> index)._c_node,
                                    (<BoolectorBVNode> value)._c_node)
        return r

    def Cond(self, BoolectorBVNode cond, BoolectorNode a, BoolectorNode b):
        if isinstance(a, BoolectorBVNode):
            r = BoolectorBVNode(self)
        else:
            assert(isinstance(a, BoolectorArrayNode))
            r = BoolectorArrayNode(self)
        r._c_node = \
            btorapi.boolector_cond(self._c_btor, cond._c_node, a._c_node,
                                      b._c_node)
        return r

    # Functions

    def Fun(self, list params, BoolectorBVNode body):
        cdef int paramc = len(params)
        cdef btorapi.BoolectorNode** c_params = \
            <btorapi.BoolectorNode**> \
                malloc(paramc * sizeof(btorapi.BoolectorNode*))

        # copy params into array
        for i in range(paramc):
            assert(isinstance(params[i], BoolectorNode))
            c_params[i] = (<BoolectorNode> params[i])._c_node

        r = BoolectorFunNode(self)
        r._c_node = \
            btorapi.boolector_fun(self._c_btor, paramc, c_params,
                                     body._c_node)

        free(c_params)
        return r

    def UF(self, BoolectorSort sort, str symbol = ""):
        cdef bytes b_str = symbol.encode()
        cdef char* c_str = b_str
        if symbol == "":
            c_str = NULL 
        r = BoolectorFunNode(self)
        r._c_node = btorapi.boolector_uf(self._c_btor, sort._c_sort, c_str)
        return r

    def Apply(self, list args, BoolectorFunNode fun):
        cdef int argc = len(args)
        cdef btorapi.BoolectorNode** c_args = \
            <btorapi.BoolectorNode**> \
	      malloc(argc * sizeof(btorapi.BoolectorNode*))

        # copy arguments into array
        for i in range(argc):
            assert(isinstance(args[i], BoolectorNode))
            c_args[i] = (<BoolectorNode> args[i])._c_node

        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_apply(self._c_btor, argc, c_args, fun._c_node)
        free(c_args)
        return r

    # Sorts

    def BitVecSort(self, int width):
        r = BoolectorSort(self)
        r._c_sort = btorapi.boolector_bitvec_sort(self._c_btor, width)
        return r

    def TupleSort(self, list sorts):
        cdef int num_elements = len(sorts)
        cdef btorapi.BoolectorSort** c_sorts = \
            <btorapi.BoolectorSort**> \
                malloc(num_elements * sizeof(btorapi.BoolectorSort*))

        for i in range(num_elements):
            assert(isinstance(sorts[i], BoolectorSort))
            c_sorts[i] = (<BoolectorSort> sorts[i])._c_sort

        r = BoolectorSort(self)
        r._c_sort = \
            btorapi.boolector_tuple_sort(self._c_btor, c_sorts, num_elements)
        free(c_sorts)
        return r

    def FunSort(self, BoolectorSort domain, BoolectorSort codomain):
        r = BoolectorSort(self)
        r._c_sort = btorapi.boolector_fun_sort(self._c_btor, domain._c_sort,
                                               codomain._c_sort)
        return r

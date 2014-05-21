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
from libc.stdio cimport stdout, FILE

BOOLECTOR_UNKNOWN = 0
BOOLECTOR_SAT = 10
BOOLECTOR_UNSAT = 20

# TODO: exceptions instead of assertions

cdef class BoolectorNode:
    cdef Boolector btor
    cdef btorapi.Btor* _c_btor
    cdef btorapi.BoolectorNode* _c_node

    def __richcmp__(BoolectorNode x, BoolectorNode y, opcode):
        if opcode == 0:
            return x.btor.Ult(x, y)
        elif opcode == 1:
            return x.btor.Ulte(x, y)
        elif opcode == 2:
            return x.btor.Eq(x, y)
        elif opcode == 3:
            return x.btor.Ne(x, y)
        elif opcode == 4:
            return x.btor.Ugt(x, y)
        else:
            assert(opcode == 5)
            return x.btor.Ugte(x, y)

    def __init__(self, Boolector boolector):
        self.btor = boolector

    def __dealloc__(self):
        btorapi.boolector_release(self.btor._c_btor, self._c_node)

    # Operator overloading methods

    # Create apply node if function is called
    # TODO: type 
    def __call__(self, *args):
        assert(self.is_fun())
        return self.btor.Apply(list(args), self)

    # Create read node if array is indexed
    def __getitem__(self, BoolectorNode index):
        assert(self.is_array())
        return self.btor.Read(self, index)

    def __len__(self):
        return btorapi.boolector_get_width(self.btor._c_btor, self._c_node)

    # Arithmetic operators

    def __neg__(self):
        return self.btor.Neg(self)

    def __invert__(self):
        return self.btor.Not(self)

    def __add__(BoolectorNode x, BoolectorNode y):
        return x.btor.Add(x, y)

    def __sub__(BoolectorNode x, BoolectorNode y):
        return x.btor.Sub(x, y)

    def __mul__(BoolectorNode x, BoolectorNode y):
        return x.btor.Mul(x, y)

    def __div__(BoolectorNode x, BoolectorNode y):
        return x.btor.Sdiv(x, y)

    def __lshift__(BoolectorNode x, BoolectorNode y):
        return x.btor.Sll(x, y)

    def __rshift__(BoolectorNode x, BoolectorNode y):
        return x.btor.Srl(x, y)

    def __and__(BoolectorNode x, BoolectorNode y):
        return x.btor.And(x, y)

    def __and__(BoolectorNode x, BoolectorNode y):
        return x.btor.And(x, y)

    def __or__(BoolectorNode x, BoolectorNode y):
        return x.btor.Or(x, y)

    def __xor__(BoolectorNode x, BoolectorNode y):
        return x.btor.Xor(x, y)

    # BoolectorNode methods

    def to_btor(self, outfile = ""):
      btorapi.boolector_dump_btor_node(self.btor._c_btor, stdout, self._c_node)

    def copy(self):
        r = BoolectorNode(self.btor)
        r._c_node = btorapi.boolector_copy(self.btor._c_btor, self._c_node)
        return r

    def is_array(self):
        return \
            btorapi.boolector_is_array(self.btor._c_btor, self._c_node) == 1

    def is_array_var(self):
        return \
            btorapi.boolector_is_array_var(self.btor._c_btor, self._c_node) == 1

    def is_fun(self):
        return btorapi.boolector_is_fun(self.btor._c_btor, self._c_node) == 1

    def is_param(self):
        return btorapi.boolector_is_param(self.btor._c_btor, self._c_node) == 1

    def is_bound_param(self):
        return btorapi.boolector_is_bound_param(self.btor._c_btor,
                                                self._c_node) == 1

    def arity(self):
        return \
            btorapi.boolector_get_fun_arity(self.btor._c_btor, self._c_node)

    def width(self):
        return btorapi.boolector_get_width(self.btor._c_btor, self._c_node)

    def index_width(self):
        return btorapi.boolector_get_index_width(self.btor._c_btor,
                   self._c_node)

    def symbol(self):
        cdef bytes py_str = btorapi.boolector_get_symbol_of_var(
                                self.btor._c_btor, self._c_node)
        return py_str

    def assignment(self):
        cdef char** c_str_i
        cdef char** c_str_v
        cdef int size
        cdef const char* c_str
        cdef bytes py_str

        if self.is_array():
            btorapi.boolector_array_assignment(self.btor._c_btor,
                                                  self._c_node,
                                                  &c_str_i, &c_str_v, &size) 
            indices = []
            values = []
            for i in range(size):
                py_str = c_str_i[i]
                indices.append(py_str.decode())
                py_str = c_str_v[i]
                values.append(py_str.decode())
            btorapi.boolector_free_array_assignment(self.btor._c_btor,
                                                       c_str_i, c_str_v, size) 
            return [indices, values]
        else:
            c_str = \
                btorapi.boolector_bv_assignment(self.btor._c_btor,
                                                   self._c_node)
            py_str = c_str
            btorapi.boolector_free_bv_assignment(self.btor._c_btor, c_str)
            return py_str.decode()


cdef class Boolector:
    cdef btorapi.Btor* _c_btor

    def __init__(self, Boolector parent = None):
        if parent is None:
            self._c_btor = btorapi.boolector_new()
        else:
            self._c_btor = btorapi.boolector_clone(parent._c_btor)
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

    def Simplify(self):
        return btorapi.boolector_simplify(self._c_btor)

    def Sat(self):
        return btorapi.boolector_sat(self._c_btor)

    def Clone(self):
        return Boolector(self)

    def Enable_model_gen(self):
        btorapi.boolector_enable_model_gen(self._c_btor)

    def Generate_model_for_all_reads(self):
        btorapi.boolector_generate_model_for_all_reads(self._c_btor)

    def Enable_inc_usage(self):
        btorapi.boolector_enable_inc_usage(self._c_btor)

    def Enable_beta_reduce_all(self):
        btorapi.boolector_enable_beta_reduce_all(self._c_btor)

    def Set_sat_solver(self, str solver):
        cdef bytes b_str = solver.encode()
        cdef char* c_str = b_str
        btorapi.boolector_set_sat_solver(self._c_btor, c_str)

    def Set_rewrite_level(self, int level):
        btorapi.boolector_set_rewrite_level(self._c_btor, level)

    def Refs(self):
        return btorapi.boolector_get_refs(self._c_btor)

    # Dump functions

    def Dump_btor(self, outfile = ""):
      btorapi.boolector_dump_btor(self._c_btor, stdout)

    def Dump_smt1(self, outfile=""):
      btorapi.boolector_dump_smt1(self._c_btor, stdout)

    def Dump_smt2(self, outfile=""):
      btorapi.boolector_dump_smt2(self._c_btor, stdout)

    # Boolector API functions (nodes)

    def Const(self, str bits):
        cdef bytes b_str = bits.encode()
        cdef char* c_str = b_str
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_const(self._c_btor, c_str)
        return r

    def Zero(self, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_zero(self._c_btor, width)
        return r

    def Ones(self, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_ones(self._c_btor, width)
        return r

    def TRUE(self):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_true(self._c_btor)
        return r

    def FALSE(self):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_false(self._c_btor)
        return r

    def One(self, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_one(self._c_btor, width)
        return r

    def Uint(self, unsigned int i, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_unsigned_int(self._c_btor, i, width)
        return r

    def Int(self, int i, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_int(self._c_btor, i, width)
        return r

    def Var(self, int width, str symbol = ""):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_var(self._c_btor, width, '')
        return r

    def Param(self, int width, str symbol = ""):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_param(self._c_btor, width, '')
        return r

    def Array(self, int elem_width, int index_width, str symbol = ""):
        cdef bytes b_str = symbol.encode()
        cdef char* c_str = b_str
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_array(self._c_btor, elem_width,
                                                 index_width, b_str)
        return r

    # Unary operators

    def Not(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_not(self._c_btor, n._c_node)
        return r

    def Neg(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_neg(self._c_btor, n._c_node)
        return r

    def Redor(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_redor(self._c_btor, n._c_node)
        return r

    def Redxor(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_redxor(self._c_btor, n._c_node)
        return r

    def Redand(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_redand(self._c_btor, n._c_node)
        return r

    def Slice(self, BoolectorNode n, int upper, int lower):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_slice(self._c_btor, n._c_node,
                                                 upper, lower)
        return r
                                                                
    def Uext(self, BoolectorNode n, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_uext(self._c_btor, n._c_node, width)
        return r

    def Sext(self, BoolectorNode n, int width):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_sext(self._c_btor, n._c_node, width)
        return r

    def Inc(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_inc(self._c_btor, n._c_node)
        return r

    def Dec(self, BoolectorNode n):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_dec(self._c_btor, n._c_node)
        return r

    # Binary operators

    def Implies(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_implies(self._c_btor, a._c_node, b._c_node)
        return r

    def Iff(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_iff(self._c_btor, a._c_node, b._c_node)
        return r

    def Xor(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_xor(self._c_btor, a._c_node, b._c_node)
        return r

    def Xnor(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_xnor(self._c_btor, a._c_node, b._c_node)
        return r

    def And(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_and(self._c_btor, a._c_node, b._c_node)
        return r

    def Nand(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_nand(self._c_btor, a._c_node, b._c_node)
        return r

    def Or(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_or(self._c_btor, a._c_node, b._c_node)
        return r

    def Nor(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_nor(self._c_btor, a._c_node, b._c_node)
        return r

    def Eq(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_eq(self._c_btor, a._c_node, b._c_node)
        return r

    def Ne(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_ne(self._c_btor, a._c_node, b._c_node)
        return r

    def Add(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_add(self._c_btor, a._c_node, b._c_node)
        return r

    def Uaddo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_uaddo(self._c_btor, a._c_node, b._c_node)
        return r

    def Saddo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_saddo(self._c_btor, a._c_node, b._c_node)
        return r

    def Mul(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_mul(self._c_btor, a._c_node, b._c_node)
        return r

    def Umulo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_umulo(self._c_btor, a._c_node, b._c_node)
        return r

    def Smulo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_smulo(self._c_btor, a._c_node, b._c_node)
        return r

    def Ult(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_ult(self._c_btor, a._c_node, b._c_node)
        return r

    def Slt(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_slt(self._c_btor, a._c_node, b._c_node)
        return r

    def Ulte(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_ulte(self._c_btor, a._c_node, b._c_node)
        return r

    def Slte(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_slte(self._c_btor, a._c_node, b._c_node)
        return r

    def Ugt(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_ugt(self._c_btor, a._c_node, b._c_node)
        return r

    def Sgt(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_sgt(self._c_btor, a._c_node, b._c_node)
        return r

    def Ugte(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_ugte(self._c_btor, a._c_node, b._c_node)
        return r

    def Sgte(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_sgte(self._c_btor, a._c_node, b._c_node)
        return r

    def Sll(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_sll(self._c_btor, a._c_node, b._c_node)
        return r

    def Srl(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_srl(self._c_btor, a._c_node, b._c_node)
        return r

    def Sra(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_sra(self._c_btor, a._c_node, b._c_node)
        return r

    def Rol(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_rol(self._c_btor, a._c_node, b._c_node)
        return r

    def Ror(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_ror(self._c_btor, a._c_node, b._c_node)
        return r

    def Sub(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = btorapi.boolector_sub(self._c_btor, a._c_node, b._c_node)
        return r

    def Usubo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_usubo(self._c_btor, a._c_node, b._c_node)
        return r

    def Ssubo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_ssubo(self._c_btor, a._c_node, b._c_node)
        return r

    def Udiv(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_udiv(self._c_btor, a._c_node, b._c_node)
        return r

    def Sdiv(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_sdiv(self._c_btor, a._c_node, b._c_node)
        return r

    def Sdivo(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_sdivo(self._c_btor, a._c_node, b._c_node)
        return r

    def Urem(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_urem(self._c_btor, a._c_node, b._c_node)
        return r

    def Srem(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_srem(self._c_btor, a._c_node, b._c_node)
        return r

    def Smod(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_smod(self._c_btor, a._c_node, b._c_node)
        return r

    def Concat(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_concat(self._c_btor, a._c_node, b._c_node)
        return r

    def Read(self, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_read(self._c_btor, a._c_node, b._c_node)
        return r

    # Ternary operators

    def Write(self, BoolectorNode array, BoolectorNode index, 
              BoolectorNode value):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_write(self._c_btor, array._c_node,
                                       index._c_node, value._c_node)
        return r

    def Cond(self, BoolectorNode cond, BoolectorNode a, BoolectorNode b):
        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_cond(self._c_btor, cond._c_node, a._c_node,
                                      b._c_node)
        return r

    # Functions

    def Fun(self, list params, BoolectorNode body):
        cdef int paramc = len(params)
        cdef btorapi.BoolectorNode** c_params = \
            <btorapi.BoolectorNode**> \
                malloc(paramc * sizeof(btorapi.BoolectorNode*))

        # copy params into array
        for i in range(paramc):
            assert(isinstance(params[i], BoolectorNode))
            c_params[i] = (<BoolectorNode> params[i])._c_node

        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_fun(self._c_btor, paramc, c_params,
                                     body._c_node)

        free(c_params)
        return r

    def Apply(self, list args, BoolectorNode fun):
        cdef int argc = len(args)
        cdef btorapi.BoolectorNode** c_args = \
            <btorapi.BoolectorNode**> \
	      malloc(argc * sizeof(btorapi.BoolectorNode*))

        # copy arguments into array
        for i in range(argc):
            assert(isinstance(args[i], BoolectorNode))
            c_args[i] = (<BoolectorNode> args[i])._c_node

        r = BoolectorNode(self)
        r._c_node = \
            btorapi.boolector_apply(self._c_btor, argc, c_args, fun._c_node)
        free(c_args)
        return r

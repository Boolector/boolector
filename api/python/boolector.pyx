# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2013-2015 Mathias Preiner.
# Copyright (C) 2014-2015 Aina Niemetz.
#
# All rights reserved.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

cimport btorapi
from libc.stdlib cimport malloc, free
from libc.stdio cimport stdout, FILE, fopen, fclose
from cpython cimport bool
from cpython.ref cimport PyObject
import math, os, sys

g_tunable_options = {"rewrite_level", "rewrite_level_pbr",
                     "beta_reduce_all", "probe_beta_reduce_all",
                     "pbra_lod_limit", "pbra_sat_limit", "pbra_ops_factor",
                     "dual_prop", "just", "ucopt", "lazy_synthesize",
                     "eliminate_slices"}

class BoolectorException(Exception):
    """ The class representing a Boolector exception."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "[pybtor] {}".format(self.msg)

# utility functions

cdef btorapi.BoolectorNode * _c_node(x):
    assert(isinstance(x, BoolectorNode))
    return (<BoolectorNode> x)._c_node

cdef class _ChPtr:
    cdef char * _c_str
    cdef bytes _py_str
    def __init__(self, str string):
        if string is None:
            self._py_str = None
            self._c_str = NULL
        else:
            self._py_str = string.encode()
            self._c_str = self._py_str

cdef str _to_str(const char * string):
    if string is NULL:
        return None
    cdef bytes py_str = string
    return str(py_str.decode())

def _is_power2(int num):
    return num != 0 and (num & (num - 1)) == 0

cdef _to_node(x, y):
    if isinstance(x, BoolectorBVNode) and isinstance(y, BoolectorBVNode):
        if (<BoolectorBVNode> x).width != (<BoolectorBVNode> y).width:
            raise BoolectorException(
                      "Both operands must have the same bit width")
        return x, y
    elif not (isinstance(x, BoolectorBVNode) or
              isinstance(y, BoolectorBVNode)):
        raise BoolectorException("At least one of the operands must be of "\
                                 "type 'BoolectorBVNode'") 
    if isinstance(x, BoolectorBVNode):
        btor = (<BoolectorBVNode> x).btor
        width = (<BoolectorBVNode> x).width
    else:
        assert(isinstance(y, BoolectorBVNode))
        btor = (<BoolectorBVNode> y).btor
        width = (<BoolectorBVNode> y).width

    x = btor.Const(x, width)
    y = btor.Const(y, width)
    return x, y

cdef int _get_argument_width(BoolectorFunNode fun, int pos):
    if fun._params:
        return (<BoolectorNode> fun._params[pos]).width
    else:
        assert(fun._sort)
        assert(fun._sort._domain)
        sort = fun._sort._domain[pos]
        if isinstance(sort, _BoolectorBoolSort):
            return 1
        else:
            assert(isinstance(sort, _BoolectorBitVecSort))
            return (<_BoolectorBitVecSort> sort)._width

def _check_precond_shift(BoolectorBVNode a, BoolectorBVNode b):
    if not _is_power2(a.width):
        raise BoolectorException(
                  "Bit width of operand 'a' must be a power of 2")
    if int(math.log(a.width, 2)) != b.width:
        raise BoolectorException(
                  "Bit width of operand 'b' must be equal to "\
                  "log2(bit width of a)") 

def _check_precond_slice(BoolectorBVNode a, int upper, int lower):
        if upper >= a.width:
            raise BoolectorException(
                      "Upper limit of slice must be lower than the bit width "\
                      "of the bit vector")
        if lower < 0 or lower > upper:
            raise BoolectorException("Lower limit must be within the bounds "\
                                      "of [upper:0]")

def _check_precond_cond(cond, a, b):
    if isinstance(cond, int) and (cond > 1 or cond < 0):
        raise BoolectorException(
                  "'cond' needs to either boolean or an integer of 0 or 1")
    if not (isinstance(a, BoolectorBVNode) or
            isinstance(b, BoolectorBVNode)) and \
       not (isinstance(a, BoolectorArrayNode) and
            isinstance(b, BoolectorArrayNode)):
        raise BoolectorException(
                  "At least one of the operands must be a bit vector")

# sort wrapper classes

cdef class BoolectorSort:
    """
    The class representing a Boolector sort.
    """
    cdef Boolector btor
    cdef btorapi.Btor * _c_btor
    cdef btorapi.BoolectorSort _c_sort

    def __init__(self, Boolector boolector):
        self.btor = boolector
        self._c_btor = boolector._c_btor

    def __dealloc__(self):
        btorapi.boolector_release_sort(self._c_btor, self._c_sort)

cdef class _BoolectorFunSort(BoolectorSort):
    cdef list _domain
    cdef BoolectorSort _codomain

cdef class _BoolectorBitVecSort(BoolectorSort):
    cdef int _width

cdef class _BoolectorBoolSort(BoolectorSort):
    pass

# option wrapper classes

cdef class BoolectorOptions:
    """
    The class representing a Boolector option iterator (see 
    :func:`~boolector.Boolector.Options`).

    """
    cdef Boolector btor
    cdef BoolectorOpt __cur

    def __init__(self, Boolector btor):
        self.btor = btor
        self.__cur = BoolectorOpt(btor,
                         _to_str(btorapi.boolector_first_opt(btor._c_btor)))

    def __iter__(self):
        return self

    def __next__(self):
        if self.__cur is None:
            raise StopIteration
        next = self.__cur
        name = _to_str(btorapi.boolector_next_opt(self.btor._c_btor,
                                                  next.__chptr._c_str))
        if name is None:
            self.__cur = None
        else:
            self.__cur = BoolectorOpt(self.btor, name)
        return next


cdef class BoolectorOpt:
    """
    The class representing a Boolector option.
    """
    cdef Boolector btor
    cdef _ChPtr __chptr
    cdef str name

    def __init__(self, Boolector boolector, str name):
        self.btor = boolector
        self.name = name
        self.__chptr = _ChPtr(name)

    def __richcmp__(BoolectorOpt opt0, BoolectorOpt opt1, opcode):
        if opcode == 2:
            return opt0.name == opt1.name
        elif opcode == 3:
            return opt0.name != opt1.name
        else:
            raise BoolectorException("Opcode '{}' not implemented for "\
                                     "__richcmp__".format(opcode))

    property shrt:
        """ The short name of a Boolector option. 
        """
        def __get__(self):
            return _to_str(btorapi.boolector_get_opt_shrt(self.btor._c_btor,
                                                          self.__chptr._c_str))

    property lng:
        """ The long name of a Boolector option.
        """
        def __get__(self):
            return self.name

    property desc:
        """ The description of a Boolector option. 
        """
        def __get__(self):
            return _to_str(btorapi.boolector_get_opt_desc(self.btor._c_btor,
                                                          self.__chptr._c_str))

    property val:
        """ The current value of a Boolector option. 
        """
        def __get__(self):
            return btorapi.boolector_get_opt_val(self.btor._c_btor,
                                                 self.__chptr._c_str)

    property dflt:
        """ The default value of a Boolector option. 
        """
        def __get__(self):
            return btorapi.boolector_get_opt_dflt(self.btor._c_btor,
                                                  self.__chptr._c_str)

    property min:
        """ The minimum value of a Boolector option. 
        """
        def __get__(self):
            return btorapi.boolector_get_opt_min(self.btor._c_btor,
                                                 self.__chptr._c_str)

    property max:
        """ The maximum value of a Boolector option. 
        """
        def __get__(self):
            return btorapi.boolector_get_opt_max(self.btor._c_btor,
                                                 self.__chptr._c_str)

    property tunable:
        def __get__(self):
            return self.lng in g_tunable_options

    def __str__(self):
        return "{}, [{}, {}], default: {}".format(self.lng,
                                                      self.min, self.max,
                                                      self.dflt)
# wrapper classes for BoolectorNode

cdef class BoolectorNode:
    """
    The class representing a Boolector node.
    """
    cdef public Boolector btor
    cdef btorapi.Btor * _c_btor
    cdef btorapi.BoolectorNode * _c_node

    def __init__(self, Boolector boolector):
        self.btor = boolector
        self._c_btor = boolector._c_btor

    def __dealloc__(self):
        if self._c_node is NULL:
            raise BoolectorException("BoolectorNode not initialized correctly")
        btorapi.boolector_release(self._c_btor, self._c_node)

    def __richcmp__(BoolectorNode x, BoolectorNode y, opcode):
        if opcode == 2:
            return x.btor.Eq(x, y)
        elif opcode == 3:
            return x.btor.Ne(x, y)
        else:
            raise BoolectorException("Opcode '{}' not implemented for "\
                                     "__richcmp__".format(opcode))

    property symbol:
        """ The symbol of a Boolector node.

            A node's symbol is used as a simple means of identfication,
            either when printing a model via 
            :func:`~boolector.Boolector.Print_model`,
            or generating file dumps via 
            :func:`~boolector.Boolector.Dump`.
        """
        def __get__(self):
            return _to_str(btorapi.boolector_get_symbol(self.btor._c_btor,
                                                        self._c_node))

        def __set__(self, str symbol):
            btorapi.boolector_set_symbol(self.btor._c_btor, self._c_node,
                                         _ChPtr(symbol)._c_str)

    property width:
        """ The bit width of a Boolector node.

            If the node is an array,
            this indicates the bit width of the array elements.
            If the node is a function,
            this indicates the bit with of the function's return value.
        """
        def __get__(self):
            return btorapi.boolector_get_width(self.btor._c_btor, self._c_node)

    property assignment:
        """ The assignment of a Boolector node.

            May be queried only after a preceding call to
            :func:`~boolector.Boolector.Sat` returned 
            :data:`~boolector.Boolector.SAT`.

            If the queried node is a bit vector, its assignment is 
            represented as string.
            If it is an array, its assignment is represented as a list
            of tuples ``(index, value)``.
            If it is a function, its assignment is represented as a list
            of tuples ``(arg_0, ..., arg_n, value)``.

        """
        def __get__(self):
            cdef char ** c_str_i
            cdef char ** c_str_v
            cdef int size
            cdef const char * c_str
            cdef bytes py_str

            if isinstance(self, BoolectorFunNode) or \
               isinstance(self, BoolectorArrayNode):
                if isinstance(self, BoolectorArrayNode):
                    btorapi.boolector_array_assignment(
                        self.btor._c_btor, self._c_node, &c_str_i, &c_str_v,
                        &size) 
                else:
                    btorapi.boolector_uf_assignment(
                        self.btor._c_btor, self._c_node, &c_str_i, &c_str_v,
                        &size) 
                model = []
                if size > 0:
                    for i in range(size):
                        index = _to_str(c_str_i[i])
                        value = _to_str(c_str_v[i])
                        if isinstance(self, BoolectorFunNode):
                            index = index.split()
                        model.append((index, value))
                    if isinstance(self, BoolectorArrayNode):
                        btorapi.boolector_free_array_assignment(
                            self.btor._c_btor, c_str_i, c_str_v, size) 
                    else:
                        btorapi.boolector_free_uf_assignment(
                            self.btor._c_btor, c_str_i, c_str_v, size) 
                return model
            else:
                c_str = \
                    btorapi.boolector_bv_assignment(self.btor._c_btor,
                                                    self._c_node)
                value = _to_str(c_str)
                btorapi.boolector_free_bv_assignment(self.btor._c_btor, c_str)
                return value

    def Dump(self, format = "btor", outfile = None):
        """ Dump (format = "btor", outfile = None)

            Dump node to output file.

            :param format: A file format identifier string (use 'btor' for BTOR_ and 'smt2' for `SMT-LIB v2`_).
            :type format: str
            :param outfile: Output file name (default: stdout).
            :type outfile: str
            
        """
        cdef FILE * c_file

        if outfile is None:
            c_file = stdout
        else:
            if os.path.isfile(outfile):
                raise BoolectorException(
                        "Outfile '{}' already exists".format(outfile)) 
            elif os.path.isdir(outfile):
                raise BoolectorException(
                        "Outfile '{}' is a directory".format(outfile)) 
            c_file = fopen(_ChPtr(outfile)._c_str, "w")

        if format.lower() == "btor":
            btorapi.boolector_dump_btor_node(self.btor._c_btor, c_file,
                                             self._c_node)
        elif format.lower() == "smt2":
            btorapi.boolector_dump_smt2_node(self.btor._c_btor, c_file,
                                             self._c_node)
        else:
            raise BoolectorException("Invalid dump format '{}'".format(format)) 
        if outfile is not None:
            fclose(c_file)

cdef class BoolectorBVNode(BoolectorNode):
    """
    The class representing a Boolector bit vector node.
    """
    def __richcmp__(x, y, opcode):
        x, y = _to_node(x, y)
        b = (<BoolectorBVNode> x).btor
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
            raise BoolectorException("Opcode '{}' not implemented for "\
                                     "__richcmp__".format(opcode))

    def __neg__(self):
        return self.btor.Neg(self)

    def __invert__(self):
        return self.btor.Not(self)

    def __add__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Add(x, y)

    def __sub__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Sub(x, y)

    def __mul__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Mul(x, y)

    def __div__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Udiv(x, y)

    def __truediv__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Udiv(x, y)

    def __mod__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Urem(x, y)

    def __lshift__(BoolectorBVNode x, y):
        return x.btor.Sll(x, y)

    def __rshift__(BoolectorBVNode x, y):
        return x.btor.Srl(x, y)

    def __and__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.And(x, y)

    def __or__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Or(x, y)

    def __xor__(x, y):
        x, y = _to_node(x, y)
        return (<BoolectorBVNode> x).btor.Xor(x, y)

    def __getitem__(self, x):
        # Use python slice notation for bit vector slicing
        if isinstance(x, slice):
            upper = x.start
            lower = x.stop
            if x.step is not None:
                raise BoolectorException(
                          "Step of 'slice' not suppored on bit vectors")
            if upper is None:
                upper = self.width - 1
            if lower is None:
                lower = 0
            if not isinstance(upper, int):
                raise BoolectorException(
                          "Upper limit of slice must be an integer")
            if not isinstance(lower, int):
                raise BoolectorException(
                          "Lower limit of slice must be an integer")
            return self.btor.Slice(self, upper, lower)
        # Extract single bit
        elif isinstance(x, int):
            return self.btor.Slice(self, x, x)
        else:
            raise BoolectorException("Expected 'int' or 'slice'")


cdef class BoolectorConstNode(BoolectorBVNode):
    """
        The class representing Boolector constant nodes.
    """
    property bits:
        """ The bit string of a Boolector constant node.
        """
        def __get__(self):
            cdef const char * c_str
            if not self.__is_const():
                raise BoolectorException("Given node is not a constant")
            c_str = btorapi.boolector_get_bits(self.btor._c_btor, self._c_node)
            value = _to_str(c_str)
            btorapi.boolector_free_bits(self.btor._c_btor, c_str)
            return value

    def __is_const(self):
        return btorapi.boolector_is_const(self.btor._c_btor, self._c_node) == 1


cdef class BoolectorArrayNode(BoolectorNode):
    """
    The class representing a Boolector array node.
    """
    # TODO: allow slices on arrays
    #       array[2:4] -> memcpy from index 2 to 4 
    #       array[:] -> copy whole array
    def __getitem__(self, index):
        return self.btor.Read(self, index)

    property index_width:
        """ The bit with of the Boolector array node indices.
        """
        def __get__(self):
            return btorapi.boolector_get_index_width(self.btor._c_btor,
                       self._c_node)


cdef class BoolectorFunNode(BoolectorNode):
    """
    The class representing a Boolector function node.
    """
    cdef list _params
    cdef _BoolectorFunSort _sort

    def __call__(self, *args):
        return self.btor.Apply(list(args), self)

    property arity:
        """ The arity of a Boolector function node.
        """
        def __get__(self):
            return \
                btorapi.boolector_get_fun_arity(self.btor._c_btor, self._c_node)


cdef class _BoolectorParamNode(BoolectorBVNode):
    pass

# wrapper class for Boolector itself

cdef class Boolector:
    """
    The class representing a Boolector instance.
    """
    cdef btorapi.Btor * _c_btor
    cdef list _option_names

    UNKNOWN = 0
    SAT = 10
    UNSAT = 20
    PARSE_ERROR = 1

    def __init__(self, Boolector parent = None):
        if parent is None:
            self._c_btor = btorapi.boolector_new()
        else:
            self._c_btor = btorapi.boolector_clone(parent._c_btor)
        self._option_names = [o.lng for o in self.Options()]
        if self._c_btor is NULL:
            raise MemoryError()

    def __dealloc__(self):
        if self._c_btor is not NULL:
            btorapi.boolector_py_delete(self._c_btor)

    # termination callback 
    
    def Set_term(self, fun, args):
        """ Set_term(fun, args)

            Set a termination callback function. 
            
            Use this function to force Boolector to prematurely terminate if
            callback function ``fun`` returns True. Arguments ``args`` to 
            ``fun`` may be passed as a single Python object (in case that 
            ``fun`` takes only one argument), a tuple, or a list of arguments.

            E.g., ::

              import time
              
              def fun1 (arg): 
                  # timeout after 1 sec.
                  return time.time() - arg > 1.0

              def fun2 (arg0, arg1):
                  # do something and return True/False
                  ...

              btor = Boolector()

              btor.Set_term(fun1, time.time())
              btor.Set_term(fun1, (time.time(),))
              btor.Set_term(fun1, [time.time()])
              
              btor.Set_term(fun2, (arg0, arg1))
              btor.Set_term(run2, [arg0, arg1])

            :param fun: A python function.
            :param args: A function argument or a list or tuple of function arguments.
        """
        cdef PyObject* funptr = <PyObject*>fun
        cdef PyObject* argsptr = <PyObject*>args
        btorapi.boolector_py_set_term(self._c_btor, funptr, argsptr)

    def Terminate(self):
        """ Terminate()

            Determine if Boolector has been terminated (and/or terminate 
            Boolector) via the previously configured termination callback
            function.

            See :func:`~boolector.Boolector.Set_term`.
            
            :return True if termination condition is fulfilled, else False.
            :rtype: bool
        """
        cdef int res
        res = btorapi.boolector_terminate(self._c_btor)
        return res > 0

    # Boolector API functions (general)

    def Assert(self, *assertions):
        """ Assert(a,...)

            Add one or more constraints. 
            
            Added constraints can not be removed.

            :param a: Bit vector expression with bit width 1.
            :type a:  :class:`~boolector.BoolectorNode`
        """
        for i in range(len(assertions)):
            a = assertions[i]
            if not isinstance(a, BoolectorNode):
              raise BoolectorException("Argument at position {0:d} is not "\
                                       "a BoolectorNode".format(i))
            n = <BoolectorNode> a
            if n.width > 1:
                raise BoolectorException("Asserted term at position {0:d} "\
                                         "must be of bit width one".format(i))
            btorapi.boolector_assert(self._c_btor, n._c_node)

    def Assume(self, *assumptions):
        """ Assume(a,...)

                Add one or more assumptions.
            
            You must enable Boolector's incremental usage via 
            :func:`~boolector.Boolector.Set_opt` before you can add
            assumptions.
            In contrast to assertions added via 
            :func:`~boolector.Boolector.Assert`, assumptions
            are discarded after each call to :func:`~boolector.Boolector.Sat`.
            Assumptions and assertions are logicall combined via Boolean
            *and*. 
            Assumption handling in Boolector is analogous to assumptions
            in MiniSAT.

            :param a: Bit vector expression with bit width 1.
            :type a:  :class:`~boolector.BoolectorNode`
        """
        for i in range(len(assumptions)):
            a = assumptions[i]
            if not isinstance(a, BoolectorNode):
              raise BoolectorException("Argument at position {0:d} is not "\
                                       "a BoolectorNode".format(i))
            n = <BoolectorNode> a
            if n.width > 1:
                raise BoolectorException("Asserted term at position {0:d} "\
                                         "must be of bit width one".format(i))
            btorapi.boolector_assume(self._c_btor, n._c_node)

    def Failed(self,  *assumptions):
        """ Failed(a,...)

            Determine if any of the given assumptions are failed assumptions.

            Failed assumptions are those assumptions, that force an
            input formula to become unsatisfiable.
            Failed assumptions handling in Boolector is analogous to 
            failed assumptions in MiniSAT.

            See :func:`~boolector.Boolector.Assume`.

            :param a: Bit vector expression with bit width 1.
            :type a:  :class:`~boolector.BoolectorNode`
            :return:  list of boolean values, where True indicates that the assumption at given index is failed, and false otherwise.
            :rtype:   list(bool)
        """
        failed = []
        for i in range(len(assumptions)):
            a = assumptions[i]
            if not isinstance(a, BoolectorNode):
              raise BoolectorException("Argument at position {0:d} is not "\
                                       "a BoolectorNode".format(i))
            n = <BoolectorNode> a
            if n.width > 1:
                raise BoolectorException("Term at position {0:d} must "\
                                         "be of bit width one".format(i))
            failed.append(
                btorapi.boolector_failed(self._c_btor, n._c_node) == 1)
        return failed

    def Fixate_assumptions(self):
        """ Fixate_assumptions()

            Add all assumptions added since the last
            :func:`~boolector.Boolector.Sat` call as assertions. 

            See :func:`~boolector.Boolector.Assume`.
        """
        btorapi.boolector_fixate_assumptions(self._c_btor)

    def Reset_assumptions(self):
        """ Reset_assumptions()

            Remove all assumptions added since the last
            :func:`~boolector.Boolector.Sat` call.

            See :func:`~boolector.Boolector.Assume`.
        """
        btorapi.boolector_reset_assumptions(self._c_btor)

    def Sat(self, int lod_limit = -1, int sat_limit = -1):
        """ Sat (lod_limit = -1, sat_limit = -1)

            Solve an input formula.

            An input formula is defined by constraints added via
            :func:`~boolector.Boolector.Assert`.
            You can guide the search for a solution to an input formula by
            making assumptions via :func:`~boolector.Boolector.Assume`.

            If you want to call this function multiple times, you must
            enable Boolector's incremental usage mode via 
            :func:`~boolector.Boolector.Set_opt`.
            Otherwise, this function may only be called once.

            You can limit the search by the number of lemmas generated
            (``lod_limit``) and the number of conflicts encountered by
            the underlying SAT solver (``sat_limit``).

            :param lod_limit: Limit for Lemmas on Demand (-1: unlimited).
            :type lod_limit:  int
            :param sat_limit: Conflict limit for the SAT solver (-1: unlimited).
            :type sat_limit:  int
            :return: :data:`~boolector.Boolector.SAT` if the input formula is satisfiable (under possibly given assumptions), :data:`~boolector.Boolector.UNSAT` if it is unsatisfiable, and :data:`~boolector.Boolector.UNKNOWN` if the instance could not be solved within given limits.

            .. note::
                Assertions and assumptions are combined via Boolean *and*.

            .. seealso::
                :data:`~boolector.BoolectorNode.assignment`
        """
        if lod_limit > 0 or sat_limit > 0:
            return btorapi.boolector_limited_sat(self._c_btor, lod_limit,
                                                 sat_limit)
        return btorapi.boolector_sat(self._c_btor)

    def Simplify(self):
        """ Simplify()

            Simplify current input formula.

            :return: :data:`~boolector.Boolector.SAT` if the input formula was simplified to true, :data:`~boolector.Boolector.UNSAT` if it was simplified to false, and :data:`~boolector.Boolector.UNKNOWN`, otherwise.

            .. note::
                Each call to :func:`~boolector.Boolector.Sat` 
                simplifies the input formula as a preprocessing step.
        """
        return btorapi.boolector_simplify(self._c_btor)

    def Clone(self):
        """ Clone()

            Clone an instance of Boolector.

            The resulting Boolector instance is an exact (but disjunct) copy of
            its parent instance.  Consequently, in a clone and its parent,
            nodes with the same id correspond to each other.  Use
            :func:`~boolector.Boolector.Match` to match corresponding nodes.

            :return: The exact (but disjunct) copy of a Boolector instance.
            :rtype: :class:`~boolector.Boolector`

            .. note::
                If Lingeling is used as SAT solver, Boolector can be cloned at
                any time, since Lingeling also supports cloning. However, if
                you use :func:`~boolector.Boolector.Clone` with MiniSAT or
                PicoSAT (no cloning suppport), Boolector can only be cloned
                prior to the first :func:`~boolector.Boolector.Sat` call.
        """
        return Boolector(self)

    # BoolectorNode methods
    def Match(self, BoolectorNode n):
        """ Match(n)

            Retrieve the node matching given node ``n`` by id.

            This is intended to be used for handling expressions of a 
            cloned instance (see :func:`~boolector.Boolector.Clone`).

            E.g., ::

              btor = Boolector()
              v = btor.Var(16, "x")
              clone = btor.Clone()
              v_cloned = clone.Match(v)

            :param n: Boolector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return:  The Boolector node that matches given node ``n`` by id.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                Only nodes created before the
                :func:`~boolector.Boolector.Clone` call can be matched.
        """
        node_type = type(n)
        r = node_type(self)
        (<BoolectorNode> r)._c_node = \
            btorapi.boolector_match_node(self._c_btor, n._c_node)
        if (<BoolectorNode> r)._c_node is NULL:
            raise BoolectorException("Could not match given node 'n'")
        return r

    # Boolector options
    def Set_opt(self, str opt, int value):
        """ Set_opt(opt, value)

            Set option.

            List of available options:

            * **model_gen**

              | Enable (``value``: 1 or 2) or disable (``value``: 0) generation of a model for satisfiable instances. 
              | There are two modes for model generation: 

              * generate model for asserted expressions only (``value``: 1)
              * generate model for all expressions (``value``: 2)

            * **incremental**

              | Enable (``value``: 1) incremental mode.
              | Note that incremental usage turns off some optimization techniques. Disabling incremental usage is currently not supported.

            * **incremental_all**

              | Enable (``value``: 1) or disable (``value``: 0) incremental solving of all formulas when parsing an input file.
              | Note that currently, incremental mode while parsing an input file is only supported for `SMT-LIB v1`_ input.

            * **incremental_in_depth**

              | Set incremental in-depth mode width (``value``: int) when parsing an input file.
              | Note that currently, incremental mode while parsing an input file is only supported for `SMT-LIB v1`_ input.  

            * **incremental_look_ahead**

              | Set incremental look_ahead mode width (``value``: int) when parsing an input file.
              | Note that currently, incremental mode while parsing an input file is only supported for `SMT-LIB v1`_ input.
               
            * **incremental_interval**

              | Set incremental interval mode width (``value``: int) when parsing an input file.
              | Note that currently, incremental mode while parsing an input file is only supported for `SMT-LIB v1`_ input.

            * **input_format**
              
              | Force input file format (``value``: `BTOR <http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf>`_: -1, `SMT-LIB v1 <http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf>`_: 1, `SMT-LIB v2 <http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf>`_: 2) when parsing an input file.
              | If unspecified, Boolector automatically detects the input file format while parsing.

            * **output_number_format**

              | Force output number format (``value``: binary: 0, hexadecimal: 1, decimal: 2):
              | Boolector uses binary by default.

            * **output_format**
          
              | Force output file format (``value``: BTOR_: -1, `SMT-LIB v1`_: 1, `SMT-LIB v2`_: 2).
              | Boolector uses BTOR_ by default.

            * **rewrite_level**

              | Set the rewrite level (``value``: 0-3) of the rewriting engine.
              | Boolector uses rewrite level 3 by default, rewrite levels are classified as follows:

              * 0: no rewriting
              * 1: term level rewriting
              * 2: more simplification techniques
              * 3: full rewriting/simplification

              | Do not alter the rewrite level of the rewriting engine after creating expressions.

            * **rewrite_level_pbr**

              | Set the rewrite level (``value``: 0-3) for partial beta reduction.
              | Boolector uses rewrite level 1 by default. Rewrite levels are classified as above.

            * **beta_reduce_all**
              
              Enable (``value``: 1) or disable (``value``: 0) the eager
              elimination of lambda expressions via beta reduction.

            * **probe_beta_reduce_all**

              Enable (``value``: 1) or disable (``value``: 0) probing of
              *beta_reduce_all* until a given lemmas on demand
              (*pbr_lod_limit*) or SAT conflicts limit (*pbra_sat_limit*).

            * **pbra_lod_limit**

              Set lemmas on demand limit for *probe_beta_reduce_all*.

            * **pbra_sat_limit**

              Set SAT conflicts limit for *probe_beta_reduce_all*.

            * **pbra_ops_factor**

              Set factor by which the size of the beta reduced formula may be
              greater than the original formula (for *probe_beta_reduce_all*).

            * **dual_prop**

              Enable (``value``: 1) or disable (``value``: 0) dual propagation
              optimization.

            * **just**

              Enable (``value``: 1) or disable (``value``: 0) justification
              optimization.
              
            * **ucopt**

              Enable (``value``: 1) or disable (``value``: 0) unconstrained
              optimization.

            * **lazy_synthesize**

              Enable (``value``: 1) or disable (``value``: 0) lazy synthesis of
              bit vector expressions.

            * **eliminate_slices**

              Enable (``value``: 1) or disable (``value``: 0) slice elimination
              on bit vector variables.

            * **pretty_print**

              Enable (``value``: 1) or disable (``value``: 0) pretty printing
              when dumping.

            * **verbosity**

              Set the level of verbosity.

            :param opt:   Option name.
            :type opt:    str
            :param value: Option value.
            :type value:  int
        """
        if opt not in self._option_names:
            raise BoolectorException("Invalid Boolector option name")
        btorapi.boolector_set_opt(self._c_btor, _ChPtr(opt)._c_str, value)

    def Get_opt(self, str opt):
        """ Get_opt(opt)

            Get the Boolector option with name ``opt``.

            For a list of all available options, see 
            :func:`~boolector.Boolector.Set_opt`.

            :param opt: Option name.
            :type opt: str
            :return: Option with name ``opt``.
            :rtype: :class:`~boolector.BoolectorOpt`
        """
        if opt not in self._option_names:
            raise BoolectorException("Invalid Boolector option name")
        return BoolectorOpt(self, opt)

    def Options(self):
        """ Options()

            Get a :class:`~boolector.BoolectorOptions` iterator.

            E.g., ::

              btor = Boolector()
              options = btor.Options()
              for o in options:
                  # do something
      
            :return: An iterator to iterate over all Boolector options.
            :rtype: :class:`~boolector.BoolectorOptions`
        """
        return BoolectorOptions(self)

    def Set_sat_solver(self, str solver, str optstr = None, bool clone = True):
        """ Set_sat_solver(solver, optstr = None, clone = True)

            Set the SAT solver to use.

            E.g., ::

              btor = Boolector()
              btor.Set_sat_solver("MiniSAT")
      
            Option ``clone`` enables non-incremental SAT solver usage
            (for every SAT call) by means of internal SAT solver cloning. 
            Use this option with caution (might have a positive or negative
            impact on overall performance).

            :param solver: Solver identifier string.
            :type solver:  str
            :param optstr: Solver option string.
            :type optstr:  str
            :param clone: Force non-incremental SAT solver usage.
            :type clone:  bool
            :return: True if setting the SAT solver was successful and False otherwise. 
            :rtype: bool

            .. note::
                Parameters ``optstr`` and ``clone`` are currently only supported
                by Lingeling.
        """
        solver = solver.strip().lower()
        if solver == "lingeling":
            return btorapi.boolector_set_sat_solver_lingeling(
                        self._c_btor, _ChPtr(optstr)._c_str, not clone) == 1
        else:
            return btorapi.boolector_set_sat_solver(
                        self._c_btor, _ChPtr(solver)._c_str) == 1

    def Print_model(self, str format = "btor", outfile = None):
        """ Print_model(format = "btor", outfile = None)
  
            Print model to output file.

            Supported model formats are Boolector's own model format ("btor")
            and `SMT-LIB v2`_ ("smt2").

            This function prints the model for all inputs to output file
            ``outfile``, e.g.::

              btor.Print_model()

            A possible model would be: ::
  
              2 00000100 x
              3 00010101 y
              4[00] 01 A
  
            which in this case prints the assignments of array variable ``A``,
            and bit vector variables ``x`` and ``y``.
            For bit vector variables, the first column indicates the id of an
            input, the second column its assignment, and the third column its
            name (symbol), if any. Array variable ``A``, on the other hand,
            has id 4, is an array with index and element bit width of 2, 
            and its value at index 0 is 1.

            The corresponding model in `SMT-LIB v2`_ format would be: ::

              btor.Print_model(format="smt2")
            
            ::

              (model
                (define-fun x () (_ BitVec 8) #b00000100)
                (define-fun y () (_ BitVec 8) #b00010101)
                (define-fun y (
                 (y_x0 (_ BitVec 2)))
                 (ite (= y_x0 #b00) #b01
                   #00))
              )

            :param format:  Model output format (default: "btor").
            :param outfile: Output file name (default: stdout).
            :type outfile:  str
        """
        cdef FILE * c_file

        if format != "btor" and format != "smt2":
            raise BoolectorException("Invalid model format '{}'".format(format))

        if outfile is None:
            c_file = stdout
        else:
            if os.path.isfile(outfile):
                raise BoolectorException(
                        "Outfile '{}' already exists".format(outfile)) 
            elif os.path.isdir(outfile):
                raise BoolectorException(
                        "Outfile '{}' is a directory".format(outfile)) 
            c_file = fopen(_ChPtr(outfile)._c_str, "w")

        btorapi.boolector_print_model(
            self._c_btor, _ChPtr(format)._c_str, c_file)

        if outfile is not None:
            fclose(c_file)

    def Parse(self, str infile, str outfile = None):
        """ Parse(infile, outfile = None)

            Parse input file.

            Input file format may be either BTOR_, `SMT-LIB v1`_, or
            `SMT-LIB v2`_, the file type is detected automatically.

            E.g., ::

              btor = Boolector()
              (result, status, error_msg) = btor.Parse("example.btor")

            :param infile: Input file name.
            :type infile:  str
            :return: A tuple (result, status, error_msg), where return value ``result`` indicates an error (:data:`~boolector.Boolector.PARSE_ERROR`) if any, and else denotes the satisfiability result (:data:`~boolector.Boolector.SAT` or :data:`~boolector.Boolector.UNSAT`) in the incremental case, and :data:`~boolector.Boolector.UNKNOWN` otherwise. Return value ``status`` indicates a (known) status (:data:`~boolector.Boolector.SAT` or :data:`~boolector.Boolector.UNSAT`) as specified in the input file. In case of an error, an explanation of that error is stored in ``error_msg``.
        """
        cdef FILE * c_infile
        cdef FILE * c_outfile
        cdef int res
        cdef char * err_msg
        cdef int status

        if not os.path.isfile(infile):
            raise BoolectorException("File '{}' does not exist".format(infile))
        c_infile = fopen(_ChPtr(infile)._c_str, "r")

        if outfile and not os.path.isfile(outfile):
            raise BoolectorException("File '{}' does not exist".format(outfile))
        if outfile is None:
            c_outfile = stdout
        else:
            c_outfile = fopen(_ChPtr(outfile)._c_str, "r") 

        res = btorapi.boolector_parse(self._c_btor, c_infile,
                _ChPtr(infile)._c_str, c_outfile, &err_msg, &status)

        fclose(c_infile)
        if outfile is not None:
            fclose(c_outfile)

        return (res, status, _to_str(err_msg))

    def Dump(self, format = "btor", outfile = None):
        """ Dump(format = "btor", outfile = None)

            Dump input formula to output file.

            :param format: A file format identifier string (use 'btor' for BTOR_, 'smt2' for `SMT-LIB v2`_, 'aig' for binary AIGER (QF_BV only), and 'aag' for ASCII AIGER (QF_BV only)).
            :type format: str
            :param outile: Output file name (default: stdout).
            :type format: str.

        """
        cdef FILE * c_file

        if outfile is None:
            c_file = stdout
        else:
            if os.path.isfile(outfile):
                raise BoolectorException(
                        "Outfile '{}' already exists".format(outfile)) 
            elif os.path.isdir(outfile):
                raise BoolectorException(
                        "Outfile '{}' is a directory".format(outfile)) 
            c_file = fopen(_ChPtr(outfile)._c_str, "w")

        if format.lower() == "btor":
            btorapi.boolector_dump_btor(self._c_btor, c_file)
        elif format.lower() == "smt2":
            btorapi.boolector_dump_smt2(self._c_btor, c_file)
        elif format.lower() == "aig":
            btorapi.boolector_dump_aiger_binary(self._c_btor, c_file, True)
        elif format.lower() == "aag":
            btorapi.boolector_dump_aiger_ascii(self._c_btor, c_file, True)
        else:
            raise BoolectorException("Invalid dump format '{}'".format(format)) 
        if outfile is not None:
            fclose(c_file)

    # Boolector nodes

    def Const(self, c, int width = 1):
        """ Const(c, width = 1)
        
            Create a bit vector constant of value ``c`` and bit width ``width``.

            :param c: Value of the constant.
            :type  c: int, bool, str
            :param width: Bit width of the constant.
            :type width:  int
            :return: A bit vector constant of value ``c`` and bit width ``width``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                Parameter ``width`` is only required if ``c`` is an integer.
        """
        cdef BoolectorConstNode r
        if isinstance(c, int) or (sys.version < '3' and isinstance(c, long)):
            if c != 0 and c.bit_length() > width:
                raise BoolectorException(
                          "Value of constant {} (bit width {}) exceeds bit "\
                          "width of {}".format(c, c.bit_length(), width))
            bitmask = int('0b'+ width * '1', 2)
            const_str = "{{0:0>{}b}}".format(width).format(c & bitmask)
            r = BoolectorConstNode(self)
            r._c_node = \
                btorapi.boolector_const(self._c_btor, _ChPtr(const_str)._c_str)
            return r
        elif isinstance(c, bool):
            r = BoolectorConstNode(self)
            if c:
                r._c_node = btorapi.boolector_true(self._c_btor)
            else:
                r._c_node = btorapi.boolector_false(self._c_btor)
            return r
        elif isinstance(c, str):
            try:
                int(c, 2)
            except ValueError:
                raise BoolectorException("Given constant string is not in"\
                                          "binary format")
            r = BoolectorConstNode(self)
            r._c_node = \
                btorapi.boolector_const(self._c_btor, _ChPtr(c)._c_str)
            return r
        elif isinstance(c, BoolectorNode):
            return c 
        else:
            raise BoolectorException(
                      "Cannot convert type '{}' to bit vector".format(
                          type(c)))

    def Var(self, int width, str symbol = None):
        """ Var(width, symbol = None)

            Create a bit vector variable with bit width ``width``.

            A variable's symbol is used as a simple means of identification,
            either when printing a model via 
            :func:`~boolector.Boolector.Print_model`,
            or generating file dumps via 
            :func:`~boolector.Boolector.Dump`.
            A symbol must be unique but may be None in case that no
            symbol should be assigned.

            :param width: Bit width of the variable.
            :type width: int
            :param symbol: Symbol of the variable.
            :type symbol: str
            :return: A bit vector variable with bit width ``width``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                In contrast to composite expressions, which are maintained
                uniquely w.r.t. to their kind, inputs (and consequently, bit
                width), variables are not.  Hence, each call to this
                function returns a fresh bit vector variable.
        """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_var(self._c_btor, width,
                                          _ChPtr(symbol)._c_str)
        return r

    def Param(self, int width, str symbol = None):
        """ Param(width, symbol = None)

            Create a function parameter with bit width ``width``.

            This kind of node is used to create parameterized expressions,
            which in turn are used to create functions.
            Once a parameter is bound to a function, it cannot be reused in
            other functions.

            See :func:`~boolector.Boolector.Fun`, 
            :func:`~boolector.Boolector.Apply`.
            
            :param width: Bit width of the function parameter.
            :type width: int
            :param symbol: Symbol of the function parameter.
            :type symbol: str
            :return: A function parameter with bit width ``width``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        r = _BoolectorParamNode(self)
        r._c_node = btorapi.boolector_param(self._c_btor, width,
                                            _ChPtr(symbol)._c_str)
        return r

    def Array(self, int elem_width, int index_width, str symbol = None):
        """ Array(elem_width, index_width, symbol = None)

            Create a one-dimensional bit vector array variable of size
            ``2**index_width`` with elements of bit width ``elem_width``.

            An array variable's symbol is used as a simple means of
            identfication, either when printing a model via 
            :func:`~boolector.Boolector.Print_model`,
            or generating file dumps via 
            :func:`~boolector.Boolector.Dump`.
            A symbol must be unique but may be None in case that no
            symbol should be assigned.
            
            :param elem_width: Bit width of the array elements.
            :type width: int
            :param index_width: Bit width of the array indices.
            :type width: int
            :param symbol: Symbol of the array variable.
            :type symbol: str
            :return: An array variable of size ``2**index_width`` with elements of bit width ``elem_width``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                In contrast to composite expressions, which are 
                maintained uniquely w.r.t. to their kind, inputs (and
                consequently, bit width), array variables are not.
                Hence, each call to this function returns a fresh bit vector
                array variable.
        """
        r = BoolectorArrayNode(self)
        r._c_node = btorapi.boolector_array(self._c_btor, elem_width,
                                            index_width, _ChPtr(symbol)._c_str)
        return r

    # Unary operators

    def Not(self, BoolectorBVNode n):
        """ Not(n)

            Create the one's complement of bit vector node ``n``.

            It is also possible to create the one's complement as follows
            (see :ref:`operator-overloading`): ::
                
                bvnot = ~n

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return:  The one's complement of bit vector node ``n``.
            :rtype:  :class:`~boolector.BoolectorNode`
        """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_not(self._c_btor, n._c_node)
        return r

    def Neg(self, BoolectorBVNode n):
        """ Neg(n)

            Create the two's complement of bit vector node ``n``.

            It is also possible to create the two's complement as follows
            (see :ref:`operator-overloading`): ::
                
                bvneg = -n
            
            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return:  The two's complement of bit vector node ``n``.
            :rtype: :class:`~boolector.BoolectorNode`
            """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_neg(self._c_btor, n._c_node)
        return r

    def Redor(self, BoolectorBVNode n):
        """ Redor(n)

            Create an *or* reduction of node ``n``.

            All bits of node ``n`` are combined by an Boolean *or*.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return:  The *or* reduction of node ``n``.
            :rtype: :class:`~boolector.BoolectorNode`
            """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_redor(self._c_btor, n._c_node)
        return r

    def Redxor(self, BoolectorBVNode n):
        """ Redxor(n)

            Create an *xor* reduction of node ``n``.

            All bits of node ``n`` are combined by an Boolean *xor*.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return:  The *xor* reduction of node ``n``.
            :rtype: :class:`~boolector.BoolectorNode`
            """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_redxor(self._c_btor, n._c_node)
        return r

    def Redand(self, BoolectorBVNode n):
        """ Redand(n)

            Create an *and* reduction of node ``n``.

            All bits of node ``n`` are combined by an Boolean *and*.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return:  The *and* reduction of node ``n``.
            :rtype: :class:`~boolector.BoolectorNode`
            """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_redand(self._c_btor, n._c_node)
        return r

    def Slice(self, BoolectorBVNode n, int upper, int lower):
        """ Slice(n, upper, lower)

            Create a bit vector slice of node ``n`` from index ``upper``
            to index ``lower``.

            It is also possible to use Python slices on bit vectors as
            follows: ::

              n[upper:lower]  # creates slice with upper limit 'upper' and lower limit 'lower'
              n[upper:]       # creates slice with upper limit 'upper' and lower limit 0
              n[:lower]       # creates slice with upper limit 'n.width - 1' and lower limit 'lower'
              n[:]            # creates copy of node 'n' 

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :param upper: Upper index, which must be greater than or equal to zero, and less than the bit width of node ``n``.
            :type upper: int
            :param lower: Lower index, which must be greater than or equal to zero, and less than or equal to ``upper``.
            :type lower: int
            :return: A Bit vector with bit width ``upper`` - ``lower`` + 1.
            :rtype: :class:`~boolector.BoolectorNode`

        """
        _check_precond_slice(n, upper, lower)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_slice(self._c_btor, n._c_node,
                                            upper, lower)
        return r
                                                                
    def Uext(self, BoolectorBVNode n, int width):
        """ Uext(n, width)

            Create unsigned extension.

            Bit vector node ``n`` is padded with ``width`` zeroes.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :param width: Number of zeros to pad.
            :type width: int
            :return: A bit vector extended by ``width`` zeroes.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_uext(self._c_btor, n._c_node, width)
        return r

    def Sext(self, BoolectorBVNode n, int width):
        """ Sext(n, width)

            Create signed extension.

            Bit vector node ``n`` is padded with ``width`` bits, where the 
            padded value depends on the value of the most significant bit
            of node ``n``.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :param width: Number of bits to pad.
            :type width: int
            :return: A bit vector extended by ``width`` bits.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sext(self._c_btor, n._c_node, width)
        return r

    def Inc(self, BoolectorBVNode n):
        """ Inc(n)

            Create a bit vector expression that increments bit vector ``n``
            by one.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return: A bit vector with the same bit width as ``n``, incremented by one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_inc(self._c_btor, n._c_node)
        return r

    def Dec(self, BoolectorBVNode n):
        """ Dec(n)

            Create a bit vector expression that decrements bit vector ``n``
            by one.

            :param n: A bit vector node.
            :type n:  :class:`~boolector.BoolectorNode`
            :return: A bit vector with the same bit width as ``n``, decremented by one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_dec(self._c_btor, n._c_node)
        return r

    # Binary operators

    def Implies(self, a, b):
        """ Implies(a, b)
          
            Create a Boolean implication.

            Parameters ``a`` and ``b`` must have bit width one
            (see :ref:`const-conversion`).

            :param a: Bit vector node representing the premise.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Bit vector node representing the conclusion.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A Boolean implication ``a`` => ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_implies(self._c_btor,
                                              _c_node(a), _c_node(b))
        return r

    def Iff(self, a, b):
        """ Iff(a, b)
          
            Create a Boolean equivalence.

            Parameters ``a`` and ``b`` must have bit width one
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A Boolean equivalence ``a`` <=> ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_iff(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Xor(self, a, b):
        """ Xor(a, b)
          
            Create a bit vector *xor*.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an *xor* as follows
            (see :ref:`operator-overloading`): ::
                
                bvxor = a ^ b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_xor(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Xnor(self, a, b):
        """ Xnor(a, b)
          
            Create a bit vector *xnor*.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_xnor(self._c_btor, _c_node(a), _c_node(b))
        return r

    def And(self, a, b):
        """ And(a, b)
          
            Create a bit vector *and*.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an *and* as follows
            (see :ref:`operator-overloading`): ::
                
                bvand = a & b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_and(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Nand(self, a, b):
        """ Nand(a, b)
          
            Create a bit vector *nand*.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_nand(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Or(self, a, b):
        """ Or(a, b)
          
            Create a bit vector *or*.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an *or* as follows
            (see :ref:`operator-overloading`): ::
                
                bvor = a | b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_or(self._c_btor,
                                         _c_node(a), _c_node(b))
        return r

    def Nor(self, a, b):
        """ Nor(a, b)
          
            Create a bit vector *nor*.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_nor(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Eq(self, a, b):
        """ Eq(a, b)
          
            Create a bit vector or array equality.

            Parameters ``a`` and ``b`` are either bit vectors with the same bit
            width, or arrays of the same type (see :ref:`const-conversion`).

            It is also possible to create an equality as follows
            (see :ref:`operator-overloading`): ::
                
                eq = a == b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        if not (isinstance(a, BoolectorArrayNode) and isinstance(b, BoolectorArrayNode)):
          a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_eq(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Ne(self, a, b):
        """ Ne(a, b)
          
            Create a bit vector or array inequality.

            Parameters ``a`` and ``b`` are either bit vectors with the same bit
            width, or arrays of the same type (see :ref:`const-conversion`).

            It is also possible to create an inequality as follows
            (see :ref:`operator-overloading`): ::
                
                ne = a != b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        if not (isinstance(a, BoolectorArrayNode) and isinstance(b, BoolectorArrayNode)):
          a, b = _to_node(a, b)
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ne(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Add(self, a, b):
        """ Add(a, b)
          
            Create a bit vector addition.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an addition as follows
            (see :ref:`operator-overloading`): ::
                
                bvadd = a + b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_add(self._c_btor, _c_node(a),
                                          _c_node(b))
        return r

    def Uaddo(self, a, b):
        """ Uaddo(a, b)
          
            Create an unsigned  bit vector addition overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the addition of ``a`` and ``b`` overflows in case both operands are treated as unsigned.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_uaddo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Saddo(self, a, b):
        """ Saddo(a, b)
          
            Create a signed bit vector addition overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the addition of ``a`` and ``b`` overflows in case both operands are treated as signed.
            :rtype: :class:`~boolector.BoolectorNode`
            """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_saddo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Mul(self, a, b):
        """ Mul(a, b)
          
            Create a bit vector multiplication.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create a multiplication as follows
            (see :ref:`operator-overloading`): ::
                
                bvmul = a * b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_mul(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Umulo(self, a, b):
        """ Umulo(a, b)
          
            Create an unsigned  bit vector multiplication overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the multiplication of ``a`` and ``b`` overflows in case both operands are treated as unsigned.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_umulo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Smulo(self, a, b):
        """ Smulo(a, b)
          
            Create a signed bit vector multiplication overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the multiplication of ``a`` and ``b`` overflows in case both operands are treated as signed.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_smulo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Ult(self, a, b):
        """ Ult(a, b)
          
            Create an unsigned less than.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an unsigned less than as follows
            (see :ref:`operator-overloading`): ::
                
                lt = a < b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ult(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Slt(self, a, b):
        """ Slt(a, b)
          
            Create a signed less than.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_slt(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Ulte(self, a, b):
        """ Ulte(a, b)
          
            Create an unsigned less than or equal.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an unsigned less than or equal as
            follows (see :ref:`operator-overloading`): ::
                
                lte = a <= b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_ulte(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Slte(self, a, b):
        """ Slte(a, b)
          
            Create a signed less than or equal.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_slte(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Ugt(self, a, b):
        """ Ugt(a, b)
          
            Create an unsigned greater than.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an unsigned greater than as follows
            (see :ref:`operator-overloading`): ::
                
                ugt = a > b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ugt(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Sgt(self, a, b):
        """ Sgt(a, b)
          
            Create a signed greater than.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sgt(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Ugte(self, a, b):
        """ Ugte(a, b)
          
            Create an unsigned greater than or equal.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create an unsigned greater than or equal as
            follows (see :ref:`operator-overloading`): ::
                
                ugte = a >= b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_ugte(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Sgte(self, a, b):
        """ Sgte(a, b)
          
            Create a signed greater than or equal.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_sgte(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Sll(self, BoolectorBVNode a, b):
        """ Sll(a, b)
          
            Create a logical shift left.

            Given bit vector node ``b``, the value it represents is the 
            number of zeroes shifted into node ``a`` from the right
            (see :ref:`const-conversion`).


            It is also possible to create a logical shift left as follows
            (see :ref:`operator-overloading`): ::
                
                bvshl = a << b

            :param a: First bit vector operand where the bit width is a power of two and greater than 1.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand with bit width log2 of the bit width of ``a``.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        b = self.Const(b, math.ceil(math.log(a.width, 2)))
        _check_precond_shift(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sll(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Srl(self, BoolectorBVNode a, b):
        """ Srl(a, b)
          
            Create a logical shift right.

            Given bit vector node ``b``, the value it represents is the 
            number of zeroes shifted into node ``a`` from the left
            (see :ref:`const-conversion`).

            It is also possible to create a logical shift right as follows
            (see :ref:`operator-overloading`): ::
                
                bvshr = a >> b

            :param a: First bit vector operand where the bit width is a power of two and greater than 1.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand with bit width log2 of the bit width of ``a``.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        b = self.Const(b, math.ceil(math.log(a.width, 2)))
        _check_precond_shift(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_srl(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Sra(self, BoolectorBVNode a, b):
        """ Sra(a, b)
          
            Create an arithmetic shift right.

            Analogously to :func:`~boolector.Boolector.Srl`, but whether
            zeroes or ones are shifted in depends on the most significant
            bit of node ``a`` (see :ref:`const-conversion`).

            :param a: First bit vector operand where the bit width is a power of two and greater than 1.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand with bit width log2 of the bit width of ``a``.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        b = self.Const(b, math.ceil(math.log(a.width, 2)))
        _check_precond_shift(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sra(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Rol(self, BoolectorBVNode a, b):
        """ Rol(a, b)
          
            Create a rotate left.

            Given bit vector node ``b``, the value it represents is the 
            number of bits by which node ``a`` is rotated to the left
            (see :ref:`const-conversion`).

            :param a: First bit vector operand where the bit width is a power of two and greater than 1.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand with bit width log2 of the bit width of ``a``.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        b = self.Const(b, math.ceil(math.log(a.width, 2)))
        _check_precond_shift(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_rol(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Ror(self, BoolectorBVNode a, b):
        """ Ror(a, b)
          
            Create a rotate right.

            Given bit vector node ``b``, the value it represents is the 
            number of bits by which node ``a`` is rotated to the right
            (see :ref:`const-conversion`).

            :param a: First bit vector operand where the bit width is a power of two and greater than 1.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand with bit width log2 of the bit width of ``a``.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        b = self.Const(b, math.ceil(math.log(a.width, 2)))
        _check_precond_shift(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_ror(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Sub(self, a, b):
        """ Sub(a, b)
          
            Create a bit vector subtraction.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            It is also possible to create a subtraction as follows
            (see :ref:`operator-overloading`): ::
                
                bvsub = a - b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = btorapi.boolector_sub(self._c_btor,
                                          _c_node(a), _c_node(b))
        return r

    def Usubo(self, a, b):
        """ Usubo(a, b)
          
            Create an unsigned  bit vector subtraction overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the subtraction of ``a`` and ``b`` overflows in case both operands are treated as unsigned.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_usubo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Ssubo(self, a, b):
        """ Ssubo(a, b)
          
            Create a signed  bit vector subtraction overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the subtraction of ``a`` and ``b`` overflows in case both operands are treated as signed.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_ssubo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Udiv(self, a, b):
        """ Udiv(a, b)
          
            Create an unsigned  bit vector division.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).
            If ``a`` is 0, the division's result is -1.

            It is also possible to create an unsigned division as follows
            (see :ref:`operator-overloading`): ::
                
                bvudiv = a / b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                This behavior (division by zero returns -1) does not exactly
                comply with the SMT-LIB v1 and v2 standards, where division by
                zero is handled as an uninterpreted function.  Our semantics
                are motivated by real circuits where division by zero cannot be
                uninterpreted and consequently returns a result.
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_udiv(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Sdiv(self, a, b):
        """ Sdiv(a, b)
          
            Create a signed  bit vector division.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).
            
            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                Signed division is expressed by means of unsigned division,
                where either node is normalized in case that its sign bit is 1.
                If the sign bits of ``a`` and ``b`` do not match, two's
                complement is performed on the result of the previous unsigned
                division.  Hence, the behavior in case of a division by zero
                depends on :func:`~boolector.Boolector.Udiv`.
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_sdiv(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Sdivo(self, a, b):
        """ Sdivo(a, b)
          
            Create a signed  bit vector division overflow detection.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).
            An overflow can occur if ``a`` represents INT_MIN and ``b``
            represents -1.

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bit width one, which indicates if the division of ``a`` and ``b`` overflows in case both operands are treated as signed.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                Unsigned bit vector division does not overflow.
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_sdivo(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Urem(self, a, b):
        """ Urem(a, b)
          
            Create an unsigned remainder.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).
            If ``b`` is 0, the result of the unsigned remainder is ``a``.

            It is also possible to create an unsigned remainder as follows
            (see :ref:`operator-overloading`): ::
                
                bvurem = a % b

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
            
            .. note::
                As in :func:`~boolector.Boolector.Udiv`, the behavior if ``b``
                is 0 does not exactly comply to the SMT-LIB v1 and v2 standards,
                where the result ist handled as uninterpreted function.
                Our semantics are motivated by real circuits, where result 
                can not be uninterpreted.
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_urem(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Srem(self, a, b):
        """ Srem(a, b)
          
            Create a signed remainder.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).
            If ``b`` is 0, the result of the unsigned remainder is ``a``.
            If ``b`` is 0, the result of the unsigned remainder is ``a``.
            
            Analogously to :func:`~boolector.Boolector.Sdiv`, the signed
            remainder is expressed by means of the unsigned remainder,
            where either node is normalized in case that its sign bit is 1. 
            Hence, in case that ``b`` is zero, the result depends on
            :func:`~boolector.Boolector.Urem`.

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_srem(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Smod(self, a, b):
        """ Smod(a, b)
          
            Create a signed remainder where its sign matches the sign of the
            divisor.

            Parameters ``a`` and ``b`` must have the same bit width
            (see :ref:`const-conversion`).
            
            If ``b`` is zero, the result depends on 
            :func:`~boolector.Boolector.Urem`.

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bit width as ``a`` and ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        a, b = _to_node(a, b)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_smod(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Concat(self, BoolectorBVNode a, BoolectorBVNode b):
        """ Concat(a,b)
          
            Create the concatenation of two bit vectors.

            :param a: First bit vector operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Second bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with bitwidth ``bit width of a + bit width of b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_concat(self._c_btor, _c_node(a), _c_node(b))
        return r

    def Read(self, BoolectorArrayNode a, b):

        """ Read(a,b)
          
            Create a read on array ``a`` at position ``b``
            (see :ref:`const-conversion`).

            It is also possible to create a read as follows
            (see :ref:`operator-overloading`): ::
                
                read = a[b]

            :param a: Array operand.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Bit vector operand.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  A bit vector node with the same bitwidth as the elements of array ``a``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        b = self.Const(b, a.index_width)
        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_read(self._c_btor, _c_node(a), _c_node(b))
        return r

    # Ternary operators

    def Write(self, BoolectorArrayNode array, index, value):
        """ Write(array,index, value)
          
            Create a write on array ``array`` at position ``index`` with value
            ``value`` (see :ref:`const-conversion`).

            The array is updated at exactly one position, all other elements
            remain unchanged.
            The bit width of ``index`` must be the same as the bit width of 
            the indices of ``array``.
            The bit width of ``value`` must be the same as the bit width of
            the elements of ``array``.

            :param array: Array operand.
            :type array:  :class:`~boolector.BoolectorNode`
            :param index: Bit vector index.
            :type index:  :class:`~boolector.BoolectorNode`
            :param value: Bit vector value.
            :type value:  :class:`~boolector.BoolectorNode`
            :return:  An array where the value at ``index`` has been updated with ``value``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        index = self.Const(index, array.index_width)
        value = self.Const(value, array.width)

        r = BoolectorArrayNode(self)
        r._c_node = \
            btorapi.boolector_write(self._c_btor, array._c_node,
                                    _c_node(index), _c_node(value))
        return r

    def Cond(self, cond, a, b):
        """ Cond(cond, a, b)
          
            Create an if-then-else.
            
            If condition ``cond`` is true, then ``a`` is returned, else ``b``
            is returned.
            ``a`` and ``b`` must be either both arrays or both bit
            vectors (see :ref:`const-conversion`).

            :param cond: Bit vector condition with bit width one.
            :type cond:  :class:`~boolector.BoolectorNode`
            :param a: Array or bit vector operand representing the *then* case.
            :type a:  :class:`~boolector.BoolectorNode`
            :param b: Array or bit vector operand representing the *else* case.
            :type b:  :class:`~boolector.BoolectorNode`
            :return:  Either ``a`` or ``b``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        _check_precond_cond(cond, a, b)
        cond = self.Const(cond, width=1)
        if isinstance(a, BoolectorBVNode) or isinstance(b, BoolectorBVNode):
            r = BoolectorBVNode(self)
            a, b = _to_node(a, b)
        else:
            assert(isinstance(a, BoolectorArrayNode))
            assert(isinstance(b, BoolectorArrayNode))
            r = BoolectorArrayNode(self)
        r._c_node = \
            btorapi.boolector_cond(self._c_btor, _c_node(cond), _c_node(a),
                                      _c_node(b))
        return r

    # Functions

    def Fun(self, list params, BoolectorBVNode body):
        """ Fun(params, body)
          
            Create a function with function body ``body``, parameterized
            over ``params``.
            
            This kind of node is similar to macros in the `SMT-LIB v2`_
            standard.

            See :func:`~boolector.Boolector.Param`,
            :func:`~boolector.Boolector.Apply`.

            :param params: A list of function parameters.
            :type params: list
            :param body: Function body parameterized over ``params``.
            :type body:  :class:`~boolector.BoolectorNode`
            :return:  A function over parameterized expression ``body``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                As soon as a parameter is bound to a function, it can
                not be reused in other functions. 
                Call a function via :func:`~boolector.Boolector.Apply`.
        """
        cdef int paramc = len(params)
        cdef btorapi.BoolectorNode ** c_params = \
            <btorapi.BoolectorNode **> \
                malloc(paramc * sizeof(btorapi.BoolectorNode *))

        # copy params into array
        for i in range(paramc):
            if not isinstance(params[i], _BoolectorParamNode):
                raise BoolectorException(
                          "Operand at position {} is not a parameter".format(i))
            c_params[i] = _c_node(params[i])

        r = BoolectorFunNode(self)
        r._params = params
        r._c_node = \
            btorapi.boolector_fun(self._c_btor, c_params, paramc, body._c_node)
        free(c_params)
        return r

    def UF(self, BoolectorSort sort, str symbol = None):
        """ UF(sort, symbol)
          
            Create an uninterpreted function with sort ``sort`` and symbol
            ``symbol``.

            An uninterpreted function's symbol is used as a simple means of 
            identification, either when printing a model via 
            :func:`~boolector.Boolector.Print_model`,
            or generating file dumps via 
            :func:`~boolector.Boolector.Dump`.
            A symbol must be unique but may be None in case that no
            symbol should be assigned.

            See :func:`~boolector.Boolector.Apply`,
            :func:`~boolector.Boolector.FunSort`.

            :param sort: Sort of the uninterpreted function.
            :type sort:  BoolectorSort
            :param symbol: Name of the uninterpreted function. 
            :type symbol: str
            :return:  A function over parameterized expression ``body``.
            :rtype: :class:`~boolector.BoolectorNode`

            .. note::
                In contrast to composite expressions, which are maintained
                uniquely w.r.t. to their kind, inputs (and consequently, bit
                width), uninterpreted functions are not.  Hence, each
                call to this function returns a fresh uninterpreted function.
        """
        if not isinstance(sort, _BoolectorFunSort):
            raise BoolectorException(
                     "Sort must be of sort '_BoolectorFunSort'")
        r = BoolectorFunNode(self)
        r._sort = sort
        r._c_node = btorapi.boolector_uf(self._c_btor, sort._c_sort,
                                         _ChPtr(symbol)._c_str)
        return r


    def Apply(self, list args, BoolectorFunNode fun):
        """ Apply(args,fun)
          
            Create a function application on function ``fun`` with arguments
            ``args`` (see :ref:`const-conversion`).
            
            It is also possible to create a function application as follows
            (see :ref:`operator-overloading`): ::
                
                app = fun(arg_0, ..., arg_n)

            See :func:`~boolector.Boolector.Fun`,
            :func:`~boolector.Boolector.UF`.

            :param args: A list of arguments to be applied.
            :type args: list
            :param fun: Function to apply arguments ``args`` to.
            :type fun:  :class:`~boolector.BoolectorNode`
            :return:  A function application on function ``fun`` with arguments ``args``.
            :rtype: :class:`~boolector.BoolectorNode`
        """
        cdef int argc = len(args)
        cdef btorapi.BoolectorNode ** c_args = \
            <btorapi.BoolectorNode **> \
              malloc(argc * sizeof(btorapi.BoolectorNode *))

        # copy arguments into array
        arg_nodes = []
        for i in range(argc):
            a = args[i]
            if not isinstance(a, BoolectorNode):
                if not (isinstance(a, int) or isinstance(a, bool)):
                    raise BoolectorException(
                              "Invalid type of argument {}".format(i))
                a = self.Const(a, _get_argument_width(fun, i))
            assert(isinstance(a, BoolectorNode))
            arg_nodes.append(a)

        for i in range(len(arg_nodes)):
            c_args[i] = _c_node(arg_nodes[i])

        r = BoolectorBVNode(self)
        r._c_node = \
            btorapi.boolector_apply(self._c_btor, c_args, argc, fun._c_node)
        free(c_args)
        return r

    # Sorts

    def BoolSort(self):
        """ BoolSort()
          
            Create Boolean sort.
            
            Currently, sorts in Boolector are used for uninterpreted functions,
            only.

            See :func:`~boolector.Boolector.UF`.

            :return:  Sort of type Boolean.
            :rtype: :class:`~boolector.BoolectorSort`
        """
        r = _BoolectorBoolSort(self)
        r._c_sort = btorapi.boolector_bool_sort(self._c_btor)
        return r

    def BitVecSort(self, int width):
        """ BitVecSort(width)
          
            Create bit vector sort of bit width ``width``.
            
            Currently, sorts in Boolector are used for uninterpreted functions,
            only.

            See :func:`~boolector.Boolector.UF`.

            :param width: Bit width.
            :type width: int
            :return:  Bit vector sort of bit width ``width``.
            :rtype: :class:`~boolector.BoolectorSort`
        """
        r = _BoolectorBitVecSort(self)
        r._width = width
        r._c_sort = btorapi.boolector_bitvec_sort(self._c_btor, width)
        return r

    def FunSort(self, list domain, BoolectorSort codomain):
        """ FunSort(domain, codomain)
          
            Create function sort.
            
            Currently, sorts in Boolector are used for uninterpreted functions,
            only.

            See :func:`~boolector.Boolector.UF`.

            :param domain: A list of all the function arguments' sorts.
            :type domain: list
            :param codomain: The sort of the function's return value.
            :type codomain: :class:`~boolector.BoolectorSort`
            :return:  Function sort, which maps ``domain`` to ``codomain``.
            :rtype: :class:`~boolector.BoolectorSort`
          """
        cdef int arity = len(domain)
        cdef btorapi.BoolectorSort * c_domain = \
            <btorapi.BoolectorSort *> \
                malloc(arity * sizeof(btorapi.BoolectorSort))

        for i in range(arity):
            if not isinstance(domain[i], BoolectorSort):
                raise BoolectorException("Function domain contains non-sort "\
                                          "objects")
            c_domain[i] = (<BoolectorSort> domain[i])._c_sort

        r = _BoolectorFunSort(self)
        r._domain = domain
        r._codomain = codomain
        r._c_sort = btorapi.boolector_fun_sort(
                        self._c_btor, c_domain, arity, codomain._c_sort)
        return r

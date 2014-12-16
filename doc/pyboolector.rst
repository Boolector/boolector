Boolector Python API documentation
==================================

.. _Boolector: http://fmv.jku.at/boolector
.. _BTOR: http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf
.. _SMT-LIB v1: http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf
.. _SMT-LIB v2: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf

Interface
---------

.. toctree::
    :maxdepth: 1

    Python interface <boolector>


Quickstart
----------


  First, create a Boolector instance: ::
    
    btor = Boolector() 

  You can configure this instance via :func:`~boolector.Boolector.Set_opt`.
  E.g., if you want to enable model generation: ::
   
    btor.Set_opt("model_gen", 1)
  
  For a detailed description of all configurable options, see
  :func:`~boolector.Boolector.Set_opt`.

  Next you can either parse an input file, and/or generate expressions to 
  be either asserted via :func:`~boolector.Boolector.Aassert`, or, 
  if incremental usage is enabled,
  assumed via :func:`~boolector.Boolector.Assume` (analogously to MiniSAT). 
  Note that Boolector's internal design is motivated by hardware design,
  hence we do not distinguish between type 'Boolean' and type 'bit vector
  of length 1'. 

  E.g., if you want to parse an input file "example.btor", 
  use :func:`~boolector.Boolector.Parse`: ::
  
    (result, status, error_msg) = btor.Parse("example.btor")
  
  Incremental usage is not enabled, hence, if the parser does not encounter
  an error, it returns :data:`~boolector.Boolector.UNKNOWN` 
  (for a more detailed description of the parsers return values,
  see :func:`~boolector.Boolector.Parse`).
  However, if the parser encounters an error, it returns 
  :data:`~boolector.Boolector.PARSE_ERROR`, and an explanation of that error is 
  stored in ``error_msg``. If the input file specifies a (known) status
  of the input formula (either satisfiable or unsatisfiable), that status
  is stored in ``status``.

  As an example for generating and asserting expressions via
  :func:`~boolector.Boolector.Assert`, consider the following example: ::

    0 < x <= 100, 0 < y <= 100, x * y < 100

  Given the Boolector instance created above, we generate and assert
  the following expressions: ::
  
    x = btor.Var(8, "x")
    y = btor.Var(8, "y")

    btor.Assert(0 < x)
    btor.Assert(x <= 100)
    btor.Assert(0 < y)
    btor.Assert(y <= 100)
    btor.Assert(x * y < 100)

    umulo = btor.Umulo(x, y)  # overflow bit of x * y
    btor.Assert(~umulo)       # do not allow overflows

  After parsing an input file and/or asserting/assuming expressions,
  the satisfiability of the resulting formula can be determined via
  :func:`~boolector.Boolector.Sat`.
  If the resulting formula is satisfiable and model generation has been
  enabled via :func:`~boolector.Boolector.Set_opt`, you can either
  print the resulting model via :func:`~boolector.Boolector.Print_model`,
  or query assignments
  of bit vector and array variables or uninterpreted functions via
  :data:`~boolector.BoolectorNode.assignment`. 
  Note that querying assignments is not limited to variables---you can query 
  the assignment of any arbitrary expression.
 
  E.g., given the example above, we first determine if the formula is
  satisfiable via :func:`~boolector.Boolector.Sat` (which it is): ::
  
   result = btor.Sat()
  
  Now you can either query the assignments of variables ``x`` and ``y`` ::

    print(x.assignment)  # prints: 00000100
    print(y.assignment)  # prints: 00010101
    print("{} {}".format(x.symbol, x.assignment))  # prints: x 00000100
    print("{} {}".format(y.symbol, y.assignment))  # prints: y 00010101 

  or print the resulting model via :func:`~boolector.Boolector.Print_model`.
  Boolector supports printing models in its own format ("btor", the default) 
  or in `SMT-LIB v2`_ format ("smt2"): ::
  
    btor.Print_model()
  
  A possible model would be: ::
  
    2 00000100 x
    3 00010101 y
  
  which in this case indicates the assignments of bit vector variables 
  ``x`` and ``y``. Note that the first column indicates the id of an input, 
  the second column its assignment, and the third column its name (or symbol)
  if any. 
  In the case that the formula includes arrays as input, their values at a
  certain index are indicated as follows: ::

    4[00] 01 A
  
  where A has id 4 and is an array with index and element bit width of 2, 
  and its value at index 0 is 1.

  Printing the above model in `SMT-LIB v2`_ format: ::

    btor.print_model (format="smt2")

  A possible model would be: ::

    (model
      (define-fun x () (_ BitVec 8) #b00000100)
      (define-fun y () (_ BitVec 8) #b00010101)
      (define-fun y (
       (y_x0 (_ BitVec 2)))
       (ite (= y_x0 #b00) #b01
         #00))
    )

.. _operator-overloading:

Python Operator Overloading
^^^^^^^^^^^^^^^^^^^^^^^^^^^
  For convenience the Boolector Python API provides the following overloaded
  operators on bit vectors (:class:`~boolector.BoolectorBVNode`):

  **Arithmetic operators:** ``+ - * / %`` ::

    x = btor.Var(32)
    y = btor.Var(32)

    bvadd  = x + y  # btor.Add(x, y)
    bvsub  = x - y  # btor.Sub(x, y)
    bvmul  = x * y  # btor.Mul(x, y)
    bvudiv = x / y  # btor.Udiv(x, y)
    bvurem = x % y  # btor.Urem(x, y)
    bvneg  = -x     # btor.Neg(x)

  **Bitwise operators:** ``~ & | ^ << >>`` ::

    z = btor.Var(5)

    bvnot = ~x      # btor.Not(x)
    bvand = x & y   # btor.And(x, y)
    bvor  = x | y   # btor.Or(x, y)
    bvxor = x ^ y   # btor.Xor(x, y)
    bvshl = x << z  # btor.Sll(x, z) 
    bvshr = x >> z  # btor.Srl(x, z) 

  **Comparison operators:** ``< <= == != >= >`` ::

    lt   = x < y   # btor.Ult(x, y)
    lte  = x <= y  # btor.Ulte(x, y)
    eq   = x == y  # btor.Eq(x, y)
    ne   = x != y  # btor.Ne(x, y)
    ugte = x >= y  # btor.Ugte(x, y)
    ugt  = x > y   # btor.Ugt(x, y)

  **Python slices:**
  It is possible to use Python slices on bit vectors (see 
  :func:`~boolector.Boolector.Slice`), e.g.: ::

    slice_5_2  = x[5:2]  # btor.Slice(x, 5, 2)
    slice_5_0  = x[5:]   # btor.Slice(x, 5, 0)
    slice_31_5 = x[:5]   # btor.Slice(x, x.width - 1, 5)
    slice_31_0 = x[:]    # btor.Slice(x, x.width - 1, 0) -- copies variable 'x'

  Further, the API also provides convenient ways to create reads
  (see :func:`~boolector.Boolector.Read`) on arrays, and function applications
  (see :func:`~boolector.Boolector.Apply`).

  **Reads on arrays:** ::

    a = btor.Array(8, 32)

    read = a[x]  # btor.Read(a, x) 

  **Function applications:** ::
  
    bv8 = btor.BitVecSort(8)
    bv32 = btor.BitVecSort(32)
    f = btor.UF(btor.FunSort([bv32, bv32], bv8))

    app = f(x, y)  # btor.Apply([x, y], f)


.. _const-conversion:

Automatic Constant Conversion
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                          
  For almost every method of :class:`~boolector.Boolector` that creates nodes,
  instead of passing arguments of the type :class:`~boolector.BoolectorNode`,
  the Python API allows to pass constants as arguments.
  The only requirement is that it must be possible to derive the bit width of
  the constant operands from the remaining operands.
  For example, binary operators like :func:`~boolector.Boolector.Add`
  operands may be a constant, and its bit width will be derived from the other
  non-constant operand, e.g.: ::

    btor.Add(x, 42)         # btor.Add(x, btor.Const(42, x.width))
    btor.And(0x2a, x)       # btor.And(btor.Const(0x2a, x.width), x)
    btor.Udiv(0b101010, x)  # btor.Udiv(btor.Const(0b101010, x.width), x)
           
  For all shift operations it is possible to define the shift width as
  constant, e.g.: ::

    btor.Sll(x, 5)  # btor.Sll(x, btor.Const(5, math.ceil(math.log(x.width, 2)))) 
    btor.Ror(x, 5)  # btor.Ror(x, btor.Const(5, math.ceil(math.log(x.width, 2)))) 

  For operations on arrays all arguments may be constant (except the array
  itself) since the bit width of the operands can be derived from the array,
  e.g.: ::

    btor.Read(a, 42)       # btor.Read(a, btor.Const(42, a.index_with))
    btor.Write(a, 42, 10)  # btor.Write(a, btor.Const(42, a.index_width), btor.Const(10, a.width))

  This also applies to the arguments of function applications, which can be
  derived from the function's signature, e.g.: ::

    btor.Apply([42, 10], f)  # btor.Apply([btor.Const(42, ...), btor.Const(10, ...)], f)

  .. note::
    Automatic constant conversion is not possible for the following operators:
    :func:`~boolector.Boolector.Not`,
    :func:`~boolector.Boolector.Neg`,
    :func:`~boolector.Boolector.Redor`,
    :func:`~boolector.Boolector.Redxor`,
    :func:`~boolector.Boolector.Redand`,
    :func:`~boolector.Boolector.Slice`,
    :func:`~boolector.Boolector.Uext`,
    :func:`~boolector.Boolector.Sext`,
    :func:`~boolector.Boolector.Inc`,
    :func:`~boolector.Boolector.Dec`, and
    :func:`~boolector.Boolector.Concat`
    as the bit with of the resulting node cannot be determined.

Options
-------
 
  Boolector can be configured either via :func:`~boolector.Boolector.Set_opt`, 
  or via environment variables of the form: ::

    BTOR<capitalized option name without '_'>=<value>

  For a list and detailed descriptions of all available options, 
  see :func:`~boolector.Boolector.Set_opt`.
 
  E.g., given a Boolector instance ``btor``, model generation is enabled either 
  via ::
  
    btor.Set_opt("model_gen", 1)
  
  or via setting the environment variable ::

    BTORMODELGEN=1


API Tracing
^^^^^^^^^^^

  API tracing allows to record every call to Boolector's public API. The
  resulting trace can be replayed and the replayed sequence behaves exactly 
  like the original Boolector run.
  This is particularly useful for debugging purposes, as it enables replaying
  erroneous behaviour.
  API tracing can be enabled either via 
  setting the environment variable BTORAPITRACE=<filename>.
 
  E.g., given a Boolector instance 'btor', enabling API tracing is done as
  follows: ::
   
    BTORAPITRACE="error.trace"


Internals
---------

  Boolector internally maintains a directed acyclic graph (DAG) of
  expressions. 
  By asserting an expression, it will be permanently added to the
  formula. 
  Assumptions, in contrast, are cleared after a call to 
  :func:`~boolector.Boolector.Sat`.
  You can query assumptions that force a formula to be unsatisfiable
  via :func:`~boolector.Boolector.Failed`.

Operators
^^^^^^^^^

  Boolector internally describes expressions by means of a set of base
  operators as documented in BTOR_.
  Boolector's API, however, provides a richer set of operators for
  convenience, where non-base operators are internally rewritten to use
  base operators only.
  E.g., two's complement (:func:`~boolector.Boolector.Neg`) is rewritten as 
  one's complement and addition of 1. 
  Note that this behaviour is not influenced by the rewrite level chosen.
 
Rewriting
^^^^^^^^^

  Boolector simplifies expressions and the expression DAG by means of 
  rewriting and supports three so-called rewrite levels.
  Increasing rewrite levels increase the extent of rewriting performed,
  and a rewrite level of 0 is equivalent to disabling rewriting at all.
  Note that Boolector not only simplifies expressions during construction
  of the expression DAG---for each call to \ref boolector_sat,
  various simplification techniques and rewriting phases are initiated.
  You can force Boolector to initiate rewriting and simplify the expression
  DAG via :func:`~boolector.Boolector.Simplify`.
  The rewrite level can be configured via :func:`~boolector.Boolector.Set_opt`.

Examples
--------

  .. literalinclude:: ../api/python/api_usage_examples.py

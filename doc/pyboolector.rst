Boolector Python API documentation
==================================

.. _Boolector: https://boolector.github.io
.. _BTOR: http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf
.. _SMT-LIB v1: http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf
.. _SMT-LIB v2: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf

Interface
---------

.. toctree::
    :maxdepth: 1

    Python interface <boolector>


Quickstart
-----------

  First, we create a Boolector instance:

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 8

  We can configure this instance via :func:`~pyboolector.Boolector.Set_opt`.
  For example, if we want to enable model generation:

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 10

  For a detailed description of all configurable options, see
  :func:`~pyboolector.Boolector.Set_opt`.

  Next, we can create expressions and assert formulas via
  :func:`~pyboolector.Boolector.Assert`.

  .. note::

      Boolector's internal design is motivated by hardware design.
      Hence we do not distinguish between type *Boolean* and type *bit-vector
      of length 1*.

  If incremental usage is enabled, formulas can optionally be assumed via
  :func:`~pyboolector.Boolector.Assume`.

  .. note::

    Assumptions are invalidated after a call to
    :func:`~pyboolector.Boolector.Sat`.

  Alternatively, we can parse an input file prior to creating and asserting
  expressions. For example, to parse an input file `example.btor`, we can use
  :func:`~pyboolector.Boolector.Parse` (auto detects the input format).

  .. code-block:: python

    (result, status, error_msg) = btor.Parse("example.btor")

  In case the input issues a call to check sat (in case of SMT-LIB v2 or
  incremental SMT-LIB v1), this function either returns
  :data:`~pyboolector.Boolector.SAT`,
  :data:`~pyboolector.Boolector.UNSAT`, or
  :data:`~pyboolector.Boolector.UNKNOWN`.
  In any other non-error case it returns
  :data:`~pyboolector.Boolector.UNKNOWN`.
  For a more detailed description of the parsers return values, see
  :func:`~pyboolector.Boolector.Parse`.

  If the parser encounters an error, it returns
  :func:`~pyboolector.Boolector.PARSE_ERROR`
  and an explanation of that error is stored
  in ``error_msg``.
  If the input file specifies a (known) status of the input formula (either
  satisfiable or unsatisfiable), that status is stored in ``status``.

  As an example for generating and asserting expressions via
  :func:`~pyboolector.Boolector.Assert`,
  consider the following example: ::

    0 < x <= 100 && 0 < y <= 100 && x * y < 100

  Assume that this example is given with x and y as natural numbers.
  We encode it with bit-vectors of size 8, and to preserve semantics,
  we have to ensure that the multiplication does not overflow.

  We first create a bit-vector sort of size 8.

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 12

  Then, we create and assert the following expressions:

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 14-37

  The satisfiability of the resulting formula can be determined via
  :func:`~pyboolector.Boolector.Sat`,

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 39

  If the resulting formula is satisfiable and model generation has been enabled
  via :func:`~pyboolector.Boolector.Set_opt`,
  we can either print the resulting model via
  :func:`~pyboolector.Boolector.Print_model`,
  or query assignments of bit-vector and array variables or uninterpreted
  functions via :func:`~pyboolector.BoolectorNode.assignment`.

  .. note::
      Querying assignments is not limited to variables. You can query
      the assignment of any arbitrary expression.

  The example above is satisfiable, and we can now either query the assignments
  of variables ``x`` and ``y`` or print the resulting model via
  :c:func:`boolector_print_model`.

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 50-53

  Boolector supports printing models in its own format ("btor") or in
  `SMT-LIB v2`_ format ("smt2"). We print the resulting model in BTOR_
  format:

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 57

  A possible model is shown below and gives the assignments of bit-vector
  variables ``x`` and ``y``.
  The first column indicates the id of the input, the second column its
  assignment, and the third column its name (or symbol) if any. ::

    2 00000001 x
    3 01011111 y

  In the case that the formula includes arrays as inputs, their values at a
  certain index are indicated as follows: ::

    4[00] 01 A

  Here, array ``A`` has id 4 with index and element bit width of 2, and its
  value at index 0 is 1.

  We now print the model of the example above in `SMT-LIB v2`_ format.

  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python
       :lines: 60

  A possible model is shown below: ::

    (
      (define-fun x () (_ BitVec 8) #b00000001)
      (define-fun y () (_ BitVec 8) #b01011111)
    )

  .. note::
      Boolector internally represents arrays as uninterpreted functions and
      prints array models as models for UF.

  The source code of the example above can be found at `examples/api/python/quickstart.py <https://github.com/boolector/boolector/tree/master/examples/api/python/quickstart.py>`_.


.. _operator-overloading:

Python Operator Overloading
^^^^^^^^^^^^^^^^^^^^^^^^^^^
  The Boolector Python API provides the following overloaded
  operators on bit-vectors (:class:`~pyboolector.BoolectorBVNode`).

  **Arithmetic Operators:** ``+ - * / %`` ::

    x = btor.Var(32)
    y = btor.Var(32)

    bvadd  = x + y  # btor.Add(x, y)
    bvsub  = x - y  # btor.Sub(x, y)
    bvmul  = x * y  # btor.Mul(x, y)
    bvudiv = x / y  # btor.Udiv(x, y)
    bvurem = x % y  # btor.Urem(x, y)
    bvneg  = -x     # btor.Neg(x)

  **Bitwise Operators:** ``~ & | ^ << >>`` ::

    z = btor.Var(5)

    bvnot = ~x      # btor.Not(x)
    bvand = x & y   # btor.And(x, y)
    bvor  = x | y   # btor.Or(x, y)
    bvxor = x ^ y   # btor.Xor(x, y)
    bvshl = x << z  # btor.Sll(x, z)
    bvshr = x >> z  # btor.Srl(x, z)

  **Comparison Operators:** ``< <= == != >= >`` ::

    lt   = x < y   # btor.Ult(x, y)
    lte  = x <= y  # btor.Ulte(x, y)
    eq   = x == y  # btor.Eq(x, y)
    ne   = x != y  # btor.Ne(x, y)
    ugte = x >= y  # btor.Ugte(x, y)
    ugt  = x > y   # btor.Ugt(x, y)

  **Python Slices:**
  It is possible to use Python slices on bit-vectors (see
  :func:`~pyboolector.Boolector.Slice`), e.g.: ::

    slice_5_2  = x[5:2]  # btor.Slice(x, 5, 2)
    slice_5_0  = x[5:]   # btor.Slice(x, 5, 0)
    slice_31_5 = x[:5]   # btor.Slice(x, x.width - 1, 5)
    slice_31_0 = x[:]    # btor.Slice(x, x.width - 1, 0) -- copies variable 'x'

  Further, the API also provides convenient ways to create reads
  (see :func:`~pyboolector.Boolector.Read`) on arrays, and function applications
  (see :func:`~pyboolector.Boolector.Apply`).

  **Reads on Arrays:** ::

    a = btor.Array(8, 32)

    read = a[x]  # btor.Read(a, x)

  **Function Applications:** ::

    bv8 = btor.BitVecSort(8)
    bv32 = btor.BitVecSort(32)
    f = btor.UF(btor.FunSort([bv32, bv32], bv8))

    app = f(x, y)  # btor.Apply([x, y], f)


.. _const-conversion:

Automatic Constant Conversion
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

  For almost every method of :class:`~pyboolector.Boolector` that creates nodes,
  instead of passing arguments of the type :class:`~pyboolector.BoolectorNode`,
  the Python API allows to pass constants as arguments.
  The only requirement is that it must be possible to derive the bit width of
  the constant operands from the remaining operands.
  For example, for binary operators like :func:`~pyboolector.Boolector.Add`,
  an operandsmay be a constant, and its bit-width will be derived from the
  other non-constant operand, e.g.: ::

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
    :func:`~pyboolector.Boolector.Not`,
    :func:`~pyboolector.Boolector.Neg`,
    :func:`~pyboolector.Boolector.Redor`,
    :func:`~pyboolector.Boolector.Redxor`,
    :func:`~pyboolector.Boolector.Redand`,
    :func:`~pyboolector.Boolector.Slice`,
    :func:`~pyboolector.Boolector.Uext`,
    :func:`~pyboolector.Boolector.Sext`,
    :func:`~pyboolector.Boolector.Inc`,
    :func:`~pyboolector.Boolector.Dec`, and
    :func:`~pyboolector.Boolector.Concat`,
    as the bit with of the resulting node cannot be determined.

Options
-------

  Boolector can be configured either via :func:`~pyboolector.Boolector.Set_opt`,
  or via environment variables of the form: ::

    BTOR<capitalized option name without '_'>=<value>

  For a list and detailed descriptions of all available options,
  see :func:`~pyboolector.Boolector.Set_opt`.

  For example, given a Boolector instance ``btor``, model generation is enabled
  either via ::

    btor.Set_opt(BTOR_OPT_MODEL_GEN, 1)

  or via setting the environment variable ::

    BTORMODELGEN=1

API Tracing
^^^^^^^^^^^

  API tracing allows to record every call to Boolector's public API. The
  resulting trace can be replayed and the replayed sequence behaves exactly
  like the original Boolector run.
  This is particularly useful for debugging purposes, as it enables replaying
  erroneous behaviour.
  API tracing can be enabled via
  setting the environment variable ``BTORAPITRACE=<filename>``.

  For example, given a Boolector instance 'btor', API tracing is enabled 
  as follows: ::

    BTORAPITRACE="error.trace"

Internals
---------

  Boolector internally maintains a directed acyclic graph (DAG) of
  expressions.
  By asserting an expression, it will be permanently added to the
  formula.
  Assumptions, in contrast, are cleared after a call to
  :func:`~pyboolector.Boolector.Sat`.
  You can query assumptions that force a formula to be unsatisfiable
  via :func:`~pyboolector.Boolector.Failed`.

Operators
^^^^^^^^^
  Boolector internally describes expressions by means of a set of base
  operators.
  Boolector's API, however, provides a richer set of operators for
  convenience, where non-base operators are internally rewritten to use
  base operators only.
  For example, two's complement (:func:`~pyboolector.Boolector.Neg`) is
  expressed by means of one's complement.

  .. note::
      This behaviour is not influenced by the configured rewrite level.

Rewriting and Preprocessing
^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Boolector simplifies expressions and the expression DAG by means of
  rewriting. It supports three so-called **rewrite levels**.
  Increasing rewrite levels increase the extent of rewriting and preprocessing
  performed.  Rewrite level of 0 is equivalent to disabling rewriting and
  preprocessing at all.

  .. note::
    Rewriting expressions by means of base operators can not be disabled,
    not even at rewrite level 0.

  Boolector not only simplifies expressions during construction
  of the expression DAG but also performs preprocessing on the DAG.
  For each call to :func:`~pyboolector.Boolector.Sat`, various simplification
  techniques and preprocessing phases are initiated.
  You can force Boolector to initiate simplifying the expression
  DAG via :func:`~pyboolector.Boolector.Simplify`.
  The rewrite level can be configured via
  :func:`~pyboolector.Boolector.Set_opt`.


Examples
--------

Quickstart Example
^^^^^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/api/python/quickstart.py
       :language: python

More Comprehensive API Usage Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/api/python/api_usage_examples.py

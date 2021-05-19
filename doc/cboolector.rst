Boolector C API documentation
=============================

.. _Boolector: https://boolector.github.io
.. _BTOR: http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf
.. _SMT-LIB v1: http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf
.. _SMT-LIB v2: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf

Interface
---------

.. toctree::
    :maxdepth: 2

    cboolector_index


Quickstart
-----------

  First, we create a Boolector instance:

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 6

  We can configure this instance via :c:func:`boolector_set_opt`
  For example, if we want to enable model generation:

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 8

  For a detailed description of all configurable options, see
  :c:func:`boolector_set_opt`.

  Next, we can generate expressions and assert formulas via
  :c:func:`boolector_assert`.

  .. note::

      Boolector's internal design is motivated by hardware design.
      Hence we do not distinguish between type *Boolean* and type *bit vector
      of length 1*.

  If incremental usage is enabled, formulas can optionally be assumed via
  :c:func:`boolector_assume`.

  .. note::

    Assumptions are invalidated after a call to :c:func:`boolector_sat`.

  Alternatively, we can parse an input file prior to creating and asserting
  expressions. For example, to parse an input file `example.btor`,
  we can use :c:func:`boolector_parse` (auto detects the input format) or
  :c:func:`boolector_parse_btor` (for parsing input files in BTOR_ format).

  .. code-block:: c

    char *error_msg;
    int status;
    int result;
    FILE *fd = fopen ("example.btor", "r");
    result = boolector_parse_btor (btor, fd, "example.btor", &error_msg, &status);

  In case the input issues a call to check sat (in case of SMT-LIB v2 or
  incremental SMT-LIB v1), this function either returns
  :c:macro:`BOOLECTOR_SAT`, :c:macro:`BOOLECTOR_UNSAT` or
  :c:macro:`BOOLECTOR_UNKNOWN`. In any other non-error case it returns
  :c:macro:`BOOLECTOR_PARSE_UNKNOWN`.
  For a more detailed description of the parsers return values, see
  :c:func:`boolector_parse`, :c:func:`boolector_parse_btor`.
  :c:func:`boolector_parse_btor2`, :c:func:`boolector_parse_smt1` and
  :c:func:`boolector_parse_smt2`.

  If the parser encounters an error, it returns
  :c:macro:`BOOLECTOR_PARSE_ERROR` and an explanation of that error is stored
  in ``error_msg``.
  If the input file specifies a (known) status of the input formula (either
  satisfiable or unsatisfiable), that status is stored in ``status``.

  As an example for generating and asserting expressions via
  :c:func:`boolector_assert`, consider the following example: ::

    0 < x <= 100 && 0 < y <= 100 && x * y < 100

  Assume that this example is given with x and y as natural numbers.
  We encode it with bit-vectors of size 8, and to preserve semantics,
  we have to ensure that the multiplication does not overflow.

  We first generate a bit-vector sort of size 8.
  
  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 11

  Then, we generate and assert the following expressions:

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 14-43

  The satisfiability of the resulting formula can be determined via
  :c:func:`boolector_sat`.

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 45

  If the resulting formula is satisfiable and model generation has been enabled
  via :c:func:`boolector_set_opt`, we can either print the resulting model via
  :c:func:`boolector_print_model`,
  or query assignments of bit vector and array variables or uninterpreted
  functions via :c:func:`boolector_bv_assignment`,
  :c:func:`boolector_array_assignment` and :c:func:`boolector_uf_assignment`.

  .. note::
      Querying assignments is not limited to variables. You can query 
      the assignment of any arbitrary expression.

  The example above is satisfiable, and we can now either query the assignments
  of variables ``x`` and ``y`` or print the resulting model via
  :c:func:`boolector_print_model`. 

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 62-63

  Boolector supports printing models in its own format ("btor") or in
  `SMT-LIB v2`_ format ("smt2"). We print the resulting model in BTOR_
  format:

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 69

  A possible model is shown below and gives the assignments of bit vector
  variables ``x`` and ``y``.
  The first column indicates the id of the input, the second column its
  assignment, and the third column its name (or symbol) if any. ::

    2 00000001 x
    3 10111111 y

  In the case that the formula includes arrays as inputs, their values at a
  certain index are indicated as follows: ::

    4[00] 01 A

  Here, A has id 4 and is an array with index and element bit width of 2, 
  and its value at index 0 is 1.

  We now print the model of the example above in `SMT-LIB v2`_ format.

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 72

  A possible model is shown below: ::

    (
      (define-fun x () (_ BitVec 8) #b00000001)
      (define-fun y () (_ BitVec 8) #b01011111)
    )

  .. note::
      Boolector internally represents arrays as uninterpreted functions and
      prints array models as models for UF.

  Finally, we have to clean up all generated expressions (see
  :ref:`c-internals` and :c:func:`boolector_release`) and delete Boolector
  instance ``btor`` via :c:func:`boolector_delete`.
  Queried assignment strings have to be freed via
  :c:func:`boolector_free_bv_assignment`,
  :c:func:`boolector_free_array_assignment` and
  :c:func:`boolector_free_uf_assignment`.

  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c
       :lines: 75-97

  The source code of the example above can be found at `examples/api/c/quickstart.c <https://github.com/boolector/boolector/tree/master/examples/api/c/quickstart.c>`_.

Options
-------

  Boolector can be configured either via :c:func:`boolector_set_opt`, 
  or via environment variables of the form: ::

    BTOR<capitalized option name without '_' and ':'>=<value>

  E.g., given a Boolector instance ``btor``, model generation is enabled either 
  via 

  .. code-block:: c

    boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);

  or via setting the environment variable:: 

    BTORMODELGEN=1

  For a list and detailed descriptions of all available options, 
  see :c:func:`boolector_set_opt`.

API Tracing
^^^^^^^^^^^

  API tracing allows to record every call to Boolector's public API. The
  resulting trace can be replayed and the replayed sequence behaves exactly 
  like the original Boolector run.
  This is particularly useful for debugging purposes, as it enables replaying
  erroneous behaviour.
  API tracing can be enabled either via :c:func:`boolector_set_trapi` or by
  setting the environment variable ``BTORAPITRACE=<filename>``.

  E.g., given a Boolector instance ``btor``, enabling API tracing is done as
  follows:

  .. code-block:: c

    FILE *fd = fopen ("error.trace", "r");
    boolector_set_trapi (btor, fd);

  or ::
  
    BTORAPITRACE="error.trace"

.. _c-internals:

Internals
---------
  Boolector internally maintains a **directed acyclic graph (DAG)** of
  expressions. As a consequence, each expression maintains a reference
  counter, which is initially set to 1.
  Each time an expression is shared, i.e., for each API call that returns
  an expression (a BoolectorNode), its reference counter is incremented
  by 1. Not considering API calls that generate expressions, this mainly
  applies to :c:func:`boolector_copy`, which simply increments the reference
  counter of an expression, and :c:func:`boolector_match_node` and
  :c:func:`boolector_match_node_by_id`, which retrieve nodes of a given
  Boolector instance by id and a given node's id.
  Expressions are released via :c:func:`boolector_release`, and if its
  reference counter is decremented to zero, it is deleted from memory.

  Note that by **asserting** an expression, it will be **permanently added** to
  the formula. This means that Boolector internally holds its reference until
  it is either eliminated via rewriting, or the Boolector instance is deleted.
  Following from that, it is safe to release an expression as soon as you
  asserted it, as long as you don't need it for further querying.

Operators
^^^^^^^^^
  Boolector internally describes expressions by means of a set of base
  operators.
  Boolector's API, however, provides a richer set of operators for
  convenience, where non-base operators are internally rewritten to use
  base operators only.
  For example, two's complement (:c:func:`boolector_neg`) is expressed by means
  of one's complement.

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
  For each call to :c:func:`boolector_sat`, various simplification techniques
  and preprocessing phases are initiated.
  You can force Boolector to initiate simplifying the expression
  DAG via :c:func:`boolector_simplify`.
  The rewrite level can be configured via :c:func:`boolector_set_opt`.

Examples
--------

Quickstart Example
^^^^^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/api/c/quickstart.c
       :language: c

Bit-Vector Examples
^^^^^^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/api/c/bv/bv1.c
     :language: c

  .. literalinclude:: ../examples/api/c/bv/bv2.c
     :language: c

Array Examples
^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/api/c/array/array1.c
     :language: c

  .. literalinclude:: ../examples/api/c/array/array2.c
     :language: c

  .. literalinclude:: ../examples/api/c/array/array3.c
     :language: c

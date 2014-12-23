Boolector C API documentation
=============================

.. _Boolector: http://fmv.jku.at/boolector
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

  First, create a Boolector instance:
    
  .. code-block:: c

    Btor *btor = boolector_new ();

  You can configure this instance via :c:func:`boolector_set_opt`
  E.g., if you want to enable model generation:

  .. code-block:: c

    boolector_set_opt (btor, "model_gen", 1);

  For a detailed description of all configurable options, see
  :c:func:`boolector_set_opt`.

  Next you can either parse an input file, and/or generate expressions to 
  be either asserted via :c:func:`boolector_assert`, or, if incremental usage
  is enabled, assumed via :c:func:`boolector_assume` (analogously to
  MiniSAT). 
  Note that Boolector's internal design is motivated by hardware design,
  hence we do not distinguish between type *Boolean* and type *bit vector
  of length 1*. 

  E.g., if you want to parse an input file "example.btor", you can either
  use :c:func:`boolector_parse` or :c:func:`boolector_parse_btor`:

  .. code-block:: c

    char *error_msg; 
    int status;
    int result;
    FILE *fd = fopen ("example.btor", "r");
    result = boolector_parse_btor (btor, fd, "example.btor", &error_msg, &status);

  Incremental usage is not enabled, hence, if the parser does not encounter
  an error, it returns :c:macro:`BOOLECTOR_UNKNOWN` (for a more detailed
  description of the parsers return values, see :c:func:`boolector_parse`).
  However, if the parser encounters an error, it returns 
  :c:macro:`BOOLECTOR_PARSE_ERROR` and an explanation of that error is 
  stored in ``error_msg``. If the input file specifies a (known) status
  of the input formula (either satisfiable or unsatisfiable), that status
  is stored in ``status``.

  As an example for generating and asserting expressions via
  :c:func:`boolector_assert`, consider the following example: ::

    0 < x <= 100, 0 < y <= 100, x * y < 100

  Given the Boolector instance created above, we generate and assert
  the following expressions:

  .. code-block:: c

    BtorNode *x = boolector_var (btor, 8, "x");
    BtorNode *y = boolector_var (btor, 8, "y");
    BtorNode *zero = boolector_zero (btor, 8);
    BtorNode *hundred = boolector_int (btor, 100, 8);

    // 0 < x
    BoolectorNode *ult_x = boolector_ult (btor, zero, x);
    boolector_assert (btor, ult_x);

    // x <= 100
    BtorNode *ulte_x = boolector_ulte (btor, x, hundred);
    boolector_assert (btor, ulte_x);

    // 0 < y
    BtorNode *ult_y = boolector_ult (btor, zero, y);
    boolector_assert (btor, ult_y);

    // y <= 100
    BtorNode *ulte_y = boolector_ulte (btor, y, hundred);
    boolector_assert (btor, ulte_y);

    // x * y
    BtorNode *mul = boolector_mul (btor, x, y);

    // x * y < 100
    BtorNode *ult = boolector_ult (btor, mul, hundred);
    boolector_assert (btor, ult);
    BtorNode *umulo = boolector_umulo (btor, x, y);
    BtorNode *numulo = boolector_not (btor, umulo);  // prevent overflow
    boolector_assert (btor, numulo)

  After parsing an input file and/or asserting/assuming expressions,
  the satisfiability of the resulting formula can be determined via
  :c:func:`boolector_sat`. If the resulting formula is satisfiable and model 
  generation has been enabled via :c:func:`boolector_set_opt`, you can either
  print the resulting model via :c:func:`boolector_print_model`,
  or query assignments
  of bit vector and array variables or uninterpreted functions via
  :c:func:`boolector_bv_assignment`, :c:func:`boolector_array_assignment` and
  :c:func:`boolector_uf_assignment`.
  Note that querying assignments is not limited to variables---you can query 
  the assignment of any arbitrary expression.

  E.g., given the example above, we first determine if the formula is
  satisfiable via :c:func:`boolector_sat` (which it is):

  .. code-block:: c

    int result = boolector_sat (btor);

  Now you can either query the assignments of variables ``x`` and ``y``:

  .. code-block:: c

    char *xstr = boolector_bv_assignment (btor, x);  // returns "00000100"
    char *ystr = boolector_bv_assignment (btor, y);  // returns "00010101"

  or print the resulting model via :c:func:`boolector_print_model`. 
  Boolector supports printing models in its own format ("btor") or in
  `SMT-LIB v2`_ format ("smt2"). Printing the resulting model in 
  Boolector's own format:

  .. code-block:: c

    boolector_print_model (btor, "btor", stdout);

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

  Printing the above model in `SMT-LIB v2`_ format:

  .. code-block:: c

    boolector_print_model (btor, "smt2", stdout);

  A possible model would be: ::

    (model
      (define-fun x () (_ BitVec 8) #b00000100)
      (define-fun y () (_ BitVec 8) #b00010101)
      (define-fun y (
       (y_x0 (_ BitVec 2)))
       (ite (= y_x0 #b00) #b01
         #00))
    )

  Note that Boolector internally represents arrays as uninterpreted functions,
  hence array models are printed as models for UF (without an explicit
  typecast).

  Finally, in case that you generated expressions, you have to clean up, 
  i.e., release those expressions 
  (see :ref:`c-internals` and :c:func:`boolector_release`), 
  and delete Boolector instance ``btor`` via :c:func:`boolector_delete`.
  E.g., following from the example above, we proceed as follows:

  .. code-block:: c

    boolector_release (btor, x);
    boolector_release (btor, y);
    boolector_release (btor, zero);
    boolector_release (btor, hundred);
    boolector_release (btor, ult_x);
    boolector_release (btor, ulte_x);
    boolector_release (btor, ult_y);
    boolector_release (btor, ulte_y);
    boolector_release (btor, mul);
    boolector_release (btor, ult);
    boolector_release (btor, numulo);
    boolector_release (btor, umulo);
    boolector_delete (btor);

  Note that in case you generated assignment strings you have to release them
  as well:

  .. code-block:: c

    boolector_free_bv_assignment (btor, xstr);
    boolector_free_bv_assignment (btor, ystr);


Options
-------

  Boolector can be configured either via :c:func:`boolector_set_opt`, 
  or via environment variables of the form: ::

    BTOR<capitalized option name without '_'>=<value>

  For a list and detailed descriptions of all available options, 
  see :c:func:`boolector_set_opt`.

  E.g., given a Boolector instance ``btor``, model generation is enabled either 
  via 

  .. code-block:: c

    boolector_set_opt (btor, "model_gen", 1);

  or via setting the environment variable:: 

    BTORMODELGEN=1

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
  Boolector internally maintains a directed acyclic graph (DAG) of
  expressions. As a consequence, each expression maintains a reference
  counter, which is initially set to 1. 
  Each time an expression is shared, i.e. for each API call that returns
  an expression (a BoolectorNode), its reference counter is incremented
  by 1. Not considering API calls that generate expressions, this mainly
  applies to :c:func:`boolector_copy`, which simply increments the reference
  counter of an expression, and :c:func:`boolector_match_node` resp.
  :c:func:`boolector_match_node_by_id`, which retrieve nodes of a given
  Boolector instance by id resp. a given node's id.
  Expressions are released via :c:func:`boolector_release`, and if its
  reference counter is decremented to zero, it is deleted from memory.
  Note that by asserting an expression, it will be permanently added to the
  formula, i.e. Boolector internally holds its reference until it is either
  eliminated via rewriting, or the Boolector instance is deleted. 
  Following from that, it is safe to release an expression as soon as you
  asserted it, as long as you don't need it for further querying.

Operators
^^^^^^^^^
  Boolector internally describes expressions by means of a set of base
  operators as documented in BTOR_.
  Boolector's API, however, provides a richer set of operators for
  convenience, where non-base operators are internally rewritten to use
  base operators only.
  E.g., two's complement (:c:func:`boolector_neg`) is rewritten as one's
  complement and addition of 1. 
  Note that this behaviour is not influenced by the rewrite level chosen.

Rewriting
^^^^^^^^^
  Boolector simplifies expressions and the expression DAG by means of 
  rewriting and supports three so-called rewrite levels.
  Increasing rewrite levels increase the extent of rewriting performed,
  and a rewrite level of 0 is equivalent to disabling rewriting at all.
  Note that Boolector not only simplifies expressions during construction
  of the expression DAG---for each call to :c:func:`boolector_sat`,
  various simplification techniques and rewriting phases are initiated.
  You can force Boolector to initiate rewriting and simplify the expression
  DAG via :c:func:`boolector_simplify`.
  The rewrite level can be configured via :c:func:`boolector_set_opt`.

Examples
--------

Bit vector examples
^^^^^^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/bv/bv1.c
     :language: c

  .. literalinclude:: ../examples/bv/bv2.c
     :language: c

Array examples
^^^^^^^^^^^^^^
  .. literalinclude:: ../examples/array/array1.c
     :language: c

  .. literalinclude:: ../examples/array/array2.c
     :language: c

  .. literalinclude:: ../examples/array/array3.c
     :language: c

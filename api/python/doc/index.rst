Welcome to Boolector's Python API documentation!
================================================

Introduction
------------

  Boolector_ is an SMT solver for the quantifier-free theory of bit vectors
  with arrays. It supports BTOR_, `SMT-LIB v1`_, and `SMT-LIB v2`_
  as input format and can be either used as a stand-alone SMT solver, or as
  back end for other tools via its public API.
  This is the documentation of Boolector's public **Python interface**.
  For further information and the latest version of Boolector, please refer
  to http://fmv.jku.at/boolector.

  .. _Boolector: http://fmv.jku.at/boolector
  .. _BTOR: http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf
  .. _SMT-LIB v1: http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf
  .. _SMT-LIB v2: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf


Interface
---------

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`


Quickstart
----------


  First, create a Boolector instance: ::
    
    btor = Boolector () 

  You can configure this instance via :func:`~boolector.Boolector.Set_opt`.
  E.g., if you want to enable model generation: ::
   
    btor.Set_opt ("model_gen", 1)
  
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
  
    x = btor.Var(8, "X")
    y = btor.Var(8, "Y")
    zero = btor.Const(0, 8)
    hundred = btor.Const(100, 8)
 
    # 0 < x
    slt_x = btor.Slt(zero, x)
    btor.Assert(slt_x)
 
    # x <= 100
    slte_x = btor.Slte(x, hundred)
    btor.Assert(slte_x)
 
    # 0 < y
    slt_y = btor.Slt(zero, y)
    btor.Assert(slt_y)
  
    # y <= 100
    slte_y = btor.Slte(y, hundred)
    btor.Assert(slte_y)
  
    # x * y
    mul = btor.Mul(x, y)
  
    # x * y < 100
    slt = btor.Slt(mul, hundred)
    btor.Assert(slt)
    smulo = btor.Smulo(x, y)
    nsmulo = btor.Not(smulo)  # prevent overflow
    btor.Assert(nsmulo)
 
  After parsing an input file and/or asserting/assuming expressions,
  the satisfiability of the resulting formula can be determined via
  :func:`~boolector.Boolector.Sat`.
  If the resulting formula is satisfiable and model generation has been
  enabled via :func:`~boolector.Boolector.Set_opt`, you can either
  print the resulting model via :func:`~boolector.Boolector.Print_model`,
  or query assignments
  of bit vector and array variables or uninterpreted functions via
  :data:`~boolector._BoolectorNode.assignment`. 
  Note that querying assignments is not limited to variables---you can query 
  the assignment of any arbitrary expression.
 
  E.g., given the example above, we first determine if the formula is
  satisfiable via :func:`~boolector.Boolector.Sat` (which it is): ::
  
   result = btor.Sat()
  
  Now you can either query the assignments of variables ``X`` and ``Y`` ::

    print (x.assignment);  # prints: 00001001
    print (y.assignment);  # prints: 00000010
    print ("{} {}".format(x.symbol, x.assignment))  # prints: X 00001001
    print ("{} {}".format(y.symbol, y.assignment))  # prints: Y 00000010

  or print the resulting model to stdout via 
  :func:`~boolector.Boolector.Print_model` : ::
  
    btor.Print_model()
  
  A possible model would be: ::
  
    2 00001001 X
    3 00000010 Y
  
  which in this case indicates the assignments of bit vector variables 
  X and Y. Note that the first column indicates the id of an input, 
  the second column its assignment, and the third column its name (or symbol)
  if any. 
  In the case that the formula includes arrays as input, their values at a
  certain index are indicated as follows: ::

    4[0] 1 A \endverbatim
  
  where A has id 4 and is an array with index and element bit width of 1, 
  and its value at index 0 is 1.


Options
-------
 
  Boolector can be configured either via :func:`~boolector.Boolector.Set_opt`, 
  or via environment variables of the form: ::

    BTOR<capitalized option name without '_'>=<value>

  For a list and detailed descriptions of all available options, 
  see :func:`~boolector.Boolector.Set_opt`.
 
  E.g., given a Boolector instance ``btor``, model generation is enabled either 
  via ::
  
    btor.Set_opt ("model_gen", 1)
  
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
 

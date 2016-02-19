/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BOOLECTOR_H_INCLUDED
#define BOOLECTOR_H_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "btortypes.h"

/*------------------------------------------------------------------------*/

/*!
  Preprocessor constant representing status ``unknown``.

  .. seealso::
    boolector_sat, boolector_limited_sat, boolector_simplify
*/
#define BOOLECTOR_UNKNOWN BTOR_RESULT_UNKNOWN
/*!
  Preprocessor constant representing status ``satisfiable``.

  .. seealso::
    boolector_sat, boolector_limited_sat, boolector_simplify
*/
#define BOOLECTOR_SAT BTOR_RESULT_SAT
/*!
  Preprocessor constant representing status ``unsatisfiable``.

  .. seealso::
    boolector_sat, boolector_limited_sat, boolector_simplify
*/
#define BOOLECTOR_UNSAT BTOR_RESULT_UNSAT
/*!
  Preprocessor constant representing status ``parse error``.

  .. seealso::
    boolector_parse
*/
#define BOOLECTOR_PARSE_ERROR 1

/*------------------------------------------------------------------------*/

/*!
  Create a new instance of Boolector.

  :return: New Boolector instance.
*/
Btor *boolector_new (void);

/*!
  Clone an instance of Boolector.

  The resulting Boolector instance is an exact copy of given Boolector instance
  ``btor``.  Consequently, in a clone and its parent, nodes with the same id
  correspond to each other.  Use boolector_match_node to match corresponding
  nodes.

  :param btor: Original Boolector instance.
  :return: The exact (but disjunct) copy of the Boolector instance ``btor``.

  .. note::
    If Lingeling is used as SAT solver, Boolector can be cloned at any time,
    since Lingeling also supports cloning. However, if you use boolector_clone
    with MiniSAT or PicoSAT (no cloning support), Boolector can only be cloned
    prior to the first boolector_sat call.
*/
Btor *boolector_clone (Btor *btor);

/*!
  Delete a boolector instance and free its resources.

  :param btor: Boolector instance.

  .. note::
    Expressions that have not been released properly will not be
    deleted from memory. Use boolector_get_refs to debug reference
    counting. You can also set option ``auto_cleanup`` via
    boolector_set_opt in order to do the cleanup automatically.
*/
void boolector_delete (Btor *btor);

/*!
   Set a termination callback.

   :param btor:  Boolector instance.
   :param fun:   The termination callback function.
   :param state: The argument to the termination callback function.

  .. seealso::
    boolector_terminate
 */
void boolector_set_term (Btor *btor, int (*fun) (void *), void *state);

/*!
  Determine if a given Boolector instance has been terminated (and or
  terminate Boolector) via the previously configured termination callback
  function.

  :param btor: Boolector instance.
  :return: True if Boolector is terminated, and false otherwise.

  .. seealso::
    boolector_set_term
 */
int boolector_terminate (Btor *btor);

/*!
  Set a verbosity message prefix.

  :param btor: Boolector instance.
  :param prefix: Prefix string.
*/
void boolector_set_msg_prefix (Btor *btor, const char *prefix);

/*!
  Get the number of external references to the boolector library.

  Internally, Boolector manages an expression DAG with reference counting.
  Use boolector_release to properly release an expression.  Before you
  finally call boolector_delete, boolector_get_refs should return 0.

  :param btor: Boolector instance.
  :return: Number of external references owned by the user.
*/
int boolector_get_refs (Btor *btor);

/*!
  Reset time statistics.

  :param btor: Boolector instance.
*/
void boolector_reset_time (Btor *btor);

/*!
  Reset statistics (time statistics not included).

  :param btor: Boolector instance.
*/
void boolector_reset_stats (Btor *btor);

/*!
  Print statistics.

  :param btor: Boolector instance.
*/
void boolector_print_stats (Btor *btor);

/*!
  Set the output API trace file and enable API tracing.

  :param btor: Boolector instance.
  :param apitrace: Output file.

  .. note::
    The API trace output file can also be set via the environment variable
    BTORAPITRACE=<filename>.
*/
void boolector_set_trapi (Btor *btor, FILE *apitrace);

/*!
  Return API trace file.

  :param btor: Boolector instance.
  :return: API trace output file.
*/
FILE *boolector_get_trapi (Btor *btor);

/*------------------------------------------------------------------------*/

/*!
  Add a constraint.

  Use this function to assert ``node``.  Added constraints can not be deleted
  anymore. After ``node`` has been asserted, it can be safely released by
  boolector_release.

  :param btor: Boolector instance.
  :param node: Bit vector expression with bit width one.
*/
void boolector_assert (Btor *btor, BoolectorNode *node);

/*!
  Add an assumption.

  Use this function to assume ``node``. You must enable Boolector's
  incremental usage via boolector_set_opt before you can add assumptions.  In
  contrast to assertions added via boolector_assert, assumptions are discarded
  after each call to boolector_sat. Assumptions and assertions are logically
  combined via Boolean ``and``. Assumption handling in Boolector is analogous
  to assumptions in MiniSAT.

  :param btor: Boolector instance.
  :param node: Bit vector expression with bit width one.
*/
void boolector_assume (Btor *btor, BoolectorNode *node);

/*!
  Determine if assumption ``node`` is a failed assumption.

  Failed assumptions are those assumptions, that force an input formula
  to become unsatisfiable. Failed assumptions handling in Boolector is
  analogous to failed assumptions in MiniSAT.

  :param btor: Boolector instance.
  :param node: Bit vector expression with bit width one.
  :return: 1 if assumption is failed, and 0 otherwise.

  .. seealso::
    boolector_assume
*/
int boolector_failed (Btor *btor, BoolectorNode *node);

/*!
  Add all assumptions as assertions.

  :param btor: Boolector instance.

  .. seealso::
    boolector_assume
*/
void boolector_fixate_assumptions (Btor *btor);

/*!
  Resets all added assumptions.

  :param btor: Boolector instance.

  .. seealso::
    boolector_assume
*/
void boolector_reset_assumptions (Btor *btor);

/*!
  Solve an input formula.

  An input formula is defined by constraints added via boolector_assert.
  You can guide the search for a solution to an input formula by making
  assumptions via boolector_assume.
  Note that assertions and assumptions are combined by boolean ``and``.

  If you want to call this function multiple times, you must enable
  Boolector's incremental usage mode via boolector_set_opt
  before. Otherwise, this function may only be called once.

  :param btor: Boolector instance.
  :return: BOOLECTOR_SAT if the instance is satisfiable and BOOLECTOR_UNSAT if the instance is unsatisfiable.

  .. seealso::
    boolector_bv_assignment, boolector_array_assignment
*/
int boolector_sat (Btor *btor);

/*!
  Solve an input formula and limit the search by the number of lemmas
  generated and the number of conflicts encountered by the underlying
  SAT solver.

  An input formula is defined by constraints added via boolector_assert.
  You can guide the search for a solution to an input formula by making
  assumptions via boolector_assume.

  If you want to call this function multiple times then you must enable
  Boolector's incremental usage mode via boolector_set_opt before.
  Otherwise, this function can only be called once.

  :param btor: Boolector instance.
  :param lod_limit: Limit for lemmas on demand (-1 unlimited).
  :param sat_limit: Conflict limit for SAT solver (-1 unlimited).
  :return: BOOLECTOR_SAT if the input formula is satisfiable (under possibly given assumptions), BOOLECTOR_UNSAT if the instance is unsatisfiable, and  BOOLECTOR_UNKNOWN if the instance could not be solved within given limits.

  .. seealso::
    boolector_bv_assignment, boolector_array_assignment
*/
int boolector_limited_sat (Btor *btor, int lod_limit, int sat_limit);

/*!
  Simplify current input formula.

  :param btor: Boolector instance.
  :return: BOOLECTOR_SAT if the input formula was simplified to true, BOOLECTOR_UNSAT if it was simplified to false, and BOOLECTOR_UNKNOWN otherwise.

  .. note::
    Each call to boolector_sat simplifies the input formula as a preprocessing
    step.
*/
int boolector_simplify (Btor *btor);

/*------------------------------------------------------------------------*/

/*!
  Set the SAT solver to use.

  Currently, we support ``Lingeling``, ``PicoSAT``, and ``MiniSAT`` as string
  value of ``solver`` (case insensitive).  This is however
  only possible if the corresponding solvers were enabled at compile time.
  Call this function after boolector_new.

  :param btor: Boolector instance
  :param solver: Solver identifier string.
  :return: Non-zero value if setting the SAT solver was successful.
*/
int boolector_set_sat_solver (Btor *btor, const char *solver);

#ifdef BTOR_USE_LINGELING
/*!
  Use Lingeling as SAT solver.

  This function is only available if Lingeling was enabled at compile time.
  Call this function after boolector_new.

  :param btor: Boolector instance.
  :param optstr: Lingeling option string.
  :param nofork: Do not use fork/clone for Lingeling.
  :return: Non-zero value if setting the SAT solver was successful.
*/
int boolector_set_sat_solver_lingeling (Btor *btor,
                                        const char *optstr,
                                        int nofork);
#endif

#ifdef BTOR_USE_PICOSAT
/*!
  Use PicoSAT as SAT solver.

  This function is only available if PicoSAT was enabled at compile time.
  Call this function after boolector_new.

  :param btor: Boolector instance.
  :return: Non-zero value if setting the SAT solver was successful.
*/
int boolector_set_sat_solver_picosat (Btor *btor);
#endif

#ifdef BTOR_USE_MINISAT
/*!
  Use MiniSAT as SAT solver.

  This function is only available if MiniSAT was enabled at compile time.
  Call this function after boolector_new.

  :param btor: Boolector instance.
  :return: Non-zero value if setting the SAT solver was successful.
*/
int boolector_set_sat_solver_minisat (Btor *btor);
#endif

/*------------------------------------------------------------------------*/

/*!
  Set option.

  List of available options:

  * **model_gen**

    | Enable (``value``: 1 or 2) or disable (``value``: 0) generation of a model
  for satisfiable instances. | There are two modes for model generation:

    * generate model for asserted expressions only (``value``: 1)
    * generate model for all expressions (``value``: 2)

  * **incremental**

    | Enable (``value``: 1) incremental mode.
    | Note that incremental usage turns off some optimization techniques.
  Disabling incremental usage is currently not supported.

  * **incremental_all**

    | Enable (``value``: 1) or disable (``value``: 0) incremental solving of all
  formulas when parsing an input file. | Note that currently, incremental mode
  while parsing an input file is only supported for `SMT-LIB v1`_ input.

  * **incremental_in_depth**

    | Set incremental in-depth mode width (``value``: uint32_t) when parsing an
  input file. | Note that currently, incremental mode while parsing an input
  file is only supported for `SMT-LIB v1`_ input.

  * **incremental_look_ahead**

    | Set incremental look_ahead mode width (``value``: uint32_t) when parsing
  an input file. | Note that currently, incremental mode while parsing an input
  file is only supported for `SMT-LIB v1`_ input.

  * **incremental_interval**

    | Set incremental interval mode width (``value``: uint_32) when parsing an
  input file. | Note that currently, incremental mode while parsing an input
  file is only supported for `SMT-LIB v1`_ input.

  * **input_format**

    | Force input file format (``value``: `BTOR
  <http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf>`_: -1, `SMT-LIB v1
  <http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf>`_: 1, `SMT-LIB
  v2 <http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf>`_:
  2) when parsing an input file. | If unspecified, Boolector automatically
  detects the input file format while parsing.

  * **output_number_format**

    | Force output number format (``value``: binary: 0, hexadecimal: 1, decimal:
  2): | Boolector uses binary by default.

  * **output_format**

    | Force output file format (``value``: BTOR_: -1, `SMT-LIB v1`_: 1, `SMT-LIB
  v2`_: 2). | Boolector uses BTOR_ by default.

  * **rewrite_level**

    | Set the rewrite level (``value``: 0-3) of the rewriting engine.
    | Boolector uses rewrite level 3 by default, rewrite levels are classified
  as follows:

    * 0: no rewriting
    * 1: term level rewriting
    * 2: more simplification techniques
    * 3: full rewriting/simplification

    | Do not alter the rewrite level of the rewriting engine after creating
  expressions.

  * **rewrite_level_pbr**

    | Set the rewrite level (``value``: 0-3) for partial beta reduction.
    | Boolector uses rewrite level 1 by default. Rewrite levels are classified
  as above.

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

  :param btor: Boolector instance.
  :param opt: Option opt.
  :param val:  Option value.
*/
void boolector_set_opt (Btor *btor, BtorOption opt, uint32_t val);

/*!
  Get the current value of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Current value of ``opt``.
*/
uint32_t boolector_get_opt (Btor *btor, BtorOption opt);

/*!
  Get the min value of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Min value of ``opt``.
*/
uint32_t boolector_get_opt_min (Btor *btor, BtorOption opt);

/*!
  Get the max value of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Max value of ``opt``.
*/
uint32_t boolector_get_opt_max (Btor *btor, BtorOption opt);

/*!
  Get the default value of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Default value of ``opt``.
*/
uint32_t boolector_get_opt_dflt (Btor *btor, BtorOption opt);

/*!
  Get the long name of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Short opt of ``opt``.
*/
const char *boolector_get_opt_lng (Btor *btor, BtorOption opt);

/*!
  Get the short name of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Short opt of ``opt``.
*/
const char *boolector_get_opt_shrt (Btor *btor, BtorOption opt);

/*!
  Get the description of an option.

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: Description of ``opt``.
*/
const char *boolector_get_opt_desc (Btor *btor, BtorOption opt);

/*!
  Check if Boolector has a given option.

  Given a Boolector instance ``btor``, you can use this in combination
  with boolector_has_opt and boolector_next_opt in order to iterate over
  Boolector options as follows:

  .. code-block:: c

    for (s = boolector_first_opt_noref (btor); boolector_has_opt_noref (btor,
  s); s = boolector_next_opt_noref (btor, s)) {...}

  :param btor: Btor instance.
  :param opt: Option opt.
  :return true if Boolector has the given option, and false otherwise.
*/
bool boolector_has_opt (Btor *Btor, BtorOption opt);

/*!
  Get the opt of the first option in Boolector's option list.

  Given a Boolector instance ``btor``, you can use this in combination
  with boolector_has_opt and boolector_next_opt in order to iterate over
  Boolector options as follows:

  .. code-block:: c

    for (s = boolector_first_opt_noref (btor); boolector_has_opt_noref (btor,
  s); s = boolector_next_opt_noref (btor, s)) {...}

  :param btor: Btor instance.
  :return: opt of the first option in Boolector's option list.
*/
BtorOption boolector_first_opt (Btor *btor);

/*!
  Given current option ``opt``, get the opt of the next option in Boolector's
  option list.

  Given a Boolector instance ``btor``, you can use this in combination
  with boolector_has_opt and boolector_next_opt in order to iterate over
  Boolector options as follows:

  .. code-block:: c

    for (s = boolector_first_opt_noref (btor); s; s = boolector_next_opt_noref
  (btor, s)) {...}

  :param btor: Btor instance.
  :param opt: Option opt.
  :return: opt of the next option in Boolector's option list, or 0 if no such next option does exist.
*/
BtorOption boolector_next_opt (Btor *btor, BtorOption opt);

/*------------------------------------------------------------------------*/

/*!
  Copy expression (increments reference counter).

  :param btor: Boolector instance.
  :param node: Boolector node to be copied.
  :return: Node ``node`` with reference counter incremented.
*/
BoolectorNode *boolector_copy (Btor *btor, BoolectorNode *node);

/*!
  Release expression (decrements reference counter).

  :param btor: Boolector instance.
  :param node: Boolector node to be released.
*/
void boolector_release (Btor *btor, BoolectorNode *node);

/*!
  Release all expressions and sorts.

  :param btor: Boolector instance.

  .. seealso::
    boolector_release, boolector_release_sort
*/
void boolector_release_all (Btor *btor);

/*!
  Create bit vector constant representing the bit vector ``bits``.

  :param btor: Boolector instance.
  :param bits: Non-empty and terminated string consisting of zeroes and/or ones representing the bit vector constant specified by ``bits``.
  :return: Bit vector constant with bit width ``strlen (bits)``.
*/
BoolectorNode *boolector_const (Btor *btor, const char *bits);

/*!
  Create bit vector constant zero with bit width ``width``.

  :param btor: Boolector instance.
  :param width: Number of bits which must be greater than zero.
  :return: Bit vector constant zero with bit width ``width``.
*/
BoolectorNode *boolector_zero (Btor *btor, int width);

/*!
  Create bit vector constant zero with bit width one.

  :param btor: Boolector instance.
  :return: Bit vector constant zero with bit width one.
*/
BoolectorNode *boolector_false (Btor *btor);

/*!
  Create bit vector constant with bit width ``width``, where each bit is set to
  one.

  :param btor: Boolector instance.
  :param width: Number of bits which must be greater than zero.
  :return: Bit vector constant -1 with bit width ``width``.
*/
BoolectorNode *boolector_ones (Btor *btor, int width);

/*!
  Create constant true. This is represented by the bit vector constant one
  with bit width one.

  :param btor: Boolector instance.
  :return: Bit vector constant one with bit width one.
*/
BoolectorNode *boolector_true (Btor *btor);

/*!
  Create bit vector constant one with bit width ``width``.

  :param btor: Boolector instance.
  :param width: Number of bits which must be greater than zero.
  :return: Bit vector constant one with bit width ``width``.
*/
BoolectorNode *boolector_one (Btor *btor, int width);

/*!
  Create bit vector constant representing the unsigned integer ``u`` with bit
  width ``width``.

  The constant is obtained by either truncating bits or by
  unsigned extension (padding with zeroes).

  :param btor: Boolector instance.
  :param u: Unsigned integer value.
  :param width: Number of bits which must be greater than zero.
  :return: Bit vector constant with bit width ``width``.
*/
BoolectorNode *boolector_unsigned_int (Btor *btor, unsigned u, int width);

/*!
  Create bit vector constant representing the signed integer ``i`` with bit
  width ``width``.

  The constant is obtained by either truncating bits or by
  signed extension (padding with ones).

  :param btor: Boolector instance.
  :param i: Signed integer value.
  :param width: Number of bits which must be greater than zero.
  :return: Bit vector constant with bit width ``width``.
*/
BoolectorNode *boolector_int (Btor *btor, int i, int width);

/*!
  Create a bit vector variable with bit width ``width`` and symbol ``symbol``.

  A variable's symbol is used as a simple means of identification, either when
  printing a model via boolector_print_model, or generating file dumps via
  boolector_dump_btor and boolector_dump_smt2.  A symbol
  must be unique but may be NULL in case that no symbol should be assigned.

  :param btor: Boolector instance.
  :param width: Number of bits which must be greater than zero.
  :param symbol: Name of variable.
  :return: Bit vector variable with bit width ``width`` and symbol ``symbol``.

  .. note:: In contrast to composite expressions, which are maintained uniquely w.r.t. to their kind, inputs (and consequently, bit width), variables are not. Hence, each call to this function returns a fresh bit vector variable.
*/
BoolectorNode *boolector_var (Btor *btor, int width, const char *symbol);

/*!
  Create a one-dimensional bit vector array of size ``2^index_width``
  with elements of bit width ``elem_width``.

  An array variable's symbol is used as a simple means of identification,
  either when printing a model via boolector_print_model, or generating file
  dumps via boolector_dump_btor and boolector_dump_smt2.
  A symbol must be unique but may be NULL in case that no symbol should be
  assigned.

  :param btor: Boolector instance.
  :param elem_width: Bit width of array elements (must be greater than zero).
  :param index_width: Bit width of array indices (must be greater than zero).
  :param symbol: Name of array variable.
  :return: Bit vector array of size ``2^index_width`` with elements of bit width ``elem_width``, and symbol ``symbol``.

  .. note::
    In contrast to composite expressions, which are maintained uniquely w.r.t.
    to their kind, inputs (and consequently, bit width), array variables are
    not.  Hence, each call to boolector_array with the same arguments will
    return a fresh array variable.
*/
BoolectorNode *boolector_array (Btor *btor,
                                int elem_width,
                                int index_width,
                                const char *symbol);

/*!
  Create an uninterpreted function with sort ``sort`` and symbol ``symbol``.
  ``btor`` Boolector instance.

  An uninterpreted function's symbol is used as a simple means of
  identification, either when printing a model via boolector_print_model, or
  generating file dumps via boolector_dump_btor and
  boolector_dump_smt2.  A symbol must be unique but may be NULL in case that no
  symbol should be assigned.

  :param sort: Sort of the uninterpreted function.
  :param symbol: Name of the uninterpreted function.
  :return: Uninterpreted function of sort ``sort`` and symbol ``symbol``.

  .. note::
    In contrast to composite expressions, which are maintained
    uniquely w.r.t. to their kind, inputs (and consequently, bit width),
    uninterpreted functions are not.
    Hence, each call to this function returns a fresh uninterpreted function.

  .. seealso::
    boolector_apply, boolector_fun_sort
*/
BoolectorNode *boolector_uf (Btor *btor,
                             BoolectorSort sort,
                             const char *symbol);

/*!
  Create the one's complement of bit vector ``node``.

  :param btor: Boolector instance.
  :param node: Bit Vector node.
  :return: Bit vector representing the one's complement of ``node`` with the same bit width as ``node``.
*/
BoolectorNode *boolector_not (Btor *btor, BoolectorNode *node);

/*!
  Create the two's complement of bit vector ``node``.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :return: Bit vector representing the two's complement of ``node`` with the same bit width as ``node``.
*/
BoolectorNode *boolector_neg (Btor *btor, BoolectorNode *node);

/*!
  Create *or* reduction of node ``node``.

  All bits of node ``node`` are combined by a Boolean *or*.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_redor (Btor *btor, BoolectorNode *node);

/*!
  Create *xor* reduction of node ``node``.

  All bits of ``node`` are combined by a Boolean *xor*.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_redxor (Btor *btor, BoolectorNode *node);

/*!
  Create *and* reduction of node ``node``.

  All bits of ``node`` are combined by a Boolean *and*.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_redand (Btor *btor, BoolectorNode *node);

/*!
  Create a bit vector slice of ``node`` from index ``upper`` to index ``lower``.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :param upper: Upper index which must be greater than or equal to zero, and less than the bit width of ``node``.
  :param lower: Lower index which must be greater than or equal to zero, and less than or equal to ``upper``.
  :return: Bit vector with bit width ``upper - lower + 1``.
*/
BoolectorNode *boolector_slice (Btor *btor,
                                BoolectorNode *node,
                                int upper,
                                int lower);

/*!
  Create unsigned extension.

  The bit vector ``node`` is padded with ``width`` * zeroes.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :param width: Number of zeroes to pad.
  :return: A bit vector extended by ``width`` zeroes.
*/
BoolectorNode *boolector_uext (Btor *btor, BoolectorNode *node, int width);

/*!
  Create signed extension.

  The bit vector ``node`` is padded with ``width`` bits where the value
  depends on the value of the most significant bit of node ``n``.

  :param btor: Boolector instance.
  :param node: Bit vector node.
  :param width: Number of bits to pad.
  :return: A bit vector extended by ``width`` bits.
*/
BoolectorNode *boolector_sext (Btor *btor, BoolectorNode *node, int width);

/*!
  Create boolean implication.

  The parameters ``n0`` and ``n1`` must have bit width one.

  :param btor: Boolector instance.
  :param n0: Bit vector node representing the premise.
  :param n1: Bit vector node representing the conclusion.
  :return: Implication n0 => n1 with bit width one.
*/
BoolectorNode *boolector_implies (Btor *btor,
                                  BoolectorNode *n0,
                                  BoolectorNode *n1);

/*!
  Create Boolean equivalence.

  The parameters ``n0`` and ``n1`` must have bit width one.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Equivalence n0 <=> n1 with bit width one.
*/
BoolectorNode *boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a bit vector *xor*.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a bit vector *xnor*.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_xnor (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a bit vector *and*.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a bit vector *nand*.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_nand (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a bit vector *or*.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a bit vector *nor*.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create bit vector or array equality.

  Both operands are either bit vectors with the same bit width or arrays
  of the same type.

  :param btor: Boolector instance.
  :param n0: First operand.
  :param n1: Second operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create bit vector or array inequality.

  Both operands are either bit vectors with the same bit width or arrays
  of the same type.

  :param btor: Boolector instance.
  :param n0: First operand.
  :param n1: Second operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create bit vector addition.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector addition with the same bit width as the operands.
*/
BoolectorNode *boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create an unsigned bit vector addition overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the addition of ``n0`` and ``n1`` overflows in case both operands are treated unsigned.
*/
BoolectorNode *boolector_uaddo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create a signed bit vector addition overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the addition of ``n0`` and ``n1`` overflows in case both operands are treated signed.
*/
BoolectorNode *boolector_saddo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create a bitvector multiplication.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector multiplication with the same bit width as the operands.
*/
BoolectorNode *boolector_mul (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create an unsigned bit vector multiplication overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the multiplication of ``n0`` and ``n1`` overflows in case both operands are treated unsigned.
*/
BoolectorNode *boolector_umulo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create signed multiplication overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the multiplication of ``n0`` and ``n1`` overflows in case both operands are treated signed.
*/
BoolectorNode *boolector_smulo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create an unsigned less than.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_ult (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a signed less than.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create an unsigned less than or equal.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_ulte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a signed less than or equal.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_slte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create an unsigned greater than.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a signed greater than.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create an unsigned greater than or equal.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_ugte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a signed greater than or equal.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one.
*/
BoolectorNode *boolector_sgte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a logical shift left.

  Given node ``n1``, the value it represents is the number of zeroes shifted
  into node ``n0`` from the right.

  :param btor: Boolector instance.
  :param n0: First bit vector operand where the bit width is a power of two and greater than 1.
  :param n1: Second bit vector operand with bit width log2 of the bit width of ``n0``.
  :return: Bit vector with the same bit width as ``n0``.
*/
BoolectorNode *boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a logical shift right.

  Given node ``n1``, the value it represents is the number of zeroes shifted
  into node ``n0`` from the left.

  :param btor: Boolector instance.
  :param n0: First bit vector operand where the bit width is a power of two and greater than 1.
  :param n1: Second bit vector operand with bit width log2 of the bit width of ``n0``.
  :return: Bit vector with the same bit width as ``n0`` and ``n1``.
*/
BoolectorNode *boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create an arithmetic shift right.

  Analogously to boolector_srl, but
  whether zeroes or ones are shifted in depends on the most significant bit
  of ``n0``.

  :param btor: Boolector instance.
  :param n0: First bit vector operand where the bit width is a power of two and greater than 1.
  :param n1: Second bit vector operand with bit width log2 of the bit width of ``n0``.
  :return: Bit vector with the same bit width as ``n0``.
*/
BoolectorNode *boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a rotate left.

  Given bit vector node ``n1``, the value it represents is the number of bits
  by which node ``n0`` is rotated to the left.

  :param btor: Boolector instance.
  :param n0: First bit vector operand where the bit width is a power of two and greater than 1.
  :param n1: Second bit vector operand with bit width log2 of the bit width of ``n0``.
  :return: Bit vector with the same bit width as ``n0``.
*/
BoolectorNode *boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a rotate right.

  Given bit vector node ``n1``, the value it represents is the number of bits by
  which node ``n0`` is rotated to the right.

  :param btor: Boolector instance.
  :param n0: First bit vector operand where the bit width is a power of two and greater than 1.
  :param n1: Second bit vector operand with bit width log2 of the bit width of ``n0``.
  :return: Bit vector with the same bit width as ``n0``.
*/
BoolectorNode *boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create a bit vector subtraction.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.
*/
BoolectorNode *boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*!
  Create an unsigned bit vector subtraction overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the subtraction of ``n0`` and ``n1`` overflows in case both operands are treated unsigned.
*/
BoolectorNode *boolector_usubo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create a signed bit vector subtraction overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the subtraction of ``n0`` and ``n1`` overflows in case both operands are treated signed.
*/
BoolectorNode *boolector_ssubo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create unsigned division.

  The parameters ``n0`` and ``n1`` must have the same bit width.
  If ``n1`` is zero, then the result is -1.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.

  .. note::
    The behavior that division by zero returns -1 does not exactly
    comply with the SMT-LIB standard 1.2 and 2.0 where division by zero is
    handled as uninterpreted function. Our semantics are motivated by
    real circuits where division by zero cannot be uninterpreted and of course
    returns a result.
*/
BoolectorNode *boolector_udiv (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create signed division.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.

  .. note::
    Signed division is expressed by means of unsigned
    division, where either node is normalized in case that its sign bit is 1.
    If the sign bits of ``a`` and ``b`` do not match, two's complement
    is performed on the result of the previous unsigned division.
    Hence, the behavior in case of a division by zero depends on
    boolector_udiv.
*/
BoolectorNode *boolector_sdiv (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a signed bit vector division overflow detection.

  The parameters ``n0`` and ``n1`` must have the same bit width.
  An overflow can happen if ``n0`` represents INT_MIN and ``n1`` represents -1.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with bit width one, which indicates if the division of ``n0`` and ``n1`` overflows in case both operands are treated signed.

  .. note::
    Unsigned division cannot overflow.
*/
BoolectorNode *boolector_sdivo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/*!
  Create an unsigned remainder.

  The parameters ``n0`` and ``n1`` must have the same bit width.
  If ``n1`` is zero, then the result is ``n0``.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.

  .. note::
    As in boolector_udiv the behavior if ``n1`` is zero, does
    not exactly comply with the SMT-LIB standard 1.2 and 2.0 where the result
    is handled as uninterpreted function. Our semantics are motivated by
    real circuits, where results can not be uninterpreted.
*/
BoolectorNode *boolector_urem (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a signed remainder.

  The parameters ``n0`` and ``n1`` must have the same bit width.
  If ``n1`` is zero, then the result is ``n0``.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.

  .. note::
    Analogously to boolector_sdiv, the signed remainder is expressed by means
    of the unsigned remainder, where either node is normalized in case that its
    sign bit is 1.  Hence, in case that ``n1`` is zero, the result depends on
    boolector_urem.
*/
BoolectorNode *boolector_srem (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create a, signed remainder where its sign matches the sign of the divisor.

  The parameters ``n0`` and ``n1`` must have the same bit width.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the same bit width as the operands.

  .. note::
    If ``n1`` is zero, the behavior of this function depends on boolector_urem.
*/
BoolectorNode *boolector_smod (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/*!
  Create the concatenation of two bit vectors.

  :param btor: Boolector instance.
  :param n0: First bit vector operand.
  :param n1: Second bit vector operand.
  :return: Bit vector with the bit width ``bit width of n0 + bit width of n1``.
*/
BoolectorNode *boolector_concat (Btor *btor,
                                 BoolectorNode *n0,
                                 BoolectorNode *n1);

/*!
  Create a read on array ``n_array`` at position ``n_index``.

  :param btor: Boolector instance.
  :param n_array: Array operand.
  :param n_index: Bit vector index. The bit width of ``n_index`` must have the same bit width as the indices of ``n_array``.
  :return: Bit vector with the same bit width as the elements of ``n_array``.
*/
BoolectorNode *boolector_read (Btor *btor,
                               BoolectorNode *n_array,
                               BoolectorNode *n_index);

/*!
  Create a write on array ``n_array`` at position ``n_index`` with value
  ``n_value``.

  The array is updated at exactly one position, all other elements remain
  unchanged. The bit width of ``n_index`` must be the same as the bit width of
  the indices of ``n_array``. The bit width of ``n_value`` must be the same as
  the bit width of the elements of ``n_array``.

  :param btor: Boolector instance.
  :param n_array: Array operand.
  :param n_index: Bit vector index.
  :param n_value: Bit vector value.
  :return: An array where the value at index ``n_index`` has been updated with ``n_value``.
*/
BoolectorNode *boolector_write (Btor *btor,
                                BoolectorNode *n_array,
                                BoolectorNode *n_index,
                                BoolectorNode *n_value);

/*!
  Create an if-then-else.

  If condition ``n_cond`` is true, then ``n_then`` is returned, else ``n_else``
  is returned.
  Nodes ``n_then`` and ``n_else`` must be either both arrays or both bit
  vectors.

  :param btor: Boolector instance.
  :param n_cond: Bit vector condition with bit width one.
  :param n_then: Array or bit vector operand representing the ``if`` case.
  :param n_else: Array or bit vector operand representing the ``else`` case.
  :return: Either ``n_then`` or ``n_else``.
*/
BoolectorNode *boolector_cond (Btor *btor,
                               BoolectorNode *n_cond,
                               BoolectorNode *n_then,
                               BoolectorNode *n_else);

/*!
  Create function parameter.

  This kind of node is used to create parameterized expressions, which are
  used to create functions. Once a parameter is bound to a function, it
  cannot be re-used in other functions.

  :param btor: Boolector instance.
  :param width: Number of bits which must be greater than zero.
  :param symbol: Name of parameter.
  :return: Parameter expression with bit width ``width`` and symbol ``symbol``.

  .. seealso::
    boolector_fun, boolector_apply
*/
BoolectorNode *boolector_param (Btor *btor, int width, const char *symbol);

/*!
  Create a function with body ``node`` parameterized over parameters
  ``param_nodes``.

  This kind of node is similar to macros in the SMT-LIB standard 2.0.
  Note that as soon as a parameter is bound to a function, it can not be
  reused in other functions.
  Call a function via boolector_apply.

  :param btor: Boolector instance.
  :param param_nodes: Parameters of function.
  :param paramc: Number of parameters.
  :param node: Function body parameterized over ``param_nodes``.
  :return: Function over parameterized expression ``node``.

  .. seealso::
    boolector_apply, boolector_param
*/
BoolectorNode *boolector_fun (Btor *btor,
                              BoolectorNode **param_nodes,
                              int paramc,
                              BoolectorNode *node);

/*!
  Create a function application on function ``n_fun`` with arguments
  ``arg_nodes``.

  :param btor: Boolector instance.
  :param arg_nodes: Arguments to be applied.
  :param argc: Number of arguments to be applied.
  :param n_fun: Function expression.
  :return: Function application on function ``n_fun`` with arguments ``arg_nodes``.

  .. seealso::
    boolector_fun, boolector_uf
*/
BoolectorNode *boolector_apply (Btor *btor,
                                BoolectorNode **arg_nodes,
                                int argc,
                                BoolectorNode *n_fun);

/*!
  Create bit vector expression that increments bit vector ``node`` by one.

  :param btor: Boolector instance.
  :param node: Bit vector operand.
  :return: Bit vector with the same bit width as ``node`` incremented by one.
*/
BoolectorNode *boolector_inc (Btor *btor, BoolectorNode *node);

/*!
  Create bit vector expression that decrements bit vector ``node`` by one.

  :param btor: Boolector instance.
  :param node: Bit vector operand.
  :return: Bit vector with the same bit width as ``node`` decremented by one.
*/
BoolectorNode *boolector_dec (Btor *btor, BoolectorNode *node);

/*!
  Create a universally quantified term.

  \forall (params[0] ... params[paramc - 1]) body

  :param btor: Boolector instance.
  :param params: Array of quantified variables.
  :param paramc: length of ``params`` array.
  :param body: Term where ``params`` may occur.
  :return: Universally quantified term with bit width 1.
 */
BoolectorNode *boolector_forall (Btor *btor,
                                 BoolectorNode *params[],
                                 int paramc,
                                 BoolectorNode *body);

/*!
  Create an existentially quantifed term.

  \exists (params[0] ... params[paramc - 1]) body

  :param btor: Boolector instance.
  :param params: Array of quantified variables.
  :param paramc: length of ``params`` array.
  :param body: Term where ``params`` may occur.
  :return: Existentially quantified term with bit width 1.
 */
BoolectorNode *boolector_exists (Btor *btor,
                                 BoolectorNode *param[],
                                 int paramc,
                                 BoolectorNode *body);

/*------------------------------------------------------------------------*/

/*!
  Return the Boolector instance to which ``node`` belongs.

  :param node: Boolector node.
  :return: Boolector instance.
*/
Btor *boolector_get_btor (BoolectorNode *node);

/*!
  Get the id of a given node.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: Id of ``node``.
*/
int boolector_get_id (Btor *btor, BoolectorNode *node);

/*!
  Retrieve the node belonging to Boolector instance ``btor`` that matches
  given ``id``.

  :param btor: Boolector instance.
  :param id: Boolector node id.
  :return: The Boolector node that matches given ``node`` in Boolector instance ``btor`` by id.

  .. note::
    Matching a node against another increases the reference
    count of the returned match, which must therefore be released appropriately
    (boolector_release).
*/
BoolectorNode *boolector_match_node_by_id (Btor *btor, int id);

/*!
  Retrieve the node belonging to Boolector instance ``btor`` that matches
  given BoolectorNode ``node`` by id. This is intended to be used for handling
  expressions of a cloned instance (boolector_clone).

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: The Boolector node that matches given ``node`` in Boolector instance ``btor`` by id.

  .. note::
    Matching a node against another increases the reference
    count of the returned match, which must therefore be released appropriately
    (boolector_release).
    Only nodes created before the boolector_clone call can be matched.
*/
BoolectorNode *boolector_match_node (Btor *btor, BoolectorNode *node);

/*!
  Get the symbol of an expression.

  :param btor: Boolector instance.
  :param var: Array or bit vector variable, parameter, uninterpreted function.
  :return: Symbol of expression.

  .. seealso::
    boolector_var, boolector_array, boolector_uf, boolector_param
*/
const char *boolector_get_symbol (Btor *btor, BoolectorNode *var);

/*!
  Set the symbol of an expression.

  Expression must be either an array or
  bit vector variable, a parameter, or an uninterpreted function).

  :param btor: Boolector instance.
  :param var: Array or bit vector variable, parameter, uninterpreted function.
  :param symbol: The symbol to be set.

  .. seealso::
    boolector_var, boolector_array, boolector_uf, boolector_param
*/
void boolector_set_symbol (Btor *btor, BoolectorNode *var, const char *symbol);

/*!
  Get the bit width of an expression.

  If the expression
  is an array, it returns the bit width of the array elements.
  If the expression
  is a function, it returns the bit width of the function's return value.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: Bit width of ``node``.
*/
int boolector_get_width (Btor *btor, BoolectorNode *node);

/*!
  Get the bit width of indices of ``n_array``.

  :param btor: Boolector instance.
  :param n_array: Array operand.
  :return: Bit width of indices of ``n_array``
*/
int boolector_get_index_width (Btor *btor, BoolectorNode *n_array);

/*!
  Get the bit vector of a constant node as a bit string.

  :param btor: Boolector instance.
  :param node: Constant node.
  :return: String representing the bits of ``node``.
*/
const char *boolector_get_bits (Btor *btor, BoolectorNode *node);

/*!
  Free a bits string for bit vector constants.

  :param btor: Boolector instance.
  :param bits: String which has to be freed.

  .. seealso::
    boolector_get_bits
*/
void boolector_free_bits (Btor *btor, const char *bits);

/*!
  Get the arity of function ``node``.

  :param btor: Boolector instance.
  :param node: Function node.
  :return: Arity of ``node``.
*/
int boolector_get_fun_arity (Btor *btor, BoolectorNode *node);

/*!
  Determine if given node is a constant node.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: True if ``node`` is a constant, and false otherwise.
*/
int boolector_is_const (Btor *btor, BoolectorNode *node);

/*!
  Determine if given node is a bit vector variable.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: True if ``node`` is a bit vector variable, and false otherwise.
*/
int boolector_is_var (Btor *btor, BoolectorNode *node);

/*!
  Determine if given node is an array node.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: True if ``node`` is an array, and false otherwise.
*/
int boolector_is_array (Btor *btor, BoolectorNode *node);

/*!
  Determine if expression is an array variable.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: True if ``node`` is an array variable, and false otherwise.
*/
int boolector_is_array_var (Btor *btor, BoolectorNode *node);

/*!
  Determine if given node is a parameter node.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: True if ``node`` is a parameter, and false otherwise.
*/
int boolector_is_param (Btor *btor, BoolectorNode *node);

/*!
  Determine if given parameter node is bound by a function.

  :param btor: Boolector instance.
  :param node: Parameter node.
  :return: True if ``node`` is bound, and false otherwise.
*/
int boolector_is_bound_param (Btor *btor, BoolectorNode *node);

/*!
  Determine if given node is a function node.

  :param btor: Boolector instance.
  :param node: Boolector node.
  :return: True if ``node`` is a function, and false otherwise.
*/
int boolector_is_fun (Btor *btor, BoolectorNode *node);

/*!
  Check if sorts of given arguments matches the function signature.

  :param btor: Boolector instance.
  :param arg_nodes: Arguments to be checked.
  :param argc: Number of arguments to be checked.
  :param n_fun: Function expression.
  :return: -1 if all sorts are correct, otherwise it returns the position of the incorrect argument.
*/
int boolector_fun_sort_check (Btor *btor,
                              BoolectorNode **arg_nodes,
                              int argc,
                              BoolectorNode *n_fun);

/*!
  Generate an assignment string for bit vector expression if
  boolector_sat has returned BOOLECTOR_SAT and model generation has been
  enabled.

  The expression can be an arbitrary bit vector expression which
  occurs in an assertion or current assumption. The assignment string has to
  be freed by boolector_free_bv_assignment.

  :param btor: Boolector instance.
  :param node: Bit vector expression.
  :return: String representing a satisfying assignment to bit vector variables and a consistent assignment for arbitrary bit vector expressions. Each character of the string can be ``0``, ``1`` or ``x``. The latter represents that the corresponding bit can be assigned arbitrarily.

  .. seealso::
    boolector_set_opt for enabling model generation.
*/
const char *boolector_bv_assignment (Btor *btor, BoolectorNode *node);

/*!
  Free an assignment string for bit vectors.

  :param btor: Boolector instance.
  :param assignment: String which has to be freed.

  .. seealso::
    boolector_bv_assignment
*/
void boolector_free_bv_assignment (Btor *btor, const char *assignment);

/*!
  Generate a model for an array expression.

  If boolector_sat has returned BOOLECTOR_SAT and model generation has been
  enabled.  The function creates and stores the array of indices into
  ``indices`` and the array of corresponding values into ``values``. The number
  size of ``indices`` resp. ``values`` is stored into ``size``. The array model
  simply inspects the set of reads rho, which is associated with each array
  expression. See our publication `Lemmas on Demand for Lambdas
  <http://fmv.jku.at/papers/PreinerNiemetzBiere-DIFTS13.pdf>`_ for details. At
  indices that do not occur in the model, it is assumed that the array stores a
  globally unique default value, for example 0.  The bit vector assignments to
  the indices and values have to be freed by boolector_free_bv_assignment.
  Furthermore, the user has to free the array of indices and the array of
  values, respectively of size ``size``.

  :param btor: Boolector instance.
  :param n_array: Array operand for which the array model should be built.
  :param indices: Pointer to array of index strings.
  :param values: Pointer to array of value strings.
  :param size: Pointer to size.

  .. seealso::
    boolector_set_opt for enabling model generation.
*/
void boolector_array_assignment (Btor *btor,
                                 BoolectorNode *n_array,
                                 char ***indices,
                                 char ***values,
                                 int *size);

/*!
  Free an assignment string for arrays of bit vectors.

  :param btor: Boolector instance.
  :param indices: Array of index strings of size ``size``.
  :param values: Array of values strings of size ``size``.
  :param size: Size of arrays ``indices`` and ``values``.

  .. seealso::
    boolector_array_assignment
*/
void boolector_free_array_assignment (Btor *btor,
                                      char **indices,
                                      char **values,
                                      int size);

/*!
  Generate a model for an uninterpreted function.
  The function creates and stores the assignments of the function's arguments
  to array ``args`` and the function's return values to array ``values``.
  Arrays ``args`` and ``values`` represent assignment pairs of arguments and
  values, i.e., instantiating a function with args[i] yields value values[i].
  For functions with arity > 1 args[i] contains a space separated string of
  argument assignments, where the order of the assignment strings corresponds
  to the order of the function's arguments.

  :param btor: Boolector instance.
  :param n_uf: Uninterpreted function node.
  :param args: Pointer to array of argument assignment strings.
  :param values: Pointer to array of value assignment strings.
  :param size: Size of arrays ``args`` and ``values``.

  .. note::
    This function can only be called if boolector_sat returned
    BOOLECTOR_SAT and model generation was enabled.

  .. seealso::
    boolector_set_opt for enabling model generation
*/
void boolector_uf_assignment (
    Btor *btor, BoolectorNode *n_uf, char ***args, char ***values, int *size);

/*!
  Free assignment strings for uninterpreted functions.

  :param btor: Boolector instance.
  :param args: Array of argument strings of size ``size``.
  :param values: Array of value string of size ``size``.
  :param size: Size of arrays ``args`` and ``values``.

  .. seealso::
    boolector_uf_assignment
*/
void boolector_free_uf_assignment (Btor *btor,
                                   char **args,
                                   char **values,
                                   int size);

/*!
  Print model to output file. This function prints the model for all inputs
  to the output file ``file``. Supported output formats for the model to be
  printed are:

  * **btor**

    Use boolector's own output format for printing models.

    .. code-block:: c

      boolector_print_model (btor, "btor", stdout);

    A possible model would be: ::

      2 00000100 x
      3 00010101 y
      4[00] 01 A

    where the first column indicates the id of an input, the second column
    its assignment, and the third column its name (or symbol), if any.
    Note that in case that an input is an uninterpreted function or an
    array variable,
    values in square brackets indicate parameter resp. index values.

  * **smt2**

    Use `SMT-LIB v2`_ format for printing models.

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

  :param btor: Boolector instance.
  :param format: A string identifying the output format.
  :param file: Output file.
*/
void boolector_print_model (Btor *btor, char *format, FILE *file);

/*------------------------------------------------------------------------*/

/*!
  Create Boolean sort.

  :param btor: Boolector instance.
  :return: Sort of type Boolean.

  .. note:
    Currently, sorts in Boolector are used for uninterpreted functions, only.

  .. seealso::
    boolector_uf
*/
BoolectorSort boolector_bool_sort (Btor *btor);

/*!
  Create bit vector sort of bit width ``width``.

  :param btor: Boolector instance.
  :param width: Bit width.
  :return: Bit vector sort of bit width ``width``.

  .. note::
    Currently, sorts in Boolector are used for uninterpreted functions, only.

  .. seealso::
    boolector_uf
*/
BoolectorSort boolector_bitvec_sort (Btor *btor, int width);

/*!
  Create function sort.

  :param btor: Boolector instance.
  :param domain: A list of all the function arguments' sorts.
  :param arity: Number of elements in domain (must be > 0).
  :param codomain: The sort of the function's return value.
  :return: Function sort which maps given domain to given codomain.

  .. note::
    Currently, sorts in Boolector are used for uninterpreted functions, only.

  .. seealso::
    boolector_uf
*/
BoolectorSort boolector_fun_sort (Btor *btor,
                                  BoolectorSort *domain,
                                  int arity,
                                  BoolectorSort codomain);

/*!
  Release sort (decrements reference counter).

  :param btor: Boolector instance.
  :param sort: Sort to be released.
*/
void boolector_release_sort (Btor *btor, BoolectorSort sort);

/*!
  Determine if ``n0`` and ``n1`` have the same sort or not.

  :param btor: Boolector instance.
  :param n0: First operand.
  :param n1: Second operand.
  :return: True if ``n0`` and ``n1`` have the same sort, and false otherwise.
*/
int boolector_is_equal_sort (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/*------------------------------------------------------------------------*/

/*!
  Parse input file.

  Input file format may be either BTOR_, `SMT-LIB v1`_, or `SMT-LIB v2`_, the
  file type is detected automatically.  If the parser encounters an error, an
  explanation of that error is stored in ``error_msg``. If the input file
  specifies a (known) status of the input formula (either sat or unsat), that
  status is stored in ``status``. All output (from commands like e.g.
  'check-sat' in `SMT-LIB v2`_) is printed to ``outfile``.

  :param btor: Boolector instance.
  :param infile: Input file.
  :param infile_name: Input file name.
  :param outfile: Output file.
  :param error_msg: Error message.
  :param status: Status of the input formula.
  :return: In the incremental case (right now `SMT-LIB v1`_ only) the function returns either BOOLECTOR_SAT, BOOLECTOR_UNSAT or BOOLECTOR_UNKNOWN, otherwise it always returns BOOLECTOR_UNKNOWN. If a parse error occurs the function returns BOOLECTOR_PARSE_ERROR.
*/
int boolector_parse (Btor *btor,
                     FILE *infile,
                     const char *infile_name,
                     FILE *outfile,
                     char **error_msg,
                     int *status);

/*!
  Parse input file in BTOR format.

  See boolector_parse.

  :param btor: Boolector instance.
  :param infile: Input file.
  :param infile_name: Input file name.
  :param outfile: Output file.
  :param error_msg: Error message.
  :param status: Status of the input formula.
  :return: BOOLECTOR_UNKNOWN or BOOLECTOR_PARSE_ERROR if a parse error occurred.
*/
int boolector_parse_btor (Btor *btor,
                          FILE *infile,
                          const char *infile_name,
                          FILE *outfile,
                          char **error_msg,
                          int *status);

/*!
  Parse input file in `SMT-LIB v1`_ format.

  See boolector_parse.

  :param btor: Boolector instance.
  :param infile: Input file.
  :param infile_name: Input file name.
  :param outfile: Input file.
  :param error_msg: Error message.
  :param status: Status of the input formula.
  :return: In the incremental case (right now `SMT-LIB v1`_ only) the function returns either BOOLECTOR_SAT, BOOLECTOR_UNSAT or BOOLECTOR_UNKNOWN, otherwise it always returns BOOLECTOR_UNKNOWN. If a parse error occurs the function returns BOOLECTOR_PARSE_ERROR.
*/
int boolector_parse_smt1 (Btor *btor,
                          FILE *infile,
                          const char *infile_name,
                          FILE *outfile,
                          char **error_msg,
                          int *status);

/*!
  Parse input file in `SMT-LIB v2`_ format. See boolector_parse.

  :param btor: Boolector instance.
  :param infile: Input file.
  :param infile_name: Input file name.
  :param outfile: Output file.
  :param error_msg: Error message.
  :param status: Status of the input formula.
  :return: BOOLECTOR_UNKNOWN or BOOLECTOR_PARSE_ERROR if a parse error occurred.
*/
int boolector_parse_smt2 (Btor *btor,
                          FILE *infile,
                          const char *infile_name,
                          FILE *outfile,
                          char **error_msg,
                          int *status);

/*------------------------------------------------------------------------*/

/*!
  Recursively dump ``node`` to file in BTOR_ format.

  :param btor: Boolector instance.
  :param file: File to which the expression should be dumped. The file must be have been opened by the user before.
  :param node: The expression which should be dumped.
*/
void boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node);

/*!
  Dump formula to file in BTOR_ format.

  :param btor: Boolector instance.
  :param file: File to which the formula should be dumped. The file must be have been opened by the user before.
*/
void boolector_dump_btor (Btor *btor, FILE *file);

#if 0
/*!
  Dump formula to file in BTOR 2.0 format.
 
  :param btor: Boolector instance.
  :param file: File to which the formula should be dumped. The file must be have been opened by the user before.
*/
void boolector_dump_btor2 (Btor * btor, FILE * file);
#endif

/*!
  Recursively dump ``node`` to file in `SMT-LIB v2`_ format.

  :param btor: Boolector instance.
  :param file: File to which the expression should be dumped. The file must be have been opened by the user before.
  :param node: The expression which should be dumped.
*/
void boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node);

/*!
  Dumps formula to file in `SMT-LIB v2`_ format.

  :param btor: Boolector instance
  :param file: Output file.
*/
void boolector_dump_smt2 (Btor *btor, FILE *file);

/*!
  Dumps bit vector formula to file in ascii AIGER format.

  :param btor: Boolector instance
  :param file: Output file.
  :param merge_roots: Merge all roots of AIG.
*/
void boolector_dump_aiger_ascii (Btor *btor, FILE *file, bool merge_roots);

/*!
  Dumps bit vector formula to file in ascii AIGER format.

  :param btor: Boolector instance
  :param file: Output file.
  :param merge_roots: Merge all roots of AIG.
*/
void boolector_dump_aiger_binary (Btor *btor, FILE *file, bool merge_roots);
#endif

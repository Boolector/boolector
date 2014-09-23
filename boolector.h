/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BOOLECTOR_H_INCLUDED
#define BOOLECTOR_H_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct Btor Btor;
typedef struct BtorNode BtorNode;
typedef struct BoolectorSort BoolectorSort;
typedef struct BtorOpt BtorOpt;

#ifdef BOOLECTOR_FORCE_API_1
#define BoolectorNode BtorNode
#else
#define BOOLECTOR_API_2
typedef struct BoolectorNode BoolectorNode;
#endif

/*------------------------------------------------------------------------*/

// TODO mention PYTHON API!
/**
 * \mainpage Boolector Documentation
 * \section Introduction
 * <a href="http://fmv.jku.at/boolector">Boolector</a> is an SMT solver for
 * the quantifier-free theory of bit vectors with arrays.
 * It supports
 * <a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR</a>,
 * <a
 href="http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf">SMT-LIB 1.2</a>,
 * and <a
 href="http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf">SMT-LIB
 2.0</a> as input format and
 * can be either used as a stand-alone SMT solver, or as backend
 * for other tools via its public API.
 * This is the documentation of Boolector's public <b>C interface</b>.
 * For further information and the latest version of Boolector, please refer
 * to <a href="http://fmv.jku.at/boolector">http://fmv.jku.at/boolector</a>.
 *
 * \section Interface
 * The public interface is defined in \ref boolector.h.
 *
 * \subsection Quickstart
 * First, create a Boolector instance via \ref boolector_new. You can configure
 * this instance via \ref boolector_set_opt, for a detailed description of all
 * configurable options, see \ref boolector_set_opt.
 * Next you can either parse an input file, and/or generate expressions to
 * be either asserted via \ref boolector_assert, or, if incremental usage is
 * enabled, assumed via \ref boolector_assume (analogously to MiniSAT).
 * Note that Boolector's internal design is motivated by hardware design,
 * hence we do not distinguish between type 'Boolean' and type 'bit vector
 * of length 1'.
 * After parsing an input file and/or asserting/assuming expressions,
 * the satifiability of the resulting formula can be determined via
 * \ref boolector_sat. If the resulting formula is satisfiable and model
 * generation has been enabled via \ref boolector_set_opt, you can either
 * print the resulting model via \ref boolector_print_model,
 * or query assignments
 * of bit vector and array variables or uninterpreted functions via
 * \ref boolector_bv_assignment, \ref boolector_array_assignment and
 * \ref boolector_uf_assignment..
 * Note that querying assignments is not limited to variables---you can query
 * the assignment of any arbitrary expression.
 *
 * \subsection Options
 *
 * Boolector can be configured either via \ref boolector_set_opt,
 * or via environment variables of the form:
 * \verbatim BTOR<capitalized option name without '_'>=<value> \endverbatim
 * For a list and detailed descriptions of all available options,
 * see \ref boolector_set_opt.
 *
 * E.g., given a Boolector instance 'btor', model generation is enabled either
 * via \verbatim boolector_set_opt (btor, "model_gen", 1); \endverbatim
 * or via setting the environment variable
 * \verbatim BTORMODELGEN=1 \endverbatim
 *
 * \subsection tracing API Tracing
 * API tracing allows to record every call to Boolector's public API. The
 * resulting trace can be replayed and the replayed sequence behaves exactly
 * like the original Boolector run.
 * This is particularly useful for debugging purposes, as it enables replaying
 * erroneous behaviour.
 * API tracing can be enabled either via \ref boolector_set_trapi or by
 * setting the environment variable BTORAPITRACE=<filename>.
 *
 * E.g., given a Boolector instance 'btor', enabling API tracing is done as
 * follows:
 * \verbatim
   FILE *fd = fopen ("error.trace", "r");
   boolector_set_trapi (btor, fd); \endverbatim
 * or
 * \verbatim BTORAPITRACE="error.trace" \endverbatim
 *
 * \section Internals
 * Boolector internally maintains a directed acyclic graph (DAG) of
 * expressions. As a consequence, each expression maintains a reference
 * counter, which is initially set to 1.
 * Each time an expression is shared, i.e. for each API call that returns
 * an expression (a BoolectorNode), its reference counter is incremented
 * by 1. Not considering API calls that generate expressions, this mainly
 * applies to \ref boolector_copy, which simply increments the reference
 * counter of an expression, and \ref boolector_match_node resp.
 * \ref boolector_match_node_by_id, which retrieve nodes of a given Boolector
 * instance by id resp. a given node's id.
 * Expressions are released via \ref boolector_release, and if its
 * reference counter is decremented to zero, it is deleted from memory.
 * Note that by asserting an expression, it will be permanently added to the
 * formula, i.e. Boolector internally holds its reference until it is either
 * eliminated via rewriting, or the Boolector instance is deleted.
 * Following from that, it is safe to release an expression as soon as you
 * asserted it, as long as you don't need it for further querying.
 *
 * Boolector simplifies expressions and the expression DAG by means of
 * rewriting and supports three so-called rewrite levels.
 * Increasing rewrite levels increase the extent of rewriting performed,
 * and a rewrite level of 0 is equivalent to disabling rewriting at all.
 * Note that Boolector not only simplifies expressions during construction
 * of the expression DAG---for each call to \ref boolector_sat,
 * various simplification techniques and rewriting phases are initiated.
 * You can force Boolector to initiate rewriting and simplify the expression
 * DAG via \ref boolector_simplify.
 * The rewrite level can be configured via \ref boolector_set_opt.
 *
 * Boolector internally uses a set of base operators.
 * The set is documented in
 *<a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR:
 Bit-Precise Modelling of Word-Level Problems for Model Checking</a>.
 * Many operators that are available in the API are rewritten as combination
 * of base operators internally. For example, two's complement is rewritten
 * as one's complement and addition of 1.  This behavior is not
 * influenced by the rewrite level.
 *
 * \subsection Assertions
 * Boolector uses two different kinds of assertions. Internally, Boolector
 * heavily uses assertions provided by the standard C library.
 * To increase performance, these assertions are disabled in releases.
 *
 * The functions of Boolector's public interface are guarded by
 * public assertions. Public assertions are always enabled. They check if
 * the functions have been correctly called by the user.
 * If not, then an error message is printed and 'abort' is called.
 * For example, we call \ref boolector_var and pass a bit width < 1. This
 * yields the following error message:
 *
 * \verbatim [boolector] boolector_var: 'width' must not be < 1 \endverbatim
 *
 * This is not a bug. The user has violated the pre-conditions of the function,
 * and therefore Boolector aborts.
 *
 * \section Examples
 * In the section <a href="examples.html">examples</a> you can
 * find bit vector and array examples. They demonstrate
 * how Boolector's public interface can be used.
 * \example bv1.c
 * \example bv2.c
 * \example array1.c
 * \example array2.c
 * \example array3.c
 *
 */

/*------------------------------------------------------------------------*/

/**
 * Preprocessor constant representing status 'unknown'.
 * \see boolector_sat, boolector_limited_sat, boolector_simplify
 */
#define BOOLECTOR_UNKNOWN 0
/**
 * Preprocessor constant representing status 'satisfiable'.
 * \see boolector_sat, boolector_limited_sat, boolector_simplify
 */
#define BOOLECTOR_SAT 10
/**
 * Preprocessor constant representing status 'unsatisfiable'.
 * \see boolector_sat, boolector_limited_sat, boolector_simplify
 */
#define BOOLECTOR_UNSAT 20
/**
 * Preprocessor constant representing status 'parse error'.
 * \see boolector_parse
 */
#define BOOLECTOR_PARSE_ERROR 1
/*------------------------------------------------------------------------*/

/**
 * Create a new instance of Boolector.
 * \return New Boolector instance.
 */
Btor *boolector_new (void);

/**
 * Clone an instance of Boolector. The resulting Boolector instance is an
 * exact copy of given Boolector instance 'btor', i.e. in a clone and its
 * parent, nodes with the same id correspond to each other.
 * Use \ref boolector_match_node to match corresponding nodes.
 * \param btor original Boolector instance.
 * \return New Boolector instance.
 */
Btor *boolector_clone (Btor *btor);

/**
 * Delete a boolector instance and free its resources.
 * \param btor Boolector instance.
 * \remarks Expressions that have not been released properly will not be
 * deleted from memory. Use \ref boolector_get_refs to debug reference
 * counting. You can also set option 'auto_cleanup' via \ref boolector_set_opt
 * in order to do the cleanup automatically.
 */
void boolector_delete (Btor *btor);

/**
 * Set a verbosity message prefix.
 * \param btor Boolector instance.
 * \param msg Prefix string.
 */
void boolector_set_msg_prefix (Btor *btor, const char *prefix);

/**
 * Return the number of external references to the boolector library.
 * Internally, Boolector manages an expression DAG with reference counting. Use
 * \ref boolector_release to properly release an expression. Before
 * you finally call \ref boolector_delete, \ref boolector_get_refs should
 * return 0.
 * \param btor Boolector instance.
 * \return Number of external references owned by the user.
 */
int boolector_get_refs (Btor *btor);

/* Reset time statistics.
 * \param btor Boolector instance.
 */
void boolector_reset_time (Btor *btor);

/* Reset statistics (time statistics not included).
 * \param btor Boolector instance.
 */
void boolector_reset_stats (Btor *btor);

/* Print statistics.
 * \param btor Boolector instance.
 */
void boolector_print_stats (Btor *btor);

/**
 * Set the output API trace file and enable API tracing.
 * \param btor Boolector instance.
 * \param apitrace Output file.
 * \remark The API trace output file can also be set via the environment
 * variable BTORAPITRACE=<filename>.
 */
void boolector_set_trapi (Btor *btor, FILE *apitrace);

/**
 * Return API trace file.
 * \param btor Boolector instance.
 * \return API trace output file.
 */
FILE *boolector_get_trapi (Btor *btor);

/*------------------------------------------------------------------------*/

/**
 * Add a constraint. Use this function to assert 'node'.
 * Added constraints can not be deleted anymore. After 'node' has
 * been asserted, it can be safely released by \ref boolector_release.
 * \param btor Boolector instance.
 * \param node Bit vector expression with bit width one.
 */
void boolector_assert (Btor *btor, BoolectorNode *node);

/**
 * Add an assumption. Use this function to assume 'node'.
 * You must enable Boolector's incremental usage via
 * \ref boolector_set_opt before.
 * In contrast to \ref boolector_assert the assumptions are
 * discarded after each call to \ref boolector_sat. Assumptions
 * and assertions are logically combined by boolean 'and'.
 * This is the same way of using assumptions as in MiniSAT.
 * \param btor Boolector instance.
 * \param node Bit vector expression with bit width one.
 */
void boolector_assume (Btor *btor, BoolectorNode *node);

/**
 * Determine if assumption 'node' is a failed assumption.
 * \param btor Boolector instance.
 * \param node Bit vector expression with bit width one.
 * \return 1 if assumption is failed, and 0 otherwise.
 */
int boolector_failed (Btor *btor, BoolectorNode *node);

/**
 * Solve an instance represented by constraints and assumptions added
 * by \ref boolector_assert and \ref boolector_assume. Note that
 * assertions and assumptions are combined by boolean 'and'.
 * If you want to call this function multiple times then you must enable
 * Boolector's incremental usage mode via \ref boolector_set_opt
 * before. Otherwise, this function can only be called once.
 * \param btor Boolector instance.
 * \return \ref BOOLECTOR_SAT if the instance is satisfiable and
 * \ref BOOLECTOR_UNSAT if the instance is unsatisfiable.
 * \see boolector_bv_assignment
 * \see boolector_array_assignment
 **/
int boolector_sat (Btor *btor);

/**
 * Solve an instance represented by constraints and assumptions added
 * by \ref boolector_assert and \ref boolector_assume. The search can be
 * limited by the number of lemmas generated 'lod_limit' and the number of
 * conflicts produced by the underlying SAT solver 'sat_limit'. Note that
 * assertions and assumptions are combined by boolean 'and'.
 * If you want to call this function multiple times then you must enable
 * Boolector's incremental usage mode via \ref boolectdor_set_opt before.
 * Otherwise, this function can only be called once.
 * \param btor Boolector instance.
 * \param lod_limit Limit for lemmas on demand (-1 unlimited).
 * \param sat_limit Conflict limit for SAT solver (-1 unlimited).
 * \return \ref BOOLECTOR_SAT if the instance is satisfiable,
 * \ref BOOLECTOR_UNSAT if the instance is unsatisfiable, and
 * \ref BTOR_UNKNOWN if the instance could not be solved within given limits.
 * \see boolector_bv_assignment
 * \see boolector_array_assignment
 **/
int boolector_limited_sat (Btor *btor, int lod_limit, int sat_limit);

/**
 * Simplify current formula without calling \ref boolector_sat.
 * \param btor Boolector instance.
 * \return \ref BOOLECTOR_SAT if the instance was simplified to true,
 * \ref BOOLECTOR_UNSAT if the instance was simplified to false, and
 * \ref BOOLECTOR_UNKNOWN otherwise.
 */
int boolector_simplify (Btor *btor);

/*------------------------------------------------------------------------*/

/**
 * Set the SAT solver to use.
 * Currently, we support 'Lingeling', 'PicoSAT', and 'MiniSAT' as string
 * value of \param solver (case insensitive).  This is however
 * only possible if the corresponding solvers were enabled at compile time.
 * Call this function after \ref boolector_new.
 * \param btor Boolector instance
 * \param solver Solver identifier string.
 * \return Non-zero value if setting the SAT solver was successful.
 */
int boolector_set_sat_solver (Btor *btor, const char *solver);

#ifdef BTOR_USE_LINGELING
/**
 * Use Lingeling as SAT solver. This function is only available if Lingeling
 * was enabled at compile time.
 * Call this function after \ref boolector_new.
 * \param btor Boolector instance.
 * \param optstr Lingeling option string.
 * \param nofork Do not use fork/clone for Lingeling.
 */
int boolector_set_sat_solver_lingeling (Btor *btor,
                                        const char *optstr,
                                        int nofork);
#endif

#ifdef BTOR_USE_PICOSAT
/**
 * Use PicoSAT as SAT solver. This function is only available if PicoSAT
 * was enabled at compile time.
 * Call this function after \ref boolector_new.
 * \param btor Boolector instance.
 */
int boolector_set_sat_solver_picosat (Btor *btor);
#endif

#ifdef BTOR_USE_MINISAT
/**
 * Use MiniSAT as SAT solver. This function is only available if MiniSAT
 * was enabled at compile time.
 * Call this function after \ref boolector_new.
 * \param btor Boolector instance.
 */
int boolector_set_sat_solver_minisat (Btor *btor);
#endif

/*------------------------------------------------------------------------*/

/**
 * Set option.
 * \param btor Boolector instance.
 * \param name Option name.
 * \param val  Option value.
 *
 * List of available options:
 *
 *   - model_gen
 *
 *     Enable (1 or 2) or disable (0) generation of a model for satisfiable
 *     instances. There are two modes for model generation: generate
 *     model for (1) asserted expressions and (2) all created expressions.
 *
 *   - incremental
 *
 *     Enable (1) incremental mode. Note that incremental usage turns
 *     off some optimization techniques. Disabling incremental usage is
 *     currently not supported.
 *
 *   - incremental_all
 *
 *     Enable (1) or disable (0) incremental solving of all formulas (when
 *     parsing an input file). Note that currently, incremental mode is only
 *     supported for SMT-LIB v1 input.
 *
 *   - incremental_in_depth
 *
 *     Set incremental in-depth mode width (when parsing an input file).
 *     Note that currently, incremental mode is only supported for SMT-LIB v1
 *     input.
 *
 *   - incremental_look_ahead
 *
 *     Set incremental look-ahead mode width (when parsing an input file).
 *     Note that currently, incremental mode is only supported for SMT-LIB v1
 *     input.
 *
 *   - incremental_interval
 *
 *     Set incremental interval mode width (when parsing an input file).
 *     Note that currently, incremental mode is only supported for SMT-LIB v1
 *     input.
 *
 *   - input_format
 *
 *     Force input file format (Btor: -1, SMT-LIB v1: 1, SMT-LIB v2: 2) when
 *     parsing an input file. If unspecified, Boolector determines the
 *     input file format while parsing.
 *
 *   - output_number_format
 *
 *     Force output number format (binary: 0, hexadecimal: 1, decimal: 2).
 *     Boolector uses binary by default.
 *
 *   - output_format
 *
 *     Force output file format (Btor: -1, SMT-LIB v1: 1, SMT-LIB v2: 2).
 *     Boolector uses Btor by default.
 *
 *   - rewrite_level
 *
 *     Set the rewrite level (0-3) of the rewriting engine. Boolector uses
 *     rewrite level 3 by default. Do not alter the rewrite level after
 *     creating expressions.
 *     (0 ... no rewriting, 3 ... full rewriting)
 *
 *   - rewrite_level_pbr
 *
 *     Set the rewrite level (0-3) for partial beta reduction. Boolector uses
 *     rewrite level 1 by default.
 *     (0 ... no rewriting, 3 ... full rewriting)
 *
 *   - beta_reduce_all
 *
 *     Enable (1) or disable (0) the eager elimination of lambda expressions
 *     via beta reduction.
 *
 *   - probe_beta_reduce_all
 *
 *     Enable (1) or disable (0) probing of 'beta_reduce_all' (until a given
 *     LOD or SAT conflicts limit.
 *
 *     + pbra_lod_limit
 *
 *       Set lemmas on demand limit for 'probe_beta_reduce_all'.
 *
 *     + pbra_sat_limit
 *
 *       Set SAT conflicts limit for 'probe_beta_reduce_all'.
 *
 *     + pbra_ops_factor
 *
 *       Set factor by which the size of the beta reduced formula may be greater
 *  	than the original formula (for 'probe_beta_reduce_all').
 *
 *   - dual_prop
 *
 *     Enable (1) or disable (0) dual propagation optimization.
 *
 *   - just
 *
 *     Enable (1) or disable (0) justification optimization.
 *
 *   - ucopt
 *
 *     Enable (1) or disable (0) unconstrained optimization.
 *
 *   - lazy_synthesize
 *
 *     Enable (1) or disable (0) lazy synthesis of bit vector expressions.
 *
 *   - eliminate_slices
 *
 *     Enable (1) or disable (0) slice elimination on bit vector variables.
 *
 *   - auto_cleanup
 *
 *     Enable (1) or disable (0) forced automatic cleanup of expressions and
 *     assignment strings on \ref boolector_delete.
 *
 *   - pretty_print
 *
 *     Enable (1) or disable (0) pretty printing when dumping.
 *
 *   - verbosity
 *
 *     Set the level of verbosity.
 *     (0 ... no verbosity, x ... increase verbosity)
 *
 *   - loglevel
 *
 *     Set log level (0-3).
 *     (0 ... no logging, 3 ... full logging)
 *
 */
void boolector_set_opt (Btor *btor, const char *opt, int val);

/**
 * Get Boolector option object.
 * \param btor Btor instance.
 * \param opt Option name.
 * \return Boolector option object. See \ref btoropt.h for more details on the
 * structure of the option object.
 */
const BtorOpt *boolector_get_opt (Btor *btor, const char *opt);

/**
 * Get the current value of an option.
 * \param btor Btor instance.
 * \param opt Option name.
 * \return Current value of \ref opt.
 */
int boolector_get_opt_val (Btor *btor, const char *opt);

/**
 * Get the first option in Boolector's option list.
 * \param btor Btor instance.
 * \return First option in Boolector's option list.
 */
const BtorOpt *boolector_first_opt (Btor *btor);

/**
 * Get the last option in Boolector's option list.
 * \param btor Btor instance.
 * \return Last option in Boolector's option list.
 */
const BtorOpt *boolector_last_opt (Btor *btor);

/**
 * Get the next option in Boolector's option list after option 'opt'.
 * \param btor Btor instance.
 * \param opt Boolector option object.
 * \return Next option in Boolector's option list.
 */
const BtorOpt *boolector_next_opt (Btor *btor, const BtorOpt *opt);

/*------------------------------------------------------------------------*/

/**
 * Copy expression (increments reference counter).
 * \param btor Boolector instance.
 * \param node Boolector node to be copied.
 * \return 'node' with reference counter incremented.
 */
BoolectorNode *boolector_copy (Btor *btor, BoolectorNode *node);

/**
 * Release expression (decrements reference counter).
 * \param btor Boolector instance.
 * \param node Boolector node to be released.
 */
void boolector_release (Btor *btor, BoolectorNode *node);

/**
 * Release all expressions and sorts
 * (\see boolector_release and \see boolector_release_sort).
 * \param btor Boolector instance.
 */
void boolector_release_all (Btor *btor);

/**
 * Create bit vector constant representing the bit vector 'bits'.
 * \param btor Boolector instance.
 * \param bits Non-empty and terminated string consisting of zeroes and/or ones.
 * representing the bit vector constant specified by 'bits'.
 * \return Bit vector constant with bit width strlen('bits').
 */
BoolectorNode *boolector_const (Btor *btor, const char *bits);

/**
 * Create bit vector constant zero with bit width 'width'.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit vector constant zero with bit width 'width'.
 */
BoolectorNode *boolector_zero (Btor *btor, int width);

/**
 * Create bit vector constant zero with bit width one.
 * \param btor Boolector instance.
 * \return Bit vector constant zero with bit width one.
 */
BoolectorNode *boolector_false (Btor *btor);

/**
 * Create bit vector constant with bit width 'width', where each bit is set to
 * one.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit vector constant -1 with bit width 'width'.
 */
BoolectorNode *boolector_ones (Btor *btor, int width);

/**
 * Create constant true. This is represented by the bit vector constant one
 * with bit width one.
 * \param btor Boolector instance.
 * \return Bit vector constant one with bit width one.
 */
BoolectorNode *boolector_true (Btor *btor);

/**
 * Create bit vector constant one with bit width 'width'.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit vector constant one with bit width 'width'.
 */
BoolectorNode *boolector_one (Btor *btor, int width);

/**
 * Create bit vector constant representing the unsigned integer 'u' with bit
 * width 'width'. The constant is obtained by either truncating bits or by
 * unsigned extension (padding with zeroes).
 * \param btor Boolector instance.
 * \param u Unsigned integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit vector constant with bit width 'width'.
 */
BoolectorNode *boolector_unsigned_int (Btor *btor, unsigned u, int width);

/**
 * Create bit vector constant representing the signed integer 'i' with bit
 * width 'width'. The constant is obtained by either truncating bits or by
 * signed extension (padding with ones).
 * \param btor Boolector instance.
 * \param i Signed integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit vector constant with bit width 'width'.
 */
BoolectorNode *boolector_int (Btor *btor, int i, int width);

/**
 * Create fresh bit vector variable with bit width 'width' and symbol 'symbol'.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \param symbol Name of variable.
 * \return Bit vector variable with bit width 'width' and symbol 'symbol'.
 * \remarks Internally, variables are \e not uniquely hashed.
 * Therefore, every call to this function returns a fresh variable.
 * The symbol is used as a simple way to identify variables in file dumps
 * (\ref boolector_dump_btor, \ref boolector_dump_smt1,
 *  \ref boolector_dump_smt2) and models for satisfiable instances.
 * Symbols must be unique but may be NULL in case that no symbol should be
 * assigned.
 */
BoolectorNode *boolector_var (Btor *btor, int width, const char *symbol);

/**
 * Create one-dimensional bit vector array of size 2 ^ 'index_width' with
 * elements of bit width 'elem_width'.
 * \param btor Boolector instance.
 * \param elem_width Bit width of array elements (must be greater than zero).
 * \param index_width Bit width of array indices (must be greater than zero).
 * \param symbol Name of array variable.
 * \return Bit vector array of size 2 ^ 'index_width' with elements of
 * bit width 'elem_width', and symbol 'symbol'.
 * \remarks Internally, array variables are \e not uniquely hashed. Therefore,
 * each call to \ref boolector_array with the same arguments will return
 * a fresh variable.
 * The symbol is used as a simple way to identify variables in file dumps
 * (\ref boolector_dump_btor, \ref boolector_dump_smt1,
 *  \ref boolector_dump_smt2) and models for satisfiable instances.
 * Symbols must be unique but may be NULL in case that no symbol should be
 * assigned.
 */
BoolectorNode *boolector_array (Btor *btor,
                                int elem_width,
                                int index_width,
                                const char *symbol);

/**
 * Create uninterpreted function with sort 'sort' and symbol 'symbol'.
 * \param btor Boolector instance.
 * \param sort Sort of the uninterpreted function.
 * \param symbol Name of the uninterpreted function.
 * \return Uninterpreted function of sort 'sort' and symbol 'symbol'.
 * \remarks
 * Internally, uninterpreted functions are \e not uniquely hashed. Therefore,
 * each call to \ref boolector_array with the same arguments will return
 * a fresh uninterpreted function.
 * The symbol is used as a simple way to identify uninterpreted functions in
 * file dumps (\ref boolector_dump_btor, \ref boolector_dump_smt1, \ref
 * boolector_dump_smt2) and models for satisfiable instances.  Symbols must be
 * unique but may be NULL in case that no symbol should be assigned.
 * \see boolector_apply, boolector_fun_sort
 */
BoolectorNode *boolector_uf (Btor *btor,
                             BoolectorSort *sort,
                             const char *symbol);

/**
 * Create one's complement of bit vector 'node'.
 * \param btor Boolector instance.
 * \param node Bit Vector node.
 * \return Bit vector representing the one's complement of 'node' with the same
 * bit width as 'node'.
 */
BoolectorNode *boolector_not (Btor *btor, BoolectorNode *node);

/**
 * Create two's complement of bit vector 'node'.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \return Bit vector representing the two's complement of 'node' with the same
 * bit width as 'node'.
 */
BoolectorNode *boolector_neg (Btor *btor, BoolectorNode *node);

/**
 * Create or reduction. All bits of 'node' are combined by or.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_redor (Btor *btor, BoolectorNode *node);

/**
 * Create xor reduction. All bits of 'node' are combined by xor.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_redxor (Btor *btor, BoolectorNode *node);

/**
 * Create and reduction. All bits of 'node' are combined by and.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_redand (Btor *btor, BoolectorNode *node);

/**
 * Create bit vector slice of 'node' from index 'upper' to index 'lower'.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \param upper Upper index which must be greater than or equal to zero, and
 * less than the bit width of 'node'.
 * \param lower Lower index which must be greater than or equal to zero, and
 * less than or equal to 'upper'.
 * \return Bit vector with bit width 'upper' - 'lower' + 1.
 */
BoolectorNode *boolector_slice (Btor *btor,
                                BoolectorNode *node,
                                int upper,
                                int lower);

/**
 * Create unsigned extension. The bit vector 'node' is padded with 'width'
 * zeroes.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \param width Number of zeroes to pad.
 * \return Bit vector with bit width: bit width of 'node' + 'width'.
 */
BoolectorNode *boolector_uext (Btor *btor, BoolectorNode *node, int width);

/**
 * Create signed extension. The bit vector 'node' is padded with 'width' bits.
 * If zeroes or ones are padded depends on the most significant bit of 'node'.
 * \param btor Boolector instance.
 * \param node Bit vector node.
 * \param width Number of bits to pad.
 * \return Bit vector with bit width: bit width of 'node' + 'width'.
 */
BoolectorNode *boolector_sext (Btor *btor, BoolectorNode *node, int width);

/**
 * Create boolean implication. The parameters 'n0' and 'n1' must have bit width
 * one.
 * \param btor Boolector instance.
 * \param n0 Bit vector node representing the premise.
 * \param n1 Bit vector node representing the conclusion.
 * \return Implication n0 => n1 with bit width one.
 */
BoolectorNode *boolector_implies (Btor *btor,
                                  BoolectorNode *n0,
                                  BoolectorNode *n1);

/**
 * Create boolean equivalence. The parameters 'n0' and 'n1' must have bit width
 * one.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Equivalence n0 <=> n1 with bit width one.
 */
BoolectorNode *boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create xor. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create xnor. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_xnor (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create and. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create nand. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_nand (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create or. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create nor. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create equality. Both operands are either bit vectors with the same
 * bit width or arrays of the same type.
 * \param btor Boolector instance.
 * \param n0 First operand.
 * \param n1 Second operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create inequality. Both operands are either bit vectors with the same
 * bit width or arrays of the same type.
 * \param btor Boolector instance.
 * \param n0 First operand.
 * \param n1 Second operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create addition. The parameters 'n0' and 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector addition with the same bit width as the operands.
 */
BoolectorNode *boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create unsigned addition overflow detection. The parameters 'n0' and 'n1'
 * must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one, which indicates if the addition of
 * 'n0' and 'n1' overflows in case both operands are treated unsigned.
 */
BoolectorNode *boolector_uaddo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create signed addition overflow detection. The parameters 'n0' and 'n1' must
 * have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one, which indicates if the addition of
 * 'n0' and 'n1' overflows in case both operands are treated signed.
 */
BoolectorNode *boolector_saddo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create multiplication. The parameters 'n0' and 'n1' must have the same bit
 * width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector multiplication with the same bit width as the operands.
 */
BoolectorNode *boolector_mul (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create unsigned multiplication overflow detection. The parameters 'n0' and
 * 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one, which indicates if the multiplication
 * of 'n0' and 'n1' overflows in case both operands are treated unsigned.
 */
BoolectorNode *boolector_umulo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create signed multiplication overflow detection. The parameters 'n0' and
 * 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one, which indicates if the multiplication
 * of 'n0' and 'n1' overflows in case both operands are treated signed.
 */
BoolectorNode *boolector_smulo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create unsigned less than. The parameters 'n0' and 'n1' must have the same
 * bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_ult (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create signed less than. The parameters 'n0' and 'n1' must have the same bit
 * width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create unsigned less than or equal. The parameters 'n0' and 'n1' must have
 * the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_ulte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create signed less than or equal. The parameters 'n0' and 'n1' must have
 * the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_slte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create unsigned greater than. The parameters 'n0' and 'n1' must have the
 * same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create signed greater than. The parameters 'n0' and 'n1' must have the same
 * bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create unsigned greater than or equal. The parameters 'n0' and 'n1' must
 * have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_ugte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create signed greater than or equal. The parameters 'n0' and 'n1' must have
 * the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 */
BoolectorNode *boolector_sgte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create shift left logical. Zeroes are shifted in from the right.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand where the bit width is a power of two
 * and greater than 1.
 * \param n1 Second bit vector operand with bit width log2 of the bit width of
 * 'n0'.
 * \return Bit vector with the same bit width as 'n0'.
 */
BoolectorNode *boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create shift right logical. Zeroes are shifted in from the left.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand where the bit width is a power of two
 * and greater than 1.
 * \param n1 Second bit vector operand with bit width log2 of
 * the bit width of 'n0'.
 * \return Bit vector with the same bit width as 'n0'.
 */
BoolectorNode *boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create shift right arithmetic. Whether zeroes or ones are shifted in depends
 * on the most significant bit of 'n0'.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand where the bit width is a power of two
 * and greater than 1.
 * \param n1 Second bit vector operand with bit width log2 of
 * the bit width of 'n0'.
 * \return Bit vector with the same bit width as 'n0'.
 */
BoolectorNode *boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create rotate left.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand where the bit width is a power of two
 * and greater than 1.
 * \param n1 Second bit vector operand with bit width log2 of
 * the bit width of 'n0'.
 * \return Bit vector with the same bit width as 'n0'.
 */
BoolectorNode *boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create rotate right.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand where the bit width is a power of two
 * and greater than 1.
 * \param n1 Second bit vector operand with bit width log2 of
 * the bit width of 'n0'.
 * \return Bit vector with the same bit width as 'n0'.
 */
BoolectorNode *boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create subtraction. The parameters 'n0' and 'n1' must have the same bit
 * width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 */
BoolectorNode *boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Create unsigned subtraction overflow detection. The parameters 'n0' and
 * 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one, which indicates if the subtraction
 * of 'n0' and 'n1' overflows in case both operands are treated unsigned.
 */
BoolectorNode *boolector_usubo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create signed subtraction overflow detection. The parameters 'n0' and 'n1'
 * must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one, which indicates if the subtraction
 * of 'n0' and 'n1' overflows in case both operands are treated signed.
 */
BoolectorNode *boolector_ssubo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create unsigned division.
 * The parameters 'n0' and 'n1' must have the same bit width.
 * If 'n1' is zero, then the result is -1.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 * \remarks The behavior that division by zero returns -1 does not exactly
 * comply with the SMT-LIB standard 1.2 and 2.0 where division by zero is
 * handled as uninterpreted function. Our semantics are motivated by
 * real circuits where division by zero cannot be uninterpreted and of course
 * returns a result.
 */
BoolectorNode *boolector_udiv (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create signed division. The parameters 'n0' and 'n1' must have the same bit
 * width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 * \remarks Signed division is expressed by unsigned division and
 * the sign bits of 'n0' and 'n1'. If the sign bit of 'n0' resp. 'n1' is
 * one then two's complement is applied to normalize them.
 * Then, unsigned division is performed. Finally, two's complement
 * is applied to the result if the sign bits of 'n0' and 'n1' are different.
 * Therefore, the behavior upon dividing zero depends on \ref boolector_udiv.
 */
BoolectorNode *boolector_sdiv (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create signed division overflow detection. The parameters 'n0' and 'n1' must
 * have the same bit width.
 * An overflow can happen if 'n0' represents INT_MIN and 'n1' represents -1.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width one.
 * \return Bit vector with bit width one, which indicates if the division
 * of 'n0' and 'n1' overflows in case both operands are treated signed.
 * \remarks Unsigned division cannot overflow.
 */
BoolectorNode *boolector_sdivo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Create unsigned remainder. The parameters 'n0' and 'n1' must have the same
 * bit width. If 'n1' is zero, then the result is 'n0'.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 * \remarks As in \ref boolector_udiv the behavior if 'n1' is zero, does
 * not exactly comply with the SMT-LIB standard 1.2 and 2.0 where the result
 * is handled as uninterpreted. Our semantics are motivated by
 * real circuits where results cannot be uninterpreted.
 */
BoolectorNode *boolector_urem (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create signed remainder.The parameters 'n0' and 'n1' must have the same bit
 * width. If 'n1' is zero, then the result is 'n0'.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 * \remarks Analogously to \ref boolector_sdiv signed remainder is expressed by
 * unsigned remainder and the sign bits of 'n0' and 'n1'.
 * Therefore, if 'n1' is zero, the result depends on \ref boolector_urem.
 */
BoolectorNode *boolector_srem (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create signed remainder where sign follows divisor. The parameters 'n0' and
 * 'n1' must have the same bit width.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with the same bit width as the operands.
 * \remarks The behavior, if 'n1' is zero depends on \ref boolector_urem.
 */
BoolectorNode *boolector_smod (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Create concatenation of two bit vectors.
 * \param btor Boolector instance.
 * \param n0 First bit vector operand.
 * \param n1 Second bit vector operand.
 * \return Bit vector with bit width: bit width of 'n0' + bit width of 'n1'.
 */
BoolectorNode *boolector_concat (Btor *btor,
                                 BoolectorNode *n0,
                                 BoolectorNode *n1);

/**
 * Create a read on array 'n_array' at position 'n_index'.
 * \param btor Boolector instance.
 * \param n_array Array operand.
 * \param n_index Bit vector index. The bit width of 'n_index' must have
 * the same bit width as the indices of 'n_array'.
 * \return Bit vector with the same bit width as the elements of 'n_array'.
 */
BoolectorNode *boolector_read (Btor *btor,
                               BoolectorNode *n_array,
                               BoolectorNode *n_index);

/**
 * Create write on array 'n_array' at position 'n_index' with value 'n_value'.
 * The array is updated at one position. All other elements remain the same.
 * \param btor Boolector instance.
 * \param n_array Array operand.
 * \param n_index Bit vector index. The bit width of 'n_index' must have
 * the same bit width as the indices of 'n_array'.
 * \param n_value Bit vector value. The bit width of 'n_value' must have
 * the same bit width as the elements of 'n_array'.
 * \return Array where the value at index 'n_index' has been updated with
 * 'n_value'.
 */
BoolectorNode *boolector_write (Btor *btor,
                                BoolectorNode *n_array,
                                BoolectorNode *n_index,
                                BoolectorNode *n_value);

/**
 * Create if-then-else. If the condition 'n_cond' is true, then 'n_if' is
 * returned, otherwise 'n_else'. Both 'n_if' and 'n_else' must be either arrays
 * or bit vectors.
 * \param btor Boolector instance.
 * \param n_cond Bit vector condition with bit width one.
 * \param n_if Operand returned in the if case.
 * \param n_else Operand returned in the else case.
 * \return Result with the same type as 'n_if' and 'n_else'.
 */
BoolectorNode *boolector_cond (Btor *btor,
                               BoolectorNode *n_cond,
                               BoolectorNode *n_if,
                               BoolectorNode *n_else);

/**
 * Create function parameter. This kind of node is used to create
 * parameterized expressions, which are used to create functions. Once a
 * parameter is bound to a function, it cannot be re-used in other functions.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \param symbol Name of parameter.
 * \return Parameter expression with bit width 'width' and symbol 'symbol'.
 * \see boolector_fun, boolector_apply
 */
BoolectorNode *boolector_param (Btor *btor, int width, const char *symbol);

/**
 * Create function with body 'node', which is parameterized over parameters
 * 'param_nodes'. This kind of node is similar to macros in the SMT-LIB
 * standard 2.0. As soon as parameters are bound to a function they cannot be
 * re-used in other functions. Calling a function is done via applies created
 * via \ref boolector_apply.
 * \param btor Boolector instance.
 * \param param_nodes Parameters of function.
 * \param paramc Number of parameters.
 * \param node Parameterized Function body.
 * \return Function over parameterized expression 'node'.
 * \see boolector_apply, boolector_param
 */
BoolectorNode *boolector_fun (Btor *btor,
                              BoolectorNode **param_nodes,
                              int paramc,
                              BoolectorNode *node);

/**
 * Create function application on function 'n_fun' with arguments 'arg_nodes'.
 * \param btor Boolector instance.
 * \param arg_nodes Arguments to be applied.
 * \param argc Number of arguments to be applied.
 * \param n_fun Function expression.
 * \return Function application on function 'n_fun' with arguments 'arg_nodes'.
 */
BoolectorNode *boolector_apply (Btor *btor,
                                BoolectorNode **arg_nodes,
                                int argc,
                                BoolectorNode *n_fun);

/**
 * Create bit vector expression that increments bit vector 'node' by one.
 * \param btor Boolector instance.
 * \param node Bit vector operand.
 * \result Bit vector with the same bit width as 'node' incremented by one.
 */
BoolectorNode *boolector_inc (Btor *btor, BoolectorNode *node);

/**
 * Create bit vector expression that decrements bit vector 'node' by one.
 * \param btor Boolector instance.
 * \param node Bit vector operand.
 * \result Bit vector with the same bit width as 'node' decremented by one.
 */
BoolectorNode *boolector_dec (Btor *btor, BoolectorNode *node);

/*------------------------------------------------------------------------*/

/**
 * Return the Boolector instance to which 'node' belongs.
 * \param node Boolector node.
 * \return Boolector instance.
 */
Btor *boolector_get_btor (BoolectorNode *node);

int boolector_get_id (Btor *btor, BoolectorNode *node);
// TODO don't forget, returned node is a copy, must be released

/* Retrieve the node belonging to Boolector instance 'btor' that matches
 * given 'id'.
 * \remark Note that matching a node against another increases the reference
 * count of the returned match, which must therefore be released appropriately
 * (\see boolector_release).
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \return The Boolector node that matches given 'node' in Boolector instance
 * 'btor by id.
 */
BoolectorNode *boolector_match_node_by_id (Btor *btor, int id);

/* Retrieve the node belonging to Boolector instance 'btor' that matches
 * given BoolectorNode 'node' by id. This is intended to be used for handling
 * expressions of a cloned instance (\see boolector_clone).
 * \remark Note that matching a node against another increases the reference
 * count of the returned match, which must therefore be released appropriately
 * (\see boolector_release).
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \return The Boolector node that matches given 'node' in Boolector instance
 * 'btor by id.
 */
BoolectorNode *boolector_match_node (Btor *btor, BoolectorNode *node);

/**
 * Get the symbol of an expression. Expression must be either an array or
 * bit vector variable, a parameter, or an uninterpreted function.
 * \param btor Boolector instance.
 * \param var Array or bit vector variable, parameter, uninterpreted function.
 * \return Symbol of expression.
 * \see boolector_var
 * \see boolector_array
 * \see boolector_uf
 * \see boolector_param
 */
const char *boolector_get_symbol (Btor *btor, BoolectorNode *var);

/**
 * Set the symbol of an expression. Expression must be either an array or
 * bit vector variable, a parameter, or an uninterpreted function).
 * \param btor Boolector instance.
 * \param var Array or bit vector variable, parameter, uninterpreted function.
 * \return Symbol of expression.
 * \see boolector_var
 * \see boolector_array
 * \see boolector_uf
 * \see boolector_param
 */
void boolector_set_symbol (Btor *btor, BoolectorNode *var, const char *symbol);

/**
 * Get the bit width of an expression. If the expression
 * is an array, it returns the bit width of the array elements.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \return Bit width of 'node'.
 */
int boolector_get_width (Btor *btor, BoolectorNode *node);

/**
 * Get the bit width of indices of 'n_array'.
 * \param btor Boolector instance.
 * \param n_array Array operand.
 * \return Bit width of indices of 'n_array'.
 */
int boolector_get_index_width (Btor *btor, BoolectorNode *n_array);

/**
 * Get the bit vector of a constant node as a bit string.
 * \param btor Boolector instance.
 * \param node Constant node.
 * \return String representing the bits of 'node'.
 */
const char *boolector_get_bits (Btor *, BoolectorNode *node);

/**
 * Get the arity of function 'node'.
 * \param btor Boolector instance.
 * \param node Function node.
 * \return Arity of 'node'.
 */
int boolector_get_fun_arity (Btor *btor, BoolectorNode *node);

/**
 * Determine if given node is a constant node.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \return True if 'node' is a constant, and false otherwise.
 */
int boolector_is_const (Btor *btor, BoolectorNode *node);

/**
 * Determine if given node is a bit vector variable.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \return True if 'node' is a bit vector variable, and false otherwise.
 */
int boolector_is_var (Btor *btor, BoolectorNode *node);

/**
 * Determine if given node is an array node.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \result True if 'node' is an array, and false otherwise.
 */
int boolector_is_array (Btor *btor, BoolectorNode *node);

/**
 * Determine if expression is an array variable.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \result True if 'node' is an array variable, and false otherwise.
 */
int boolector_is_array_var (Btor *btor, BoolectorNode *node);

/**
 * Determine if given node is a parameter node.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \result True if 'node' is a parameter, and false otherwise.
 */
int boolector_is_param (Btor *btor, BoolectorNode *node);

/**
 * Determine if given parameter node is bound by a function.
 * \param btor Boolector instance.
 * \param node Parameter node.
 * \result True if 'node' is bound, and false otherwise.
 */
int boolector_is_bound_param (Btor *btor, BoolectorNode *node);

/**
 * Determine if given node is a function node.
 * \param btor Boolector instance.
 * \param node Boolector node.
 * \result True if 'node' is a function, and false otherwise.
 */
int boolector_is_fun (Btor *btor, BoolectorNode *node);

/**
 * Check if sorts of given arguments matches the function signature.
 * \param btor Boolector instance.
 * \param arg_nodes Arguments to be checked.
 * \param argc Number of arguments to be checked.
 * \param n_fun Function expression.
 * \return -1 if all sorts are correct, otherwise it returns the position of
 * the incorrect argument.
 */
int boolector_fun_sort_check (Btor *btor,
                              BoolectorNode **arg_nodes,
                              int argc,
                              BoolectorNode *n_fun);

/**
 * Generate an assignment string for bit vector expression if \ref
 * boolector_sat has returned \ref BOOLECTOR_SAT and model generation has been
 * enabled. The expression can be an arbitrary bit vector expression which
 * occurs in an assertion or current assumption. The assignment string has to
 * be freed by \ref boolector_free_bv_assignment.
 * \param btor Boolector instance.
 * \param node Bit vector expression.
 * \return String representing a satisfying assignment to bit vector variables
 * and a consistent assignment for arbitrary bit vector expressions.
 * Each character of the string can be '0', '1' or 'x'. The latter
 * represents that the corresponding bit can be assigned arbitrarily.
 * \see For enabling model generation see boolector_set_opt
 */
const char *boolector_bv_assignment (Btor *btor, BoolectorNode *node);

/**
 * Free an assignment string for bit vectors.
 * \param btor Boolector instance.
 * \param assignment String which has to be freed.
 * \see boolector_bv_assignment
 */
void boolector_free_bv_assignment (Btor *btor, const char *assignment);

/**
 * Generate a model for an array expression.
 * If \ref boolector_sat has returned \ref BOOLECTOR_SAT and model generation
 * has been enabled.
 * The function creates and stores the array of indices into 'indices' and the
 * array of corresponding values into 'values'. The number size of 'indices'
 * resp. 'values' is stored into 'size'. The array model simply inspects the
 * set of reads rho, which is associated with each array expression. See our
 * publication <a
 * href="http://fmv.jku.at/papers/BrummayerBiere-SMT08.pdf">Lemmas on Demand for
 * the Extensional Theory of Arrays</a> for details. At indices that do not
 * occur in the model, it is assumed that the array stores a globally unique
 * default value, for example 0.  The bit vector assignments to the indices and
 * values have to be freed by \ref boolector_free_bv_assignment. Furthermore,
 * the user has to free the array of indices and the array of values,
 * respectively of size 'size'. \param btor Boolector instance. \param n_array
 * Array operand for which the array model should be built. \param indices
 * Pointer to array of index strings. \param values Pointer to array of value
 * strings. \param size Pointer to size. \see For enabling model generation see
 * boolector_set_opt
 */
void boolector_array_assignment (Btor *btor,
                                 BoolectorNode *n_array,
                                 char ***indices,
                                 char ***values,
                                 int *size);

/**
 * Free an assignment string for arrays of bit vectors.
 * \param btor Boolector instance.
 * \param indices Array of index strings of size
 * \param array of index strings of size
 * \param array of values strings of size
 * \see boolector_array_assignment
 */
void boolector_free_array_assignment (Btor *btor,
                                      char **indices,
                                      char **values,
                                      int size);

/**
 * Print model to output file. This function prints the model for all inputs
 * to the output file 'file'.
 * \param btor Boolector instance.
 * \param file Output file.
 */
void boolector_print_model (Btor *btor, FILE *file);

/*------------------------------------------------------------------------*/

/**
 * Create Boolean sort.
 * \param btor Boolector instance.
 * \remark Right now sorts in Boolector are only used to create sorts for
 * uninterpreted functions.
 * uninterpreted functions.
 * \see boolector_uf
 */
BoolectorSort *boolector_bool_sort (Btor *btor);

/**
 * Create bit vector sort of width 'width'.
 * \param btor Boolector instance.
 * \param len Bit width.
 * \return Bit vector sort of width 'width'.
 * \remark Right now sorts in Boolector are only used to create sorts for
 * uninterpreted functions.
 * \see boolector_uf
 */
BoolectorSort *boolector_bitvec_sort (Btor *btor, int width);

/**
 * Create function sort.
 * \param btor Boolector instance.
 * \param domain List of arguments' sorts.
 * \param arity Number of elements in domain (must be > 0).
 * \param codomain Sort of function return value.
 * \remark Right now sorts in Boolector are only used to create sorts for
 * uninterpreted functions.
 * \see boolector_uf
 */
BoolectorSort *boolector_fun_sort (Btor *btor,
                                   BoolectorSort **domain,
                                   int arity,
                                   BoolectorSort *codomain);

/**
 * Release sort (decrements reference counter).
 * \param btor Boolector instance.
 * \param sort Sort to be released.
 */
void boolector_release_sort (Btor *btor, BoolectorSort *sort);

/*------------------------------------------------------------------------*/

/**
 * Parse input file. Input file format may be either BTOR, SMT-LIB v1, or
 * SMT-LIB v2 and is determined automatically.
 * If the parser encounters an error, an explanation of that error is stored
 * in 'error_msg'. If the input file specifies a (known) status of the input
 * formula (either sat or unsat), that status is stored in 'status'.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 * \return In the incremental case (right now SMT-LIB v1 only) the function
 * returns either \ref BOOLECTOR_SAT, \ref BOOLECTOR_UNSAT or
 * \ref BOOLECTOR_UNKNOWN, otherwise it always returns \ref BOOLECTOR_UNKNOWN.
 * If a parse error occurs the function returns \ref BOOLECTOR_PARSE_ERROR.
 */
int boolector_parse (Btor *btor,
                     FILE *file,
                     const char *file_name,
                     char **error_msg,
                     int *status);

/**
 * Parse input file in BTOR format. See \ref boolector_parse.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 * \return \ref BOOLECTOR_UNKNOWN or \ref BOOLECTOR_PARSE_ERROR if a parse
 * error occurred.
 */
int boolector_parse_btor (Btor *btor,
                          FILE *file,
                          const char *file_name,
                          char **error_msg,
                          int *status);

/**
 * Parse input file in SMT-LIB v1 format. See \ref boolector_parse.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 * \return In the incremental case (right now SMT-LIB v1 only) the function
 * returns either \ref BOOLECTOR_SAT, \ref BOOLECTOR_UNSAT or
 * \ref BOOLECTOR_UNKNOWN, otherwise it always returns \ref BOOLECTOR_UNKNOWN.
 * If a parse error occurs the function returns \ref BOOLECTOR_PARSE_ERROR.
 */
int boolector_parse_smt1 (Btor *btor,
                          FILE *file,
                          const char *file_name,
                          char **error_msg,
                          int *status);

/**
 * Parse input file in SMT-LIB v2 format. See \ref boolector_parse.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 * \return \ref BOOLECTOR_UNKNOWN or \ref BOOLECTOR_PARSE_ERROR if a parse
 * error occurred.
 */
int boolector_parse_smt2 (Btor *btor,
                          FILE *file,
                          const char *file_name,
                          char **error_msg,
                          int *status);

/*------------------------------------------------------------------------*/

/**
 * Recursively dump 'node' to file in
 * <a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR</a>
 * format.
 *
 * \param btor Boolector instance.
 * \param file File to which the expression should be dumped.
 * The file must be have been opened by the user before.
 * \param node The expression which should be dumped.
 */
void boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node);

/**
 * Dump formula to file in
 * <a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR</a>
 * format.
 *
 * \param btor Boolector instance.
 * \param file File to which the formula should be dumped.
 * The file must be have been opened by the user before.
 */
void boolector_dump_btor (Btor *btor, FILE *file);

#if 0
/**
 * Dump formula to file in BTOR 2.0 format.
 *
 * \param btor Boolector instance.
 * \param file File to which the formula should be dumped.
 * The file must be have been opened by the user before.
 */
void boolector_dump_btor2 (Btor * btor, FILE * file);
#endif

/**
 * Recursively dump 'node' to file in
 * <a href="http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf">SMT-LIB
 * v1</a> format. \param btor Boolector instance. \param file File to which the
 * expression should be dumped. The file must be have been opened by the user
 * before. \param node The expression which should be dumped.
 */
void boolector_dump_smt1_node (Btor *btor, FILE *file, BoolectorNode *node);

/**
 * Dump formula to file in <a
 * href="http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf">SMT-LIB
 * v1</a> format. \param btor Boolector instance \param file Output file.
 */
void boolector_dump_smt1 (Btor *btor, FILE *file);

/**
 * Recursively dump 'node' to file in
 *<a
 *href="http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf">SMT-LIB
 *2.0</a> format. \param btor Boolector instance. \param file File to which the
 *expression should be dumped. The file must be have been opened by the user
 *before. \param node The expression which should be dumped.
 */
void boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node);

/**
 * Dumps formula to file in
 * <a
 * href="http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf">SMT-LIB
 * 2.0</a> format. \param btor Boolector instance \param file Output file.
 */
void boolector_dump_smt2 (Btor *btor, FILE *file);

/* DEPRECATED API */

/**
 * \deprecated
 * Enable model generation.
 * \param btor Boolector instance.
 * \see boolector_set_opt
 * \remark
 * This function is deprecated, use \ref boolector_set_opt with model_gen=1
 * instead.
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
void
boolector_enable_model_gen (Btor *btor);

/**
 * \deprecated
 * Enable model generation for all reads.
 * \param btor Boolector instance.
 * \remark
 * This function is deprecated, use \ref boolector_set_opt with model_gen=2
 * instead.
 * \see boolector_set_opt
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
void
boolector_generate_model_for_all_reads (Btor *btor);

/**
 * \deprecated
 * Enable incremental usage.
 * \param btor Boolector instance.
 * \see boolector_set_opt
 * \remark
 * This function is deprecated, use \ref boolector_set_opt with incremental=1
 * instead.
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
void
boolector_enable_inc_usage (Btor *btor);

/**
 * \deprecated
 * Set the rewrite level of the rewriting engine.
 * \param btor Boolector instance.
 * \param val Rewrite level ranging from
 * 0 (no rewriting) to 3 (full rewriting).
 * \see boolector_set_opt
 * \remark
 * This function is deprecated use \ref boolector_set_opt with
 * rewrite_level=0...3 instead.
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
void
boolector_set_rewrite_level (Btor *btor, int val);

/**
 * \deprecated
 * Set level of verbosity.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt_verbosity instead.)
 * \param btor Boolector instance.
 * \param val Verbosity level.
 * \see boolector_set_opt
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
void
boolector_set_verbosity (Btor *btor, int val);

/**
 * \deprecated
 * Set log level.
 * \param btor Boolector instance.
 * \param val Log level.
 * \see boolector_set_opt
 * \remark
 * This function is deprecated, use \ref boolector_set_opt with loglevel=<int>
 * instead.
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
void
boolector_set_loglevel (Btor *btor, int val);

/**
 * \deprecated
 * Get the symbol of a variable.
 * \param btor Boolector instance.
 * \param var Array or bit vector variable.
 * \return Symbol of variable.
 * \see boolector_set_opt
 * \remark
 * This function is deprecated, use \ref boolector_get_symbol instead.
 */
#ifdef __GNUC__
__attribute__ ((deprecated))
#endif
const char *
boolector_get_symbol_of_var (Btor *btor, BoolectorNode *var);

#endif

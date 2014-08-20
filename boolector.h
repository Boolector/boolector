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

#ifdef __GNUC__
#define BTOR_DEPRECATED(f) f __attribute__ ((deprecated))
#else
#define BTOR_DEPRECATED(f) f
#endif

/*------------------------------------------------------------------------*/

/**
 * \mainpage Boolector Documentation
 * \section Introduction
 * This is the documentation of Boolector's public interface. Boolector
 * is an SMT solver for the quantifier-free theory of bit-vectors
 * in combination with the quantifier-free extensional theory of arrays.
 * Please visit our <a href="http://fmv.jku.at/boolector">website</a>.
 * It contains:
 * - the latest version
 * - publications related to Boolector
 * - a link to our discussion platform
 * - news
 *
 * Boolector can be used as stand-alone SMT solver which reads either
 *<a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR</a>
 * and <a
 *href="http://goedel.cs.uiowa.edu/smtlib/papers/format-v1.2-r06.08.30.pdf">SMT-LIB
 *1.2</a>. Furthermore, Boolector provides a public API in order to use
 *Boolector as backend in other tools.
 *
 * \section Interface
 * The public interface is defined in \ref boolector.h.
 *
 * First of all, the user has to create
 * a boolector instance by calling \ref boolector_new. This instance
 * is needed by all other functions. After creating an instance, the
 * rewrite level of the rewriting engine can be set by
 * \ref boolector_set_rewrite_level and/or
 * model generation can be enabled by \ref boolector_enable_model_gen. Then,
 * the user can build expressions of bit-vectors and arrays. As the design of
 * Boolector was motivated by real hardware, we do not distinguish between
 * the type 'boolean' and the type 'bit-vector of bit-width one'.
 * After building expressions the user can assert them by
 * \ref boolector_assert. The resulting instance can be decided
 * by \ref boolector_sat. If model generation has been enabled
 * and the instance is satisfiable, the user can obtain assignments to
 * bit-vectors resp. arrays by
 * \ref boolector_bv_assignment resp. \ref boolector_array_assignment.
 * The assignments are not limited to variables.
 * They can be obtained for arbitrary expressions.
 * Finally, Boolector supports incremental usage with assumptions analogously
 * to MiniSAT. The incremental usage can be enabled
 * via \ref boolector_set_opt Assumptions can be added by \ref boolector_assume.
 *
 * \section Internals
 * Internally, Boolector manages an expression DAG. This means that each
 * expression has a reference counter which is initially set to one.
 * Each sharing increments the reference counter. An expression can be
 * copied by \ref boolector_copy which simply increments the reference counter.
 * An expression can be released by \ref boolector_release which decreases
 * the reference counter. If the reference counter reaches zero, then
 * the expression node is deleted from memory.
 *
 * Already during construction of the expression DAG,
 * rewriting is performed. This rewriting should simplify the DAG already
 * during construction. When \ref boolector_sat is called, Boolector
 * starts an extra rewriting phase to simplify the DAG.
 * The rewrite level can be configured by \ref boolector_set_rewrite_level.
 *
 * Boolector internally uses a set of base operators.
 * The set is documented in
 *<a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR:
 *Bit-Precise Modelling of Word-Level Problems for Model Checking</a>. Many
 *operators that are available in the API are rewritten as combination of base
 *operators internally. For example, two's complement is rewritten as one's
 *complement and addition of 1.  This behavior is not influenced by the rewrite
 *level.
 *
 * \subsection Assertions
 * Boolector uses two different kinds of assertions. Internally, Boolector
 * heavily uses assertions provided by the standard C library.
 * To increase performance, these assertions are disabled in releases.
 *
 * The functions of Boolector's public interface are guarded by
 * public assertions. Public assertions are always enabled. They check if
 * the functions have been correctly called by the user.
 * If not, then an error message is printed out and 'abort' is called.
 * For example, we call \ref boolector_var and
 * pass NULL as symbol name. Then, we obtain the following error message:
 *
 * \verbatim [boolector] boolector_var: 'symbol' must not be NULL \endverbatim
 *
 * This is not a bug. The user has violated the pre-conditions of the function,
 * and therefore Boolector aborts.
 *
 * \section Examples
 * In the section <a href="examples.html">examples</a> you can
 * find bit-vector and array examples. They demonstrate
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
 * \see boolector_sat, boolector_simplify
 */
#define BOOLECTOR_UNKNOWN 0
/**
 * Preprocessor constant representing status 'satisfiable'.
 * \see boolector_sat, boolector_simplify
 */
#define BOOLECTOR_SAT 10
/**
 * Preprocessor constant representing status 'unsatisfiable'.
 * \see boolector_sat, boolector_simplify
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
 * Clone an instance of Boolector.
 * \param btor original Boolector instance.
 * \return New Boolector instance.
 */
Btor *boolector_clone (Btor *btor);

/**
 * Delete a boolector instance and frees its resources.
 * \param btor Boolector instance.
 * \remarks Expressions that have not been release properly will not be
 * deleted from memory. Use \ref boolector_get_refs to debug reference
 * counting.
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
 * Set and get the output API trace file.
 */
void boolector_set_trapi (Btor *btor, FILE *apitrace);

/**
 * TODO
 */
FILE *boolector_get_trapi (Btor *btor);

/*------------------------------------------------------------------------*/

/**
 * Add a constraint. Use this function to assert 'node'.
 * Added constraints can not be deleted anymore. After 'node' has
 * been asserted, it can be safely released by \ref boolector_release.
 * \param btor Boolector instance.
 * \param node Bit-vector expression with bit-width one.
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
 * \param node Bit-vector expression with bit-width one.
 */
void boolector_assume (Btor *btor, BoolectorNode *node);

/**
 * Determine if assumption 'node' is a failed assumption.
 * \param btor Boolector instance.
 * \param node Bit-vector expression with bit-width one.
 * \return 1 if assumption is failed, and 0 otherwise.
 */
int boolector_failed (Btor *btor, BoolectorNode *node);

/**
 * Solve an instance represented by constraints and assumptions added
 * by \ref boolector_assert and \ref boolector_assume. Note that
 * assertions and assumptions are combined by boolean 'and'.
 * If you want to call this function multiple times then you must enable
 * Boolector's incremental usage mode via \ref boolector_set_opt
 * before. Otherwise, this function can only * be called once.
 * \param btor Boolector instance.
 * \return It returns \ref BOOLECTOR_SAT if the instance is satisfiable and
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
 * Boolector's incremental usage mode by calling
 * \ref boolector_enable_inc_usage before. Otherwise, this function can only
 * be called once.
 * \param btor Boolector instance.
 * \param lod_limit Limit for lemmas on demand (-1 unlimited).
 * \param sat_limit Conflict limit for SAT solver (-1 unlimited).
 * \return It returns \ref BOOLECTOR_SAT if the instance is satisfiable and
 * \ref BOOLECTOR_UNSAT if the instance is unsatisfiable.
 * \see boolector_bv_assignment
 * \see boolector_array_assignment
 **/
int boolector_limited_sat (Btor *btor, int lod_limit, int sat_limit);

/**
 * TODO
 */
int boolector_simplify (Btor *btor);

/*------------------------------------------------------------------------*/

/**
 * Set the SAT solver to use.
 * Currently, we support 'Lingeling', 'PicoSAT', and 'MiniSAT' as string
 * value of \param solver (case insensitive).  This is however
 * only possible if the corresponding solvers were enabled at compile time.
 * The return value is non-zero if setting the SAT solver call was
 * successful.  Call this function after \ref boolector_new.
 * \param btor Boolector instance
 * \param solver Solver identifier string.
 * \param opt_str Solver options string.
 */
int boolector_set_sat_solver (Btor *btor,
                              const char *solver,
                              const char *optstr,
                              int nofork);

#ifdef BTOR_USE_LINGELING
int boolector_set_sat_solver_lingeling (Btor *btor,
                                        const char *optstr,
                                        int nofork);
#endif

#ifdef BTOR_USE_PICOSAT
int boolector_set_sat_solver_picosat (Btor *btor);
#endif

#ifdef BTOR_USE_MINISAT
int boolector_set_sat_solver_minisat (Btor *btor);
#endif

/*------------------------------------------------------------------------*/

/**
 * Set option.
 * \param btor Boolector instance.
 * \param name Option name.
 * \param val  Option value..
 * \see boolector_sat
 *
 * List of options:
 *
 * - 'model_gen':
 *	Enable (1) or disable (0) generation of a model for satisifiable
 *	instances.
 *
 * - 'model_gen_all_reads':
 *	Enable (1) or disable (0) generation of a model for all reads.
 *	By default boolector generates assignments for reads within the
 *	cone of assertions, only. This options forces the generation of
 *	assignments for all reads during model generation.
 *
 * - 'incremental':
 *	Enable (1) incremental mode. Note that incremental usage turns
 *	off some optimization techniques. Disabling incremental usage is
 *	currently not supported.
 *
 * - 'incremental_all':
 *	Enable (1) or disable (0) incremental solving of all formulas (when
 *	parsing an input file). Note that currently, incremental mode is only
 *	supported for SMT-LIB v1 input.
 *
 * - 'incremental_in_depth':
 *	Set incremental in-depth mode width (when parsing an input file).
 *	Note that currently, incremental mode is only supported for SMT-LIB v1
 *	input.
 *
 * - 'incremental_look_ahead':
 *	Set incremental look-ahead mode width (when parsing an input file).
 *	Note that currently, incremental mode is only supported for SMT-LIB v1
 *	input.
 *
 * - 'incremental_interval':
 *	Set incremental interval mode width (when parsing an input file).
 *	Note that currently, incremental mode is only supported for SMT-LIB v1
 *	input.
 *
 * - 'input_format':
 *	Force input file format (Btor: -1, SMT-LIB v1: 1, SMT-LIB v2: 2) when
 *	parsing an input file. If unspecified, Boolector determines the
 *	input file format while parsing.
 *
 * - 'output_number_format':
 *	Force output number format (binary: 0, hexadecimal: 1, decimal: 2).
 *	Boolector uses binary by default.
 *
 * - 'output_format':
 *	Force output file format (Btor: -1, SMT-LIB v1: 1, SMT-LIB v2: 2).
 *	Boolector uses Btor by default.
 *
 * - 'rewrite_level':
 *      Set the rewrite level (0-3) of the rewriting engine. Boolector uses
 *      rewrite level 3 by default. Do not alter the rewrite level after
 *      creating expressions.
 *      (0 ... no rewriting, 3 ... full rewriting)
 *
 * - 'rewrite_level_pbr':
 *	Set the rewrite level (0-3) for partial beta reduction. Boolector uses
 *	rewrite level 1 by default.
 *      (0 ... no rewriting, 3 ... full rewriting)
 *
 * - 'beta_reduce_all':
 *	Enable (1) or disable (0) the eager elimination of lambda expressions
 *	via beta reduction.
 *
 * - 'probe_beta_reduce_all':
 *	Enable (1) or disable (0) probing of 'beta_reduce_all' (until a given
 *	LOD or SAT conflicts limit.
 *
 * - 'pbra_lod_limit':
 *      Set LOD limit for 'probe_beta_reduce_all'.
 *
 * - 'pbra_sat_limit':
 *	Set SAT conflicts limit for 'probe_beta_reduce_all'.
 *
 * - 'pbra_ops_factor':
 *	Set factor by which the size of the beta reduced formula may be greater
 *	than the original formula (for 'probe_beta_reduce_all').
 *
 * - 'dual_prop':
 *	Enable (1) or disable (0) dual propagation optimization.
 *
 * - 'just':
 *	Enable (1) or disable (0) justification optimization.
 *
 * - 'ucopt':
 *	Enable (1) or disable (0) unconstrained optimization.
 *
 * - 'force_cleanup':
 *      Enable (1) or disable (0) forced automatic cleanup of expressions and
 *      assignment strings on \ref boolector_delete.
 *
 * - 'pretty_print':
 *      Enable (1) or disable (0) pretty printing when dumping.
 *
 * - 'verbosity':
 *	Set the level of verbosity.
 *	(0 ... do not be verbose, x ... increase verbosity)
 *
 * - 'loglevel':
 *	Set log level (0-3).
 *	(0 ... no logging, 3 ... full logging)
 *
 */
void boolector_set_opt (Btor *btor, const char *opt, int val);

const BtorOpt *boolector_get_opt (Btor *btor, const char *opt);
int boolector_get_opt_val (Btor *btor, const char *opt);

const BtorOpt *boolector_first_opt (Btor *btor);

const BtorOpt *boolector_last_opt (Btor *btor);

const BtorOpt *boolector_next_opt (Btor *btor, const BtorOpt *opt);

/*------------------------------------------------------------------------*/

/**
 * Copy expression (increments reference counter).
 * \param btor Boolector instance.
 * \param node Operand.
 * \return The expression 'node'.
 */
BoolectorNode *boolector_copy (Btor *btor, BoolectorNode *node);

/**
 * Release expression (decrements reference counter).
 * \param btor Boolector instance.
 * \param node Operand.
 */
void boolector_release (Btor *btor, BoolectorNode *node);

/**
 * Bit-vector constant representing the bit-vector 'bits'.
 * \param btor Boolector instance.
 * \param bits Non-empty and terminated string consisting of zeroes and/or ones.
 * representing the bit-vector constant specified by 'bits'.
 * \return Bit-vector constant with bit-width strlen('bits').
 */
BoolectorNode *boolector_const (Btor *btor, const char *bits);

/**
 * Bit-vector constant zero.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant zero with bit-width 'width'.
 */
BoolectorNode *boolector_zero (Btor *btor, int width);

/**
 * Bit-vector constant zero with bit-width one.
 * \param btor Boolector instance.
 * \return Bit-vector constant zero with bit-width one.
 */
BoolectorNode *boolector_false (Btor *btor);

/**
 * Binary constant representing 'width' ones.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant -1 with bit-width 'width'.
 */
BoolectorNode *boolector_ones (Btor *btor, int width);

/**
 * Bit-vector constant one with bit-width one.
 * \param btor Boolector instance.
 * \return Bit-vector constant one with bit-width one.
 */
BoolectorNode *boolector_true (Btor *btor);

/**
 * Bit-vector constant one.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant one with bit-width 'width'.
 */
BoolectorNode *boolector_one (Btor *btor, int width);

/**
 * Binary constant representing the unsigned integer 'u' with bit-width 'width'.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * \param btor Boolector instance.
 * \param u Unsigned integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant with bit-width 'width'.
 */
BoolectorNode *boolector_unsigned_int (Btor *btor, unsigned u, int width);

/**
 * Binary constant representing the signed integer 'i' with bit-width 'width'.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * \param btor Boolector instance.
 * \param i Signed integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant with bit-width 'width'.
 */
BoolectorNode *boolector_int (Btor *btor, int i, int width);

/**
 * Fresh bit-vector variable with bit-width 'width'.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \param symbol Name of variable.
 * \return Bit-vector variable with bit-width 'width' and symbol 'symbol'.
 * \remarks Internally, variables are \e not uniquely hashed.
 * Therefore, every call to this function returns a fresh variable.
 * The symbol is only used as a simple way to identify variables
 * in file dumps of \ref boolector_dump_btor and \ref boolector_dump_smt.
 * The user has to make sure that the symbols are unique. Otherwise, the
 * dump may be incorrect. If you are not interested in dumping expressions,
 * just pass NULL as symbol.
 */
BoolectorNode *boolector_var (Btor *btor, int width, const char *symbol);

/**
 * One-dimensional bit-vector array of size 2 ^ 'index_width' with elements of
 * bit-width 'elem_width'.
 * \param btor Boolector instance.
 * \param elem_width Number of bits of array elements. The parameter must be
 * greater than zero.
 * \param index_width Number of bits of array addresses. The parameter must be
 * greater than zero.
 * \param symbol Name of variable.
 * \return Bit-vector array of size 2 ^ 'index_width' with elements of
 * bit-width 'elem_width', and symbol 'symbol'.
 * \remarks Internally, array variables are \e not uniquely hashed. Therefore,
 * each call to \ref boolector_array with the same arguments will return
 * a fresh variable.
 ** The symbol is only used as a simple way to identify variables
 * in file dumps of \ref boolector_dump_btor and \ref boolector_dump_smt.
 * The user has to make sure that the symbols are unique. Otherwise, the
 * dump may be incorrect.
 * If you are not interested in dumping expressions,
 * just pass NULL as symbol.
 */
BoolectorNode *boolector_array (Btor *btor,
                                int elem_width,
                                int index_width,
                                const char *symbol);

/**
 * One's complement.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \return Bit-vector with the same bit-width as 'node'.
 */
BoolectorNode *boolector_not (Btor *btor, BoolectorNode *node);

/**
 * Two's complement.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \return Bit-vector with the same bit-width as 'node'.
 */
BoolectorNode *boolector_neg (Btor *btor, BoolectorNode *node);

/**
 * Or reduction. All bits are combined by or.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_redor (Btor *btor, BoolectorNode *node);

/**
 * Xor reduction. All bits are combined by xor.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_redxor (Btor *btor, BoolectorNode *node);

/**
 * And reduction. All bits are combined by and.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_redand (Btor *btor, BoolectorNode *node);

/**
 * Bit-vector slice of 'node' from index 'upper' to index 'lower'.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \param upper Upper index which must be greater than or equal to zero, and
 * less than the bit-width of 'node'.
 * \param lower Lower index which must be greater than or equal to zero, and
 * less than or equal to 'upper'.
 * \return Bit-vector with bit-width 'upper' - 'lower' + 1.
 */
BoolectorNode *boolector_slice (Btor *btor,
                                BoolectorNode *node,
                                int upper,
                                int lower);

/**
 * Unsigned extension. The operand 'node' is padded with 'width' zeroes.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \param width Number of zeroes to pad.
 * \return Bit-vector with bit-width: bit-width of 'node' + 'width'.
 */
BoolectorNode *boolector_uext (Btor *btor, BoolectorNode *node, int width);

/**
 * Signed extension. The operand 'node' is padded with 'width' bits. If zeroes
 * or ones are padded depends on the most significant bit of 'node'.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \param width Number of bits to pad.
 * \return Bit-vector with bit-width: bit-width of 'node' + 'width'.
 */
BoolectorNode *boolector_sext (Btor *btor, BoolectorNode *node, int width);

/**
 * Implication. The parameters * 'n0' and 'n1' must have bit-width one.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_implies (Btor *btor,
                                  BoolectorNode *n0,
                                  BoolectorNode *n1);

/**
 * Equivalence. The parameters 'n0' and 'n1' must have bit-width one.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Xor. The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Xnor. The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_xnor (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * And. The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Nand. The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_nand (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Or. The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Nor. The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/** Equality. Either both operands are bit-vectors with the same
 * bit-width or both operands are arrays of the same type.
 * \param btor Boolector instance.
 * \param n0 First operand.
 * \param n1 Second operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/** Inequality. Either both operands are bit-vectors with the same
 * bit-width or both operands are arrays of the same type.
 * \param btor Boolector instance.
 * \param n0 First operand.
 * \param n1 Second operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Addition.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Unsigned addition overflow detection. The result represents if the addition
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_uaddo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Signed addition overflow detection. The result represents if the addition
 * overflows when both operands are interpreted as signed.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_saddo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Multiplication.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_mul (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Unsigned multiplication overflow detection.
 * The result represents if the multiplication
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_umulo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Signed multiplication overflow detection.
 * The result represents if the multiplication
 * overflows when both operands are interpreted as signed.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_smulo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Unsigned less than.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_ult (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Signed less than.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Unsigned less than or equal.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_ulte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Signed less than or equal.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_slte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Unsigned greater than.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Signed greater than.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Unsigned greater than or equal.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_ugte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Signed greater than or equal.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_sgte (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Shift left.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param n1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'n0'.
 * \return Bit-vector with the same bit-width as 'n0'.
 */
BoolectorNode *boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Shift right logical. Zeroes are shifted in.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param n1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'n0'.
 * \return Bit-vector with the same bit-width as 'n0'.
 */
BoolectorNode *boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Shift right arithmetic. Whether zeroes or ones are shifted in depends
 * on the most significant bit of 'n0'.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param n1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'n0'.
 * \return Bit-vector with the same bit-width as 'n0'.
 */
BoolectorNode *boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Rotate left.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param n1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'n0'.
 * \return Bit-vector with the same bit-width as 'n0'.
 */
BoolectorNode *boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Rotate right.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param n1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'n0'.
 * \return Bit-vector with the same bit-width as 'n0'.
 */
BoolectorNode *boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Subtraction.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BoolectorNode *boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1);

/**
 * Unsigned subtraction overflow detection.
 * The result represents if the subtraction
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_usubo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Signed subtraction overflow detection.
 * The result represents if the subtraction
 * overflows when both operands are interpreted as signed.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BoolectorNode *boolector_ssubo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Unsigned division.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * If 'n1' is zero, then the result is -1.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks The behavior that division by zero returns -1 does not exactly
 * comply with the SMT-LIB standard 1.2 where division by zero is
 * handled as uninterpreted function. Our semantics are motivated by
 * real circuits where division by zero cannot be uninterpreted and of course
 * returns a result.
 */
BoolectorNode *boolector_udiv (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Signed division.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
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
 * Signed division overflow detection.
 * The result represents if the division
 * overflows when both operands are interpreted as signed.
 * This happens when 'n0' represents INT_MIN and 'n1' represents -1.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 * \remarks Unsigned division cannot overflow.
 */
BoolectorNode *boolector_sdivo (Btor *btor,
                                BoolectorNode *n0,
                                BoolectorNode *n1);

/**
 * Unsigned remainder.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * If 'n1' is zero, then the result is 'n0'.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks As in \ref boolector_udiv the behavior if 'n1' is zero, does
 * not exactly comply with the SMT-LIB standard 1.2 where the result
 * is handled as uninterpreted. Our semantics are motivated by
 * real circuits where results cannot be uninterpreted.
 */
BoolectorNode *boolector_urem (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Signed remainder.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * If 'n1' is zero, then the result is 'n0'.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks Analogously to \ref boolector_sdiv signed remainder is expressed by
 * unsigned remainder and the sign bits of 'n0' and 'n1'.
 * Therefore, if 'n1' is zero, the result depends on \ref boolector_urem.
 */
BoolectorNode *boolector_srem (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Signed remainder where sign follows divisor.
 * The parameters 'n0' and 'n1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks The behavior, if 'n1' is zero depends on \ref boolector_urem.
 */
BoolectorNode *boolector_smod (Btor *btor,
                               BoolectorNode *n0,
                               BoolectorNode *n1);

/**
 * Concatenation.
 * \param btor Boolector instance.
 * \param n0 First bit-vector operand.
 * \param n1 Second bit-vector operand.
 * \return Bit-vector with bit-width: bit-width of 'n0' + bit-width of 'n1'.
 */
BoolectorNode *boolector_concat (Btor *btor,
                                 BoolectorNode *n0,
                                 BoolectorNode *n1);

/**
 * Array read on array 'n_array' at position 'n_index'.
 * \param btor Boolector instance.
 * \param n_array Array operand.
 * \param n_index Bit-vector index. The bit-width of 'n_index' must have
 * the same bit-width as the indices of 'n_array'.
 * return Bit-vector with the same bit-width as the elements of 'n_array'.
 */
BoolectorNode *boolector_read (Btor *btor,
                               BoolectorNode *n_array,
                               BoolectorNode *n_index);

/**
 * Array write on array 'n_array' at position 'n_index' with value 'n_value'.
 * The array is updated at one position. All other elements remain the same.
 * \param btor Boolector instance.
 * \param n_array Array operand.
 * \param n_index Bit-vector index. The bit-width of 'n_index' must have
 * the same bit-width as the indices of 'n_array'.
 * \param n_value Bit-vector value. The bit-width of 'n_value' must have
 * the same bit-width as the elements of 'n_array'.
 * \return Array where the value at one specific index has been updated.
 */
BoolectorNode *boolector_write (Btor *btor,
                                BoolectorNode *n_array,
                                BoolectorNode *n_index,
                                BoolectorNode *n_value);

/**
 * If-then-else. If the condition 'n_cond' is one, then
 * 'n_if' is returned, otherwise 'n_else'.
 * Either 'n_if' and 'n_else' must be both arrays, or they must be both
 * bit-vectors.
 * \param btor Boolector instance.
 * \param n_cond Bit-vector condition with bit-width one.
 * \param n_if Operand returned in the if case.
 * \param n_else Operand returned in the else case.
 * \return Result with the same type as 'n_if' and 'n_else'.
 */
BoolectorNode *boolector_cond (Btor *btor,
                               BoolectorNode *n_cond,
                               BoolectorNode *n_if,
                               BoolectorNode *n_else);

/**
 * Parameter.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \param symbol Name of parameter.
 * \result Parameter expression.
 */
BoolectorNode *boolector_param (Btor *btor, int width, const char *symbol);

/**
 * Function.
 * \param btor Boolector instance.
 * \param paramc Number of parameters.
 * \param param_nodes Parameters of function.
 * \param node Function body.
 * \result Function parameter.
 */
BoolectorNode *boolector_fun (Btor *btor,
                              int paramc,
                              BoolectorNode **param_nodes,
                              BoolectorNode *node);

/**
 * Uninterpreted function.
 * \param btor Boolector instance.
 * \param sort Sort of the uninterpreted function.
 */
BoolectorNode *boolector_uf (Btor *btor,
                             BoolectorSort *sort,
                             const char *symbol);

/**
 * Creates an argument expression consisting of 'argc' argument expressions
 * given as 'arg_nodes'.
 * \param btor Boolector instance.
 * \param argc Argument count.
 * \param arg_nodes Argument nodes.
 * \result Argument expression.
 */
BoolectorNode *boolector_args (Btor *btor, int argc, BoolectorNode **arg_nodes);

/**
 * Create a function application expression.
 * \param btor Boolector instance.
 * \param argc Number of arguments to be applied.
 * \param arg_nodes Arguments to be applied.
 * \param n_fun Function expression.
 * \result Function application expression.
 */
BoolectorNode *boolector_apply (Btor *btor,
                                int argc,
                                BoolectorNode **arg_nodes,
                                BoolectorNode *n_fun);

/* Apply argument expression 'n_args' to function 'n_fun'.
 * \param btor Boolector instance.
 * \param n_args Argument expression.
 * \param n_fun Function expression.
 */
BoolectorNode *boolector_apply_args (Btor *btor,
                                     BoolectorNode *n_args,
                                     BoolectorNode *n_fun);

/**
 * Increment bit-vector by one.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \result Bit-vector with the same bit-width as 'node'.
 */
BoolectorNode *boolector_inc (Btor *btor, BoolectorNode *node);

/**
 * Decrement bit-vector by one.
 * \param btor Boolector instance.
 * \param node Bit-vector operand.
 * \result Bit-vector with the same bit-width as 'node'.
 */
BoolectorNode *boolector_dec (Btor *btor, BoolectorNode *node);

/*------------------------------------------------------------------------*/

/**
 * Return the Boolector instance to which 'node' belongs.
 * \param node Boolector node.
 * \return Boolector instance.
 */
Btor *boolector_get_btor (BoolectorNode *node);

/**
 * TODO
 */
int boolector_is_const (Btor *btor, BoolectorNode *node);

/**
 * TODO
 */
int boolector_is_var (Btor *btor, BoolectorNode *node);

/**
 * TODO
 */
const char *boolector_get_bits (Btor *, BoolectorNode *node);

/**
 * Determine if expression is an array. If not, expression is a bit-vector.
 * \param btor Boolector instance.
 * \param node Operand.
 * \result True if expression is an array, and false otherwise.
 */
int boolector_is_array (Btor *btor, BoolectorNode *node);

/**
 * Determine if expression is an array variable.
 * \param btor Boolector instance.
 * \param node Operand.
 * \result True if expression is an array variable, and false otherwise.
 */
int boolector_is_array_var (Btor *btor, BoolectorNode *node);

/**
 * Determine if given node is a parameter expression.
 * \param btor Boolector instance.
 * \param node Operand.
 * \result True if expression is a parameter, and false otherwise.
 */
int boolector_is_param (Btor *btor, BoolectorNode *node);

/**
 * Determine if given parameter node is bound by a function.
 * \param btor Boolector instance.
 * \param node Parameter node.
 * \result True if paramter is bound, and false otherwise.
 */
int boolector_is_bound_param (Btor *btor, BoolectorNode *node);

/**
 * Determine if expression is a function.
 * \param btor Boolector instance.
 * \param node Operand.
 * \result True if epxression is a function, and false otherwise.
 */
int boolector_is_fun (Btor *btor, BoolectorNode *node);

/**
 * Get the arity of function 'node'.
 * \param btor Boolector instance.
 * \param node Function.
 * \return arity of 'node'.
 */
int boolector_get_fun_arity (Btor *btor, BoolectorNode *node);

/**
 * Determine if expression is an argument expression.
 * \param btor Boolector instance.
 * \param node Operand.
 * \result True if epxression is an argument, and false otherwise.
 */
int boolector_is_args (Btor *btor, BoolectorNode *node);

/**
 * Get the arity of argument 'node'.
 * \param btor Boolector instance.
 * \param node Argument expression.
 * \return arity of 'node'.
 */
int boolector_get_args_arity (Btor *btor, BoolectorNode *node);

/**
 * Get the bit-width of an expression. If the expression
 * is an array, it returns the bit-width of the array elements.
 * \param btor Boolector instance.
 * \param node Operand.
 * \return bit-width of 'node'.
 */
int boolector_get_width (Btor *btor, BoolectorNode *node);

/**
 * Get the bit-width of indices of 'n_array'.
 * \param btor Boolector instance.
 * \param n_array Array operand.
 * \return bit-width of indices of 'n_array'.
 */
int boolector_get_index_width (Btor *btor, BoolectorNode *n_array);

/**
 * Check if sorts of given arguments matches the function signature.
 * \param btor Boolector instance.
 * \param argc Number of arguments to be checked.
 * \param arg_nodes Arguments to be checked.
 * \param n_fun Function expression.
 * \return -1 if all sorts are correct, otherwise returns the position of the
 *         incorrect argument.
 */
int boolector_fun_sort_check (Btor *btor,
                              int argc,
                              BoolectorNode **arg_nodes,
                              BoolectorNode *n_fun);

/**
 * Get the symbol of a variable.
 * (Note: this function is deprecated,
 * use \ref boolector_get_symbol instead!)
 * \param btor Boolector instance.
 * \param var Array or bit-vector variable.
 * \return Symbol of variable.
 * \see boolector_var
 * \see boolector_array
 */
const char *boolector_get_symbol_of_var (Btor *btor, BoolectorNode *var);

/**
 * Get the symbol of an expression (array or bit-vector variable, uninterpreted
 * function).
 * \param btor Boolector instance.
 * \param var Array or bit-vector variable, or uninterpreted function.
 * \return Symbol of expression.
 * \see boolector_var
 * \see boolector_array
 * \see boolector_uf
 */
const char *boolector_get_symbol (Btor *btor, BoolectorNode *var);
/**
 * Generate an assignment string for bit-vector expression if \ref boolector_sat
 * has returned \ref BOOLECTOR_SAT and model generation has been enabled.
 * The expression can be an arbitrary
 * bit-vector expression which occurs in an assertion or current assumption.
 * The assignment string has to be freed by \ref boolector_free_bv_assignment.
 * \param btor Boolector instance.
 * \param node Bit-vector expression.
 * \return String representing a satisfying assignment to bit-vector variables
 * and a consistent assignment for arbitrary bit-vector expressions.
 * Each character of the string can be '0', '1' or 'x'. The latter
 * represents that the corresponding bit can be assigned arbitrarily.
 * \see boolector_enable_model_gen
 */
const char *boolector_bv_assignment (Btor *btor, BoolectorNode *node);

/**
 * Free an assignment string for bit-vectors.
 * \param btor Boolector instance.
 * \param assignment String which has to be freed.
 * \see boolector_bv_assignment
 */
void boolector_free_bv_assignment (Btor *btor, const char *assignment);

/**
 * Generate a model for an array expression.
 * if \ref boolector_sat
 * has returned \ref BOOLECTOR_SAT and model generation has been enabled.
 * The function creates and stores
 * the array of indices into 'indices' and the array of
 * corresponding values into 'values'. The
 * number size of 'indices' resp. 'values' is stored into 'size'. The array
 * model simply inspects the set of reads rho, which is associated with
 * each array expression. See our publication
 * <a href="http://fmv.jku.at/papers/BrummayerBiere-SMT08.pdf">Lemmas on Demand
 * for the Extensional Theory of Arrays</a> for details. At indices that do not
 * occur in the model, it is assumed that the array stores a globally unique
 * default value, for example 0. The bit-vector assignments to the indices and
 * values have to be freed by \ref boolector_free_bv_assignment. Furthermore,
 * the user has to free the array of indices and the array of values,
 * respectively of size 'size'. \param btor Boolector instance. \param n_array
 * Array operand for which the array model should be built. \param indices
 * Pointer to array of index strings. \param values Pointer to array of value
 * strings. \param size Pointer to size. \see boolector_enable_model_gen
 */
void boolector_array_assignment (Btor *btor,
                                 BoolectorNode *n_array,
                                 char ***indices,
                                 char ***values,
                                 int *size);

/**
 * Free an assignment string for arrays of bit-vectors.
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
 * TODO
 */
void boolector_print_model (Btor *btor, FILE *file);

/*------------------------------------------------------------------------*/

BoolectorSort *boolector_bool_sort (Btor *btor);

/**
 * TODO
 */
BoolectorSort *boolector_bitvec_sort (Btor *btor, int len);

/**
 * TODO
 */
BoolectorSort *boolector_array_sort (Btor *btor,
                                     BoolectorSort *index,
                                     BoolectorSort *elem);

/**
 * TODO
 */
BoolectorSort *boolector_fun_sort (Btor *btor,
                                   BoolectorSort **domain,
                                   int arity,
                                   BoolectorSort *codomain);

#if 0
/**
 * TODO
 */
BoolectorSort *boolector_tuple_sort (Btor * btor, BoolectorSort ** elements,
				    int num_elements);
#endif

/**
 * TODO
 */
void boolector_release_sort (Btor *btor, BoolectorSort *sort);

/*------------------------------------------------------------------------*/

/* Parse input file. Input file format may be either BTOR, SMT-LIB v1, or
 * SMT-LIB v2 and is determined automatically.
 * If the parser encounters an error, an explanation of that error is stored
 * in 'error_msg'. If the input file specifies a (known) status of the input
 * formula (either sat or unsat), that status is stored in 'status'.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 */
int boolector_parse (Btor *btor,
                     FILE *file,
                     const char *file_name,
                     char **error_msg,
                     int *status);

/* Parse input file in BTOR format. See \ref boolector_parse.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 */
int boolector_parse_btor (Btor *btor,
                          FILE *file,
                          const char *file_name,
                          char **error_msg,
                          int *status);

/* Parse input file in SMT-LIB v1 format. See \ref boolector_parse.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 */
int boolector_parse_smt1 (Btor *btor,
                          FILE *file,
                          const char *file_name,
                          char **error_msg,
                          int *status);

/* Parse input file in SMT-LIB v2 format. See \ref boolector_parse.
 * \param btor Boolector instance.
 * \param file Input file.
 * \param file_name Input file name.
 * \param error_msg Error message.
 * \param status Status of the input formula.
 */
int boolector_parse_smt2 (Btor *btor,
                          FILE *file,
                          const char *file_name,
                          char **error_msg,
                          int *status);

/*------------------------------------------------------------------------*/

/**
 * Recursively dump expression to file.
 *<a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR</a> is
 * used as format.
 *
 * \param btor Boolector instance.
 * \param file File to which the expression should be dumped.
 * The file must be have been opened by the user before.
 * \param node The expression which should be dumped.
 */
void boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node);

/**
 * Dump formula to file in BTOR format.
 *
 * \param btor Boolector instance.
 * \param file File to which the formula should be dumped.
 * The file must be have been opened by the user before.
 */
void boolector_dump_btor (Btor *btor, FILE *file);

/**
 * Dump formula to file in BTOR 2.0 format.
 *
 * \param btor Boolector instance.
 * \param file File to which the formula should be dumped.
 * The file must be have been opened by the user before.
 */
void boolector_dump_btor2 (Btor *btor, FILE *file);

/**
 * Recursively dump expression to file.
 *<a href="http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf">SMT-LIB
 * \param btor Boolector instance.
 * \param file File to which the expression should be dumped.
 * The file must be have been opened by the user before.
 * \param node The expression which should be dumped.
 */
void boolector_dump_smt1_node (Btor *btor, FILE *file, BoolectorNode *node);

/**
 * Dump formula to file in SMT-LIB v1 format.
 *<a href="http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf">SMT-LIB
 * \param btor Boolector instance.
 * \param btor Boolector instance
 * \param file Output file.
 */
void boolector_dump_smt1 (Btor *btor, FILE *file);

/**
 * Recursively dump expression to file.
 *<a
 *href="http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf">SMT-LIB
 *2.0</a> is used as format. \param btor Boolector instance. \param file File to
 *which the expression should be dumped. The file must be have been opened by
 *the user before. \param node The expression which should be dumped.
 */
void boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node);

/**
 * Dumps formula to file in SMT-LIB v2 format.
 *<a
 *href="http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf">SMT-LIB
 *2.0</a> is used as format. \param btor Boolector instance. \param btor
 *Boolector instance \param file Output file.
 */
void boolector_dump_smt2 (Btor *btor, FILE *file);

/* DEPRECATED API */

/**
 * Enable model generation.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt_model_gen instead!)
 * \param btor Boolector instance.
 * \see boolector_set_model_gen
 */
BTOR_DEPRECATED (void boolector_enable_model_gen (Btor *btor));

/**
 * Enable model generation for all reads.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt_model_gen_all_reads instead!)
 * \param btor Boolector instance.
 * \see boolector_set_opt_model_gen_all_reads
 */
BTOR_DEPRECATED (void boolector_generate_model_for_all_reads (Btor *btor));

/**
 * Enable incremental usage.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt instead!
 * \param btor Boolector instance.
 * \see boolector_set_opt
 */
BTOR_DEPRECATED (void boolector_enable_inc_usage (Btor *btor));

/**
 * Set the rewrite level of the rewriting engine.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt_rewrite_level instead.)
 * \param btor Boolector instance.
 * \param val Rewrite level ranging from
 * 0 (no rewriting) to 3 (full rewriting).
 * \see boolector_set_opt_rewrite_level
 */
BTOR_DEPRECATED (void boolector_set_rewrite_level (Btor *btor, int val));

/**
 * Set level of verbosity.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt_verbosity instead.)
 * \param btor Boolector instance.
 * \param val Verbosity level.
 * \see boolector_set_opt_verbosity
 */
BTOR_DEPRECATED (void boolector_set_verbosity (Btor *btor, int val));

/**
 * Set log level.
 * (Note: this function is deprecated,
 * use \ref boolector_set_opt_loglevel instead.)
 * \param btor Boolector instance.
 * \param val Log level.
 * \see boolector_set_opt_loglevel
 */
BTOR_DEPRECATED (void boolector_set_loglevel (Btor *btor, int val));

#endif

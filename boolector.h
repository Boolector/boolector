/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012 Mathias Preiner.
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

typedef struct BtorNode BtorNode;
typedef struct BtorSort BtorSort;
typedef struct Btor Btor;

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
 * by \ref boolector_enable_inc_usage. Assumptions can be added by
 * \ref boolector_assume.
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
 * Preprocessor constant representing status 'satisfiable'.
 * \see boolector_sat
 */
#define BOOLECTOR_SAT 10
/**
 * Preprocessor constant representing status 'unsatisfiable'.
 * \see boolector_sat
 */
#define BOOLECTOR_UNSAT 20

/*------------------------------------------------------------------------*/

/**
 * Creates new instance of Boolector.
 * \return New Boolector instance.
 */
Btor *boolector_new (void);

/**
 * Clones an instance of Boolector.
 * \param btor original Boolector instance.
 * \return New Boolector instance.
 */
Btor *boolector_clone (Btor *btor);

/**
 * Enables model generation. If you want Boolector to produce
 * a model in the satisfiable case, call this function
 * after \ref boolector_new.
 * \param btor Boolector instance.
 * \see boolector_sat
 */
void boolector_enable_model_gen (Btor *btor);

/**
 * By default Boolector only generates assignments for reads
 * in the cone of assertions.  If you require models for all
 * 'reads' you can use this function to force Boolector to
 * synthesize all reads during the next model generation.
 */
void boolector_generate_model_for_all_reads (Btor *btor);

/**
 * Enables incremental usage of Boolector. This allows to add assumptions
 * by \ref boolector_assume and to call \ref boolector_sat multiple times.
 * Note that this mode turns off some optimization techniques that cannot
 * be applied anymore.
 * \param btor Boolector instance.
 */
void boolector_enable_inc_usage (Btor *btor);

/**
 * Sets the SAT solver to use.
 * Currently, we support 'Lingeling', 'PicoSAT', and 'MiniSAT' as string
 * value of \para solver ignoring the case of characters.  This is however
 * only possible if at compile time the corresponding solvers were enabled.
 * The return value is non-zero if setting the SAT solver call was
 * successful.  Call this function after \ref boolector_new.
 */
int boolector_set_sat_solver (Btor *btor, const char *solver);

/**
 * Sets the rewrite level of the rewriting engine.
 * Boolector uses rewrite level 3 per default. Call this function
 * before creating any expressions.
 * \param btor Boolector instance.
 * \param rewrite_level Rewrite level ranging from
 * 0 (no rewriting) to 3 (full rewriting).
 */
void boolector_set_rewrite_level (Btor *btor, int rewrite_level);

/**
 * Returns the number of external references to the boolector library.
 * Internally, Boolector manages an expression DAG with reference counting. Use
 * \ref boolector_release to properly release an expression. Before
 * you finally call \ref boolector_delete, \ref boolector_get_refs should
 * return 0.
 * \param btor Boolector instance.
 * \return Number of external references owned by the user.
 */
int boolector_get_refs (Btor *btor);

/**
 * Deletes boolector instance and frees its resources.
 * \param btor Boolector instance.
 * \remarks Expressions that have not been release properly will not be
 * deleted from memory. Use \ref boolector_get_refs to debug reference
 * counting.
 */
void boolector_delete (Btor *btor);

/*------------------------------------------------------------------------*/

/**
 * Bit-vector constant representing the bit-vector 'bits'.
 * \param btor Boolector instance.
 * \param bits Non-empty and terminated string consisting of zeroes and/or ones.
 * representing the bit-vector constant specified by 'bits'.
 * \return Bit-vector constant with bit-width strlen('bits').
 */
BtorNode *boolector_const (Btor *btor, const char *bits);

/**
 * Bit-vector constant zero.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant zero with bit-width 'width'.
 */
BtorNode *boolector_zero (Btor *btor, int width);

/**
 * Bit-vector constant zero with bit-width one.
 * \param btor Boolector instance.
 * \return Bit-vector constant zero with bit-width one.
 */
BtorNode *boolector_false (Btor *btor);

/**
 * Binary constant representing 'width' ones.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant -1 with bit-width 'width'.
 */
BtorNode *boolector_ones (Btor *btor, int width);

/**
 * Bit-vector constant one with bit-width one.
 * \param btor Boolector instance.
 * \return Bit-vector constant one with bit-width one.
 */
BtorNode *boolector_true (Btor *btor);

/**
 * Bit-vector constant one.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant one with bit-width 'width'.
 */
BtorNode *boolector_one (Btor *btor, int width);

/**
 * Binary constant representing the unsigned integer 'u' with bit-width 'width'.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * \param btor Boolector instance.
 * \param u Unsigned integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant with bit-width 'width'.
 */
BtorNode *boolector_unsigned_int (Btor *btor, unsigned u, int width);

/**
 * Binary constant representing the signed integer 'i' with bit-width 'width'.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * \param btor Boolector instance.
 * \param i Signed integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant with bit-width 'width'.
 */
BtorNode *boolector_int (Btor *btor, int i, int width);

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
BtorNode *boolector_var (Btor *btor, int width, const char *symbol);

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
BtorNode *boolector_array (Btor *btor,
                           int elem_width,
                           int index_width,
                           const char *symbol);

/**
 * One's complement.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with the same bit-width as 'exp'.
 */
BtorNode *boolector_not (Btor *btor, BtorNode *exp);

/**
 * Two's complement.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with the same bit-width as 'exp'.
 */
BtorNode *boolector_neg (Btor *btor, BtorNode *exp);

/**
 * Or reduction. All bits are combined by or.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_redor (Btor *btor, BtorNode *exp);

/**
 * Xor reduction. All bits are combined by xor.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_redxor (Btor *btor, BtorNode *exp);

/**
 * And reduction. All bits are combined by and.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_redand (Btor *btor, BtorNode *exp);

/**
 * Bit-vector slice of 'exp' from index 'upper' to index 'lower'.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \param upper Upper index which must be greater than or equal to zero, and
 * less than the bit-width of 'exp'.
 * \param lower Lower index which must be greater than or equal to zero, and
 * less than or equal to 'upper'.
 * \return Bit-vector with bit-width 'upper' - 'lower' + 1.
 */
BtorNode *boolector_slice (Btor *btor, BtorNode *exp, int upper, int lower);

/**
 * Unsigned extension. The operand 'exp' is padded with 'width' zeroes.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \param width Number of zeroes to pad.
 * \return Bit-vector with bit-width: bit-width of 'exp' + 'width'.
 */
BtorNode *boolector_uext (Btor *btor, BtorNode *exp, int width);

/**
 * Signed extension. The operand 'exp' is padded with 'width' bits. If zeroes
 * or ones are padded depends on the most significant bit of 'exp'.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \param width Number of bits to pad.
 * \return Bit-vector with bit-width: bit-width of 'exp' + 'width'.
 */
BtorNode *boolector_sext (Btor *btor, BtorNode *exp, int width);

/**
 * Implication. The parameters * 'e0' and 'e1' must have bit-width one.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_implies (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Equivalence. The parameters 'e0' and 'e1' must have bit-width one.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_iff (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Xor. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_xor (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Xnor. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_xnor (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * And. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_and (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Nand. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_nand (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Or. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_or (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Nor. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_nor (Btor *btor, BtorNode *e0, BtorNode *e1);

/** Equality. Either both operands are bit-vectors with the same
 * bit-with or both operands are arrays of the same type.
 * \param btor Boolector instance.
 * \param e0 First operand.
 * \param e1 Second operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_eq (Btor *btor, BtorNode *e0, BtorNode *e1);

/** Inequality. Either both operands are bit-vectors with the same
 * bit-with or both operands are arrays of the same type.
 * \param btor Boolector instance.
 * \param e0 First operand.
 * \param e1 Second operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_ne (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Addition.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_add (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned addition overflow detection. The result represents if the addition
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_uaddo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed addition overflow detection. The result represents if the addition
 * overflows when both operands are interpreted as signed.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_saddo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Multiplication.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_mul (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned multiplication overflow detection.
 * The result represents if the multiplication
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_umulo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed multiplication overflow detection.
 * The result represents if the multiplication
 * overflows when both operands are interpreted as signed.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_smulo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned less than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_ult (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed less than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_slt (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned less than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_ulte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed less than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_slte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned greater than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_ugt (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed greater than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_sgt (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned greater than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_ugte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed greater than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_sgte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Shift left.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorNode *boolector_sll (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Shift right logical. Zeroes are shifted in.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorNode *boolector_srl (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Shift right arithmetic. Whether zeroes or ones are shifted in depends
 * on the most significant bit of 'e0'.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorNode *boolector_sra (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Rotate left.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorNode *boolector_rol (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Rotate right.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorNode *boolector_ror (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Subtraction.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorNode *boolector_sub (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned subtraction overflow detection.
 * The result represents if the subtraction
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_usubo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed subtraction overflow detection.
 * The result represents if the subtraction
 * overflows when both operands are interpreted as signed.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorNode *boolector_ssubo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned division.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * If 'e1' is zero, then the result is -1.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks The behavior that division by zero returns -1 does not exactly
 * comply with the SMT-LIB standard 1.2 where division by zero is
 * handled as uninterpreted function. Our semantics are motivated by
 * real circuits where division by zero cannot be uninterpreted and of course
 * returns a result.
 */
BtorNode *boolector_udiv (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed division.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks Signed division is expressed by unsigned division and
 * the sign bits of 'e0' and 'e1'. If the sign bit of 'e0' resp. 'e1' is
 * one then two's complement is applied to normalize them.
 * Then, unsigned division is performed. Finally, two's complement
 * is applied to the result if the sign bits of 'e0' and 'e1' are different.
 * Therefore, the behavior upon dividing zero depends on \ref boolector_udiv.
 */
BtorNode *boolector_sdiv (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed division overflow detection.
 * The result represents if the division
 * overflows when both operands are interpreted as signed.
 * This happens when 'e0' represents INT_MIN and 'e1' represents -1.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 * \remarks Unsigned division cannot overflow.
 */
BtorNode *boolector_sdivo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Unsigned remainder.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * If 'e1' is zero, then the result is 'e0'.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks As in \ref boolector_udiv the behavior if 'e1' is zero, does
 * not exactly comply with the SMT-LIB standard 1.2 where the result
 * is handled as uninterpreted. Our semantics are motivated by
 * real circuits where results cannot be uninterpreted.
 */
BtorNode *boolector_urem (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed remainder.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * If 'e1' is zero, then the result is 'e0'.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks Analogously to \ref boolector_sdiv signed remainder is expressed by
 * unsigned remainder and the sign bits of 'e0' and 'e1'.
 * Therefore, if 'e1' is zero, the result depends on \ref boolector_urem.
 */
BtorNode *boolector_srem (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Signed remainder where sign follows divisor.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks The behavior, if 'e1' is zero depends on \ref boolector_urem.
 */
BtorNode *boolector_smod (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Concatenation.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width: bit-width of 'e0' + bit-width of 'e1'.
 */
BtorNode *boolector_concat (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Array read on array 'e_array' at position 'e_index'.
 * \param btor Boolector instance.
 * \param e_array Array operand.
 * \param e_index Bit-vector index. The bit-width of 'e_index' must have
 * the same bit-width as the indices of 'e_array'.
 * return Bit-vector with the same bit-width as the elements of 'e_array'.
 */
BtorNode *boolector_read (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/**
 * Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * The array is updated at one position. All other elements remain the same.
 * \param btor Boolector instance.
 * \param e_array Array operand.
 * \param e_index Bit-vector index. The bit-width of 'e_index' must have
 * the same bit-width as the indices of 'e_array'.
 * \param e_value Bit-vector value. The bit-width of 'e_value' must have
 * the same bit-width as the elements of 'e_array'.
 * \return Array where the value at one specific index has been updated.
 */
BtorNode *boolector_write (Btor *btor,
                           BtorNode *e_array,
                           BtorNode *e_index,
                           BtorNode *e_value);

/**
 * If-then-else. If the condition 'e_cond' is one, then
 * 'e_if' is returned, otherwise 'e_else'.
 * Either 'e_if' and 'e_else' must be both arrays, or they must be both
 * bit-vectors.
 * \param btor Boolector instance.
 * \param e_cond Bit-vector condition with bit-width one.
 * \param e_if Operand returned in the if case.
 * \param e_else Operand returned in the else case.
 * \return Result with the same type as 'e_if' and 'e_else'.
 */
BtorNode *boolector_cond (Btor *btor,
                          BtorNode *e_cond,
                          BtorNode *e_if,
                          BtorNode *e_else);

// TODO: remove? it is redudant due to boolector_fun  (MA)
/**
 * Lambda expression.
 * \param btor Boolector instance.
 * \param param Parameter bound by lambda expression.
 * \param exp Lambda expression body.
 */
BtorNode *boolector_lambda (Btor *btor, BtorNode *param, BtorNode *exp);

/**
 * Parameter.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \param symbol Name of parameter.
 */
BtorNode *boolector_param (Btor *btor, int width, const char *symbol);

/**
 * Function.
 * \param btor Boolector instance.
 * \param paramc Number of parameters.
 * \param params Parameters of function.
 * \param exp Function body.
 * \result Function parameter.
 */
BtorNode *boolector_fun (Btor *btor,
                         int paramc,
                         BtorNode **params,
                         BtorNode *exp);

/**
 * Creates a function application expression.
 * \param btor Boolector instance.
 * \param argc Number of arguments to be applied.
 * \param args Arguments to be applied.
 * \param fun Function expression.
 * \result Function application expression.
 */
BtorNode *boolector_apply (Btor *btor,
                           int argc,
                           BtorNode **args,
                           BtorNode *fun);

/**
 * Increments bit-vector by one.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \result Bit-vector with the same bit-width as 'exp'.
 */
BtorNode *boolector_inc (Btor *btor, BtorNode *exp);

/**
 * Decrements bit-vector by one.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \result Bit-vector with the same bit-width as 'exp'.
 */
BtorNode *boolector_dec (Btor *btor, BtorNode *exp);

/**
 * Determines if expression is an array. If not, expression is a bit-vector.
 * \param btor Boolector instance.
 * \param exp Operand.
 * \result True if expression is an array, and false otherwise.
 */
int boolector_is_array (Btor *btor, BtorNode *exp);

/**
 * Determines if expression is a function.
 * \param btor Boolector instance.
 * \param exp Operand.
 * \result True if epxression is a function, and false otherwise.
 */
int boolector_is_fun (Btor *btor, BtorNode *exp);

/**
 * Gets the arity of function 'exp'.
 * \param btor Boolector instance.
 * \param exp Function.
 * \return arity of 'exp'.
 */
int boolector_get_fun_arity (Btor *btor, BtorNode *exp);

/**
 * Gets the bit-width of an expression. If the expression
 * is an array, it returns the bit-width of the array elements.
 * \param btor Boolector instance.
 * \param exp Operand.
 * \return bit-width of 'exp'.
 */
int boolector_get_width (Btor *btor, BtorNode *exp);

/**
 * Gets the bit-width of indices of 'e_array'.
 * \param btor Boolector instance.
 * \param e_array Array operand.
 * \return bit-width of indices of 'e_array'.
 */
int boolector_get_index_width (Btor *btor, BtorNode *e_array);

/**
 * Checks if sorts of given arguments matches the function signature.
 * \param btor Boolector instance.
 * \param argc Number of arguments to be checked.
 * \param args Arguments to be checked.
 * \param fun Function expression.
 * \return -1 if all sorts are correct, otherwise returns the position of the
 *         incorrect argument.
 */
int boolector_fun_sort_check (Btor *btor,
                              int argc,
                              BtorNode **args,
                              BtorNode *fun);

/**
 * Gets the symbol of a variable.
 * \param btor Boolector instance.
 * \param var Array or bit-vector variable.
 * \return Symbol of variable.
 * \see boolector_var
 * \see boolector_array
 */
const char *boolector_get_symbol_of_var (Btor *btor, BtorNode *var);

/**
 * Copies expression (increments reference counter).
 * \param btor Boolector instance.
 * \param exp Operand.
 * \return The expression 'exp'.
 */
BtorNode *boolector_copy (Btor *btor, BtorNode *exp);

/**
 * Releases expression (decrements reference counter).
 * \param btor Boolector instance.
 * \param exp Operand.
 */
void boolector_release (Btor *btor, BtorNode *exp);

/**
 * Recursively dumps expression to file.
 *<a href="http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf">BTOR</a> is
 * used as format.
 *
 * \param btor Boolector instance.
 * \param file File to which the expression should be dumped.
 * The file must be have been opened by the user before.
 * \param exp The expression which should be dumped.
 */
void boolector_dump_btor (Btor *btor, FILE *file, BtorNode *exp);

/**
 * Recursively dumps expression to file.
 *<a
 *href="http://goedel.cs.uiowa.edu/smtlib/papers/format-v1.2-r06.08.30.pdf">SMT-LIB
 *1.2</a> is used as format. \param btor Boolector instance. \param file File to
 *which the expression should be dumped. The file must be have been opened by
 *the user before. \param exp The expression which should be dumped.
 */
void boolector_dump_smt (Btor *btor, FILE *file, BtorNode *exp);

/**
 * Recursively dumps expression to file.
 *<a
 *href="http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf">SMT-LIB
 *2.0</a> is used as format. \param btor Boolector instance. \param file File to
 *which the expression should be dumped. The file must be have been opened by
 *the user before. \param exp The expression which should be dumped.
 */
void boolector_dump_smt2 (Btor *btor, FILE *file, BtorNode *exp);

/**
 * Adds constraint. Use this function to assert 'exp'.
 * Added constraints can not be deleted anymore. After 'exp' has
 * been asserted, it can be safely released by \ref boolector_release.
 * \param btor Boolector instance.
 * \param exp Bit-vector expression with bit-width one.
 */
void boolector_assert (Btor *btor, BtorNode *exp);

/**
 * Adds assumption. Use this function to assume 'exp'.
 * You must enable Boolector's incremental usage by calling
 * \ref boolector_enable_inc_usage before.
 * In contrast to \ref boolector_assert the assumptions are
 * discarded after each call to \ref boolector_sat. Assumptions
 * and assertions are logically combined by boolean 'and'.
 * This is the same way of using assumptions as in MiniSAT.
 * \param btor Boolector instance.
 * \param exp Bit-vector expression with bit-width one.
 */
void boolector_assume (Btor *btor, BtorNode *exp);

/**
 * Solves SAT instance represented by constraints and assumptions added
 * by \ref boolector_assert and \ref boolector_assume. Note that
 * assertions and assumptions are combined by boolean 'and'.
 * If you want to call this function multiple times then you must enable
 * Boolector's incremental usage mode by calling
 * \ref boolector_enable_inc_usage before. Otherwise, this function can only
 * be called once.
 * \param btor Boolector instance.
 * \return It returns \ref BOOLECTOR_SAT if the instance is satisfiable and
 * \ref BOOLECTOR_UNSAT if the instance is unsatisfiable.
 * \see boolector_bv_assignment
 * \see boolector_array_assignment
 **/
int boolector_sat (Btor *btor);

/**
 * Builds assignment string for bit-vector expression if \ref boolector_sat
 * has returned \ref BOOLECTOR_SAT and model generation has been enabled.
 * The expression can be an arbitrary
 * bit-vector expression which occurs in an assertion or current assumption.
 * The assignment string has to be freed by \ref boolector_free_bv_assignment.
 * \param btor Boolector instance.
 * \param exp Bit-vector expression.
 * \return String representing a satisfying assignment to bit-vector variables
 * and a consistent assignment for arbitrary bit-vector expressions.
 * Each character of the string can be '0', '1' or 'x'. The latter
 * represents that the corresponding bit can be assigned arbitrarily.
 * \see boolector_enable_model_gen
 */
char *boolector_bv_assignment (Btor *btor, BtorNode *exp);

/**
 * Frees an assignment string for bit-vectors.
 * \param btor Boolector instance.
 * \param assignment String which has to be freed.
 * \see boolector_bv_assignment
 */
void boolector_free_bv_assignment (Btor *btor, char *assignment);

/**
 * Builds a model for an array expression.
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
 * respectively of size 'size'. \param btor Boolector instance. \param e_array
 * Array operand for which the array model should be built. \param indices
 * Pointer to array of index strings. \param values Pointer to array of value
 * strings. \param size Pointer to size. \see boolector_enable_model_gen
 */
void boolector_array_assignment (
    Btor *btor, BtorNode *e_array, char ***indices, char ***values, int *size);

/**
 * Frees an assignment string for arrays of bit-vectors.
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

#endif

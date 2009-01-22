#ifndef BOOLECTOR_H_INCLUDED
#define BOOLECTOR_H_INCLUDED

#include "btorexp.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PUBLIC INTERFACE                                                       */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Declarations                                                           */
/*------------------------------------------------------------------------*/

/**
 * Preprocessor constant representing status 'satisfiable'.
 * \see boolector_sat
 */
#define BTOR_SAT 10
/**
 * Preprocessor constant representing status 'unsatisfiable'.
 * \see boolector_sat
 */
#define BTOR_UNSAT 20
/**
 * Preprocessor constant representing status 'unknown'.
 * \see boolector_sat
 */
#define BTOR_UNKNOWN 0

/*------------------------------------------------------------------------*/
/* Boolector                                                              */
/*------------------------------------------------------------------------*/

/**
 * Creates new instance of Boolector.
 * \return New Boolector instance.
 * \remarks At the moment Boolector does not support multiple instances.
 * Boolector uses PicoSAT as backend which does not support multiple instances.
 * However, we plan to support multiple instances in the future.
 */
Btor *boolector_new (void);

/**
 * Enables model generation. If you want Boolector to produce
 * a model in the satisfiable case, call this function after \ref boolector_new.
 * \param btor Boolector instance.
 */
void boolector_enable_model_gen (Btor *btor);

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
 * Deletes boolector instance and frees its resources.
 * \param btor Boolector instance.
 */
void boolector_delete (Btor *btor);

/*------------------------------------------------------------------------*/
/* BtorExpression                                                         */
/*------------------------------------------------------------------------*/

/**
 * Bit-vector constant representing the bit-vector 'bits'.
 * \param btor Boolector instance.
 * \param bits Non-empty Nul-terminated string consisting of zeroes and/or ones.
 * representing the bit-vector constant specified by 'bits'.
 * \return Bit-vector constant with bit-width strlen('bits').
 */
BtorExp *boolector_const (Btor *btor, const char *bits);

/**
 * Bit-vector constant zero.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant zero with bit-width 'width'.
 */
BtorExp *boolector_zero (Btor *btor, int width);

/**
 * Bit-vector constant zero with bit-width one.
 * \param btor Boolector instance.
 * \return Bit-vector constant zero with bit-width one.
 */
BtorExp *boolector_false (Btor *btor);

/**
 * Binary constant representing 'width' ones.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant -1 with bit-width 'width'.
 */
BtorExp *boolector_ones (Btor *btor, int width);

/**
 * Bit-vector constant one with bit-width one.
 * \param btor Boolector instance.
 * \return Bit-vector constant one with bit-width one.
 */
BtorExp *boolector_true (Btor *btor);

/**
 * Bit-vector constant one.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant one with bit-width 'width'.
 */
BtorExp *boolector_one (Btor *btor, int width);

/**
 * Binary constant representing the unsigned integer 'u' with bit-width 'width'.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * \param btor Boolector instance.
 * \param u Unsigned integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant with bit-width 'width'.
 */
BtorExp *boolector_unsigned_int (Btor *btor, unsigned u, int width);

/**
 * Binary constant representing the signed integer 'i' with bit-width 'width'.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * \param btor Boolector instance.
 * \param i Signed integer value.
 * \param width Number of bits which must be greater than zero.
 * \return Bit-vector constant with bit-width 'width'.
 */
BtorExp *boolector_int (Btor *btor, int i, int width);

/**
 * Bit-vector variable with bit-width 'width'.
 * \param btor Boolector instance.
 * \param width Number of bits which must be greater than zero.
 * \param symbol String symbol which can be used to identify the variable in
 * a model.
 * \return Bit-vector variable with bit-width 'width' and symbol 'symbol'.
 */
BtorExp *boolector_var (Btor *btor, int width, const char *symbol);

/**
 * One-dimensional bit-vector array of size 2 ^ 'index_width' with elements of
 * bit-width 'elem_width'.
 * \param btor Boolector instance.
 * \param elem_width Number of bits of array elements. The parameter must be
 * greater than zero.
 * \param index_width Number of bits of array addresses. The parameter must be
 * greater than zero.
 * \param symbol String symbol which can be used to identify the array in
 * a model.
 * \return Bit-vector array of size 2 ^ 'index_width' with elements of
 * bit-width 'elem_width', and symbol 'symbol'.
 */
BtorExp *boolector_array (Btor *btor,
                          int elem_width,
                          int index_width,
                          const char *symbol);

/**
 * One's complement.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with the same bit-width as 'exp'.
 */
BtorExp *boolector_not (Btor *btor, BtorExp *exp);

/**
 * Two's complement.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with the same bit-width as 'exp'.
 */
BtorExp *boolector_neg (Btor *btor, BtorExp *exp);

/**
 * Or reduction. All bits are combined by or.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_redor (Btor *btor, BtorExp *exp);
/**
 * Xor reduction. All bits are combined by xor.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_redxor (Btor *btor, BtorExp *exp);

/**
 * And reduction. All bits are combined by and.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_redand (Btor *btor, BtorExp *exp);

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
BtorExp *boolector_slice (Btor *btor, BtorExp *exp, int upper, int lower);

/**
 * Unsigned extension. The operand 'exp' is padded with 'width' zeroes.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \param width Number of zeroes to pad.
 * \return Bit-vector with bit-width: bit-width of 'exp' + 'width'.
 */
BtorExp *boolector_uext (Btor *btor, BtorExp *exp, int width);

/**
 * Signed extension. The operand 'exp' is padded with 'width' bits. If zeroes
 * or ones are padded depends on the most significant bit of 'exp'.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \param width Number of bits to pad.
 * \return Bit-vector with bit-width: bit-width of 'exp' + 'width'.
 */
BtorExp *boolector_sext (Btor *btor, BtorExp *exp, int width);

/**
 * Implication. The parameters * 'e0' and 'e1' must have bit-width one.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_implies (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Equivalence. The parameters 'e0' and 'e1' must have bit-width one.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_iff (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Xor. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_xor (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Xnor. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_xnor (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * And. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_and (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Nand. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_nand (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Or. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_or (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Nor. The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_nor (Btor *btor, BtorExp *e0, BtorExp *e1);

/** Equality. Either both operands are bit-vectors with the same
 * bit-with or both operands are arrays of the same type.
 * \param btor Boolector instance.
 * \param e0 First operand.
 * \param e1 Second operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_eq (Btor *btor, BtorExp *e0, BtorExp *e1);

/** Inequality. Either both operands are bit-vectors with the same
 * bit-with or both operands are arrays of the same type.
 * \param btor Boolector instance.
 * \param e0 First operand.
 * \param e1 Second operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_ne (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Addition.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_add (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Unsigned addition overflow detection. The result represents if the addition
 * overflows when both operands are interpreted as unsigned.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_uaddo (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Signed addition overflow detection. The result represents if the addition
 * overflows when both operands are interpreted as signed.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_saddo (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Multiplication.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_mul (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_umulo (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_smulo (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Unsigned less than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_ult (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Signed less than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_slt (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Unsigned less than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_ulte (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Signed less than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_slte (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Unsigned greater than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_ugt (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Signed greater than.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_sgt (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Unsigned greater than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_ugte (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Signed greater than or equal.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width one.
 */
BtorExp *boolector_sgte (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift left.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorExp *boolector_sll (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift right logical. Zeroes are shifted in.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorExp *boolector_srl (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift right arithmetic. Whether zeroes or ones are shifted in depends
 * on the most significant bit of 'e0'.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorExp *boolector_sra (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Rotate left.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorExp *boolector_rol (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Rotate right.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand where the bit-width is a power of two
 * and greater than 1.
 * \param e1 Second bit-vector operand with bit-width log2 of
 * the bit-width of 'e0'.
 * \return Bit-vector with the same bit-width as 'e0'.
 */
BtorExp *boolector_ror (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Subtraction.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 */
BtorExp *boolector_sub (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_usubo (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_ssubo (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_udiv (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_sdiv (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_sdivo (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_urem (Btor *btor, BtorExp *e0, BtorExp *e1);

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
BtorExp *boolector_srem (Btor *btor, BtorExp *e0, BtorExp *e1);

/**
 * Signed remainder where sign follows divisor.
 * The parameters 'e0' and 'e1' must have the same bit-width.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with the same bit-width as the operands.
 * \remarks The behavior, if 'e1' is zero depends on \ref boolector_urem.
 */
BtorExp *boolector_smod (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Concatenation.
 * \param btor Boolector instance.
 * \param e0 First bit-vector operand.
 * \param e1 Second bit-vector operand.
 * \return Bit-vector with bit-width: bit-width of 'e0' + bit-width of 'e1'.
 */
BtorExp *boolector_concat (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Array read on array 'e_array' at position 'e_index'.
 * \param btor Boolector instance.
 * \param e_array Array operand.
 * \param e_index Bit-vector index. The bit-width of 'e_index' must have
 * the same bit-width as the indices of 'e_array'.
 * return Bit-vector with the same bit-width as the elements of 'e_array'.
 */
BtorExp *boolector_read (Btor *btor, BtorExp *e_array, BtorExp *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * The array is updated at one position. All other elements remain the same.
 * \param btor Boolector instance.
 * \param e_array Array operand.
 * \param e_index Bit-vector index. The bit-width of 'e_index' must have
 * the same bit-width as the indices of 'e_array'.
 * \param e_value Bit-vector value. The bit-width of 'e_value' must have
 * the same bit-width as the elements of 'e_array'.
 * \return Array where the value at one specific index has been updated.
 */
BtorExp *boolector_write (Btor *btor,
                          BtorExp *e_array,
                          BtorExp *e_index,
                          BtorExp *e_value);

/* If-then-else. If the condition 'e_cond' is one, then
 * 'e_if' is returned, otherwise 'e_else'.
 * Either 'e_if' and 'e_else' must be both arrays, or they must be both
 * bit-vectors.
 * \param btor Boolector instance.
 * \param e_cond Bit-vector condition with bit-width one.
 * \param e_if Operand returned in the if case.
 * \param e_else Operand returned in the else case.
 * \return Result with the same type as 'e_if' and 'e_else'.
 */
BtorExp *boolector_cond (Btor *btor,
                         BtorExp *e_cond,
                         BtorExp *e_if,
                         BtorExp *e_else);

/**
 * Increments bit-vector by one.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \result Bit-vector with the same bit-width as 'exp'.
 */
BtorExp *boolector_inc (Btor *btor, BtorExp *exp);

/**
 * Decrements bit-vector by one.
 * \param btor Boolector instance.
 * \param exp Bit-vector operand.
 * \result Bit-vector with the same bit-width as 'exp'.
 */
BtorExp *boolector_dec (Btor *btor, BtorExp *exp);

/**
 * Determines if expression is an array. If not, expression is a bit-vector.
 * \param btor Boolector instance.
 * \param exp Operand.
 * \result True if expression is an array, and false otherwise.
 */
int boolector_is_array (Btor *btor, BtorExp *exp);

/**
 * Gets the bit-width of an expression. If the expression
 * is an array, it returns the bit-width of the array elements.
 * \param btor Boolector instance.
 * \param exp Operand.
 * \return bit-width of 'exp'.
 */
int boolector_get_width (Btor *btor, BtorExp *exp);

/**
 * Gets the bit-width of indices of 'e_array'.
 * \param btor Boolector instance.
 * \param e_array Array operand.
 * \return bit-width of indices of 'e_array'.
 */
int boolector_get_index_width (Btor *btor, BtorExp *e_array);

/**
 * Gets the symbol of a variable.
 * \param btor Boolector instance.
 * \param var Array or bit-vector variable.
 * \return Symbol of variable.
 */
const char *boolector_get_symbol_of_var (Btor *btor, BtorExp *var);

/**
 * Copies expression (increments reference counter).
 * \param btor Boolector instance.
 * \param exp Operand.
 * \return The expression 'exp'.
 */
BtorExp *boolector_copy (Btor *btor, BtorExp *exp);

/**
 * Releases expression (decrements reference counter).
 * \param btor Boolector instance.
 * \param exp Operand.
 */
void boolector_release (Btor *btor, BtorExp *exp);

/**
 * Recursively dumps expression to file. BTOR 1.0 is used as format.
 * \param btor Boolector instance.
 * \param file File to which the expression should be dumped.
 * The file must be have been opened by the user before.
 * \param root The expression which should be dumped.
 */
void boolector_dump_btor (Btor *btor, FILE *file, BtorExp *root);

/**
 * Recursively dumps expression to file. SMT-LIB 1.2 is used as format.
 * \param btor Boolector instance.
 * \param file File to which the expression should be dumped.
 * The file must be have been opened by the user before.
 * \param root The expression which should be dumped.
 */
void boolector_dump_smt (Btor *btor, FILE *file, BtorExp *root);

/**
 * Adds constraint. Use this function to assert 'exp'.
 * Added constraints can not be deleted anymore. After 'exp' has
 * been asserted, it can be safely released by \ref boolector_release.
 * \param btor Boolector instance.
 * \param exp Bit-vector expression with bit-width one.
 */
void boolector_assert (Btor *btor, BtorExp *exp);

/**
 * Adds assumption. Use this function to assume 'exp'.
 * In contrast to \ref boolector_assert the assumptions are
 * discarded after each call to \ref boolector_sat. Assumptions
 * and constraints are logically combined by boolean and.
 * \param btor Boolector instance.
 * \param exp Bit-vector expression with bit-width one.
 */
void boolector_assume (Btor *btor, BtorExp *exp);

/**
 * Solves SAT instance represented by constraints and assumptions added
 * by \ref boolector_assert and \ref boolector_assume. Note that
 * assertions and assumptions are combined by boolean and.
 * \param btor Boolector instance.
 * \param refinement_limit Sets the maximum number of iterative refinements
 * which must be greater than or equal to zero. Use INT_MAX as default.
 * \return It returns \ref BTOR_SAT if the instance is satisfiable and
 * \ref BTOR_UNSAT if the instance is unsatisfiable. If Boolector cannot decide
 * the instance within the refinement limit, it returns \ref BTOR_UNKNOWN.
 **/
int boolector_sat (Btor *btor, int refinement_limit);

/**
 * Builds assignment string for bit-vector expression if \ref boolector_sat
 * has returned \ref BTOR_SAT and model generation is enabled.
 * The expression can be an arbitrary
 * bit-vector expression which occurs in an assertion or current assumption.
 * The assignment string has to be freed by \ref boolector_free_bv_assignment.
 * \param btor Boolector instance.
 * \param exp Bit-vector expression.
 * \return String representing a satisfying assignment to bit-vector variables
 * and a consistent assignment for arbitrary bit-vector expressions.
 * Each character of the string can be '0', '1' or 'x'. The latter
 * represents that the corresponding bit can be assigned arbitrarily.
 */
char *boolector_bv_assignment (Btor *btor, BtorExp *exp);

/**
 * Builds a model for an array expression. The function creates and stores
 * the array of indices into 'indices' and the array of
 * corresponding values into 'values'. The
 * number size of 'indices' resp. 'values' is stored into 'size'. The array
 * model simply inspects the set of reads rho, which is associated with
 * each array expression. See our publication
 * "lemmas on demand for the extensional arrays" for details. At indices that
 * do not occur in the model, the array can have a unique default value, for
 * example 0 with the respective bit-width. The bit-vector assignments
 * to the indices and values have to be freed by
 * \ref boolector_free_bv_assignment. Furthermore, the user has to
 * free the array of indices and the array of values, respectively
 * of size 'size'.
 * \param btor Boolector instance.
 * \param e_array Array operand for which the array model should be built.
 * \param indices Pointer to array of index strings.
 * \param values Pointer to array of value strings.
 * \param size Pointer to size.
 */
void boolector_array_assignment (
    Btor *btor, BtorExp *e_array, char ***indices, char ***values, int *size);
/**
 * Frees an assignment string for bit-vectors.
 * \param btor Boolector instance.
 * \param assignment String which has to be freed.
 */
void boolector_free_bv_assignment (Btor *btor, char *assignment);

#endif

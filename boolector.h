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

#define BTOR_SAT 10
#define BTOR_UNSAT 20
#define BTOR_UNKNOWN 0

typedef enum BtorUnderApproxMode BtorUnderApproxMode;

/*------------------------------------------------------------------------*/
/* Boolector                                                              */
/*------------------------------------------------------------------------*/

/* Creates new boolector instance. */
Btor *boolector_new (void);

/* Sets rewrite level [0,2] */
void boolector_set_rewrite_level (Btor *btor, int rewrite_level);

/* Sets verbosity [-1,3] of btor and all sub-components
 * if verbosity is set to -1, then boolector is in "quiet mode" and
 * does not print any output
 */
void boolector_set_verbosity (Btor *btor, int verbosity);

/* Sets under-approximation mode.
 * 0 -> under-approximation disabled
 * 1 -> under-approximation where bit-width is incremented by one
 * 2 -> under-approximation where bit-width is doubled
 */
void boolector_set_under_approx_mode (Btor *btor, int mode);

/* Deletes boolector. */
void boolector_delete (Btor *btor);

/*------------------------------------------------------------------------*/
/* BtorExpression                                                         */
/*------------------------------------------------------------------------*/

/* Implicit precondition of all functions taking expressions as inputs:
 * The length 'len' of all input expressions have to be greater than zero.
 */

/* Binary constant.
 * strlen(bits) > 0
 * len(result) = strlen(bits)
 */
BtorExp *boolector_const (Btor *btor, const char *bits);

/* Binary constant representing 'len' zeros.
 * len > 0
 * len(result) = len
 */
BtorExp *boolector_zero (Btor *btor, int len);

/* Constant respresenting FALSE
 * len(result) = 1
 */
BtorExp *boolector_false (Btor *btor);

/* Binary constant representing 'len' ones.
 * len > 0
 * len(result) = len
 */
BtorExp *boolector_ones (Btor *btor, int len);

/* Constant respresenting TRUE
 * len(result) = 1
 */
BtorExp *boolector_true (Btor *btor);

/* Binary constant representing 1 with 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorExp *boolector_one (Btor *btor, int len);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * len > 0
 */
BtorExp *boolector_unsigned_int (Btor *btor, unsigned u, int len);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * len > 0
 */
BtorExp *boolector_int (Btor *emg, int i, int len);

/* Variable representing 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorExp *boolector_var (Btor *btor, int len, const char *symbol);

/* Array of size 2 ^ 'index_len' with elements of length 'elem_len'.
 * elem_len > 0
 * index_len > 0
 */
BtorExp *boolector_array (Btor *btor, int elem_len, int index_len);

/* One's complement.
 * len(result) = len(exp)
 */
BtorExp *boolector_not (Btor *btor, BtorExp *exp);

/* Two's complement.
 * len(result) = len(exp)
 */
BtorExp *boolector_neg (Btor *btor, BtorExp *exp);

/* OR reduction.
 * len(result) = 1
 */
BtorExp *boolector_redor (Btor *btor, BtorExp *exp);

/* XOR reduction.
 * len(result) = 1
 */
BtorExp *boolector_redxor (Btor *btor, BtorExp *exp);

/* AND reduction.
 * len(result) = 1
 */
BtorExp *boolector_redand (Btor *btor, BtorExp *exp);

/* Slice a sub-vector from 'upper' to 'lower'.
 * upper < len(exp)
 * lower >= 0
 * upper >= lower
 * len(result) = upper - lower + 1
 */
BtorExp *boolector_slice (Btor *btor, BtorExp *exp, int upper, int lower);

/* Unsigned extension of 'len' bits.
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorExp *boolector_uext (Btor *btor, BtorExp *exp, int len);

/* Signed extension of 'len' bits (keep sign).
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorExp *boolector_sext (Btor *btor, BtorExp *exp, int len);

/* Logical IMPLICATION.
 * len(e0) = len(e1) = 1
 * len(result) = 1
 */
BtorExp *boolector_implies (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical EQUIVALENCE.
 * len(e0) = len(e1) = 1
 * len(result) = 1
 */
BtorExp *boolector_iff (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector XOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_xor (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector XNOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_xnor (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector AND.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_and (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector NAND.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_nand (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector OR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_or (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector NOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_nor (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Bit-vector or array equality.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_eq (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Bit-vector or array inequality.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_ne (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Adder.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_add (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if adding two unsigned operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_uaddo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if adding two signed operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_saddo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Multiplier.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_mul (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_umulo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if multiplying two signed operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_smulo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned less than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_ult (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed less than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_slt (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned less than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_ulte (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed less than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_slte (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned greater than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_ugt (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed greater than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_sgt (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned greater than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_ugte (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed greater than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_sgte (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift left logical.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *boolector_sll (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift right logical.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *boolector_srl (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift right arithmetic.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *boolector_sra (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Rotate left.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *boolector_rol (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Rotate right.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *boolector_ror (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Subtractor.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_sub (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_usubo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if e0 - e1 leads to an overflow if both are signed.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_ssubo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned divider.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_udiv (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed divider.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_sdiv (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *boolector_sdivo (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned modulo.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_urem (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed modulo.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_srem (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed modulo variant.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *boolector_smod (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Concatenation.
 * len(result) = len(e0) + len(e1)
 */
BtorExp *boolector_concat (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Array read on array 'e_array' at position 'e_index'.
 * index_len(e_array) = len(e_index)
 * len(result) = elem_len(e_array)
 */
BtorExp *boolector_read (Btor *btor, BtorExp *e_array, BtorExp *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_len(e_array) = len(e_index)
 * elem_len(e_array) = len(e_value)
 */
BtorExp *boolector_write (Btor *btor,
                          BtorExp *e_array,
                          BtorExp *e_index,
                          BtorExp *e_value);

/* If-then-else.
 * len(e_cond) = 1
 * len(e_if) = len(e_else)
 * len(result) = len(e_if) = len(e_else)
 */
BtorExp *boolector_cond (Btor *btor,
                         BtorExp *e_cond,
                         BtorExp *e_if,
                         BtorExp *e_else);

/* Increments bit-vector expression by one */
BtorExp *boolector_inc (Btor *btor, BtorExp *exp);

/* Decrements bit-vector expression by one */
BtorExp *boolector_dec (Btor *btor, BtorExp *exp);

/* Gets the number of bits of an expression.
 * If 'exp' is an array, then result is the number of bits of its elements */
int boolector_get_len (Btor *btor, BtorExp *exp);

/* Determines if expression is an array or not. */
int boolector_is_array (Btor *btor, BtorExp *exp);

/* Gets the number of bits used by indices on 'e_array'. */
int boolector_get_len_index (Btor *btor, BtorExp *e_array);

/* Gets the symbol of a variable. */
char *boolector_get_symbol_of_var (Btor *btor, BtorExp *var);

/* Copies expression (increments reference counter). */
BtorExp *boolector_copy (Btor *btor, BtorExp *exp);

/* Releases expression (decrements reference counter). */
void boolector_release (Btor *btor, BtorExp *exp);

/* Dumps expression(s) to file in BTOR format. */
void boolector_dump_btor (Btor *btor, FILE *file, BtorExp *root);

/* Dumps expression to file in SMT format. */
void boolector_dump_smt (Btor *btor, FILE *file, BtorExp *root);

/* Adds constraint. */
void boolector_add_constraint (Btor *btor, BtorExp *exp);

/* Adds assumption. */
void boolector_add_assumption (Btor *btor, BtorExp *exp);

/* Solves SAT instance.
 * The paramenter 'refinement_limit' sets the maximum number
 * of iterative refinements. Use INT_MAX as default. */
int boolector_sat (Btor *btor, int refinement_limit);

/* Builds current assignment string of expression (in the SAT case)
 * and returns it.
 * Do not call before calling 'boolector_sat_btor'.
 * The assignment strings will be automatically deleted by 'boolector_delete'.
 * strlen(result) = len(exp)
 */
const char *boolector_assignment (Btor *btor, BtorExp *exp);

#endif

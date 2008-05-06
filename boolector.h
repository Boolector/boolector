#ifndef BOOLECTOR_H_INCLUDED
#define BOOLECTOR_H_INCLUDED

#include "btorhash.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PUBLIC INTERFACE                                                       */
/*------------------------------------------------------------------------*/

#define BTOR_SAT 10
#define BTOR_UNSAT 20
#define BTOR_UNKNOWN 0

/*------------------------------------------------------------------------*/
/* Declarations                                                           */
/*------------------------------------------------------------------------*/

typedef struct BtorExp BtorExp;

typedef struct Btor Btor;

/*------------------------------------------------------------------------*/
/* Btor                                                             */
/*------------------------------------------------------------------------*/

/* Creates new boolector instance. */
Btor *btor_new_btor (void);

/* Sets rewrite level [0,2] */
void btor_set_rewrite_level_btor (Btor *btor, int rewrite_level);

/* Sets verbosity [-1,3] of btor and all sub components
 * if verbosity is set to -1, then boolector is in "quiet mode" and
 * does not print any output
 */
void btor_set_verbosity_btor (Btor *btor, int verbosity);

/* Turns replay on or off */
void btor_set_replay_btor (Btor *btor, int replay);

/* Deletes boolector. */
void btor_delete_btor (Btor *btor);

const char *btor_version (void);

/*------------------------------------------------------------------------*/
/* BtorExpression                                                         */
/*------------------------------------------------------------------------*/

/* Implicit precondition of all functions taking expressions as inputs:
 * The length len of all input expressions have to be greater than zero.
 */

/* Binary constant.
 * strlen(bits) > 0
 * len(result) = strlen(bits)
 */
BtorExp *btor_const_exp (Btor *btor, const char *bits);

/* Binary constant representing len zeros.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_zero_exp (Btor *btor, int len);

/* Constant respresenting FALSE */
BtorExp *btor_false_exp (Btor *btor);

/* Binary constant representing len ones.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_ones_exp (Btor *btor, int len);

/* Constant respresenting TRUE */
BtorExp *btor_true_exp (Btor *btor);

/* Binary constant representing 1 with len bits.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_one_exp (Btor *btor, int len);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * len > 0
 */
BtorExp *btor_unsigned_to_exp (Btor *btor, unsigned u, int len);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * len > 0
 */
BtorExp *btor_int_to_exp (Btor *emg, int i, int len);

/* Variable representing len bits.
 * len(result) = len
 */
BtorExp *btor_var_exp (Btor *btor, int len, const char *symbol);

/* Array of size 2 ^ index_len with elements of elem_len bits.
 * elem_len > 0
 * index_len > 0
 */
BtorExp *btor_array_exp (Btor *btor, int elem_len, int index_len);

/* One's complement.
 * len(result) = len(exp)
 */
BtorExp *btor_not_exp (Btor *btor, BtorExp *exp);

/* Two's complement.
 * len(result) = len(exp)
 */
BtorExp *btor_neg_exp (Btor *btor, BtorExp *exp);

/* Result represents if two's complement leads to
 * an overflow. For example INT_MIN * -1.
 * len(result) = 1
 */
BtorExp *btor_nego_exp (Btor *btor, BtorExp *exp);

/* Logical OR reduction.
 * len(result) = 1
 */
BtorExp *btor_redor_exp (Btor *btor, BtorExp *exp);

/* Logical XOR reduction.
 * len(result) = 1
 */
BtorExp *btor_redxor_exp (Btor *btor, BtorExp *exp);

/* Logical AND reduction.
 * len(result) = 1
 */
BtorExp *btor_redand_exp (Btor *btor, BtorExp *exp);

/* Slice a subvector from upper to lower.
 * upper < len(exp)
 * lower >= 0
 * upper >= lower
 * len(result) = upper - lower + 1
 */
BtorExp *btor_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower);

/* Unsigned extension of len bits.
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorExp *btor_uext_exp (Btor *btor, BtorExp *exp, int len);

/* Signed extension of len bits (keep sign).
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorExp *btor_sext_exp (Btor *btor, BtorExp *exp, int len);

/* Logical and bit-vector OR.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_or_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical IMPLICATION.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_implies_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical EQUIVALENCE.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_iff_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical and bit-vector XOR.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_xor_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical and bit-vector XNOR.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_xnor_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical and bit-vector AND.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_and_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical and bit-vector NAND.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_nand_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Logical and bit-vector NOR.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_nor_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* bit-vector equality.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_eq_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* bit-vector inequality.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ne_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Adder.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_add_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if adding two unsigned operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_uaddo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if adding two signed operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_saddo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Multiplier.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_mul_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_umulo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if multiplying two signed operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_smulo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Usigned less than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ult_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed less than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_slt_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Usigned less than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ulte_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed less than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_slte_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Usigned greater than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ugt_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed greater than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_sgt_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Usigned greater than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ugte_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed greater than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_sgte_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Shift left logical.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_sll_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Shift right logical.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_srl_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Shift right arithmetic.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_sra_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Rotate left.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_rol_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Rotate right.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_ror_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Subtractor.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_sub_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 - e2 leads to an overflow if both are unsigned.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_usubo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 - e2 leads to an overflow if both are signed.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ssubo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Unsigned divider.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_udiv_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed divider.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_sdiv_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 / e2 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_sdivo_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Unsigned modulo.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_urem_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed modulo.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_srem_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Signed modulo variant.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_smod_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Concatenation.
 * len(result) = len(e1) + len(e2)
 */
BtorExp *btor_concat_exp (Btor *btor, BtorExp *e1, BtorExp *e2);

/* Array read on array e_array at position e_index.
 * index_len(e_array) = len(e_index)
 * len(result) = elem_len(e_array)
 */
BtorExp *btor_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index);

/* Array write on array e_array at position e_index with value e_value.
 * index_len(e_array) = len(e_index)
 * elem_len(e_array) = len(e_value)
 */
BtorExp *btor_write_exp (Btor *btor,
                         BtorExp *e_array,
                         BtorExp *e_index,
                         BtorExp *e_value);

/* If then else.
 * len(e_cond) = 1
 * len(e_if) = len(e_else)
 * len(result) = len(e_if) = len(e_else)
 */
BtorExp *btor_cond_exp (Btor *btor,
                        BtorExp *e_cond,
                        BtorExp *e_if,
                        BtorExp *e_else);

/* Increments bit-vector expression by one */
BtorExp *btor_inc_exp (Btor *btor, BtorExp *exp);

/* Decrements bit-vector expression by one */
BtorExp *btor_dec_exp (Btor *btor, BtorExp *exp);

/* Gets the length of an expression representing the number of bits. */
int btor_get_exp_len (Btor *btor, BtorExp *exp);

/* Determines if exp is an array or not. */
int btor_is_array_exp (Btor *btor, BtorExp *exp);

/* Gets the number of bits used by indices of e_array. */
int btor_get_index_exp_len (Btor *btor, BtorExp *e_array);

/* Gets the symbol of a variable. */
char *btor_get_symbol_exp (Btor *btor, BtorExp *exp);

/* Copies expression (increments reference counter). */
BtorExp *btor_copy_exp (Btor *btor, BtorExp *exp);

/* Releases expression (decrements reference counter). */
void btor_release_exp (Btor *btor, BtorExp *exp);

/* Dumps expression(s) to file in BTOR format. */
void btor_dump_exp (Btor *btor, FILE *file, BtorExp *exp);
void btor_dump_exps (Btor *btor, FILE *file, BtorExp **exps, int n);
void btor_dump_exps_after_substitution (Btor *btor,
                                        FILE *file,
                                        BtorExp **exps,
                                        int n);

/* Dumps expression to file in SMT format. */
void btor_dump_smt (Btor *btor, FILE *file, BtorExp *root);

/* Adds top level constraint. */
void btor_add_constraint_exp (Btor *btor, BtorExp *exp);

/* Rewriting added constraints.
 */
void btor_rewrite_btor (Btor *btor);

/* Dump added constraints and current assumptions to file 'file'. */
void btor_replay_btor (Btor *btor, FILE *file);

/* Adds assumption. */
void btor_add_assumption_exp (Btor *btor, BtorExp *exp);

/* Solves sat instance.
 * The paramenter 'refinement_limit' sets the maximum number
 * of iterative refinments */
int btor_sat_btor (Btor *btor, int refinement_limit);

/* Builds current assignment string of expression (in the SAT case)
 * and returns it.
 * Do not call before calling btor_sat_exp.
 * strlen(result) = len(exp)
 */
char *btor_assignment_exp (Btor *btor, BtorExp *exp);

#endif

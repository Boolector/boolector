#ifndef BOOLECTOR_H_INCLUDED
#define BOOLECTOR_H_INCLUDED

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PUBLIC INTERFACE                                                       */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Declarations                                                           */
/*------------------------------------------------------------------------*/

typedef struct BtorExp BtorExp;

typedef struct BtorExpMgr BtorExpMgr;

/*------------------------------------------------------------------------*/
/* BtorExpMgr                                                             */
/*------------------------------------------------------------------------*/

/* Create new expression manager. An expression manager is used by nearly
 * all functions of the expression layer. */
BtorExpMgr *btor_new_exp_mgr (int rewrite_level,
                              int dump_trace,
                              int verbosity,
                              FILE *trace_file);

/* Delete expression manager */
void btor_delete_exp_mgr (BtorExpMgr *emgr);

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
BtorExp *btor_const_exp (BtorExpMgr *emgr, const char *bits);

/* Binary constant representing len zeros.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_zeros_exp (BtorExpMgr *emgr, int len);

/* Binary constant representing len ones.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_ones_exp (BtorExpMgr *emgr, int len);

/* Binary constant representing 1 with len bits.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_one_exp (BtorExpMgr *emgr, int len);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * len > 0
 */
BtorExp *btor_unsigned_to_exp (BtorExpMgr *emgr, unsigned u, int len);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * len > 0
 */
BtorExp *btor_int_to_exp (BtorExpMgr *emg, int i, int len);

/* Variable representing len bits.
 * Variables are sticky and cannot be deleted.
 * len(result) = len
 */
BtorExp *btor_var_exp (BtorExpMgr *emgr, int len, const char *symbol);

/* Array of size 2^index_len with elements of elem_len bits.
 * Arrays are sticky and cannot be deleted.
 * elem_len > 0
 * index_len > 0
 */
BtorExp *btor_array_exp (BtorExpMgr *emgr, int elem_len, int index_len);

/* One's complement.
 * len(result) = len(exp)
 */
BtorExp *btor_not_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Two's complement.
 * len(result) = len(exp)
 */
BtorExp *btor_neg_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Result represents if two's complement leads to
 * an overflow. For example INT_MIN * -1.
 * len(result) = 1
 */
BtorExp *btor_nego_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Logical OR reduction.
 * len(exp) > 1
 * len(result) = 1
 */
BtorExp *btor_redor_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Logical XOR reduction.
 * len(exp) > 1
 * len(result) = 1
 */
BtorExp *btor_redxor_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Logical AND reduction.
 * len(exp) > 1
 * len(result) = 1
 */
BtorExp *btor_redand_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Slice a subvector from upper to lower.
 * upper < len(exp)
 * lower >= 0
 * upper >= lower
 * len(result) = upper - lower + 1
 */
BtorExp *btor_slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower);

/* Unsigned extension of len bits.
 * len(result) = len(exp) + len
 */
BtorExp *btor_uext_exp (BtorExpMgr *emgr, BtorExp *exp, int len);

/* Signed extension of len bits (keep sign).
 * len(result) = len(exp) + len
 */
BtorExp *btor_sext_exp (BtorExpMgr *emgr, BtorExp *exp, int len);

/* Logical OR.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_or_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical IMPLICATION.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_implies_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical EQUIVALENCE.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_iff_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical XOR.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_xor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical XNOR.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_xnor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical AND.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_and_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical NAND.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_nand_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical NOR.
 * len(e1) = len(e2) = 1
 * len(result) = 1
 */
BtorExp *btor_nor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Equality.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_eq_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Inequality.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ne_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Adder.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_add_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if adding two unsigned operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_uaddo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if adding two signed operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_saddo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Multiplier.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_mul_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_umulo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if multiplying two signed operands leads to an overflow.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_smulo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Usigned less than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ult_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed less than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_slt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Usigned less than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ulte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed less than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_slte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Usigned greater than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ugt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed greater than.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_sgt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Usigned greater than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ugte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed greater than or equal.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_sgte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Shift left logical.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_sll_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Shift right logical.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_srl_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Shift right arithmetic.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_sra_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Rotate left.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_rol_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Rotate right.
 * is_power_of_2(len(e1))
 * len(e2) = log2(len(e1))
 * len(result) len(e1)
 */
BtorExp *btor_ror_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Subtractor.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_sub_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 - e2 leads to an overflow if both are unsigned.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_usubo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 - e2 leads to an overflow if both are signed.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_ssubo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned divider.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_udiv_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed divider.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_sdiv_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 / e2 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * len(e1) = len(e2)
 * len(result) = 1
 */
BtorExp *btor_sdivo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned modulo.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_urem_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed modulo.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_srem_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed modulo variant.
 * len(e1) = len(e2)
 * len(result) = len(e1) = len(e2)
 */
BtorExp *btor_smod_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Concatenation.
 * len(result) = len(e1) + len(e2)
 */
BtorExp *btor_concat_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Array read on array e_array at position e_index.
 * index_len(e_array) = len(e_index)
 * len(result) = elem_len(e_array)
 */
BtorExp *btor_read_exp (BtorExpMgr *emgr, BtorExp *e_array, BtorExp *e_index);

/* Array write on array e_array at position e_index with value e_value.
 * index_len(e_array) = len(e_index)
 * elem_len(e_array) = len(e_value)
 */
BtorExp *btor_write_exp (BtorExpMgr *emgr,
                         BtorExp *e_array,
                         BtorExp *e_index,
                         BtorExp *e_value);

/* If then else.
 * len(e_cond) = 1
 * len(e_if) = len(e_else)
 * len(result) = len(e_if) = len(e_else)
 */
BtorExp *btor_cond_exp (BtorExpMgr *emgr,
                        BtorExp *e_cond,
                        BtorExp *e_if,
                        BtorExp *e_else);

/* Gets the length of an expression representing the number of bits. */
int btor_get_exp_len (BtorExpMgr *emgr, BtorExp *exp);

/* Determines if exp is an array or not. */
int btor_is_array_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Gets the number of bits used by indices of e_array. */
int btor_get_index_exp_len (BtorExpMgr *emgr, BtorExp *e_array);

/* Gets the symbol of a variable. */
char *btor_get_symbol_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Copies expression (increment reference counter). */
BtorExp *btor_copy_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Releases expression (decrement reference counter).
 * If reference counter reaches 0,
 * then also the children are released
 * and expression is deleted from memory.
 */
void btor_release_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Dumps expression to file in BTOR format. */
void btor_dump_exp (BtorExpMgr *emgr, FILE *file, BtorExp *exp);

/* Dumps expression to file in SMT format. */
void btor_dump_smt (BtorExpMgr *emgr, FILE *file, BtorExp *root);

/* Adds top level constraint. */
void btor_add_constraint_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Adds assumption. */
void btor_add_assumption_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Solves sat instance. */
int btor_sat_exp (BtorExpMgr *emgr);

/* Builds current assignment string of expression (in the SAT case)
 * and returns it.
 * Do not call before calling btor_sat_exp.
 * strlen(result) = len(exp)
 */
char *btor_assignment_exp (BtorExpMgr *emgr, BtorExp *exp);

#endif

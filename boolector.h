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

/* Create new expression manager. An expression manager is used by all main
 * functions. */
BtorExpMgr *btor_new_exp_mgr (int rewrite_level,
                              int dump_trace,
                              int verbosity,
                              FILE *trace_file);

/* Delete expression manager */
void btor_delete_exp_mgr (BtorExpMgr *emgr);

/*------------------------------------------------------------------------*/
/* BtorExpression                                                         */
/*------------------------------------------------------------------------*/

/* Binary constant.
 * The string length of bits has to be greater than zero. */
BtorExp *btor_const_exp (BtorExpMgr *emgr, const char *bits);

/* Binary constant representing len zeros.
 * The length len has to be greater than zero. */
BtorExp *btor_zeros_exp (BtorExpMgr *emgr, int len);

/* Binary constant representing len ones.
 * The length len has to be greater than zero. */
BtorExp *btor_ones_exp (BtorExpMgr *emgr, int len);

/* Binary constant representing 1 with len bits.
 * The length len has to be greater than zero. */
BtorExp *btor_one_exp (BtorExpMgr *emgr, int len);

/* Variable representing len bits.
 * The length len has to be greater than zero.
 * Variables are sticky and cannot be deleted. */
BtorExp *btor_var_exp (BtorExpMgr *emgr, int len, const char *symbol);

/* Array of size 2^index_len with elements of elem_len bits.
 * Arrays are sticky and cannot be deleted. */
BtorExp *btor_array_exp (BtorExpMgr *emgr, int elem_len, int index_len);

/* One's complement. */
BtorExp *btor_not_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Two's complement. */
BtorExp *btor_neg_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Result represents if two's complement leads to
 * an overflow. For example INT_MIN * -1. The length of the result is 1. */
BtorExp *btor_nego_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Logical OR reduction. */
BtorExp *btor_redor_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Logical XOR reduction. */
BtorExp *btor_redxor_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Logical AND reduction. */
BtorExp *btor_redand_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Slice a subvector from upper to lower of len upper - lower + 1.
 * The following preconditions on upper and lower must hold:
 * upper < len(exp)
 * lower >= 0
 * upper >= lower */
BtorExp *btor_slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower);

/* Unsigned extension of len bits. */
BtorExp *btor_uext_exp (BtorExpMgr *emgr, BtorExp *exp, int len);

/* Signed extension of len bits (keep sign). */
BtorExp *btor_sext_exp (BtorExpMgr *emgr, BtorExp *exp, int len);

/* Logical OR. Operands must have length 1. */
BtorExp *btor_or_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical IMPLICATION. Operands must have length 1. */
BtorExp *btor_implies_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical EQUIVALENCE. Operands must have length 1. */
BtorExp *btor_iff_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical XOR. Operands must have length 1. */
BtorExp *btor_xor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical XNOR. Operands must have length 1. */
BtorExp *btor_xnor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical AND. Operands must have length 1. */
BtorExp *btor_and_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical NAND. Operands must have length 1. */
BtorExp *btor_nand_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Logical NOR. Operands must have length 1. */
BtorExp *btor_nor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Equality. The length of the operands have to be equal.
 * The length of the result is 1. */
BtorExp *btor_eq_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Inequality. The length of the operands have to be equal.
 * The length of the result is 1. */
BtorExp *btor_ne_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Adder. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_add_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if adding two unsigned operands leads to an overflow.
 * The length of the result is 1. */
BtorExp *btor_uaddo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if adding two signed operands leads to an overflow.
 * The length of the result is 1. */
BtorExp *btor_saddo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Multiplier. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_mul_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * The length of the result is 1. */
BtorExp *btor_umulo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if multiplying two signed operands leads to an overflow.
 * The length of the result is 1. */
BtorExp *btor_smulo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Usigned less than. The length of the result is 1. */
BtorExp *btor_ult_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed less than. The length of the result is 1. */
BtorExp *btor_slt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned less than or equal. The length of the result is 1. */
BtorExp *btor_ulte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed less than or equal. The length of the result is 1. */
BtorExp *btor_slte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned greater than. The length of the result is 1. */
BtorExp *btor_ugt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed greater than. The length of the result is 1. */
BtorExp *btor_sgt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned greater than or equal. The length of the result is 1. */
BtorExp *btor_ugte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed greater than or equal. The length of the result is 1. */
BtorExp *btor_sgte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Shift left logical. The length of e1 has to be a power of 2.
 * The length of e2 has to be log2 of the length of e1. */
BtorExp *btor_sll_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Shift right logical. The length of e1 has to be a power of 2.
 * The length of e2 has to be log2 of the length of e1. */
BtorExp *btor_srl_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Shift right arithmetic. The length of e1 has to be a power of 2.
 * The length of e2 has to be log2 of the length of e1. */
BtorExp *btor_sra_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Rotate left. The length of e1 has to be a power of 2.
 * The length of e2 has to be log2 of the length of e1. */
BtorExp *btor_rol_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Rotate right. The length of e1 has to be a power of 2.
 * The length of e2 has to be log2 of the length of e1. */
BtorExp *btor_ror_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Subtractor. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_sub_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 - e2 leads to an overflow if both are unsigned.
 * The length of the result is 1. */
BtorExp *btor_usubo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 - e2 leads to an overflow if both are signed.
 * The length of the result is 1. */
BtorExp *btor_ssubo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned divider. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_udiv_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed divider. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_sdiv_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Result represents if e1 / e2 leads to an overflow if both are signed.
 * For example INT_MIN / -1. The length of the result is 1. */
BtorExp *btor_sdivo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Unsigned modulo. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_urem_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Signed modulo. The length of the operands have to be equal. The
 * length of the result is equal to the length of the operands. */
BtorExp *btor_srem_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_smod_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Concatenation. The result of the concatenation has length of e1 + length
 * of e2. */
BtorExp *btor_concat_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* Array read on array e_array at position e_index. */
BtorExp *btor_read_exp (BtorExpMgr *emgr, BtorExp *e_array, BtorExp *e_index);

/* Array write on array e_array at position e_index with value e_value. */
BtorExp *btor_write_exp (BtorExpMgr *emgr,
                         BtorExp *e_array,
                         BtorExp *e_index,
                         BtorExp *e_value);

/* If then else. e_cond must have length 1. The length of e_if and e_else
 * have to be equal. The length of the result is equal to the length of
 * e_if and e_else. */
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

/* Copy expression (increment reference counter). */
BtorExp *btor_copy_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Release expression (decrement reference counter). */
void btor_release_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Dump expression to file. */
void btor_dump_exp (BtorExpMgr *emgr, FILE *file, BtorExp *exp);

/* Solve sat problem with root exp. */
int btor_sat_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Get an assignment of a variable (in the SAT case). Do not call before
 * calling btor_sat_exp. */
char *btor_get_assignment_var_exp (BtorExpMgr *emgr, BtorExp *exp);

#endif

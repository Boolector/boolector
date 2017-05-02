/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "btorbv.h"
#include "btornode.h"
#include "btorsort.h"

/* Binary constant.
 * strlen(bits) > 0
 * width(result) = strlen(bits)
 */
BtorNode *btor_const_exp (Btor *btor, const BtorBitVector *bits);

/* Binary constant representing zero.
 */
BtorNode *btor_zero_exp (Btor *btor, BtorSortId sort);

/* Binary constant representing all ones.
 */
BtorNode *btor_ones_exp (Btor *btor, BtorSortId sort);

/* Binary constant representing 1.
 */
BtorNode *btor_one_exp (Btor *btor, BtorSortId sort);

/* Constant respresenting TRUE
 * width(result) = 1
 */
BtorNode *btor_true_exp (Btor *btor);

/* Constant respresenting FALSE
 * width(result) = 1
 */
BtorNode *btor_false_exp (Btor *btor);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 */
BtorNode *btor_int_exp (Btor *emg, int32_t i, BtorSortId sort);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 */
BtorNode *btor_unsigned_exp (Btor *btor, uint32_t u, BtorSortId sort);

/* Bit-vector variable.
 */
BtorNode *btor_var_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* Lambda variable.
 */
BtorNode *btor_param_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* Array variable.
 */
BtorNode *btor_array_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* Uninterpreted function with sort 'sort'.
 */
BtorNode *btor_uf_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* One's complement.
 * width(result) = width(exp)
 */
BtorNode *btor_not_exp (Btor *btor, BtorNode *exp);

/* Two's complement.
 * width(result) = width(exp)
 */
BtorNode *btor_neg_exp (Btor *btor, BtorNode *exp);

/* OR reduction.
 * width(result) = 1
 */
BtorNode *btor_redor_exp (Btor *btor, BtorNode *exp);

/* XOR reduction.
 * width(result) = 1
 */
BtorNode *btor_redxor_exp (Btor *btor, BtorNode *exp);

/* AND reduction.
 * width(result) = 1
 */
BtorNode *btor_redand_exp (Btor *btor, BtorNode *exp);

/* BtorSlice a sub-vector from 'upper' to 'lower'.
 * upper < width(exp)
 * lower >= 0
 * upper >= lower
 * width(result) = upper - lower + 1
 */
BtorNode *btor_slice_exp (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower);

/* Unsigned extension of 'width' bits.
 * width >= 0
 * width(result) = width(exp) + width
 */
BtorNode *btor_uext_exp (Btor *btor, BtorNode *exp, uint32_t width);

/* Signed extension of 'width' bits (keep sign).
 * width >= 0
 * width(result) = width(exp) + width
 */
BtorNode *btor_sext_exp (Btor *btor, BtorNode *exp, uint32_t width);

/* Logical IMPLICATION.
 * width(e0) = width(e1) = 1
 * width(result) = 1
 */
BtorNode *btor_implies_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical EQUIVALENCE.
 * width(e0) = width(e1) = 1
 * width(result) = 1
 */
BtorNode *btor_iff_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_xor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XNOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_xnor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector AND.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

#if 0
BtorNode *btor_and_n_exp (Btor * btor, BtorNode *args[], uint32_t argc);
#endif

/* Logical and bit-vector NAND.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_nand_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector OR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_or_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector NOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_nor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array equality.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array inequality.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ne_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Adder.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_uaddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_saddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Multiplier.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_umulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_smulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_slt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ulte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_slte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ugt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_sgt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ugte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_sgte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift left logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) width(e0)
 */
BtorNode *btor_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right arithmetic.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_sra_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_rol_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_ror_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Subtractor.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_sub_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_usubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are signed.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ssubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned divider.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed divider.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_sdiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_sdivo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_srem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo variant.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_smod_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Concatenation.
 * width(result) = width(e0) + width(e1)
 */
BtorNode *btor_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Array read on array 'e_array' at position 'e_index'.
 * index_width(e_array) = width(e_index)
 * width(result) = elem_width(e_array)
 */
BtorNode *btor_read_exp (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_width(e_array) = width(e_index)
 * elem_width(e_array) = width(e_value)
 */
BtorNode *btor_write_exp (Btor *btor,
                          BtorNode *e_array,
                          BtorNode *e_index,
                          BtorNode *e_value);

/* Lambda expression with variable 'e_param' bound in 'e_exp'.
 */
BtorNode *btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp);

/* Function expression with 'paramc' number of parameters 'params' and a
 * function body 'exp'.
 */
BtorNode *btor_fun_exp (Btor *btor,
                        BtorNode *params[],
                        uint32_t paramc,
                        BtorNode *exp);

/* Apply expression that applies argument expression 'args' to 'fun'.
 */
BtorNode *btor_apply_exp (Btor *btor, BtorNode *fun, BtorNode *args);

/* Apply expression that applies 'argc' number of arguments to 'fun'.
 */
BtorNode *btor_apply_exps (Btor *btor,
                           BtorNode *args[],
                           uint32_t argc,
                           BtorNode *fun);

/* Argument expression with 'argc' arguments.
 */
BtorNode *btor_args_exp (Btor *btor, BtorNode *args[], uint32_t argc);

/* If-then-else.
 * width(e_cond) = 1
 * width(e_if) = width(e_else)
 * width(result) = width(e_if) = width(e_else)
 */
BtorNode *btor_cond_exp (Btor *btor,
                         BtorNode *e_cond,
                         BtorNode *e_if,
                         BtorNode *e_else);

/* Increments bit-vector expression by one */
BtorNode *btor_inc_exp (Btor *btor, BtorNode *exp);

/* Decrements bit-vector expression by one */
BtorNode *btor_dec_exp (Btor *btor, BtorNode *exp);

#endif

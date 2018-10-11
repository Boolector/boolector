/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "btorbv.h"
#include "btornode.h"
#include "btorsort.h"

/*------------------------------------------------------------------------*/

/* Convenience wrapper function. */
BtorNode *btor_exp_create (Btor *btor,
                           BtorNodeKind kind,
                           BtorNode *e[],
                           uint32_t arity);

/*------------------------------------------------------------------------*/

/* Binary constant.
 * strlen(bits) > 0
 * width(result) = strlen(bits)
 */
BtorNode *btor_exp_const (Btor *btor, const BtorBitVector *bits);

/* Binary constant representing zero.
 */
BtorNode *btor_exp_zero (Btor *btor, BtorSortId sort);

/* Binary constant representing all ones.
 */
BtorNode *btor_exp_ones (Btor *btor, BtorSortId sort);

/* Binary constant representing 1.
 */
BtorNode *btor_exp_one (Btor *btor, BtorSortId sort);

/* Constant respresenting TRUE
 * width(result) = 1
 */
BtorNode *btor_exp_true (Btor *btor);

/* Constant respresenting FALSE
 * width(result) = 1
 */
BtorNode *btor_exp_false (Btor *btor);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 */
BtorNode *btor_exp_int (Btor *btor, int32_t i, BtorSortId sort);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 */
BtorNode *btor_exp_unsigned (Btor *btor, uint32_t u, BtorSortId sort);

/* Bit-vector variable.
 */
BtorNode *btor_exp_var (Btor *btor, BtorSortId sort, const char *symbol);

/* Lambda variable.
 */
BtorNode *btor_exp_param (Btor *btor, BtorSortId sort, const char *symbol);

/* Array variable.
 */
BtorNode *btor_exp_array (Btor *btor, BtorSortId sort, const char *symbol);

/* Uninterpreted function with sort 'sort'.
 */
BtorNode *btor_exp_uf (Btor *btor, BtorSortId sort, const char *symbol);

/* One's complement.
 * width(result) = width(exp)
 */
BtorNode *btor_exp_bv_not (Btor *btor, BtorNode *exp);

/* Two's complement.
 * width(result) = width(exp)
 */
BtorNode *btor_exp_bv_neg (Btor *btor, BtorNode *exp);

/* OR reduction.
 * width(result) = 1
 */
BtorNode *btor_exp_bv_redor (Btor *btor, BtorNode *exp);

/* XOR reduction.
 * width(result) = 1
 */
BtorNode *btor_exp_bv_redxor (Btor *btor, BtorNode *exp);

/* AND reduction.
 * width(result) = 1
 */
BtorNode *btor_exp_bv_redand (Btor *btor, BtorNode *exp);

/* BtorSlice a sub-vector from 'upper' to 'lower'.
 * upper < width(exp)
 * lower >= 0
 * upper >= lower
 * width(result) = upper - lower + 1
 */
BtorNode *btor_exp_bv_slice (Btor *btor,
                             BtorNode *exp,
                             uint32_t upper,
                             uint32_t lower);

/* Unsigned extension of 'width' bits.
 * width >= 0
 * width(result) = width(exp) + width
 */
BtorNode *btor_exp_bv_uext (Btor *btor, BtorNode *exp, uint32_t width);

/* Signed extension of 'width' bits (keep sign).
 * width >= 0
 * width(result) = width(exp) + width
 */
BtorNode *btor_exp_bv_sext (Btor *btor, BtorNode *exp, uint32_t width);

/* Logical IMPLICATION.
 * width(e0) = width(e1) = 1
 * width(result) = 1
 */
BtorNode *btor_exp_implies (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical EQUIVALENCE.
 * width(e0) = width(e1) = 1
 * width(result) = 1
 */
BtorNode *btor_exp_iff (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_bv_xor (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XNOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_xnor (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector AND.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_bv_and (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_exp_and_n (Btor *btor, BtorNode *args[], uint32_t argc);

/* Logical and bit-vector NAND.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_nand (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector OR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_or (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector NOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_nor (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array equality.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_eq (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array inequality.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_ne (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Adder.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_add (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_uaddo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_saddo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Multiplier.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_mul (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_umulo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_smulo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_ult (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_slt (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_ulte (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_slte (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_ugt (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_sgt (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_ugte (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_sgte (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift left logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) width(e0)
 */
BtorNode *btor_exp_sll (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_srl (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right arithmetic.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_sra (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_rol (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_ror (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Subtractor.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_sub (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_usubo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are signed.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_ssubo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned divider.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_udiv (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed divider.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_sdiv (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_sdivo (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_urem (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_srem (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo variant.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_smod (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Concatenation.
 * width(result) = width(e0) + width(e1)
 */
BtorNode *btor_exp_concat (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Repetition.
 * width(result) = n * width(exp)
 */
BtorNode *btor_exp_repeat (Btor *btor, BtorNode *exp, uint32_t n);

/* Array read on array 'e_array' at position 'e_index'.
 * index_width(e_array) = width(e_index)
 * width(result) = elem_width(e_array)
 */
BtorNode *btor_exp_read (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_width(e_array) = width(e_index)
 * elem_width(e_array) = width(e_value)
 */
BtorNode *btor_exp_write (Btor *btor,
                          BtorNode *e_array,
                          BtorNode *e_index,
                          BtorNode *e_value);
BtorNode *btor_write_exp_node (Btor *btor,
                               BtorNode *e_array,
                               BtorNode *e_index,
                               BtorNode *e_value);

/* Updates function 'fun' with 'value' for arguments 'args' (function write). */
BtorNode *btor_exp_update (Btor *btor,
                           BtorNode *fun,
                           BtorNode *args,
                           BtorNode *value);

/* Lambda expression that represents an array write. */
BtorNode *btor_exp_lambda_write (Btor *btor,
                                 BtorNode *e_array,
                                 BtorNode *e_index,
                                 BtorNode *e_value);

/* Lambda expression with variable 'e_param' bound in 'e_exp'.
 */
BtorNode *btor_exp_lambda (Btor *btor, BtorNode *e_param, BtorNode *e_exp);

/* Forall expression with variable 'param' and 'body'. */
BtorNode *btor_exp_forall (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_exp_forall_n (Btor *btor,
                             BtorNode *params[],
                             uint32_t paramc,
                             BtorNode *body);

/* Exists expression with variable 'param' and 'body' */
BtorNode *btor_exp_exists (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_exp_exists_n (Btor *btor,
                             BtorNode *params[],
                             uint32_t paramc,
                             BtorNode *body);

#if 0
BtorNode *btor_invert_quantifier (Btor * btor, BtorNode * quantifier);
#endif

/* Function expression with 'paramc' number of parameters 'params' and a
 * function body 'exp'.
 */
BtorNode *btor_exp_fun (Btor *btor,
                        BtorNode *params[],
                        uint32_t paramc,
                        BtorNode *exp);

/* Apply expression that applies argument expression 'args' to 'fun'.
 */
BtorNode *btor_exp_apply (Btor *btor, BtorNode *fun, BtorNode *args);

/* Apply expression that applies 'argc' number of arguments to 'fun'.
 */
BtorNode *btor_exp_apply_n (Btor *btor,
                            BtorNode *fun,
                            BtorNode *args[],
                            uint32_t argc);

/* Argument expression with 'argc' arguments.
 */
BtorNode *btor_exp_args (Btor *btor, BtorNode *args[], uint32_t argc);

/* If-then-else.
 * width(e_cond) = 1
 * width(e_if) = width(e_else)
 * width(result) = width(e_if) = width(e_else)
 */
BtorNode *btor_exp_cond (Btor *btor,
                         BtorNode *e_cond,
                         BtorNode *e_if,
                         BtorNode *e_else);

/* Increments bit-vector expression by one */
BtorNode *btor_exp_inc (Btor *btor, BtorNode *exp);

/* Decrements bit-vector expression by one */
BtorNode *btor_exp_dec (Btor *btor, BtorNode *exp);

#endif

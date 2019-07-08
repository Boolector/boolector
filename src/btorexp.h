/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017-2019 Aina Niemetz.
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

/* Create a variable of given sort. */
BtorNode *btor_exp_var (Btor *btor, BtorSortId sort, const char *symbol);

/* Create a parameter (to a function) of given sort. */
BtorNode *btor_exp_param (Btor *btor, BtorSortId sort, const char *symbol);

/* Create an array variable of given sort. */
BtorNode *btor_exp_array (Btor *btor, BtorSortId sort, const char *symbol);

/* Create an uninterpreted function of given sort. */
BtorNode *btor_exp_uf (Btor *btor, BtorSortId sort, const char *symbol);

/*------------------------------------------------------------------------*/

/* Create a bit-vector constant of size 1 respresenting TRUE. */
BtorNode *btor_exp_true (Btor *btor);

/* Create a bit-vector constant of size 1 respresenting FALSE. */
BtorNode *btor_exp_false (Btor *btor);

/**
 * Create logical IMPLICATION.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_implies (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create logical EQUIVALENCE
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_iff (Btor *btor, BtorNode *e0, BtorNode *e1);

/*------------------------------------------------------------------------*/

/**
 * Create equality.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_eq (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create inequality.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_ne (Btor *btor, BtorNode *e0, BtorNode *e1);

/*------------------------------------------------------------------------*/

/**
 * Create if-then-else .
 * width(e_cond) = 1
 * width(e_if) = width(e_else)
 * width(result) = width(e_if) = width(e_else)
 */
BtorNode *btor_exp_cond (Btor *btor,
                         BtorNode *e_cond,
                         BtorNode *e_if,
                         BtorNode *e_else);

/*------------------------------------------------------------------------*/

/* Create a bit-vector constant representing the given string of bits. */
BtorNode *btor_exp_bv_const (Btor *btor, const BtorBitVector *bits);

/* Create a bit-vector constant representing zero. */
BtorNode *btor_exp_bv_zero (Btor *btor, BtorSortId sort);

/* Create a bit-vector constant representing all ones. */
BtorNode *btor_exp_bv_ones (Btor *btor, BtorSortId sort);

/* Create a bit-vector constant representing 1. */
BtorNode *btor_exp_bv_one (Btor *btor, BtorSortId sort);

/* Create a bit-vector constant representing the minimum signed value. */
BtorNode *btor_exp_bv_min_signed (Btor *btor, BtorSortId sort);

/* Create a bit-vector constant representing the maximum signed value. */
BtorNode *btor_exp_bv_max_signed (Btor *btor, BtorSortId sort);

/**
 * Create a bit-vector constant representing the given signed integer.
 * The constant is obtained by either truncating bits or by signed extension.
 */
BtorNode *btor_exp_bv_int (Btor *btor, int32_t i, BtorSortId sort);

/**
 * Create a bit-vector constant representing the given unsigned integer.
 * The constant is obtained by either truncating bits or by unsigned extension.
 */
BtorNode *btor_exp_bv_unsigned (Btor *btor, uint32_t u, BtorSortId sort);

/*------------------------------------------------------------------------*/

/* Create a bit-vector one's complement. */
BtorNode *btor_exp_bv_not (Btor *btor, BtorNode *exp);

/* Create a bit-Vector two's complement. */
BtorNode *btor_exp_bv_neg (Btor *btor, BtorNode *exp);

/* Create a bit-vector OR reduction. */
BtorNode *btor_exp_bv_redor (Btor *btor, BtorNode *exp);

/* Create a bit-vector XOR reduction. */
BtorNode *btor_exp_bv_redxor (Btor *btor, BtorNode *exp);

/* Create a bit-vector AND reduction. */
BtorNode *btor_exp_bv_redand (Btor *btor, BtorNode *exp);

/* Create a slice of the given bit-vector from index 'upper' to 'lower'. */
BtorNode *btor_exp_bv_slice (Btor *btor,
                             BtorNode *exp,
                             uint32_t upper,
                             uint32_t lower);

/* Create an unsigned extension of the given bit-vector by 'width' bits. */
BtorNode *btor_exp_bv_uext (Btor *btor, BtorNode *exp, uint32_t width);

/* Create a signed extension of the given bit-vector by 'width' bits. */
BtorNode *btor_exp_bv_sext (Btor *btor, BtorNode *exp, uint32_t width);

/**
 * Create logical (bit-vector of size 1) and bit-vector XOR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_xor (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector XNOR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_xnor (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector AND.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_and (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create n-ary bit-vector AND (represented as a chain of binary ANDs).
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_and_n (Btor *btor, BtorNode *args[], uint32_t argc);

/**
 * Create logical (bit-vector of size 1) and bit-vector NAND.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_nand (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector OR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_or (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector NOR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_nor (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector addition.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_add (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned overflow check for add.
 * Result represents if adding two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_uaddo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed overflow check for add.
 * Result represents if adding two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_saddo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector multiplication.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BtorNode *btor_exp_bv_mul (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned overflow check for multiplication.
 * Result represents if multiplying two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_umulo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed overflow check for multiplication.
 * Result represents if multiplying two signed operands leads to an
 * overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_smulo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned less than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_ult (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed less than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_slt (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned less than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_ulte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed less than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_slte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned greater than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_ugt (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed greater than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_sgt (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned greater than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_ugte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed greater than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BtorNode *btor_exp_bv_sgte (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector logical shift left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_sll (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector logical shift right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_srl (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector arithmetic shift right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_sra (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector rotate left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_rol (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector rotate right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_ror (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector subtraction.
 * width(e0) = width(e1)
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_sub (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned overflow check for subtraction.
 * Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_bv_usubo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed overflow check for subtraction.
 * Result represents if e0 - e1 leads to an overflow if both are signed.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_bv_ssubo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned division.
 * width(e0) = width(e1)
 * width(result) = width(e0)
 */
BtorNode *btor_exp_bv_udiv (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed division.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_bv_sdiv (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed overflow check for division.
 * Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_exp_bv_sdivo (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector unsigned modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_bv_urem (Btor *btor, BtorNode *e0, BtorNode *e1);

/**
 * Create bit-vector signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_bv_srem (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Create bit-vector signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_exp_bv_smod (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Create bit-vector concatenation.
 * width(result) = width(e0) + width(e1)
 */
BtorNode *btor_exp_bv_concat (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Create bit-vector repetition.
 * width(result) = n * width(exp)
 */
BtorNode *btor_exp_bv_repeat (Btor *btor, BtorNode *exp, uint32_t n);

/* Create bit-vector increment by one */
BtorNode *btor_exp_bv_inc (Btor *btor, BtorNode *exp);

/* Create bit-vector decrement by one */
BtorNode *btor_exp_bv_dec (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Array read on array 'e_array' at position 'e_index'.
 * index_width(e_array) = width(e_index)
 * width(result) = elem_width(e_array)
 */
BtorNode *btor_exp_read (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/* Create array write on array 'e_array' at position 'e_index' with value
 * 'e_value'.
 * index_width(e_array) = width(e_index)
 * elem_width(e_array) = width(e_value)
 */
BtorNode *btor_exp_write (Btor *btor,
                          BtorNode *e_array,
                          BtorNode *e_index,
                          BtorNode *e_value);

/*------------------------------------------------------------------------*/

/**
 * Create function expression with 'paramc' number of parameters 'params' and
 * a function body 'exp'.
 */
BtorNode *btor_exp_fun (Btor *btor,
                        BtorNode *params[],
                        uint32_t paramc,
                        BtorNode *exp);

/* Create apply expression that applies argument expression 'args' to 'fun'. */
BtorNode *btor_exp_apply (Btor *btor, BtorNode *fun, BtorNode *args);

/* Create apply expression that applies 'argc' number of arguments to 'fun'. */
BtorNode *btor_exp_apply_n (Btor *btor,
                            BtorNode *fun,
                            BtorNode *args[],
                            uint32_t argc);

/* Create argument expression with 'argc' arguments. */
BtorNode *btor_exp_args (Btor *btor, BtorNode *args[], uint32_t argc);

/**
 * Create update.
 * Updates function 'fun' with 'value' for arguments 'args' (function write).
 */
BtorNode *btor_exp_update (Btor *btor,
                           BtorNode *fun,
                           BtorNode *args,
                           BtorNode *value);

/* Create lambda expression that represents an array write. */
BtorNode *btor_exp_lambda_write (Btor *btor,
                                 BtorNode *e_array,
                                 BtorNode *e_index,
                                 BtorNode *e_value);

/* Create lambda expression with variable 'e_param' bound in 'e_exp'. */
BtorNode *btor_exp_lambda (Btor *btor, BtorNode *e_param, BtorNode *e_exp);

/*------------------------------------------------------------------------*/

/* Create forall expression with variable 'param' and 'body'. */
BtorNode *btor_exp_forall (Btor *btor, BtorNode *param, BtorNode *body);
/* Create forall expression with variables 'params' and 'body'. */
BtorNode *btor_exp_forall_n (Btor *btor,
                             BtorNode *params[],
                             uint32_t paramc,
                             BtorNode *body);

/* Create exists expression with variable 'param' and 'body' */
BtorNode *btor_exp_exists (Btor *btor, BtorNode *param, BtorNode *body);
/* Create exists expression with variables 'params' and 'body' */
BtorNode *btor_exp_exists_n (Btor *btor,
                             BtorNode *params[],
                             uint32_t paramc,
                             BtorNode *body);

#if 0
BtorNode *btor_invert_quantifier (Btor * btor, BtorNode * quantifier);
#endif

#endif

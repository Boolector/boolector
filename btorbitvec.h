/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBITVEC_H_INCLUDED
#define BTORBITVEC_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "btorconst.h"
#include "btortypes.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#define BTOR_BV_TYPE uint32_t
#define BTOR_BV_TYPE_BW (sizeof (BTOR_BV_TYPE) * 8)

struct BtorBitVector
{
  uint32_t width; /* length of bit vector */
  uint32_t len;   /* length of 'bits' array */

  /* 'bits' represents the bit vector in 32-bit chunks, first bit of 32-bit bv
   * in bits[0] is MSB, bit vector is 'filled' from LSB, hence spare bits (if
   * any) come in front of the MSB and are zeroed out.
   * E.g., for a bit vector of width 31, representing value 1:
   *
   *    bits[0] = 0 0000....1
   *              ^ ^--- MSB
   *              |--- spare bit
   * */
  BTOR_BV_TYPE bits[];
};

typedef struct BtorBitVector BtorBitVector;

BTOR_DECLARE_STACK (BtorBitVectorPtr, BtorBitVector *);

BtorBitVector *btor_new_bv (BtorMemMgr *mm, uint32_t bw);

BtorBitVector *btor_new_random_bv (BtorMemMgr *mm, BtorRNG *rng, uint32_t bw);

BtorBitVector *btor_new_random_range_bv (BtorMemMgr *mm,
                                         BtorRNG *rng,
                                         uint32_t bw,
                                         BtorBitVector *from,
                                         BtorBitVector *to);
BtorBitVector *btor_new_random_bit_range_bv (
    BtorMemMgr *mm, BtorRNG *rng, uint32_t bw, uint32_t up, uint32_t lo);

BtorBitVector *btor_char_to_bv (BtorMemMgr *mm, char *assignment);
BtorBitVector *btor_uint64_to_bv (BtorMemMgr *mm, uint64_t value, uint32_t bw);

BtorBitVector *btor_get_assignment_bv (BtorMemMgr *mm,
                                       BtorNode *exp,
                                       bool init_x_values);

BtorBitVector *btor_copy_bv (BtorMemMgr *mm, const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

size_t btor_size_bv (const BtorBitVector *bv);
void btor_free_bv (BtorMemMgr *mm, BtorBitVector *bv);
int btor_compare_bv (const BtorBitVector *a, const BtorBitVector *b);
uint32_t btor_hash_bv (const BtorBitVector *bv);

void btor_print_bv (const BtorBitVector *bv);
void btor_print_all_bv (const BtorBitVector *bv);
char *btor_bv_to_char_bv (BtorMemMgr *mm, const BtorBitVector *bv);
uint64_t btor_bv_to_uint64_bv (const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

/* index 0 is LSB, width - 1 is MSB */
int btor_get_bit_bv (const BtorBitVector *bv, uint32_t pos);
/* index 0 is LSB, width - 1 is MSB */
void btor_set_bit_bv (BtorBitVector *bv, uint32_t pos, uint32_t value);

bool btor_is_true_bv (const BtorBitVector *bv);
bool btor_is_false_bv (const BtorBitVector *bv);

bool btor_is_zero_bv (const BtorBitVector *bv);
bool btor_is_ones_bv (const BtorBitVector *bv);
bool btor_is_one_bv (const BtorBitVector *bv);

/* return p for bv = 2^p, and -1 if bv is not a power of 2 */
int btor_power_of_two_bv (const BtorBitVector *bv);
/* return bv as int if its value can be converted into a positive
 * integer of bw 32, and -1 otherwise */
int btor_small_positive_int_bv (const BtorBitVector *bv);
/* return the number of leading zeroes (starting from the MSB) */
int btor_get_num_leading_zeros_bv (const BtorBitVector *bv);
/* return the number of leading ones (starting from the MSB) */
int btor_get_num_leading_ones_bv (const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

BtorBitVector *btor_one_bv (BtorMemMgr *mm, uint32_t bw);
BtorBitVector *btor_ones_bv (BtorMemMgr *mm, uint32_t bw);

BtorBitVector *btor_neg_bv (BtorMemMgr *mm, BtorBitVector *bv);
BtorBitVector *btor_not_bv (BtorMemMgr *mm, BtorBitVector *bv);
BtorBitVector *btor_inc_bv (BtorMemMgr *mm, BtorBitVector *bv);
BtorBitVector *btor_dec_bv (BtorMemMgr *mm, BtorBitVector *bv);

BtorBitVector *btor_add_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_sub_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_and_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_xor_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);

BtorBitVector *btor_eq_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_ult_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_sll_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_srl_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_mul_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b);

BtorBitVector *btor_udiv_bv (BtorMemMgr *mm,
                             BtorBitVector *a,
                             BtorBitVector *b);

BtorBitVector *btor_urem_bv (BtorMemMgr *mm,
                             BtorBitVector *a,
                             BtorBitVector *b);

BtorBitVector *btor_concat_bv (BtorMemMgr *mm,
                               BtorBitVector *a,
                               BtorBitVector *b);

BtorBitVector *btor_slice_bv (BtorMemMgr *mm,
                              BtorBitVector *bv,
                              uint32_t upper,
                              uint32_t lower);

BtorBitVector *btor_uext_bv (BtorMemMgr *mm, BtorBitVector *bv0, uint32_t len);

BtorBitVector *btor_sext_bv (BtorMemMgr *mm, BtorBitVector *bv0, uint32_t len);

BtorBitVector *btor_flipped_bit_bv (BtorMemMgr *mm,
                                    BtorBitVector *bv,
                                    uint32_t pos);

BtorBitVector *btor_flipped_bit_range_bv (BtorMemMgr *mm,
                                          BtorBitVector *bv,
                                          uint32_t up,
                                          uint32_t lo);

/*------------------------------------------------------------------------*/

bool btor_is_umulo_bv (BtorMemMgr *mm, BtorBitVector *bv0, BtorBitVector *bv1);

/*------------------------------------------------------------------------*/

BtorBitVector *btor_gcd_ext_bv (Btor *btor,
                                BtorBitVector *bv1,
                                BtorBitVector *bv2,
                                BtorBitVector **fx,
                                BtorBitVector **fy);

BtorBitVector *btor_mod_inverse_bv (BtorMemMgr *mm, BtorBitVector *bv);

/*------------------------------------------------------------------------*/

enum BtorSpecialConstBitVector
{
  BTOR_SPECIAL_CONST_BV_ZERO,
  BTOR_SPECIAL_CONST_BV_ONE,
  BTOR_SPECIAL_CONST_BV_ONES,
  BTOR_SPECIAL_CONST_BV_ONE_ONES,
  BTOR_SPECIAL_CONST_BV_NONE
};

typedef enum BtorSpecialConstBitVector BtorSpecialConstBitVector;

BtorSpecialConstBitVector btor_is_special_const_bv (BtorBitVector *bv);

/*------------------------------------------------------------------------*/

struct BtorBitVectorTuple
{
  uint32_t arity;
  BtorBitVector **bv;
};

typedef struct BtorBitVectorTuple BtorBitVectorTuple;

BtorBitVectorTuple *btor_new_bv_tuple (BtorMemMgr *mm, uint32_t arity);
void btor_free_bv_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t);

BtorBitVectorTuple *btor_copy_bv_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t);

size_t btor_size_bv_tuple (BtorBitVectorTuple *t);

void btor_add_to_bv_tuple (BtorMemMgr *mm,
                           BtorBitVectorTuple *t,
                           BtorBitVector *bv,
                           uint32_t pos);

int btor_compare_bv_tuple (BtorBitVectorTuple *t0, BtorBitVectorTuple *t1);

uint32_t btor_hash_bv_tuple (BtorBitVectorTuple *t);

/*------------------------------------------------------------------------*/

#endif

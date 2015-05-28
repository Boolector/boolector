/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCONSTBV_H_INCLUDED
#define BTORCONSTBV_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "btorexp.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#define BTOR_BV_TYPE uint32_t
#define BTOR_BV_TYPE_BW (sizeof (BTOR_BV_TYPE) * 8)

struct BtorBitVector
{
  int width; /* length of bit vector */
  int len;   /* length of 'bits' array */

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

BtorBitVector *btor_new_bv (BtorMemMgr *mm, int bw);

BtorBitVector *btor_new_random_bv (BtorMemMgr *mm, BtorRNG *rng, int bw);
BtorBitVector *btor_new_random_range_bv (BtorMemMgr *mm,
                                         BtorRNG *rng,
                                         int bw,
                                         BtorBitVector *from,
                                         BtorBitVector *to);
BtorBitVector *btor_new_random_bit_range_bv (
    BtorMemMgr *mm, BtorRNG *rng, int bw, int up, int lo);

BtorBitVector *btor_char_to_bv (BtorMemMgr *mm, char *assignment);
BtorBitVector *btor_uint64_to_bv (BtorMemMgr *mm, uint64_t value, int bw);
BtorBitVector *btor_assignment_bv (BtorMemMgr *mm, BtorNode *exp, int bw);
BtorBitVector *btor_copy_bv (BtorMemMgr *mm, BtorBitVector *bv);

size_t btor_size_bv (BtorBitVector *bv);
void btor_free_bv (BtorMemMgr *mm, BtorBitVector *bv);
int btor_compare_bv (BtorBitVector *bv1, BtorBitVector *bv2);
bool btor_is_zero_bv (const BtorBitVector *bv);
bool btor_is_one_bv (const BtorBitVector *bv);
unsigned int btor_hash_bv (BtorBitVector *bv);

void btor_print_bv (BtorBitVector *bv);
void btor_print_all_bv (BtorBitVector *bv);
char *btor_bv_to_char_bv (BtorMemMgr *mm, const BtorBitVector *bv);
uint64_t btor_bv_to_uint64_bv (BtorBitVector *bv);
/* index 0 is LSB, width - 1 is MSB */
int btor_get_bit_bv (const BtorBitVector *bv, int pos);
/* index 0 is LSB, width - 1 is MSB */
void btor_set_bit_bv (BtorBitVector *bv, int pos, int value);
int btor_is_true_bv (BtorBitVector *bv);
int btor_is_false_bv (BtorBitVector *bv);

/*------------------------------------------------------------------------*/

BtorBitVector *btor_one_bv (BtorMemMgr *mm, int bw);
BtorBitVector *btor_ones_bv (BtorMemMgr *mm, int bw);

BtorBitVector *btor_neg_bv (BtorMemMgr *mm, BtorBitVector *bv);
BtorBitVector *btor_not_bv (BtorMemMgr *mm, BtorBitVector *bv);
BtorBitVector *btor_inc_bv (BtorMemMgr *mm, BtorBitVector *bv);
BtorBitVector *btor_dec_bv (BtorMemMgr *mm, BtorBitVector *bv);

BtorBitVector *btor_add_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_and_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_xor_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_eq_bv (BtorMemMgr *mm,
                           BtorBitVector *bv0,
                           BtorBitVector *bv1);
BtorBitVector *btor_ult_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_sll_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_srl_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_mul_bv (BtorMemMgr *mm,
                            BtorBitVector *bv0,
                            BtorBitVector *bv1);
BtorBitVector *btor_udiv_bv (BtorMemMgr *mm,
                             BtorBitVector *bv0,
                             BtorBitVector *bv1);
BtorBitVector *btor_urem_bv (BtorMemMgr *mm,
                             BtorBitVector *bv0,
                             BtorBitVector *bv1);
BtorBitVector *btor_concat_bv (BtorMemMgr *mm,
                               BtorBitVector *bv0,
                               BtorBitVector *bv1);
BtorBitVector *btor_slice_bv (BtorMemMgr *mm,
                              BtorBitVector *bv0,
                              int up,
                              int lo);
BtorBitVector *btor_uext_bv (BtorMemMgr *mm, BtorBitVector *bv0, int len);
BtorBitVector *btor_sext_bv (BtorMemMgr *mm, BtorBitVector *bv0, int len);

BtorBitVector *btor_flipped_bit_bv (BtorMemMgr *mm, BtorBitVector *bv, int pos);
BtorBitVector *btor_flipped_bit_range_bv (BtorMemMgr *mm,
                                          BtorBitVector *bv,
                                          int up,
                                          int lo);

/*------------------------------------------------------------------------*/

bool btor_is_umulo_bv (BtorMemMgr *mm, BtorBitVector *bv0, BtorBitVector *bv1);

/*------------------------------------------------------------------------*/

BtorBitVector *btor_gcd_ext_bv (Btor *btor,
                                BtorBitVector *bv1,
                                BtorBitVector *bv2,
                                BtorBitVector **fx,
                                BtorBitVector **fy);

/*------------------------------------------------------------------------*/

struct BtorBitVectorTuple
{
  int arity;
  BtorBitVector **bv;
};

typedef struct BtorBitVectorTuple BtorBitVectorTuple;

BtorBitVectorTuple *btor_new_bv_tuple (BtorMemMgr *mm, int arity);
BtorBitVectorTuple *btor_copy_bv_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t);

size_t btor_size_bv_tuple (BtorBitVectorTuple *t);
void btor_free_bv_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t);
int btor_compare_bv_tuple (BtorBitVectorTuple *t0, BtorBitVectorTuple *t1);
unsigned int btor_hash_bv_tuple (BtorBitVectorTuple *t);

void btor_add_to_bv_tuple (BtorMemMgr *mm,
                           BtorBitVectorTuple *t,
                           BtorBitVector *bv,
                           int pos);

#endif

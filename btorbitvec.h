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

struct BitVector
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

typedef struct BitVector BitVector;

BitVector *btor_new_bv (BtorMemMgr *mm, int bw);

BitVector *btor_new_random_bv (BtorMemMgr *mm, BtorRNG *rng, int bw);
BitVector *btor_new_random_range_bv (
    BtorMemMgr *mm, BtorRNG *rng, int bw, BitVector *from, BitVector *to);
BitVector *btor_new_random_bit_range_bv (
    BtorMemMgr *mm, BtorRNG *rng, int bw, int up, int lo);

BitVector *btor_char_to_bv (BtorMemMgr *mm, char *assignment);
BitVector *btor_uint64_to_bv (BtorMemMgr *mm, uint64_t value, int bw);
BitVector *btor_assignment_bv (BtorMemMgr *mm, BtorNode *exp, int bw);
BitVector *btor_copy_bv (BtorMemMgr *mm, BitVector *bv);

size_t btor_size_bv (BitVector *bv);
void btor_free_bv (BtorMemMgr *mm, BitVector *bv);
int btor_compare_bv (BitVector *bv1, BitVector *bv2);
bool btor_is_zero_bv (const BitVector *bv);
bool btor_is_one_bv (const BitVector *bv);
unsigned int btor_hash_bv (BitVector *bv);

void btor_print_bv (BitVector *bv);
void btor_print_all_bv (BitVector *bv);
char *btor_bv_to_char_bv (BtorMemMgr *mm, const BitVector *bv);
uint64_t btor_bv_to_uint64_bv (BitVector *bv);
/* index 0 is LSB, width - 1 is MSB */
int btor_get_bit_bv (const BitVector *bv, int pos);
/* index 0 is LSB, width - 1 is MSB */
void btor_set_bit_bv (BitVector *bv, int pos, int value);
int btor_is_true_bv (BitVector *bv);
int btor_is_false_bv (BitVector *bv);

BitVector *btor_neg_bv (BtorMemMgr *mm, BitVector *bv);
BitVector *btor_not_bv (BtorMemMgr *mm, BitVector *bv);
BitVector *btor_inc_bv (BtorMemMgr *mm, BitVector *bv);
BitVector *btor_dec_bv (BtorMemMgr *mm, BitVector *bv);
BitVector *btor_add_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_and_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_xor_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_eq_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_ult_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_sll_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_srl_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_mul_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_udiv_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_urem_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_concat_bv (BtorMemMgr *mm, BitVector *bv0, BitVector *bv1);
BitVector *btor_slice_bv (BtorMemMgr *mm, BitVector *bv0, int up, int lo);
BitVector *btor_uext_bv (BtorMemMgr *mm, BitVector *bv0, int len);
BitVector *btor_sext_bv (BtorMemMgr *mm, BitVector *bv0, int len);

BitVector *btor_flipped_bit_bv (BtorMemMgr *mm, BitVector *bv, int pos);
BitVector *btor_flipped_bit_range_bv (BtorMemMgr *mm,
                                      BitVector *bv,
                                      int up,
                                      int lo);

/*------------------------------------------------------------------------*/

BitVector *btor_gcd_ext_bv (
    Btor *btor, BitVector *bv1, BitVector *bv2, BitVector **fx, BitVector **fy);

/*------------------------------------------------------------------------*/

struct BitVectorTuple
{
  int arity;
  BitVector **bv;
};

typedef struct BitVectorTuple BitVectorTuple;

BitVectorTuple *btor_new_bv_tuple (BtorMemMgr *mm, int arity);
BitVectorTuple *btor_copy_bv_tuple (BtorMemMgr *mm, BitVectorTuple *t);

size_t btor_size_bv_tuple (BitVectorTuple *t);
void btor_free_bv_tuple (BtorMemMgr *mm, BitVectorTuple *t);
int btor_compare_bv_tuple (BitVectorTuple *t0, BitVectorTuple *t1);
unsigned int btor_hash_bv_tuple (BitVectorTuple *t);

void btor_add_to_bv_tuple (BtorMemMgr *mm,
                           BitVectorTuple *t,
                           BitVector *bv,
                           int pos);

#endif

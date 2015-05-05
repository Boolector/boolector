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

BitVector *btor_new_bv (BtorMemMgr *, int);
BitVector *btor_new_random_bv (BtorMemMgr *, BtorRNG *, int);
BitVector *btor_new_random_range_bv (BtorMemMgr *, BtorRNG *, int, int, int);
BitVector *btor_char_to_bv (BtorMemMgr *, char *);
BitVector *btor_uint64_to_bv (BtorMemMgr *, uint64_t, int);
BitVector *btor_assignment_bv (BtorMemMgr *, BtorNode *, int);
BitVector *btor_copy_bv (BtorMemMgr *, BitVector *);

size_t btor_size_bv (BitVector *);
void btor_free_bv (BtorMemMgr *, BitVector *);
int btor_compare_bv (BitVector *, BitVector *);
bool btor_is_zero_bv (const BitVector *);
unsigned int btor_hash_bv (BitVector *);

void btor_print_bv (BitVector *);
void btor_print_all_bv (BitVector *);
char *btor_bv_to_char_bv (BtorMemMgr *, const BitVector *);
uint64_t btor_bv_to_uint64_bv (BitVector *);
/* index 0 is LSB, width - 1 is MSB */
int btor_get_bit_bv (const BitVector *, int);
/* index 0 is LSB, width - 1 is MSB */
void btor_set_bit_bv (BitVector *, int, int);
int btor_is_true_bv (BitVector *);
int btor_is_false_bv (BitVector *);

BitVector *btor_neg_bv (BtorMemMgr *, BitVector *);
BitVector *btor_not_bv (BtorMemMgr *, BitVector *);
BitVector *btor_xor_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_inc_bv (BtorMemMgr *, BitVector *);
BitVector *btor_dec_bv (BtorMemMgr *, BitVector *);
BitVector *btor_flipped_bit_bv (BtorMemMgr *, BitVector *, int);
BitVector *btor_flipped_bit_range_bv (BtorMemMgr *, BitVector *, int, int);

BitVector *btor_add_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_and_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_eq_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_ult_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_sll_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_srl_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_mul_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_udiv_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_urem_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_concat_bv (BtorMemMgr *, BitVector *, BitVector *);
BitVector *btor_slice_bv (BtorMemMgr *, BitVector *, int, int);
BitVector *btor_uext_bv (BtorMemMgr *, BitVector *, int);
BitVector *btor_sext_bv (BtorMemMgr *, BitVector *, int);

/*------------------------------------------------------------------------*/

struct BitVectorTuple
{
  int arity;
  BitVector **bv;
};

typedef struct BitVectorTuple BitVectorTuple;

BitVectorTuple *btor_new_bv_tuple (BtorMemMgr *, int);
void btor_free_bv_tuple (BtorMemMgr *, BitVectorTuple *);
BitVectorTuple *btor_copy_bv_tuple (BtorMemMgr *, BitVectorTuple *);
size_t btor_size_bv_tuple (BitVectorTuple *);
void btor_add_to_bv_tuple (BtorMemMgr *, BitVectorTuple *, BitVector *, int);
int btor_compare_bv_tuple (BitVectorTuple *, BitVectorTuple *);
unsigned int btor_hash_bv_tuple (BitVectorTuple *);

#endif

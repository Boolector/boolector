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

#include <stdint.h>
#include "btorexp.h"
#include "utils/btormem.h"

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

BtorBitVector *btor_new_bv (BtorMemMgr *, int);
BtorBitVector *btor_char_to_bv (BtorMemMgr *, char *);
BtorBitVector *btor_uint64_to_bv (BtorMemMgr *, uint64_t, int);
BtorBitVector *btor_assignment_bv (BtorMemMgr *, BtorNode *, int);
BtorBitVector *btor_copy_bv (BtorMemMgr *, BtorBitVector *);
size_t btor_size_bv (BtorBitVector *);
void btor_free_bv (BtorMemMgr *, BtorBitVector *);
int btor_compare_bv (BtorBitVector *, BtorBitVector *);
unsigned int btor_hash_bv (BtorBitVector *);

void btor_print_bv (BtorBitVector *);
void btor_print_all_bv (BtorBitVector *);
char *btor_bv_to_char_bv (BtorMemMgr *, const BtorBitVector *);
uint64_t btor_bv_to_uint64_bv (BtorBitVector *);
int btor_get_bit_bv (const BtorBitVector *, int);
int btor_is_true_bv (BtorBitVector *);
int btor_is_false_bv (BtorBitVector *);

BtorBitVector *btor_neg_bv (BtorMemMgr *, BtorBitVector *);
BtorBitVector *btor_not_bv (BtorMemMgr *, BtorBitVector *);
BtorBitVector *btor_add_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_and_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_eq_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_ult_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_sll_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_srl_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_mul_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_udiv_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_urem_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_concat_bv (BtorMemMgr *, BtorBitVector *, BtorBitVector *);
BtorBitVector *btor_slice_bv (BtorMemMgr *, BtorBitVector *, int, int);

/*------------------------------------------------------------------------*/

struct BtorBitVectorTuple
{
  int arity;
  BtorBitVector **bv;
};

typedef struct BtorBitVectorTuple BtorBitVectorTuple;

BtorBitVectorTuple *btor_new_bv_tuple (BtorMemMgr *, int);
void btor_free_bv_tuple (BtorMemMgr *, BtorBitVectorTuple *);
BtorBitVectorTuple *btor_copy_bv_tuple (BtorMemMgr *, BtorBitVectorTuple *);
size_t btor_size_bv_tuple (BtorBitVectorTuple *);
void btor_add_to_bv_tuple (BtorMemMgr *,
                           BtorBitVectorTuple *,
                           BtorBitVector *,
                           int);
int btor_compare_bv_tuple (BtorBitVectorTuple *, BtorBitVectorTuple *);
unsigned int btor_hash_bv_tuple (BtorBitVectorTuple *);

#endif

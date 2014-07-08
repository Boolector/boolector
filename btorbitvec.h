/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCONSTBV_H_INCLUDED
#define BTORCONSTBV_H_INCLUDED

#include <stdint.h>
#include "btorcore.h"

#define BTOR_BV_TYPE uint32_t
#define BTOR_BV_TYPE_BW (sizeof (BTOR_BV_TYPE) * 8)

struct BitVector
{
  int width;
  int len;
  /* spare bits at the beginning are zeroed out */
  BTOR_BV_TYPE *bits;
};

typedef struct BitVector BitVector;

#define BTOR_INVERT_BV(bv) ((BitVector *) (1ul ^ (unsigned long int) (bv)))
#define BTOR_IS_INVERTED_BV(bv) (1ul & (unsigned long int) (bv))
#define BTOR_REAL_ADDR_BV(bv) ((BitVector *) (~3ul & (unsigned long int) (bv)))

BitVector *btor_new_bv (Btor *, int);
BitVector *btor_char_to_bv (Btor *, char *);
BitVector *btor_uint64_to_bv (Btor *, uint64_t, int);
BitVector *btor_assignment_bv (Btor *, BtorNode *, int);
BitVector *btor_copy_bv (Btor *, BitVector *);
size_t btor_size_bv (BitVector *);
void btor_free_bv (Btor *, BitVector *);
int btor_compare_bv (BitVector *, BitVector *);
unsigned int btor_hash_bv (BitVector *);

void btor_print_bv (BitVector *);
void btor_print_all_bv (BitVector *);
char *btor_bv_to_char_bv (Btor *, const BitVector *);
uint64_t btor_bv_to_uint64_bv (BitVector *);
int btor_get_bit_bv (const BitVector *, int);
int btor_is_true_bv (BitVector *);
int btor_is_false_bv (BitVector *);

BitVector *btor_neg_bv (Btor *, BitVector *);
BitVector *btor_not_bv (Btor *, BitVector *);
BitVector *btor_add_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_and_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_eq_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_ult_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_sll_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_srl_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_mul_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_udiv_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_urem_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_concat_bv (Btor *, BitVector *, BitVector *);
BitVector *btor_slice_bv (Btor *, BitVector *, int, int);

/*------------------------------------------------------------------------*/

struct BitVectorTuple
{
  int arity;
  BitVector **bv;
};

typedef struct BitVectorTuple BitVectorTuple;

BitVectorTuple *btor_new_bv_tuple (Btor *, int);
void btor_free_bv_tuple (Btor *, BitVectorTuple *);
BitVectorTuple *btor_copy_bv_tuple (Btor *, BitVectorTuple *);
size_t btor_size_bv_tuple (BitVectorTuple *);
void btor_add_to_bv_tuple (Btor *, BitVectorTuple *, BitVector *, int);
int btor_compare_bv_tuple (BitVectorTuple *, BitVectorTuple *);
unsigned int btor_hash_bv_tuple (BitVectorTuple *);

#endif

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *  Copyright (C) 2018 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBV_H_INCLUDED
#define BTORBV_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "btortypes.h"
#include "utils/btormem.h"
#include "utils/btorrng.h"
#include "utils/btorstack.h"

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

BtorBitVector *btor_bv_new (BtorMemMgr *mm, uint32_t bw);

BtorBitVector *btor_bv_new_random (BtorMemMgr *mm, BtorRNG *rng, uint32_t bw);

BtorBitVector *btor_bv_new_random_range (BtorMemMgr *mm,
                                         BtorRNG *rng,
                                         uint32_t bw,
                                         const BtorBitVector *from,
                                         const BtorBitVector *to);

BtorBitVector *btor_bv_new_random_bit_range (
    BtorMemMgr *mm, BtorRNG *rng, uint32_t bw, uint32_t up, uint32_t lo);

BtorBitVector *btor_bv_char_to_bv (BtorMemMgr *mm, const char *assignment);

BtorBitVector *btor_bv_dec_to_bv (BtorMemMgr *mm,
                                  const char *decimal_string,
                                  uint32_t bw);

BtorBitVector *btor_bv_uint64_to_bv (BtorMemMgr *mm,
                                     uint64_t value,
                                     uint32_t bw);

BtorBitVector *btor_bv_int64_to_bv (BtorMemMgr *mm, int64_t value, uint32_t bw);

BtorBitVector *btor_bv_const (BtorMemMgr *mm, const char *str, uint32_t bw);

BtorBitVector *btor_bv_constd (BtorMemMgr *mm, const char *str, uint32_t bw);

BtorBitVector *btor_bv_consth (BtorMemMgr *mm, const char *str, uint32_t bw);

BtorBitVector *btor_bv_get_assignment (BtorMemMgr *mm, BtorNode *exp);

BtorBitVector *btor_bv_copy (BtorMemMgr *mm, const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

size_t btor_bv_size (const BtorBitVector *bv);
void btor_bv_free (BtorMemMgr *mm, BtorBitVector *bv);
int32_t btor_bv_compare (const BtorBitVector *a, const BtorBitVector *b);
uint32_t btor_bv_hash (const BtorBitVector *bv);

void btor_bv_print (const BtorBitVector *bv);
void btor_bv_print_all (const BtorBitVector *bv);
void btor_bv_print_without_new_line (const BtorBitVector *bv);

char *btor_bv_to_char (BtorMemMgr *mm, const BtorBitVector *bv);
char *btor_bv_to_hex_char (BtorMemMgr *mm, const BtorBitVector *bv);
char *btor_bv_to_dec_char (BtorMemMgr *mm, const BtorBitVector *bv);

uint64_t btor_bv_to_uint64 (const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

/* index 0 is LSB, width - 1 is MSB */
uint32_t btor_bv_get_bit (const BtorBitVector *bv, uint32_t pos);
/* index 0 is LSB, width - 1 is MSB */
void btor_bv_set_bit (BtorBitVector *bv, uint32_t pos, uint32_t value);

void btor_bv_flip_bit (BtorBitVector *bv, uint32_t pos);

bool btor_bv_is_true (const BtorBitVector *bv);
bool btor_bv_is_false (const BtorBitVector *bv);

bool btor_bv_is_zero (const BtorBitVector *bv);
bool btor_bv_is_ones (const BtorBitVector *bv);
bool btor_bv_is_one (const BtorBitVector *bv);
bool btor_bv_is_min_signed (const BtorBitVector *bv);
bool btor_bv_is_max_signed (const BtorBitVector *bv);

/* return p for bv = 2^p, and -1 if bv is not a power of 2 */
int64_t btor_bv_power_of_two (const BtorBitVector *bv);
/* return bv as integer if its value can be converted into a positive
 * integer of bw 32, and -1 otherwise */
int32_t btor_bv_small_positive_int (const BtorBitVector *bv);

/* count trailing zeros (starting from LSB) */
uint32_t btor_bv_get_num_trailing_zeros (const BtorBitVector *bv);
/* count leading zeros (starting from MSB) */
uint32_t btor_bv_get_num_leading_zeros (const BtorBitVector *bv);
/* count leading ones (starting from MSB) */
uint32_t btor_bv_get_num_leading_ones (const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

#define btor_bv_zero(MM, BW) btor_bv_new (MM, BW)

BtorBitVector *btor_bv_one (BtorMemMgr *mm, uint32_t bw);
BtorBitVector *btor_bv_ones (BtorMemMgr *mm, uint32_t bw);
BtorBitVector *btor_bv_min_signed (BtorMemMgr *mm, uint32_t bw);
BtorBitVector *btor_bv_max_signed (BtorMemMgr *mm, uint32_t bw);

BtorBitVector *btor_bv_neg (BtorMemMgr *mm, const BtorBitVector *bv);
BtorBitVector *btor_bv_not (BtorMemMgr *mm, const BtorBitVector *bv);
BtorBitVector *btor_bv_inc (BtorMemMgr *mm, const BtorBitVector *bv);
BtorBitVector *btor_bv_dec (BtorMemMgr *mm, const BtorBitVector *bv);

BtorBitVector *btor_bv_redor (BtorMemMgr *mm, const BtorBitVector *bv);
BtorBitVector *btor_bv_redand (BtorMemMgr *mm, const BtorBitVector *bv);

BtorBitVector *btor_bv_add (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_sub (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_and (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_implies (BtorMemMgr *mm,
                                const BtorBitVector *a,
                                const BtorBitVector *b);

BtorBitVector *btor_bv_nand (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

BtorBitVector *btor_bv_nor (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_or (BtorMemMgr *mm,
                           const BtorBitVector *a,
                           const BtorBitVector *b);

BtorBitVector *btor_bv_xnor (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

BtorBitVector *btor_bv_xor (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_eq (BtorMemMgr *mm,
                           const BtorBitVector *a,
                           const BtorBitVector *b);

BtorBitVector *btor_bv_ne (BtorMemMgr *mm,
                           const BtorBitVector *a,
                           const BtorBitVector *b);

BtorBitVector *btor_bv_ult (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_ulte (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

BtorBitVector *btor_bv_sll (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_srl (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_mul (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

BtorBitVector *btor_bv_udiv (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

BtorBitVector *btor_bv_urem (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

BtorBitVector *btor_bv_ite (BtorMemMgr *mm,
                            const BtorBitVector *c,
                            const BtorBitVector *t,
                            const BtorBitVector *e);

BtorBitVector *btor_bv_concat (BtorMemMgr *mm,
                               const BtorBitVector *a,
                               const BtorBitVector *b);

BtorBitVector *btor_bv_slice (BtorMemMgr *mm,
                              const BtorBitVector *bv,
                              uint32_t upper,
                              uint32_t lower);

BtorBitVector *btor_bv_uext (BtorMemMgr *mm,
                             const BtorBitVector *bv0,
                             uint32_t len);

BtorBitVector *btor_bv_sext (BtorMemMgr *mm,
                             const BtorBitVector *bv0,
                             uint32_t len);

BtorBitVector *btor_bv_flipped_bit (BtorMemMgr *mm,
                                    const BtorBitVector *bv,
                                    uint32_t pos);

BtorBitVector *btor_bv_flipped_bit_range (BtorMemMgr *mm,
                                          const BtorBitVector *bv,
                                          uint32_t up,
                                          uint32_t lo);

/*------------------------------------------------------------------------*/

bool btor_bv_is_umulo (BtorMemMgr *mm,
                       const BtorBitVector *bv0,
                       const BtorBitVector *bv1);

/*------------------------------------------------------------------------*/

#if 0
BtorBitVector * btor_bv_gcd_ext (Btor * btor,
				 const BtorBitVector * bv1,
				 const BtorBitVector * bv2,
				 BtorBitVector ** fx,
				 BtorBitVector ** fy);
#endif

BtorBitVector *btor_bv_mod_inverse (BtorMemMgr *mm, const BtorBitVector *bv);

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

BtorSpecialConstBitVector btor_bv_is_special_const (const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

struct BtorBitVectorTuple
{
  uint32_t arity;
  BtorBitVector **bv;
};

typedef struct BtorBitVectorTuple BtorBitVectorTuple;

BtorBitVectorTuple *btor_bv_new_tuple (BtorMemMgr *mm, uint32_t arity);
void btor_bv_free_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t);

BtorBitVectorTuple *btor_bv_copy_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t);

size_t btor_bv_size_tuple (BtorBitVectorTuple *t);

void btor_bv_add_to_tuple (BtorMemMgr *mm,
                           BtorBitVectorTuple *t,
                           const BtorBitVector *bv,
                           uint32_t pos);

int32_t btor_bv_compare_tuple (const BtorBitVectorTuple *t0,
                               const BtorBitVectorTuple *t1);

uint32_t btor_bv_hash_tuple (const BtorBitVectorTuple *t);

/*------------------------------------------------------------------------*/

#endif

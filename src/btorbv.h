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

typedef struct BtorBitVector BtorBitVector;

BTOR_DECLARE_STACK (BtorBitVectorPtr, BtorBitVector *);

/* Create a new bit-vector of given bit-width, initialized to zero. */
BtorBitVector *btor_bv_new (BtorMemMgr *mm, uint32_t bw);

/* Create a new random bit-vector of given bit-width. */
BtorBitVector *btor_bv_new_random (BtorMemMgr *mm, BtorRNG *rng, uint32_t bw);

/* Create a new random bit-vector within the given value range. */
BtorBitVector *btor_bv_new_random_range (BtorMemMgr *mm,
                                         BtorRNG *rng,
                                         uint32_t bw,
                                         const BtorBitVector *from,
                                         const BtorBitVector *to);

/**
 * Create a new bit-vecotr of given bit-width and randomly set bits within given
 * index range. Bits outside of given index range are initialized with zero.
 */
BtorBitVector *btor_bv_new_random_bit_range (
    BtorMemMgr *mm, BtorRNG *rng, uint32_t bw, uint32_t up, uint32_t lo);

/**
 * Create bit-vector from given binary string.
 * The bit-width of the resulting bit-vector is the length of the given string.
 */
BtorBitVector *btor_bv_char_to_bv (BtorMemMgr *mm, const char *assignment);

/* Create bit-vector of given bit-width from given unsigned integer value. */
BtorBitVector *btor_bv_uint64_to_bv (BtorMemMgr *mm,
                                     uint64_t value,
                                     uint32_t bw);

/* Create bit-vector of given bit-width from given integer value. */
BtorBitVector *btor_bv_int64_to_bv (BtorMemMgr *mm, int64_t value, uint32_t bw);

/**
 * Create bit-vector from given binary string.
 * The bit-width of the resulting bit-vector is the length of the given string.
 */
BtorBitVector *btor_bv_const (BtorMemMgr *mm, const char *str, uint32_t bw);

/* Create bit-vector of given bit-width from given decimal string. */
BtorBitVector *btor_bv_constd (BtorMemMgr *mm, const char *str, uint32_t bw);

/* Create bit-vector of given bit-width from given hexadecimal string. */
BtorBitVector *btor_bv_consth (BtorMemMgr *mm, const char *str, uint32_t bw);

/* Get AIG vector assignment of given node as bit-vector. */
BtorBitVector *btor_bv_get_assignment (BtorMemMgr *mm, BtorNode *exp);

/* Create a (deep) copy of the given bit-vector. */
BtorBitVector *btor_bv_copy (BtorMemMgr *mm, const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

/* Return the size in bytes of the given bit-vector. */
size_t btor_bv_size (const BtorBitVector *bv);

/* Free memory allocated for the given bit-vector. */
void btor_bv_free (BtorMemMgr *mm, BtorBitVector *bv);

/**
 * Compare bit-vectors 'a' and 'b'.
 * Return 0 if 'a' and 'b' are equal, 1 if a > b, and -1 if a < b.
 */
int32_t btor_bv_compare (const BtorBitVector *a, const BtorBitVector *b);

/* Return a hash value for the given bit-vector. */
uint32_t btor_bv_hash (const BtorBitVector *bv);

/* Print given bit-vector to stdout, terminated with a new line. */
void btor_bv_print (const BtorBitVector *bv);
/* Print given bit-vector to stdout, without terminating new line. */
void btor_bv_print_without_new_line (const BtorBitVector *bv);
/**
 * Print 32 bit chunks of underlying bits array of given bit-vector to stdout.
 * Superfluous bits and actual bits belonging to the bit-vector (in case that
 * the underlying array allows to represent more than bv->width bits) are
 * separated with a '|'. For debugging purposes only. Does not print anything
 * if compiled with GMP.
 */
void btor_bv_print_all (const BtorBitVector *bv);

/* Convert given bit-vector to a binary string. */
char *btor_bv_to_char (BtorMemMgr *mm, const BtorBitVector *bv);
/* Convert given bit-vector to a hexadecimal string. */
char *btor_bv_to_hex_char (BtorMemMgr *mm, const BtorBitVector *bv);
/* Convert given bit-vector to a decimal string. */
char *btor_bv_to_dec_char (BtorMemMgr *mm, const BtorBitVector *bv);

/* Convert given bit-vector to an unsigned 64 bit integer. */
uint64_t btor_bv_to_uint64 (const BtorBitVector *bv);

/*------------------------------------------------------------------------*/

/* Get the bit-width of given bit-vector. */
uint32_t btor_bv_get_width (const BtorBitVector *bv);

/**
 * Get the length of the bits array of the given bit-vector.
 * This function returns 0 if compiled with GMP.
 */
uint32_t btor_bv_get_len (const BtorBitVector *bv);

/* Get value of bit at given index (index 0 is LSB, width - 1 is MSB). */
uint32_t btor_bv_get_bit (const BtorBitVector *bv, uint32_t pos);
/* Get value of bit at given index (index 0 is LSB, width - 1 is MSB). */
void btor_bv_set_bit (BtorBitVector *bv, uint32_t pos, uint32_t value);

/* Flip bit at given index. */
void btor_bv_flip_bit (BtorBitVector *bv, uint32_t pos);

/* Return true if given bit-vector represents true ('1'). */
bool btor_bv_is_true (const BtorBitVector *bv);
/* Return true if given bit-vector represents false ('0'). */
bool btor_bv_is_false (const BtorBitVector *bv);

/* Return true if given bit-vector represents 0 (all bits set to 0). */
bool btor_bv_is_zero (const BtorBitVector *bv);
/* Return true if given bit-vector represents ~0 (all bits set to 1). */
bool btor_bv_is_ones (const BtorBitVector *bv);
/* Return true if given bit-vector represents 1. */
bool btor_bv_is_one (const BtorBitVector *bv);
/* Return true if given bit-vector represents the min. signed value (10...0). */
bool btor_bv_is_min_signed (const BtorBitVector *bv);
/* Return true if given bit-vector represents the max. signed value (01...1). */
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

/* Create a bit-vector of given bit-width that represents 1. */
BtorBitVector *btor_bv_one (BtorMemMgr *mm, uint32_t bw);
/* Create a bit-vector of given bit-width that represents ~0. */
BtorBitVector *btor_bv_ones (BtorMemMgr *mm, uint32_t bw);

/**
 * Create a bit-vector of given bit-width that represents the minimum signed
 * value 10...0.
 */
BtorBitVector *btor_bv_min_signed (BtorMemMgr *mm, uint32_t bw);
/**
 * Create a bit-vector of given bit-width that represents the maximum signed
 * value 01...1.
 */
BtorBitVector *btor_bv_max_signed (BtorMemMgr *mm, uint32_t bw);

/* Create the negation (two's complement0 of the given bit-vector. */
BtorBitVector *btor_bv_neg (BtorMemMgr *mm, const BtorBitVector *bv);
/* Create the bit-wise negation of the given bit-vector. */
BtorBitVector *btor_bv_not (BtorMemMgr *mm, const BtorBitVector *bv);
/* Create the increment (+1) of the given bit-vector. */
BtorBitVector *btor_bv_inc (BtorMemMgr *mm, const BtorBitVector *bv);
/* Create the decrement (-1) of the given bit-vector. */
BtorBitVector *btor_bv_dec (BtorMemMgr *mm, const BtorBitVector *bv);

/* Create a bit-vector representing the redor of given bit-vector. */
BtorBitVector *btor_bv_redor (BtorMemMgr *mm, const BtorBitVector *bv);
/* Create a bit-vector representing the redand of given bit-vector. */
BtorBitVector *btor_bv_redand (BtorMemMgr *mm, const BtorBitVector *bv);

/* Create the addition of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_add (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the subtraction of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_sub (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the bit-wise and of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_and (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the boolean implication of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_implies (BtorMemMgr *mm,
                                const BtorBitVector *a,
                                const BtorBitVector *b);

/* Create the bit-wise nand of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_nand (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the bit-wise nor of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_nor (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the bit-wise or of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_or (BtorMemMgr *mm,
                           const BtorBitVector *a,
                           const BtorBitVector *b);

/* Create the bit-wise xnor of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_xnor (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the bit-wise xor of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_xor (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the equality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_eq (BtorMemMgr *mm,
                           const BtorBitVector *a,
                           const BtorBitVector *b);

/* Create the disequality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_ne (BtorMemMgr *mm,
                           const BtorBitVector *a,
                           const BtorBitVector *b);

/* Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_ult (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the signed less than or equal inequality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_ulte (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_ugt (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BtorBitVector *btor_bv_ugte (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_slt (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BtorBitVector *btor_bv_slte (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_sgt (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BtorBitVector *btor_bv_sgte (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the logical shift left of bit-vectors 'a' by 'shift'. */
BtorBitVector *btor_bv_sll_uint64 (BtorMemMgr *mm,
                                   const BtorBitVector *a,
                                   uint64_t shift);

/* Create the logical shift left of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_sll (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the logical shift right of bit-vectors 'a' by 'shift'. */
BtorBitVector *btor_bv_srl_uint64 (BtorMemMgr *mm,
                                   const BtorBitVector *a,
                                   uint64_t shift);

/* Create the logical shift right of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_srl (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the arithmetic shift right of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_sra (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the multiplication of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_mul (BtorMemMgr *mm,
                            const BtorBitVector *a,
                            const BtorBitVector *b);

/* Create the unsigned division of of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_udiv (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the unsigned remainder of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_urem (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the signed division of of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_sdiv (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the signed remainder of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_srem (BtorMemMgr *mm,
                             const BtorBitVector *a,
                             const BtorBitVector *b);

/* Create the if-then-else conditional c ? a : b. */
BtorBitVector *btor_bv_ite (BtorMemMgr *mm,
                            const BtorBitVector *c,
                            const BtorBitVector *t,
                            const BtorBitVector *e);

/* Create the concatenation of bit-vectors 'a' and 'b'. */
BtorBitVector *btor_bv_concat (BtorMemMgr *mm,
                               const BtorBitVector *a,
                               const BtorBitVector *b);

/* Create the slice from bit index upper to lower of given the bit-vector. */
BtorBitVector *btor_bv_slice (BtorMemMgr *mm,
                              const BtorBitVector *bv,
                              uint32_t upper,
                              uint32_t lower);

/* Create the unsigned/zero extension by 'len' bits of the given bit-vector. */
BtorBitVector *btor_bv_uext (BtorMemMgr *mm,
                             const BtorBitVector *bv0,
                             uint32_t len);

/* Create the signed extension by 'len' bits of the given bit-vector. */
BtorBitVector *btor_bv_sext (BtorMemMgr *mm,
                             const BtorBitVector *bv0,
                             uint32_t len);

/* Create a copy of given bit-vector with the bit at given index flipped. */
BtorBitVector *btor_bv_flipped_bit (BtorMemMgr *mm,
                                    const BtorBitVector *bv,
                                    uint32_t pos);

/**
 * Create a copy of given bit-vector with the bits at given index range
 * (from upper index 'up' to lower index 'lo') flipped.
 */
BtorBitVector *btor_bv_flipped_bit_range (BtorMemMgr *mm,
                                          const BtorBitVector *bv,
                                          uint32_t up,
                                          uint32_t lo);

/*------------------------------------------------------------------------*/

/* Return true if 'bv0' * 'bv1' produces an overflow. */
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

/**
 * Calculate modular inverse for given bit-vector by means of the Extended
 * Euclidian Algorithm.
 *
 * Note that c must be odd (the greatest common divisor gcd (c, 2^bw) must be
 * and is in this case always 1).
 */
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

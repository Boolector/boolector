/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2020 Mathias Preiner.
 *  Copyright (C) 2015-2020 Aina Niemetz.
 *  Copyright (C) 2018 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbv.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorcore.h"
#include "utils/btorutil.h"

#include <limits.h>

#ifdef BTOR_USE_GMP
#include <gmp.h>
#endif

/*------------------------------------------------------------------------*/

struct BtorBitVector
{
  uint32_t width; /* length of bit vector */
#ifdef BTOR_USE_GMP
  mpz_t val;
#else
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
#endif
};

/*------------------------------------------------------------------------*/

#define BTOR_MASK_REM_BITS(bv)                       \
  ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1) \
   >> (BTOR_BV_TYPE_BW - 1 - (bv->width % BTOR_BV_TYPE_BW)))

/*------------------------------------------------------------------------*/

#ifndef BTOR_USE_GMP
#ifndef NDEBUG
static bool
rem_bits_zero_dbg (BtorBitVector *bv)
{
  return (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
}
#endif

static void
set_rem_bits_to_zero (BtorBitVector *bv)
{
  if (bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
}
#endif

#ifndef NDEBUG
static bool
check_bits_sll_dbg (const BtorBitVector *bv,
                    const BtorBitVector *res,
                    uint32_t shift)
{
  assert (bv);
  assert (res);
  assert (bv->width == res->width);

  uint32_t i;

  if (shift >= bv->width)
  {
    for (i = 0; i < bv->width; i++) assert (btor_bv_get_bit (bv, i) == 0);
  }
  else
  {
    for (i = 0; shift + i < bv->width; i++)
      assert (btor_bv_get_bit (bv, i) == btor_bv_get_bit (res, shift + i));
  }

  return true;
}
#endif

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_new (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init (res->val);
#else
  uint32_t i;

  i = bw / BTOR_BV_TYPE_BW;
  if (bw % BTOR_BV_TYPE_BW > 0) i += 1;

  assert (i > 0);
  res =
      btor_mem_malloc (mm, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * i);
  BTOR_CLRN (res->bits, i);
  res->len = i;
  assert (res->len);
  res->width = bw;
  assert (res->width <= res->len * BTOR_BV_TYPE_BW);
#endif
  return res;
}

BtorBitVector *
btor_bv_new_random (BtorMemMgr *mm, BtorRNG *rng, uint32_t bw)
{
  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_urandomb (res->val, *((gmp_randstate_t *) rng->gmp_state), bw);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  res = btor_bv_new_random_bit_range (mm, rng, bw, bw - 1, 0);
#endif
  return res;
}

BtorBitVector *
btor_bv_new_random_range (BtorMemMgr *mm,
                          BtorRNG *rng,
                          uint32_t bw,
                          const BtorBitVector *from,
                          const BtorBitVector *to)
{
  assert (mm);
  assert (rng);
  assert (bw > 0);
  assert (bw == from->width);
  assert (from->width == to->width);
  assert (btor_bv_compare (from, to) <= 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  mpz_t n_to;

  res = btor_bv_new (mm, bw);
  mpz_init_set (n_to, to->val);
  mpz_sub (n_to, n_to, from->val);
  mpz_add_ui (n_to, n_to, 1);

  mpz_urandomm (res->val, *((gmp_randstate_t *) rng->gmp_state), n_to);
  mpz_add (res->val, res->val, from->val);
  mpz_clear (n_to);
#else
  BtorBitVector *resext, *fromext, *toext, *tmp1, *tmp2;

  /* we allow to = 1...1 */
  fromext = btor_bv_uext (mm, from, 1);
  toext   = btor_bv_uext (mm, to, 1);

  res    = btor_bv_new_random (mm, rng, bw);
  resext = btor_bv_uext (mm, res, 1);
  btor_bv_free (mm, res);

  tmp1 = btor_bv_inc (mm, toext);          // to + 1
  tmp2 = btor_bv_sub (mm, tmp1, fromext);  // to + 1 - from
  btor_bv_free (mm, tmp1);

  tmp1   = resext;
  resext = btor_bv_urem (mm, tmp1, tmp2);  // res %= to + 1 - from
  btor_bv_free (mm, tmp1);

  tmp1   = resext;
  resext = btor_bv_add (mm, tmp1, fromext);  // res += from

  btor_bv_free (mm, tmp1);
  btor_bv_free (mm, tmp2);
  btor_bv_free (mm, fromext);
  btor_bv_free (mm, toext);

  res = btor_bv_slice (mm, resext, from->width - 1, 0);
  btor_bv_free (mm, resext);
#endif
  return res;
}

BtorBitVector *
btor_bv_new_random_bit_range (
    BtorMemMgr *mm, BtorRNG *rng, uint32_t bw, uint32_t up, uint32_t lo)
{
  assert (mm);
  assert (rng);
  assert (bw > 0);
  assert (lo <= up);

  uint32_t i;
  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  res = btor_bv_new_random (mm, rng, bw);
#else
  res = btor_bv_new (mm, bw);
  for (i = 1; i < res->len; i++)
    res->bits[i] = (BTOR_BV_TYPE) btor_rng_rand (rng);
  res->bits[0] = (BTOR_BV_TYPE) btor_rng_pick_rand (
      rng, 0, ((~0) >> (BTOR_BV_TYPE_BW - bw % BTOR_BV_TYPE_BW)) - 1);
  set_rem_bits_to_zero (res);
#endif
  for (i = 0; i < lo; i++) btor_bv_set_bit (res, i, 0);
  for (i = up + 1; i < res->width; i++) btor_bv_set_bit (res, i, 0);

  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_char_to_bv (BtorMemMgr *mm, const char *assignment)
{
  assert (mm);
  assert (assignment);
  assert (strlen (assignment) > 0);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = strlen (assignment);
  mpz_init_set_str (res->val, assignment, 2);
#else
  res = btor_bv_const (mm, assignment, strlen (assignment));
#endif
  return res;
}

BtorBitVector *
btor_bv_uint64_to_bv (BtorMemMgr *mm, uint64_t value, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init_set_ui (res->val, value);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  res = btor_bv_new (mm, bw);
  assert (res->len > 0);
  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_int64_to_bv (BtorMemMgr *mm, int64_t value, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init_set_si (res->val, value);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  BtorBitVector *tmp;
  res = btor_bv_new (mm, bw);
  assert (res->len > 0);

  /* ensure that all bits > 64 are set to 1 in case of negative values */
  if (value < 0 && bw > 64)
  {
    tmp = btor_bv_not (mm, res);
    btor_bv_free (mm, res);
    res = tmp;
  }

  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_const (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (btor_util_check_bin_to_bv (mm, str, bw));

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init_set_str (res->val, str, 2);
#else
  uint32_t i, j, bit;
  res = btor_bv_new (mm, bw);
  for (i = 0; i < bw; i++)
  {
    j = bw - 1 - i;
    assert (str[j] == '0' || str[j] == '1');
    bit = str[j] == '0' ? 0 : 1;
    btor_bv_set_bit (res, i, bit);
  }
#endif
  return res;
}

BtorBitVector *
btor_bv_constd (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (btor_util_check_dec_to_bv (mm, str, bw));

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init_set_str (res->val, str, 10);
#else
  bool is_neg, is_min_val;
  BtorBitVector *tmp;
  char *bits;
  uint32_t size_bits;

  is_min_val = false;
  is_neg     = (str[0] == '-');
  bits       = btor_util_dec_to_bin_str (mm, is_neg ? str + 1 : str);
  size_bits  = strlen (bits);
  if (is_neg)
  {
    is_min_val = (bits[0] == '1');
    for (size_t i = 1; is_min_val && i < size_bits; i++)
      is_min_val = (bits[i] == '0');
  }
  assert (((is_neg && !is_min_val) || size_bits <= bw)
          && (!is_neg || is_min_val || size_bits + 1 <= bw));

  res = btor_bv_char_to_bv (mm, bits);
  btor_mem_freestr (mm, bits);
  assert (res->width == size_bits);
  /* zero-extend to bw */
  if (size_bits < bw)
  {
    tmp = btor_bv_uext (mm, res, bw - size_bits);
    btor_bv_free (mm, res);
    res = tmp;
  }
  if (is_neg)
  {
    tmp = btor_bv_neg (mm, res);
    btor_bv_free (mm, res);
    res = tmp;
  }
#endif
  return res;
}

BtorBitVector *
btor_bv_consth (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (btor_util_check_hex_to_bv (mm, str, bw));

  BtorBitVector *res;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init_set_str (res->val, str, 16);
#else
  BtorBitVector *tmp;
  char *bits;
  uint32_t size_bits;

  bits      = btor_util_hex_to_bin_str (mm, str);
  size_bits = strlen (bits);
  assert (size_bits <= bw);
  res = btor_bv_char_to_bv (mm, bits);
  btor_mem_freestr (mm, bits);
  assert (res->width == size_bits);
  /* zero-extend to bw */
  if (size_bits < bw)
  {
    tmp = btor_bv_uext (mm, res, bw - size_bits);
    btor_bv_free (mm, res);
    res = tmp;
  }
#endif
  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_get_assignment (BtorMemMgr *mm, BtorNode *exp)
{
  assert (mm);
  assert (exp);
  assert (!btor_node_is_proxy (exp));

  BtorBitVector *res;

  uint32_t i, j, width;
  int32_t bit;
  bool inv;
  BtorNode *real_exp;
  BtorAIGVec *av;
  BtorAIGMgr *amgr;

  exp      = btor_node_get_simplified (btor_node_real_addr (exp)->btor, exp);
  real_exp = btor_node_real_addr (exp);

  if (!real_exp->av)
    return btor_bv_new (mm, btor_node_bv_get_width (real_exp->btor, real_exp));

  amgr  = btor_get_aig_mgr (real_exp->btor);
  av    = real_exp->av;
  width = av->width;
  res   = btor_bv_new (mm, width);
  inv   = btor_node_is_inverted (exp);

  for (i = 0, j = width - 1; i < width; i++, j--)
  {
    bit = btor_aig_get_assignment (amgr, av->aigs[j]);
    if (inv) bit *= -1;
    assert (bit == -1 || bit == 1);
    btor_bv_set_bit (res, i, bit == 1 ? 1 : 0);
  }
  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_copy (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;

  res = btor_bv_new (mm, bv->width);
  assert (res->width == bv->width);
#ifdef BTOR_USE_GMP
  mpz_set (res->val, bv->val);
#else
  assert (res->len == bv->len);
  memcpy (res->bits, bv->bits, sizeof (*(bv->bits)) * bv->len);
#endif
  assert (btor_bv_compare (res, (BtorBitVector *) bv) == 0);
  return res;
}

/*------------------------------------------------------------------------*/

size_t
btor_bv_size (const BtorBitVector *bv)
{
  assert (bv);
  (void) bv;
  size_t res;
#ifdef BTOR_USE_GMP
  res = sizeof (BtorBitVector);
#else
  res = sizeof (BtorBitVector) + bv->len * sizeof (BTOR_BV_TYPE);
#endif
  return res;
}

void
btor_bv_free (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);
#ifdef BTOR_USE_GMP
  mpz_clear (bv->val);
  btor_mem_free (mm, bv, sizeof (BtorBitVector));
#else
  btor_mem_free (
      mm, bv, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * bv->len);
#endif
}

int32_t
btor_bv_compare (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);

  if (a->width != b->width) return -1;
#ifdef BTOR_USE_GMP
  return mpz_cmp (a->val, b->val);
#else
  uint32_t i;
  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;
  if (i == a->len) return 0;
  if (a->bits[i] > b->bits[i]) return 1;
  assert (a->bits[i] < b->bits[i]);
  return -1;
#endif
}

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};

#define NPRIMES ((uint32_t) (sizeof hash_primes / sizeof *hash_primes))

uint32_t
btor_bv_hash (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, j = 0, n, res = 0;
  uint32_t x, p0, p1;

  res = bv->width * hash_primes[j++];

#ifdef BTOR_USE_GMP
  // least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 0, n = mpz_size (bv->val); i < n; ++i)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    limb = mpz_getlimbn (bv->val, i);
    if (mp_bits_per_limb == 64)
    {
      uint32_t lo = (uint32_t) limb;
      uint32_t hi = (uint32_t) (limb >> 32);
      x           = lo ^ res;
      x           = ((x >> 16) ^ x) * p0;
      x           = ((x >> 16) ^ x) * p1;
      x           = ((x >> 16) ^ x);
      p0          = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      p1 = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      x = x ^ hi;
    }
    else
    {
      assert (mp_bits_per_limb == 32);
      x = res ^ limb;
    }
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
#else
  for (i = 0, j = 0, n = bv->len; i < n; i++)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    x   = bv->bits[i] ^ res;
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
#endif
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_bv_print_without_new_line (const BtorBitVector *bv)
{
  assert (bv);

  int64_t i;
  for (i = bv->width - 1; i >= 0; i--) printf ("%d", btor_bv_get_bit (bv, i));
}

void
btor_bv_print (const BtorBitVector *bv)
{
  btor_bv_print_without_new_line (bv);
  printf ("\n");
}

void
btor_bv_print_all (const BtorBitVector *bv)
{
  assert (bv);
  (void) bv;

#ifndef BTOR_USE_GMP
  int64_t i;
  for (i = BTOR_BV_TYPE_BW * bv->len - 1; i >= 0; i--)
  {
    if ((uint32_t) i == (BTOR_BV_TYPE_BW * bv->len + 1 - bv->width))
      printf ("|");
    if (i > 0 && (BTOR_BV_TYPE_BW * bv->len - 1 - i) % BTOR_BV_TYPE_BW == 0)
      printf (".");
    printf ("%d", btor_bv_get_bit (bv, i));
  }
  printf ("\n");
#endif
}

/*------------------------------------------------------------------------*/

char *
btor_bv_to_char (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  char *res;
  uint32_t bw = bv->width;

  BTOR_CNEWN (mm, res, bw + 1);
#ifdef BTOR_USE_GMP
  char *tmp     = mpz_get_str (0, 2, bv->val);
  uint32_t n    = strlen (tmp);
  uint32_t diff = bw - n;
  assert (n <= bw);
  memset (res, '0', diff);
  memcpy (res + diff, tmp, n);
  assert (strlen (res) == bw);
  free (tmp);
#else
  uint32_t i, bit;

  for (i = 0; i < bw; i++)
  {
    bit             = btor_bv_get_bit (bv, i);
    res[bw - 1 - i] = bit ? '1' : '0';
  }
  res[bw] = '\0';
#endif
  return res;
}

char *
btor_bv_to_hex_char (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  char *res;
  uint32_t len;

  len = (bv->width + 3) / 4;
  BTOR_CNEWN (mm, res, len + 1);

#ifdef BTOR_USE_GMP
  char *tmp     = mpz_get_str (0, 16, bv->val);
  uint32_t n    = strlen (tmp);
  uint32_t diff = len - n;
  assert (n <= len);
  memset (res, '0', diff);
  memcpy (res + diff, tmp, n);
  assert (strlen (res) == len);
  free (tmp);
#else
  uint32_t i, j, k, tmp;
  char ch;

  for (i = 0, j = len - 1; i < bv->width;)
  {
    tmp = btor_bv_get_bit (bv, i++);
    for (k = 1; i < bv->width && k <= 3; i++, k++)
      tmp |= btor_bv_get_bit (bv, i) << k;
    ch       = tmp < 10 ? '0' + tmp : 'a' + (tmp - 10);
    res[j--] = ch;
  }
#endif
  return res;
}

static uint32_t
get_first_one_bit_idx (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_scan1 (bv->val, 0);
#else
  uint32_t i;
  for (i = bv->width - 1; i < UINT32_MAX; i--)
  {
    if (btor_bv_get_bit (bv, i)) break;
    if (i == 0) return UINT32_MAX;
  }
  return i;
#endif
}

#ifdef BTOR_USE_GMP
static uint32_t
get_first_zero_bit_idx (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_scan0 (bv->val, 0);
#else
  uint32_t i;
  for (i = bv->width - 1; i < UINT32_MAX; i--)
  {
    if (!btor_bv_get_bit (bv, i)) break;
    if (i == 0) return UINT32_MAX;
  }
  return i;
#endif
}
#endif

char *
btor_bv_to_dec_char (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  char *res;

#ifdef BTOR_USE_GMP
  char *tmp = mpz_get_str (0, 10, bv->val);
  res       = btor_mem_strdup (mm, tmp);
  free (tmp);
#else
  BtorBitVector *tmp, *div, *rem, *ten;
  uint32_t i;
  char ch, *p, *q;
  BtorCharStack stack;

  if (btor_bv_is_zero (bv))
  {
    BTOR_CNEWN (mm, res, 2);
    res[0] = '0';
    return res;
  }

  BTOR_INIT_STACK (mm, stack);

  if (bv->width < 4)
  {
    ten = btor_bv_uint64_to_bv (mm, 10, 4);
    tmp = btor_bv_uext (mm, (BtorBitVector *) bv, 4 - bv->width);
  }
  else
  {
    ten = btor_bv_uint64_to_bv (mm, 10, bv->width);
    tmp = btor_bv_copy (mm, bv);
  }
  while (!btor_bv_is_zero (tmp))
  {
    div = btor_bv_udiv (mm, tmp, ten);
    rem = btor_bv_urem (mm, tmp, ten);
    ch  = 0;
    for (i = get_first_one_bit_idx (rem); i < UINT32_MAX; i--)
    {
      ch <<= 1;
      if (btor_bv_get_bit (rem, i)) ch += 1;
    }
    assert (ch < 10);
    ch += '0';
    BTOR_PUSH_STACK (stack, ch);
    btor_bv_free (mm, rem);
    btor_bv_free (mm, tmp);
    tmp = div;
  }
  btor_bv_free (mm, tmp);
  btor_bv_free (mm, ten);
  if (BTOR_EMPTY_STACK (stack)) BTOR_PUSH_STACK (stack, '0');
  BTOR_NEWN (mm, res, BTOR_COUNT_STACK (stack) + 1);
  q = res;
  p = stack.top;
  while (p > stack.start) *q++ = *--p;
  assert (res + BTOR_COUNT_STACK (stack) == q);
  *q = 0;
  assert ((uint32_t) BTOR_COUNT_STACK (stack) == strlen (res));
  BTOR_RELEASE_STACK (stack);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

uint64_t
btor_bv_to_uint64 (const BtorBitVector *bv)
{
  assert (bv);
  assert (bv->width <= sizeof (uint64_t) * 8);

  uint64_t res;

#ifdef BTOR_USE_GMP
  res = mpz_get_ui (bv->val);
#else
  assert (bv->len <= 2);
  uint32_t i;
  res = 0;
  for (i = 0; i < bv->len; i++)
    res |= ((uint64_t) bv->bits[i]) << (BTOR_BV_TYPE_BW * (bv->len - 1 - i));
#endif

  return res;
}

/*------------------------------------------------------------------------*/

uint32_t
btor_bv_get_width (const BtorBitVector *bv)
{
  assert (bv);
  return bv->width;
}

uint32_t
btor_bv_get_len (const BtorBitVector *bv)
{
  assert (bv);
  (void) bv;
#ifdef BTOR_USE_GMP
  return 0;
#else
  return bv->len;
#endif
}

uint32_t
btor_bv_get_bit (const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  return mpz_tstbit (bv->val, pos);
#else
  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;

  return (bv->bits[bv->len - 1 - i] >> j) & 1;
#endif
}

void
btor_bv_set_bit (BtorBitVector *bv, uint32_t pos, uint32_t bit)
{
  assert (bv);
  assert (bit == 0 || bit == 1);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  if (bit)
  {
    mpz_setbit (bv->val, pos);
  }
  else
  {
    mpz_clrbit (bv->val, pos);
  }
#else
  assert (bv->len > 0);
  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;
  assert (i < bv->len);

  if (bit)
  {
    bv->bits[bv->len - 1 - i] |= (1u << j);
  }
  else
  {
    bv->bits[bv->len - 1 - i] &= ~(1u << j);
  }
#endif
}

void
btor_bv_flip_bit (BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (pos < bv->width);

#ifdef BTOR_USE_GMP
  mpz_combit (bv->val, pos);
#else
  assert (bv->len > 0);
  btor_bv_set_bit (bv, pos, btor_bv_get_bit (bv, pos) ? 0 : 1);
#endif
}

/*------------------------------------------------------------------------*/

bool
btor_bv_is_true (const BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return btor_bv_get_bit (bv, 0);
}

bool
btor_bv_is_false (const BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return !btor_bv_get_bit (bv, 0);
}

bool
btor_bv_is_zero (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_cmp_ui (bv->val, 0) == 0;
#else
  uint32_t i;
  for (i = 0; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
#endif
}

bool
btor_bv_is_ones (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, n;
#ifdef BTOR_USE_GMP
  uint64_t m, max;
  mp_limb_t limb;
  if ((n = mpz_size (bv->val)) == 0) return false;  // zero
  m = bv->width / mp_bits_per_limb;
  if (bv->width % mp_bits_per_limb) m += 1;
  if (m != n) return false;  // less limbs used than expected, not ones
  max = mp_bits_per_limb == 64 ? UINT64_MAX : UINT32_MAX;
  for (i = 0; i < n - 1; i++)
  {
    limb = mpz_getlimbn (bv->val, i);
    if (((uint64_t) limb) != max) return false;
  }
  limb = mpz_getlimbn (bv->val, n - 1);
  if (bv->width == (uint32_t) mp_bits_per_limb)
    return ((uint64_t) limb) == max;
  m = mp_bits_per_limb - bv->width % mp_bits_per_limb;
  return ((uint64_t) limb) == (max >> m);
#else
  for (i = bv->len - 1; i >= 1; i--)
  {
    if (bv->bits[i] != UINT32_MAX) return false;
  }
  n = BTOR_BV_TYPE_BW - bv->width % BTOR_BV_TYPE_BW;
  assert (n > 0);
  if (n == BTOR_BV_TYPE_BW) return bv->bits[0] == UINT32_MAX;
  return bv->bits[0] == (UINT32_MAX >> n);
#endif
}

bool
btor_bv_is_one (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  return mpz_cmp_ui (bv->val, 1) == 0;
#else
  uint32_t i;
  if (bv->bits[bv->len - 1] != 1) return false;
  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return false;
  return true;
#endif
}

bool
btor_bv_is_min_signed (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  if (get_first_one_bit_idx (bv) != bv->width - 1) return false;
#else
  uint32_t i;
  if (bv->bits[0] != (1u << ((bv->width % BTOR_BV_TYPE_BW) - 1))) return false;
  for (i = 1; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
#endif
  return true;
}

bool
btor_bv_is_max_signed (const BtorBitVector *bv)
{
  assert (bv);

#ifdef BTOR_USE_GMP
  if (get_first_zero_bit_idx (bv) != bv->width - 1) return false;
#else
  uint32_t i, msc;

  msc = (BTOR_BV_TYPE_BW - (bv->width % BTOR_BV_TYPE_BW) + 1);
  if (msc == BTOR_BV_TYPE_BW)
  {
    if (bv->bits[0] != 0) return false;
  }
  else if (bv->bits[0] != (~0u >> msc))
  {
    return false;
  }
  for (i = 1; i < bv->len; i++)
    if (bv->bits[i] != ~0u) return false;
#endif
  return true;
}

int64_t
btor_bv_power_of_two (const BtorBitVector *bv)
{
  assert (bv);

  int64_t i, j;
  uint32_t bit;
  bool iszero;

  for (i = 0, j = 0, iszero = true; i < bv->width; i++)
  {
    bit = btor_bv_get_bit (bv, i);
    if (!bit) continue;
    if (bit && !iszero) return -1;
    assert (bit && iszero);
    j      = i;
    iszero = false;
  }
  return j;
}

int32_t
btor_bv_small_positive_int (const BtorBitVector *bv)
{
  assert (bv);

  int32_t res;
  uint32_t i, n;
#ifdef BTOR_USE_GMP
  if (!(n = mpz_size (bv->val))) return 0;
  mp_limb_t limb;
  for (i = 0; i < n; i++)
  {
    limb = mpz_getlimbn (bv->val, i);
    if (i == n - 1)
    {
      if (mp_bits_per_limb == 64)
      {
        if (limb >> 32 != 0)
        {
          return -1;
        }
      }
    }
    else
    {
      if (limb != 0)
      {
        return -1;
      }
    }
  }
  res = (int32_t) limb;
  if (res < 0) return -1;
#else
  for (i = 0, n = bv->len - 1; i < n; i++)
    if (bv->bits[i] != 0) return -1;
  if (((int32_t) bv->bits[bv->len - 1]) < 0) return -1;
  res = bv->bits[bv->len - 1];
#endif
  return res;
}

uint32_t
btor_bv_get_num_trailing_zeros (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t res = 0;
#ifdef BTOR_USE_GMP
  res = mpz_scan1(bv->val, 0);
  if (res > bv->width) res = bv->width;
#else
  uint32_t i;

  for (i = 0, res = 0; i < bv->width; i++)
  {
    if (btor_bv_get_bit (bv, i)) break;
    res += 1;
  }
#endif
  return res;
}

/**
 * Get the first limb and return the number of limbs needed to represented
 * given bit-vector if all zero limbs are disregarded.
 */
#ifdef BTOR_USE_GMP
static uint32_t
get_limb (const BtorBitVector *bv,
          mp_limb_t *limb,
          uint32_t nbits_rem,
          bool zeros)
{
  /* GMP normalizes the limbs, the left most (most significant) is never 0 */
  uint32_t i, n_limbs, n_limbs_total;
  mp_limb_t res = 0u, mask;

  n_limbs = mpz_size (bv->val);

  /* for leading zeros */
  if (zeros)
  {
    *limb = n_limbs ? mpz_getlimbn (bv->val, n_limbs - 1) : 0;
    return n_limbs;
  }

  /* for leading ones */
  n_limbs_total = bv->width / mp_bits_per_limb + (nbits_rem ? 1 : 0);
  if (n_limbs != n_limbs_total)
  {
    /* no leading ones, simulate */
    *limb = nbits_rem ? ~(~((mp_limb_t) 0) << nbits_rem) : ~((mp_limb_t) 0);
    return n_limbs_total;
  }
  mask = ~((mp_limb_t) 0) << nbits_rem;
  for (i = 0; i < n_limbs; i++)
  {
    res = mpz_getlimbn (bv->val, n_limbs - 1 - i);
    if (nbits_rem && i == 0)
    {
      res = res | mask;
    }
    res = ~res;
    if (res > 0) break;
  }
  *limb = res;
  return n_limbs - i;
}
#else
static uint32_t
get_limb (const BtorBitVector *bv,
          BTOR_BV_TYPE *limb,
          uint32_t nbits_rem,
          bool zeros)
{
  uint32_t i;
  BTOR_BV_TYPE res = 0u, mask;

  /* for leading zeros */
  if (zeros)
  {
    for (i = 0; i < bv->len; i++)
    {
      res = bv->bits[i];
      if (res > 0) break;
    }
  }
  /* for leading ones */
  else
  {
    mask = ~((BTOR_BV_TYPE) 0) << nbits_rem;
    for (i = 0; i < bv->len; i++)
    {
      res = bv->bits[i];
      if (nbits_rem && i == 0)
      {
        res = res | mask;
      }
      res = ~res;
      if (res > 0) break;
    }
  }

  *limb = res;
  return bv->len - i;
}
#endif

#if !defined(__GNUC__) && !defined(__clang__)
static uint32_t
#ifdef BTOR_USE_GMP
clz_limb (uint32_t nbits_per_limb, mp_limb_t limb)
#else
clz_limb (uint32_t nbits_per_limb, BTOR_BV_TYPE limb)
#endif
{
  uint32_t w;
#ifdef BTOR_USE_GMP
  mp_limb_t mask;
  mp_limb_t one = 1u;
#else
  BTOR_BV_TYPE mask;
  BTOR_BV_TYPE one = 1u;
#endif
  for (w = 0, mask = 0; w < nbits_per_limb; w++)
  {
    mask += (one << w);
    if ((limb & ~mask) == 0) break;
  }
  return nbits_per_limb - 1 - w;
}
#endif

static uint32_t
get_num_leading (const BtorBitVector *bv, bool zeros)
{
  assert (bv);

  uint32_t res = 0, nbits_pad;
  /* The number of limbs required to represent the actual value.
   * Zero limbs are disregarded. */
  uint32_t n_limbs;
  /* Number of limbs required when representing all bits. */
  uint32_t n_limbs_total;
  /* The number of bits that spill over into the most significant limb,
   * assuming that all bits are represented). Zero if the bit-width is a
   * multiple of n_bits_per_limb. */
  uint32_t nbits_rem;
  uint32_t nbits_per_limb;
#ifdef BTOR_USE_GMP
  mp_limb_t limb;
#else
  BTOR_BV_TYPE limb;
#endif

#ifdef BTOR_USE_GMP
  nbits_per_limb = mp_bits_per_limb;
#else
  nbits_per_limb = BTOR_BV_TYPE_BW;
#endif

  nbits_rem = bv->width % nbits_per_limb;

  n_limbs = get_limb (bv, &limb, nbits_rem, zeros);
  if (n_limbs == 0) return bv->width;

#if defined(__GNUC__) || defined(__clang__)
  res = nbits_per_limb == 64 ? __builtin_clzll (limb) : __builtin_clz (limb);
#else
  res = clz_limb (nbits_per_limb, limb);
#endif
  n_limbs_total = bv->width / nbits_per_limb + 1;
  nbits_pad     = nbits_per_limb - nbits_rem;
  res += (n_limbs_total - n_limbs) * nbits_per_limb - nbits_pad;
  return res;
}

uint32_t
btor_bv_get_num_leading_zeros (const BtorBitVector *bv)
{
  return get_num_leading (bv, true);
}

uint32_t
btor_bv_get_num_leading_ones (const BtorBitVector *bv)
{
  assert (bv);

  return get_num_leading (bv, false);
#if 0
  uint32_t res = 0;
  uint32_t i;

  for (i = bv->width - 1, res = 0; i < UINT32_MAX; i--)
  {
    if (!btor_bv_get_bit (bv, i)) break;
    res += 1;
  }
  return res;
#endif
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_one (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init_set_ui (res->val, 1);
#else
  res = btor_bv_new (mm, bw);
  btor_bv_set_bit (res, 0, 1);
#endif
  return res;
}

BtorBitVector *
btor_bv_ones (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_one (mm, bw);
  mpz_mul_2exp (res->val, res->val, bw);
  mpz_sub_ui (res->val, res->val, 1);
#else
  BtorBitVector *tmp;
  tmp = btor_bv_new (mm, bw);
  res = btor_bv_not (mm, tmp);
  btor_bv_free (mm, tmp);
#endif
  return res;
}

BtorBitVector *
btor_bv_min_signed (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res;
  res = btor_bv_new (mm, bw);
#ifdef BTOR_USE_GMP
  mpz_setbit (res->val, bw - 1);
#else
  btor_bv_set_bit (res, bw - 1, 1);
#endif
  return res;
}

BtorBitVector *
btor_bv_max_signed (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res;
  res = btor_bv_ones (mm, bw);
  btor_bv_set_bit (res, bw - 1, 0);
  return res;
}

BtorBitVector *
btor_bv_neg (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = bv->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_not (mm, bv);
  mpz_add_ui (res->val, res->val, 1);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  BtorBitVector *not_bv, *one;
  not_bv = btor_bv_not (mm, bv);
  one    = btor_bv_uint64_to_bv (mm, 1, bw);
  res    = btor_bv_add (mm, not_bv, one);
  btor_bv_free (mm, not_bv);
  btor_bv_free (mm, one);
#endif
  return res;
}

BtorBitVector *
btor_bv_not (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = bv->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_com (res->val, bv->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  uint32_t i;
  res = btor_bv_new (mm, bw);
  for (i = 0; i < bv->len; i++) res->bits[i] = ~bv->bits[i];
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_inc (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = bv->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_add_ui (res->val, bv->val, 1);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  BtorBitVector *one;
  one = btor_bv_uint64_to_bv (mm, 1, bw);
  res = btor_bv_add (mm, bv, one);
  btor_bv_free (mm, one);
#endif
  return res;
}

BtorBitVector *
btor_bv_dec (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = bv->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_sub_ui (res->val, bv->val, 1);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  BtorBitVector *one, *negone;
  one    = btor_bv_uint64_to_bv (mm, 1, bw);
  negone = btor_bv_neg (mm, one);
  res    = btor_bv_add (mm, bv, negone);
  btor_bv_free (mm, one);
  btor_bv_free (mm, negone);
#endif
  return res;
}

BtorBitVector *
btor_bv_redand (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_is_ones (bv) ? btor_bv_one (mm, 1) : btor_bv_zero (mm, 1);
#else
  uint32_t i;
  uint32_t bit;
  uint32_t mask0;

  res = btor_bv_new (mm, 1);
  assert (rem_bits_zero_dbg (res));

  if (bv->width == BTOR_BV_TYPE_BW * bv->len)
    mask0 = ~(BTOR_BV_TYPE) 0;
  else
    mask0 = BTOR_MASK_REM_BITS (bv);

  bit = (bv->bits[0] == mask0);

  for (i = 1; bit && i < bv->len; i++)
    if (bv->bits[i] != ~(BTOR_BV_TYPE) 0) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_redor (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

#ifdef BTOR_USE_GMP
  mp_limb_t limb;
  size_t i, n;
  for (i = 0, n = mpz_size (bv->val); i < n; i++)
  {
    limb = mpz_getlimbn (bv->val, i);
    if (((uint64_t) limb) != 0) return btor_bv_one (mm, 1);
  }
  return btor_bv_zero (mm, 1);
#else
  uint32_t i;
  uint32_t bit;
  BtorBitVector *res;

  res = btor_bv_new (mm, 1);
  assert (rem_bits_zero_dbg (res));
  bit = 0;
  for (i = 0; !bit && i < bv->len; i++)
    if (bv->bits[i]) bit = 1;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
  return res;
#endif
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_add (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_add (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  int64_t i;
  uint64_t x, y, sum;
  BTOR_BV_TYPE carry;

  if (bw <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (mm, x + y, bw);
  }
  else
  {
    res   = btor_bv_new (mm, bw);
    carry = 0;
    for (i = a->len - 1; i >= 0; i--)
    {
      sum          = (uint64_t) a->bits[i] + b->bits[i] + carry;
      res->bits[i] = (BTOR_BV_TYPE) sum;
      carry        = (BTOR_BV_TYPE) (sum >> 32);
    }
  }

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_sub (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  uint32_t bw = a->width;
  res         = btor_bv_new (mm, bw);
  mpz_sub (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  BtorBitVector *negb;

  negb = btor_bv_neg (mm, b);
  res  = btor_bv_add (mm, a, negb);
  btor_bv_free (mm, negb);
#endif
  return res;
}

BtorBitVector *
btor_bv_and (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_and (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] & b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_implies (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);
  assert (a->width == 1);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_is_zero (a) || btor_bv_is_one (b) ? btor_bv_one (mm, 1)
                                                  : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = ~a->bits[i] | b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_or (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_ior (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] | b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_nand (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_and (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] & b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_nor (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_ior (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] | b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_xnor (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_xor (res->val, a->val, b->val);
  mpz_com (res->val, res->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] ^ ~b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_xor (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_xor (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] ^ b->bits[i];

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_eq (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) == 0 ? btor_bv_one (mm, 1)
                                      : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (mm, 1);
  bit = 1;
  for (i = 0; i < a->len; i++)
  {
    if (a->bits[i] != b->bits[i])
    {
      bit = 0;
      break;
    }
  }
  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_ne (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) != 0 ? btor_bv_one (mm, 1)
                                      : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (mm, 1);
  bit = 1;
  for (i = 0; i < a->len; i++)
  {
    if (a->bits[i] != b->bits[i])
    {
      bit = 0;
      break;
    }
  }
  btor_bv_set_bit (res, 0, !bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_ult (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res =
      mpz_cmp (a->val, b->val) < 0 ? btor_bv_one (mm, 1) : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a >= b */
  if (i == a->len || a->bits[i] >= b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_ulte (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) <= 0 ? btor_bv_one (mm, 1)
                                      : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a > b */
  if (i < a->len && a->bits[i] > b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_ugt (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res =
      mpz_cmp (a->val, b->val) > 0 ? btor_bv_one (mm, 1) : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a <= b */
  if (i == a->len || a->bits[i] <= b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_ugte (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = mpz_cmp (a->val, b->val) >= 0 ? btor_bv_one (mm, 1)
                                      : btor_bv_zero (mm, 1);
#else
  assert (a->len == b->len);
  uint32_t i, bit;

  res = btor_bv_new (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a < b */
  if (i < a->len && a->bits[i] < b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_slt (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_one (mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_zero (mm, 1);
  }
  else
  {
    res = btor_bv_ult (mm, a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_slte (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_one (mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_zero (mm, 1);
  }
  else
  {
    res = btor_bv_ulte (mm, a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_sgt (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_zero (mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_one (mm, 1);
  }
  else
  {
    res = btor_bv_ugt (mm, a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_sgte (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = btor_bv_get_bit (a, bw - 1);
  msb_b = btor_bv_get_bit (b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = btor_bv_zero (mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = btor_bv_one (mm, 1);
  }
  else
  {
    res = btor_bv_ugte (mm, a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_sll_uint64 (BtorMemMgr *mm, const BtorBitVector *a, uint64_t shift)
{
  assert (mm);
  assert (a);

  BtorBitVector *res;
  uint32_t bw = a->width;

  res = btor_bv_new (mm, bw);
  if (shift >= bw) return res;

#ifdef BTOR_USE_GMP
  mpz_mul_2exp (res->val, a->val, shift);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  uint32_t skip, i, j, k;
  BTOR_BV_TYPE v;

  k    = shift % BTOR_BV_TYPE_BW;
  skip = shift / BTOR_BV_TYPE_BW;

  v = 0;
  for (i = a->len - 1, j = res->len - 1 - skip;; i--, j--)
  {
    v            = (k == 0) ? a->bits[i] : v | (a->bits[i] << k);
    res->bits[j] = v;
    v            = (k == 0) ? a->bits[i] : a->bits[i] >> (BTOR_BV_TYPE_BW - k);
    if (i == 0 || j == 0) break;
  }
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
#endif
  assert (check_bits_sll_dbg (a, res, shift));
  return res;
}

static bool
shift_is_uint64 (BtorMemMgr *mm,
                 const BtorBitVector *b,
                 uint64_t *res)
{
  assert (mm);
  assert (b);
  assert (res);

  uint64_t zeroes;
  BtorBitVector *shift;

  if (b->width <= 64)
  {
    *res = btor_bv_to_uint64 (b);
    return true;
  }

  zeroes = btor_bv_get_num_leading_zeros (b);
  if (zeroes < b->width - 64) return false;

  shift =
      btor_bv_slice (mm, b, zeroes < b->width ? b->width - 1 - zeroes : 0, 0);
  assert (shift->width <= 64);
  *res = btor_bv_to_uint64 (shift);
  btor_bv_free (mm, shift);
  return true;
}

BtorBitVector *
btor_bv_sll (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  uint64_t ushift;

  if (shift_is_uint64 (mm, b, &ushift))
  {
    return btor_bv_sll_uint64 (mm, a, ushift);
  }
  return btor_bv_new (mm, a->width);
}

BtorBitVector *
btor_bv_sra (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  if (btor_bv_get_bit (a, a->width - 1))
  {
    BtorBitVector *not_a       = btor_bv_not (mm, a);
    BtorBitVector *not_a_srl_b = btor_bv_srl (mm, not_a, b);
    res                        = btor_bv_not (mm, not_a_srl_b);
    btor_bv_free (mm, not_a);
    btor_bv_free (mm, not_a_srl_b);
  }
  else
  {
    res = btor_bv_srl (mm, a, b);
  }
#ifndef BTOR_USE_GMP
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_srl_uint64 (BtorMemMgr *mm, const BtorBitVector *a, uint64_t shift)
{
  assert (mm);
  assert (a);

  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  if (shift >= a->width) return res;
#ifdef BTOR_USE_GMP
  mpz_fdiv_q_2exp (res->val, a->val, shift);
#else
  uint32_t skip, i, j, k;
  BTOR_BV_TYPE v;
  k = shift % BTOR_BV_TYPE_BW;
  skip = shift / BTOR_BV_TYPE_BW;
  v = 0;
  for (i = 0, j = skip; i < a->len && j < a->len; i++, j++)
  {
    v = (k == 0) ? a->bits[i] : v | (a->bits[i] >> k);
    res->bits[j] = v;
    v = (k == 0) ? a->bits[i] : a->bits[i] << (BTOR_BV_TYPE_BW - k);
  }
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_srl (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  uint64_t ushift;

  if (shift_is_uint64 (mm, b, &ushift))
  {
    return btor_bv_srl_uint64 (mm, a, ushift);
  }
  return btor_bv_new (mm, a->width);
}

BtorBitVector *
btor_bv_mul (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
  uint32_t bw = a->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_mul (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  uint32_t i;
  uint64_t x, y;
  BtorBitVector *and, *shift, *add;

  if (bw <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (mm, x * y, bw);
  }
  else
  {
    res = btor_bv_new (mm, bw);
    for (i = 0; i < bw; i++)
    {
      if (btor_bv_get_bit (b, i))
        and = btor_bv_copy (mm, a);
      else
        and = btor_bv_new (mm, bw);
      shift = btor_bv_sll_uint64 (mm, and, i);
      add   = btor_bv_add (mm, res, shift);
      btor_bv_free (mm, and);
      btor_bv_free (mm, shift);
      btor_bv_free (mm, res);
      res = add;
    }
  }
#endif
  return res;
}

#ifndef BTOR_USE_GMP
static void
udiv_urem_bv (BtorMemMgr *mm,
              const BtorBitVector *a,
              const BtorBitVector *b,
              BtorBitVector **q,
              BtorBitVector **r)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  assert (a->len == b->len);
  int64_t i;
  bool is_true;
  uint64_t x, y, z;
  uint32_t bw = a->width;

  BtorBitVector *neg_b, *quot, *rem, *ult, *eq, *tmp;

  if (bw <= 64)
  {
    x = btor_bv_to_uint64 (a);
    y = btor_bv_to_uint64 (b);
    if (y == 0)
    {
      y = x;
      x = UINT64_MAX;
    }
    else
    {
      z = x / y;
      y = x % y;
      x = z;
    }
    quot = btor_bv_uint64_to_bv (mm, x, bw);
    rem  = btor_bv_uint64_to_bv (mm, y, bw);
  }
  else
  {
    neg_b = btor_bv_neg (mm, b);
    quot  = btor_bv_new (mm, bw);
    rem   = btor_bv_new (mm, bw);

    for (i = bw - 1; i >= 0; i--)
    {
      tmp = btor_bv_sll_uint64 (mm, rem, 1);
      btor_bv_free (mm, rem);
      rem = tmp;
      btor_bv_set_bit (rem, 0, btor_bv_get_bit (a, i));

      ult     = btor_bv_ult (mm, b, rem);
      is_true = btor_bv_is_true (ult);
      btor_bv_free (mm, ult);

      if (is_true) goto UDIV_UREM_SUBTRACT;

      eq      = btor_bv_eq (mm, b, rem);
      is_true = btor_bv_is_true (eq);
      btor_bv_free (mm, eq);

      if (is_true)
      {
      UDIV_UREM_SUBTRACT:
        tmp = btor_bv_add (mm, rem, neg_b);
        btor_bv_free (mm, rem);
        rem = tmp;
        btor_bv_set_bit (quot, i, 1);
      }
    }
    btor_bv_free (mm, neg_b);
  }

  if (q)
    *q = quot;
  else
    btor_bv_free (mm, quot);

  if (r)
    *r = rem;
  else
    btor_bv_free (mm, rem);
}
#endif

BtorBitVector *
btor_bv_udiv (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  uint32_t bw = a->width;
  if (btor_bv_is_zero (b)) return btor_bv_ones (mm, bw);
  res = btor_bv_new (mm, bw);
  mpz_fdiv_q (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  udiv_urem_bv (mm, a, b, &res, 0);
  assert (res);
#endif
  return res;
}

BtorBitVector *
btor_bv_urem (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  uint32_t bw = a->width;
  if (btor_bv_is_zero (b)) return btor_bv_copy (mm, a);
  res = btor_bv_new (mm, bw);
  mpz_fdiv_r (res->val, a->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  assert (a->len == b->len);
  udiv_urem_bv (mm, a, b, 0, &res);
  assert (res);
#endif
  return res;
}

BtorBitVector *
btor_bv_sdiv (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  bool is_signed_a, is_signed_b;
  uint32_t bw;
  BtorBitVector *res, *div, *neg_a, *neg_b;

  bw          = a->width;
  is_signed_a = btor_bv_get_bit (a, bw - 1);
  is_signed_b = btor_bv_get_bit (b, bw - 1);

  if (is_signed_a && !is_signed_b)
  {
    neg_a = btor_bv_neg (mm, a);
    div   = btor_bv_udiv (mm, neg_a, b);
    res   = btor_bv_neg (mm, div);
    btor_bv_free (mm, neg_a);
    btor_bv_free (mm, div);
  }
  else if (!is_signed_a && is_signed_b)
  {
    neg_b = btor_bv_neg (mm, b);
    div   = btor_bv_udiv (mm, a, neg_b);
    res   = btor_bv_neg (mm, div);
    btor_bv_free (mm, neg_b);
    btor_bv_free (mm, div);
  }
  else if (is_signed_a && is_signed_b)
  {
    neg_a = btor_bv_neg (mm, a);
    neg_b = btor_bv_neg (mm, b);
    res   = btor_bv_udiv (mm, neg_a, neg_b);
    btor_bv_free (mm, neg_a);
    btor_bv_free (mm, neg_b);
  }
  else
  {
    res = btor_bv_udiv (mm, a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_srem (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);

  bool is_signed_a, is_signed_b;
  uint32_t bw;
  BtorBitVector *res, *rem, *neg_a, *neg_b;

  bw          = a->width;
  is_signed_a = btor_bv_get_bit (a, bw - 1);
  is_signed_b = btor_bv_get_bit (b, bw - 1);

  if (is_signed_a && !is_signed_b)
  {
    neg_a = btor_bv_neg (mm, a);
    rem   = btor_bv_urem (mm, neg_a, b);
    res   = btor_bv_neg (mm, rem);
    btor_bv_free (mm, neg_a);
    btor_bv_free (mm, rem);
  }
  else if (!is_signed_a && is_signed_b)
  {
    neg_b = btor_bv_neg (mm, b);
    res   = btor_bv_urem (mm, a, neg_b);
    btor_bv_free (mm, neg_b);
  }
  else if (is_signed_a && is_signed_b)
  {
    neg_a = btor_bv_neg (mm, a);
    neg_b = btor_bv_neg (mm, b);
    rem   = btor_bv_urem (mm, neg_a, neg_b);
    res   = btor_bv_neg (mm, rem);
    btor_bv_free (mm, neg_a);
    btor_bv_free (mm, neg_b);
    btor_bv_free (mm, rem);
  }
  else
  {
    res = btor_bv_urem (mm, a, b);
  }
  return res;
}

BtorBitVector *
btor_bv_concat (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);

  BtorBitVector *res;
  uint32_t bw = a->width + b->width;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_mul_2exp (res->val, a->val, b->width);
  mpz_add (res->val, res->val, b->val);
  mpz_fdiv_r_2exp (res->val, res->val, bw);
#else
  int64_t i, j, k;
  BTOR_BV_TYPE v;

  res = btor_bv_new (mm, bw);

  j = res->len - 1;

  /* copy bits from bit vector b */
  for (i = b->len - 1; i >= 0; i--) res->bits[j--] = b->bits[i];

  k = b->width % BTOR_BV_TYPE_BW;

  /* copy bits from bit vector a */
  if (k == 0)
  {
    assert (j >= 0);
    for (i = a->len - 1; i >= 0; i--) res->bits[j--] = a->bits[i];
  }
  else
  {
    j += 1;
    assert (res->bits[j] >> k == 0);
    v = res->bits[j];
    for (i = a->len - 1; i >= 0; i--)
    {
      v = v | (a->bits[i] << k);
      assert (j >= 0);
      res->bits[j--] = v;
      v              = a->bits[i] >> (BTOR_BV_TYPE_BW - k);
    }
    assert (j <= 0);
    if (j == 0) res->bits[j] = v;
  }

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_slice (BtorMemMgr *mm,
               const BtorBitVector *bv,
               uint32_t upper,
               uint32_t lower)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw = upper - lower + 1;
#ifdef BTOR_USE_GMP
  res = btor_bv_new (mm, bw);
  mpz_fdiv_r_2exp (res->val, bv->val, upper + 1);
  mpz_fdiv_q_2exp (res->val, res->val, lower);
#else
  uint32_t i, j;

  res = btor_bv_new (mm, bw);
  for (i = lower, j = 0; i <= upper; i++)
    btor_bv_set_bit (res, j++, btor_bv_get_bit (bv, i));

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_sext (BtorMemMgr *mm, const BtorBitVector *bv, uint32_t len)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw;

  if (len == 0)
  {
    return btor_bv_copy (mm, bv);
  }

  bw = bv->width;
#ifdef BTOR_USE_GMP
  if (btor_bv_get_bit (bv, bw - 1))
  {
    size_t i, n;
    res = btor_bv_copy (mm, bv);
    res->width += len;
    for (i = bw, n = bw + len; i < n; i++) mpz_setbit (res->val, i);
  }
  else
  {
    res = btor_bv_uext (mm, bv, len);
  }
#else
  BtorBitVector *tmp;
  tmp = btor_bv_get_bit (bv, bw - 1) ? btor_bv_ones (mm, len)
                                     : btor_bv_zero (mm, len);
  res = btor_bv_concat (mm, tmp, bv);
  btor_bv_free (mm, tmp);
  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_uext (BtorMemMgr *mm, const BtorBitVector *bv, uint32_t len)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;
  uint32_t bw;

  if (len == 0)
  {
    return btor_bv_copy (mm, bv);
  }

  bw  = bv->width + len;
  res = btor_bv_new (mm, bw);
#ifdef BTOR_USE_GMP
  mpz_set (res->val, bv->val);
#else
  memcpy (
      res->bits + res->len - bv->len, bv->bits, sizeof (*(bv->bits)) * bv->len);
#endif
  return res;
}

BtorBitVector *
btor_bv_ite (BtorMemMgr *mm,
             const BtorBitVector *c,
             const BtorBitVector *t,
             const BtorBitVector *e)
{
  assert (c);
  assert (t);
  assert (e);
  assert (t->width == e->width);

  BtorBitVector *res;
#ifdef BTOR_USE_GMP
  res = btor_bv_is_one (c) ? btor_bv_copy (mm, t) : btor_bv_copy (mm, e);
#else
  assert (c->len == 1);
  assert (t->len > 0);
  assert (t->len == e->len);
  BTOR_BV_TYPE cc, nn;
  uint32_t i;

  cc = btor_bv_get_bit (c, 0) ? (~(BTOR_BV_TYPE) 0) : 0;
  nn = ~cc;

  res = btor_bv_new (mm, t->width);
  for (i = 0; i < t->len; i++)
    res->bits[i] = (cc & t->bits[i]) | (nn & e->bits[i]);

  assert (rem_bits_zero_dbg (res));
#endif
  return res;
}

BtorBitVector *
btor_bv_flipped_bit (BtorMemMgr *mm, const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (pos < bv->width);

  BtorBitVector *res;
  res = btor_bv_copy (mm, bv);
  btor_bv_flip_bit (res, pos);
  return res;
}

BtorBitVector *
btor_bv_flipped_bit_range (BtorMemMgr *mm,
                           const BtorBitVector *bv,
                           uint32_t upper,
                           uint32_t lower)
{
  assert (mm);
  assert (lower <= upper);
  assert (upper < bv->width);

  BtorBitVector *res;
  uint32_t i;

  res = btor_bv_copy (mm, bv);
  for (i = lower; i <= upper; i++)
    btor_bv_set_bit (res, i, btor_bv_get_bit (res, i) ? 0 : 1);
  return res;
}

/*------------------------------------------------------------------------*/

bool
btor_bv_is_umulo (BtorMemMgr *mm,
                  const BtorBitVector *a,
                  const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->width == b->width);
#ifndef BTOR_USE_GMP
  assert (a->len == b->len);
#endif

  bool res = false;
  uint32_t bw = a->width;

  if (a->width > 1)
  {
#ifdef BTOR_USE_GMP
    (void) mm;
    mpz_t mul;
    mpz_init (mul);
    mpz_mul (mul, a->val, b->val);
    mpz_fdiv_q_2exp (mul, mul, bw);
    res = mpz_cmp_ui (mul, 0) != 0;
    mpz_clear (mul);
#else
    BtorBitVector *aext, *bext, *mul, *o;
    aext = btor_bv_uext (mm, a, bw);
    bext = btor_bv_uext (mm, b, bw);
    mul  = btor_bv_mul (mm, aext, bext);
    o    = btor_bv_slice (mm, mul, mul->width - 1, bw);
    if (!btor_bv_is_zero (o)) res = true;
    btor_bv_free (mm, aext);
    btor_bv_free (mm, bext);
    btor_bv_free (mm, mul);
    btor_bv_free (mm, o);
#endif
  }
  return res;
}

/*------------------------------------------------------------------------*/

#if 0
BtorBitVector *
btor_bv_gcd_ext (Btor * btor,
		 const BtorBitVector * bv1,
		 const BtorBitVector * bv2,
		 BtorBitVector ** fx,
		 BtorBitVector ** fy)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (btor_bv_compare (bv1, bv2) <= 0);
  assert (fx);
  assert (fy);

  BtorBitVector *a, *b, *x, *y, *lx, *ly, *gcd = 0;
  BtorBitVector *zero, *mul, *neg, *tx, *ty, *r, *q = 0;

  zero = btor_bv_new (btor->mm, bv1->width);

  a = btor_bv_copy (btor->mm, bv1);
  b = btor_bv_copy (btor->mm, bv2);

  x = btor_bv_copy (btor->mm, zero);            // 0
  y = btor_bv_flipped_bit (btor->mm, zero, 0);  // 1

  lx = btor_bv_flipped_bit (btor->mm, zero, 0); // 1
  ly = btor_bv_copy (btor->mm, zero);           // 0

  r = btor_bv_copy (btor->mm, bv1);

  while (btor_bv_compare (b, zero) > 0)
    {
      if (gcd) btor_bv_free (btor->mm, gcd);
      gcd = btor_bv_copy (btor->mm, r);

      btor_bv_free (btor->mm, r);
      r = btor_bv_urem (btor->mm, a, b);    // r = a % b

      if (q) btor_bv_free (btor->mm, q);
      q = btor_bv_udiv (btor->mm, a, b);    // q = a / b

      btor_bv_free (btor->mm, a);
      a = btor_bv_copy (btor->mm, b);       // a = b
      btor_bv_free (btor->mm, b);
      b = btor_bv_copy (btor->mm, r);       // b = r

      tx = btor_bv_copy (btor->mm, x);      // tx = x
      mul = btor_bv_mul (btor->mm, x, q);
      neg = btor_bv_neg (btor->mm, mul);
      btor_bv_free (btor->mm, x);
      x = btor_bv_add (btor->mm, lx, neg);  // x = lx - x * q
      btor_bv_free (btor->mm, neg);
      btor_bv_free (btor->mm, mul);
      btor_bv_free (btor->mm, lx);
      lx = tx;                              // lx = tx

      ty = btor_bv_copy (btor->mm, y);      // ty = y
      mul = btor_bv_mul (btor->mm, y, q);
      neg = btor_bv_neg (btor->mm, mul);
      btor_bv_free (btor->mm, y);
      y = btor_bv_add (btor->mm, ly, neg);  // y = ly - y * q
      btor_bv_free (btor->mm, neg);
      btor_bv_free (btor->mm, mul);
      btor_bv_free (btor->mm, ly);
      ly = ty;                              // ly = ty
    }

  *fx = lx;
  *fy = ly;
  btor_bv_free (btor->mm, r);
  btor_bv_free (btor->mm, q);
  btor_bv_free (btor->mm, a);
  btor_bv_free (btor->mm, b);
  btor_bv_free (btor->mm, x);
  btor_bv_free (btor->mm, y);
  btor_bv_free (btor->mm, zero);
  return gcd;
}
#endif

/* Calculate modular inverse for bv by means of the Extended Euclidian
 * Algorithm. Note that c must be odd (the greatest
 * common divisor gcd (c, 2^bw) must be and is in this case always 1).  */
BtorBitVector *
btor_bv_mod_inverse (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);
  assert (btor_bv_get_bit (bv, 0)); /* bv must be odd */

  /* a = 2^bw
   * b = bv
   * lx * a + ly * b = gcd (a, b) = 1
   * -> lx * a = lx * 2^bw = 0 (2^bw_[bw] = 0)
   * -> ly * b = bv^-1 * bv = 1
   * -> ly is modular inverse of bv */

  BtorBitVector *res;
  uint32_t bw;

  bw = bv->width;

#ifdef BTOR_USE_GMP
  BTOR_NEW (mm, res);
  res->width = bw;
#if 1
  if (bw == 1)
  {
    mpz_init_set_ui (res->val, 1);
  }
  else
  {
    mpz_t twobw;
    mpz_init (twobw);
    mpz_init (res->val);
    mpz_setbit (twobw, bw);
    mpz_invert (res->val, bv->val, twobw);
    mpz_fdiv_r_2exp (res->val, res->val, bw);
    mpz_clear (twobw);
  }
#else
  uint32_t ebw = bw + 1;
  mpz_t a, b, y, ty, q, yq, r;

  BTOR_NEW (mm, res);
  res->width = bw;
  mpz_init (res->val);

  mpz_init (a);
  mpz_setbit (a, bw); /* 2^bw */

  mpz_init_set (b, bv->val);

  mpz_init_set_ui (y, 1);
  mpz_init (ty);
  mpz_init (yq);

  mpz_init (q);
  mpz_init (r);

  while (mpz_cmp_ui (b, 0))
  {
    mpz_tdiv_qr (q, r, a, b);
    mpz_fdiv_r_2exp (q, q, ebw);
    mpz_fdiv_r_2exp (r, r, ebw);

    mpz_set (a, b);
    mpz_set (b, r);
    mpz_set (ty, y);
    mpz_mul (yq, y, q);
    mpz_fdiv_r_2exp (yq, yq, ebw);
    mpz_sub (y, res->val, yq);      /* y = ly - y * q */
    mpz_fdiv_r_2exp (y, y, ebw);
    mpz_set (res->val, ty);
  }
  mpz_fdiv_r_2exp (res->val, res->val, bw);

  mpz_clear (a);
  mpz_clear (b);
  mpz_clear (y);
  mpz_clear (ty);
  mpz_clear (yq);
  mpz_clear (q);
  mpz_clear (r);
#endif

#ifndef NDEBUG
  mpz_t ty;
  assert (res->width == bv->width);
  mpz_init (ty);
  mpz_mul (ty, bv->val, res->val);
  mpz_fdiv_r_2exp (ty, ty, bw);
  assert (!mpz_cmp_ui (ty, 1));
  mpz_clear (ty);
#endif
#else
  uint32_t i;
  BtorBitVector *a, *b, *y, *ly, *ty, *q, *yq, *r;
  uint32_t ebw = bw + 1;

  a = btor_bv_new (mm, ebw);
  btor_bv_set_bit (a, bw, 1); /* 2^bw */

  b = btor_bv_new (mm, ebw); /* extend to bw of a */
  for (i = 0; i < bw; i++) btor_bv_set_bit (b, i, btor_bv_get_bit (bv, i));

  y  = btor_bv_one (mm, ebw);
  ly = btor_bv_new (mm, ebw);

  while (!btor_bv_is_zero (b))
  {
    udiv_urem_bv (mm, a, b, &q, &r);

    btor_bv_free (mm, a);

    a = b;
    b = r;

    ty = y;
    yq = btor_bv_mul (mm, y, q);
    btor_bv_free (mm, q);
    y = btor_bv_sub (mm, ly, yq); /* y = ly - y * q */
    btor_bv_free (mm, yq);

    btor_bv_free (mm, ly);
    ly = ty;
  }

  res = btor_bv_slice (mm, ly, bv->width - 1, 0);

#ifndef NDEBUG
  assert (res->width == bv->width);
  ty = btor_bv_mul (mm, bv, res);
  assert (btor_bv_is_one (ty));
  btor_bv_free (mm, ty);
#endif
  btor_bv_free (mm, ly);
  btor_bv_free (mm, y);
  btor_bv_free (mm, b);
  btor_bv_free (mm, a);
#endif

  return res;
}

/*------------------------------------------------------------------------*/

BtorSpecialConstBitVector
btor_bv_is_special_const (const BtorBitVector *bv)
{
  assert (bv);

  if (btor_bv_is_zero (bv)) return BTOR_SPECIAL_CONST_BV_ZERO;
  if (btor_bv_is_one (bv))
    return bv->width == 1 ? BTOR_SPECIAL_CONST_BV_ONE_ONES
                          : BTOR_SPECIAL_CONST_BV_ONE;
  if (btor_bv_is_ones (bv))
  {
    assert (bv->width > 1);
    return BTOR_SPECIAL_CONST_BV_ONES;
  }
  return BTOR_SPECIAL_CONST_BV_NONE;
}

/*------------------------------------------------------------------------*/

BtorBitVectorTuple *
btor_bv_new_tuple (BtorMemMgr *mm, uint32_t arity)
{
  assert (mm);

  BtorBitVectorTuple *res = 0;

  BTOR_CNEW (mm, res);
  if (arity) BTOR_CNEWN (mm, res->bv, arity);
  res->arity = arity;
  return res;
}

void
btor_bv_add_to_tuple (BtorMemMgr *mm,
                      BtorBitVectorTuple *t,
                      const BtorBitVector *bv,
                      uint32_t pos)
{
  assert (mm);
  assert (t);
  assert (bv);
  assert (pos < t->arity);
  assert (!t->bv[pos]);
  t->bv[pos] = btor_bv_copy (mm, bv);
}

void
btor_bv_free_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t)
{
  assert (mm);
  assert (t);

  uint32_t i;

  if (t->arity)
  {
    for (i = 0; i < t->arity; i++) btor_bv_free (mm, t->bv[i]);
    btor_mem_free (mm, t->bv, sizeof (BtorBitVectorTuple *) * t->arity);
  }
  btor_mem_free (mm, t, sizeof (BtorBitVectorTuple));
}

int32_t
btor_bv_compare_tuple (const BtorBitVectorTuple *t0,
                       const BtorBitVectorTuple *t1)
{
  assert (t0);
  assert (t1);

  uint32_t i;
  if (t0->arity != t1->arity) return -1;

  for (i = 0; i < t0->arity; i++)
  {
    assert (t0->bv[i]);
    assert (t1->bv[i]);
    if (t0->bv[i]->width != t1->bv[i]->width
        || btor_bv_compare (t0->bv[i], t1->bv[i]) != 0)
      return 1;
  }
  return 0;
}

uint32_t
btor_bv_hash_tuple (const BtorBitVectorTuple *t)
{
  assert (t);

  uint32_t hash = 0;
  uint32_t i, j = 0;

  for (i = 0; i < t->arity; i++)
  {
    assert (t->bv[i]);
    hash += btor_bv_hash (t->bv[i]) * hash_primes[j++];
    if (j == NPRIMES) j = 0;
  }
  return hash;
}

BtorBitVectorTuple *
btor_bv_copy_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t)
{
  assert (mm);
  assert (t);

  BtorBitVectorTuple *res = 0;
  uint32_t i;

  res = btor_bv_new_tuple (mm, t->arity);

  for (i = 0; i < t->arity; i++)
  {
    assert (t->bv[i]);
    res->bv[i] = btor_bv_copy (mm, t->bv[i]);
  }
  return res;
}

size_t
btor_bv_size_tuple (BtorBitVectorTuple *t)
{
  assert (t);

  uint32_t i;
  size_t res = 0;

  res = sizeof (BtorBitVectorTuple) + t->arity * sizeof (BtorBitVector *);
  for (i = 0; i < t->arity; i++) res += btor_bv_size (t->bv[i]);
  return res;
}

/*------------------------------------------------------------------------*/

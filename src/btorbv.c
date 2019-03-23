/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *  Copyright (C) 2015-2019 Aina Niemetz.
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

#define BTOR_MASK_REM_BITS(bv)                       \
  ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1) \
   >> (BTOR_BV_TYPE_BW - 1 - (bv->width % BTOR_BV_TYPE_BW)))

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static bool
rem_bits_zero_dbg (BtorBitVector *bv)
{
  return (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
}

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

static void
set_rem_bits_to_zero (BtorBitVector *bv)
{
  if (bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_new (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  uint32_t i;
  BtorBitVector *res;

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

  BtorBitVector *res, *resext, *fromext, *toext, *tmp1, *tmp2;

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

  res = btor_bv_new (mm, bw);
  for (i = 1; i < res->len; i++)
    res->bits[i] = (BTOR_BV_TYPE) btor_rng_rand (rng);
  res->bits[0] = (BTOR_BV_TYPE) btor_rng_pick_rand (
      rng, 0, ((~0) >> (BTOR_BV_TYPE_BW - bw % BTOR_BV_TYPE_BW)) - 1);

  for (i = 0; i < lo; i++) btor_bv_set_bit (res, i, 0);
  for (i = up + 1; i < res->width; i++) btor_bv_set_bit (res, i, 0);

  set_rem_bits_to_zero (res);

  return res;
}

BtorBitVector *
btor_bv_new_random (BtorMemMgr *mm, BtorRNG *rng, uint32_t bw)
{
  return btor_bv_new_random_bit_range (mm, rng, bw, bw - 1, 0);
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_char_to_bv (BtorMemMgr *mm, const char *assignment)
{
  assert (mm);
  assert (assignment);
  assert (strlen (assignment) > 0);

  return btor_bv_const (mm, assignment, strlen (assignment));
}

BtorBitVector *
btor_bv_uint64_to_bv (BtorMemMgr *mm, uint64_t value, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res;

  res = btor_bv_new (mm, bw);
  assert (res->len > 0);
  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_int64_to_bv (BtorMemMgr *mm, int64_t value, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res, *tmp;

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
  return res;
}

BtorBitVector *
btor_bv_const (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (btor_util_check_bin_to_bv (mm, str, bw));

  uint32_t i, j, bit;
  BtorBitVector *res;

  res = btor_bv_new (mm, bw);
  for (i = 0; i < bw; i++)
  {
    j = bw - 1 - i;
    assert (str[j] == '0' || str[j] == '1');
    bit = str[j] == '0' ? 0 : 1;
    btor_bv_set_bit (res, i, bit);
  }
  return res;
}

BtorBitVector *
btor_bv_constd (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (btor_util_check_dec_to_bv (mm, str, bw));

  bool is_neg, is_min_val;
  ;
  BtorBitVector *res, *tmp;
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
  return res;
}

BtorBitVector *
btor_bv_consth (BtorMemMgr *mm, const char *str, uint32_t bw)
{
  assert (btor_util_check_hex_to_bv (mm, str, bw));

  BtorBitVector *res, *tmp;
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
  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_get_assignment (BtorMemMgr *mm, BtorNode *exp)
{
  assert (mm);
  assert (exp);

  uint32_t i, j, width;
  int32_t bit;
  bool inv;
  BtorNode *real_exp;
  BtorBitVector *res;
  BtorAIGVec *av;
  BtorAIGMgr *amgr;

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
  assert (res->len == bv->len);
  memcpy (res->bits, bv->bits, sizeof (*(bv->bits)) * bv->len);
  assert (btor_bv_compare (res, (BtorBitVector *) bv) == 0);
  return res;
}

/*------------------------------------------------------------------------*/

size_t
btor_bv_size (const BtorBitVector *bv)
{
  assert (bv);
  return sizeof (BtorBitVector) + bv->len * sizeof (BTOR_BV_TYPE);
}

void
btor_bv_free (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);
  btor_mem_free (
      mm, bv, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * bv->len);
}

int32_t
btor_bv_compare (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);

  uint32_t i;

  if (a->width != b->width) return -1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  if (i == a->len) return 0;

  if (a->bits[i] > b->bits[i]) return 1;

  assert (a->bits[i] < b->bits[i]);
  return -1;
}

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};

#define NPRIMES ((uint32_t) (sizeof hash_primes / sizeof *hash_primes))

uint32_t
btor_bv_hash (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t res = 0, i, j = 0, x, p0, p1;

  res = bv->width * hash_primes[j++];
  for (i = 0, j = 0; i < bv->len; i++)
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
}

/*------------------------------------------------------------------------*/

char *
btor_bv_to_char (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  uint32_t i, bw, bit;
  char *res;

  bw = bv->width;
  BTOR_NEWN (mm, res, bw + 1);
  for (i = 0; i < bw; i++)
  {
    bit             = btor_bv_get_bit (bv, i);
    res[bw - 1 - i] = bit ? '1' : '0';
  }
  res[bw] = '\0';

  return res;
}

char *
btor_bv_to_hex_char (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  uint32_t len, i, j, k, tmp;
  char *res, ch;

  len = (bv->width + 3) / 4;
  BTOR_CNEWN (mm, res, len + 1);
  for (i = 0, j = len - 1; i < bv->width;)
  {
    tmp = btor_bv_get_bit (bv, i++);
    for (k = 1; i < bv->width && k <= 3; i++, k++)
      tmp |= btor_bv_get_bit (bv, i) << k;
    ch       = tmp < 10 ? '0' + tmp : 'a' + (tmp - 10);
    res[j--] = ch;
  }

  return res;
}

static uint32_t
get_first_one_bit_idx (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;

  for (i = bv->width - 1; i < UINT32_MAX; i--)
  {
    if (btor_bv_get_bit (bv, i)) break;
    if (i == 0) return UINT32_MAX;
  }
  return i;
}

char *
btor_bv_to_dec_char (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *tmp, *div, *rem, *ten;
  uint32_t i;
  char *res, ch, *p, *q;
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
  return res;
}

/*------------------------------------------------------------------------*/

uint64_t
btor_bv_to_uint64 (const BtorBitVector *bv)
{
  assert (bv);
  assert (bv->width <= sizeof (uint64_t) * 8);
  assert (bv->len <= 2);

  uint32_t i;
  uint64_t res;

  res = 0;
  for (i = 0; i < bv->len; i++)
    res |= ((uint64_t) bv->bits[i]) << (BTOR_BV_TYPE_BW * (bv->len - 1 - i));

  return res;
}

/*------------------------------------------------------------------------*/

uint32_t
btor_bv_get_bit (const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (pos < bv->width);

  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;

  return (bv->bits[bv->len - 1 - i] >> j) & 1;
}

void
btor_bv_set_bit (BtorBitVector *bv, uint32_t pos, uint32_t bit)
{
  assert (bv);
  assert (bv->len > 0);
  assert (bit == 0 || bit == 1);
  assert (pos < bv->width);

  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;
  assert (i < bv->len);

  if (bit)
    bv->bits[bv->len - 1 - i] |= (1u << j);
  else
    bv->bits[bv->len - 1 - i] &= ~(1u << j);
}

void
btor_bv_flip_bit (BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (bv->len > 0);
  assert (pos < bv->width);

  btor_bv_set_bit (bv, pos, btor_bv_get_bit (bv, pos) ? 0 : 1);
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

  uint32_t i;
  for (i = 0; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
}

bool
btor_bv_is_ones (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, n;
  for (i = bv->len - 1; i >= 1; i--)
    if (bv->bits[i] != UINT32_MAX) return false;
  if (bv->width == BTOR_BV_TYPE_BW)
    return bv->bits[0] == UINT32_MAX;
  else
  {
    n = BTOR_BV_TYPE_BW - bv->width % BTOR_BV_TYPE_BW;
    assert (n > 0);
    if (bv->bits[0] != UINT32_MAX >> n) return false;
  }
  return true;
}

bool
btor_bv_is_one (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;

  if (bv->bits[bv->len - 1] != 1) return false;
  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return false;
  return true;
}

bool
btor_bv_is_min_signed (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;

  if (bv->bits[0] != (1u << ((bv->width % BTOR_BV_TYPE_BW) - 1))) return false;
  for (i = 1; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
}

bool
btor_bv_is_max_signed (const BtorBitVector *bv)
{
  assert (bv);

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

  uint32_t i;

  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return -1;
  if (((int32_t) bv->bits[bv->len - 1]) < 0) return -1;
  return bv->bits[bv->len - 1];
}

uint32_t
btor_bv_get_num_trailing_zeros (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, res;

  for (i = 0, res = 0; i < bv->width; i++)
  {
    if (btor_bv_get_bit (bv, i)) break;
    res += 1;
  }

  return res;
}

uint32_t
btor_bv_get_num_leading_zeros (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, res;

  for (i = bv->width - 1, res = 0; i < UINT32_MAX; i--)
  {
    if (btor_bv_get_bit (bv, i)) break;
    res += 1;
  }

  return res;
}

uint32_t
btor_bv_get_num_leading_ones (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, res;

  for (i = bv->width - 1, res = 0; i < UINT32_MAX; i--)
  {
    if (!btor_bv_get_bit (bv, i)) break;
    res += 1;
  }

  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_one (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res = btor_bv_new (mm, bw);
  btor_bv_set_bit (res, 0, 1);
  return res;
}

BtorBitVector *
btor_bv_ones (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res, *tmp;

  tmp = btor_bv_new (mm, bw);
  res = btor_bv_not (mm, tmp);
  btor_bv_free (mm, tmp);

  return res;
}

BtorBitVector *
btor_bv_min_signed (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res;

  res = btor_bv_new (mm, bw);
  btor_bv_set_bit (res, bw - 1, 1);
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

  BtorBitVector *not_bv, *one, *neg_b;

  not_bv = btor_bv_not (mm, bv);
  one    = btor_bv_uint64_to_bv (mm, 1, bv->width);
  neg_b  = btor_bv_add (mm, not_bv, one);
  btor_bv_free (mm, not_bv);
  btor_bv_free (mm, one);

  return neg_b;
}

BtorBitVector *
btor_bv_not (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, bv->width);
  for (i = 0; i < bv->len; i++) res->bits[i] = ~bv->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_inc (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res, *one;

  one = btor_bv_uint64_to_bv (mm, 1, bv->width);
  res = btor_bv_add (mm, bv, one);
  btor_bv_free (mm, one);
  return res;
}

BtorBitVector *
btor_bv_dec (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res, *one, *negone;

  one    = btor_bv_uint64_to_bv (mm, 1, bv->width);
  negone = btor_bv_neg (mm, one);
  res    = btor_bv_add (mm, bv, negone);
  btor_bv_free (mm, one);
  btor_bv_free (mm, negone);
  return res;
}

BtorBitVector *
btor_bv_redand (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  uint32_t i;
  uint32_t bit;
  uint32_t mask0;
  BtorBitVector *res;

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
  return res;
}

BtorBitVector *
btor_bv_redor (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

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
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_bv_add (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  int64_t i;
  uint64_t x, y, sum;
  BtorBitVector *res;
  BTOR_BV_TYPE carry;

  if (a->width <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (mm, x + y, a->width);
  }
  else
  {
    res   = btor_bv_new (mm, a->width);
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
  return res;
}

BtorBitVector *
btor_bv_sub (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  BtorBitVector *negb, *res;

  negb = btor_bv_neg (mm, b);
  res  = btor_bv_add (mm, a, negb);
  btor_bv_free (mm, negb);
  return res;
}

BtorBitVector *
btor_bv_and (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] & b->bits[i];

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_implies (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = ~a->bits[i] | b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_or (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] | b->bits[i];

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_nand (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] & b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_nor (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = ~(a->bits[i] | b->bits[i]);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_xnor (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] ^ ~b->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_xor (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width);
  for (i = 0; i < a->len; i++) res->bits[i] = a->bits[i] ^ b->bits[i];

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_eq (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i, bit;
  BtorBitVector *res;

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
  return res;
}

BtorBitVector *
btor_bv_ne (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i, bit;
  BtorBitVector *res;

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
  return res;
}

BtorBitVector *
btor_bv_ult (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i, bit;
  BtorBitVector *res;

  res = btor_bv_new (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a == b */
  if (i == a->len || a->bits[i] >= b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_ulte (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i, bit;
  BtorBitVector *res;

  res = btor_bv_new (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a == b */
  if (i < a->len && a->bits[i] > b->bits[i]) bit = 0;

  btor_bv_set_bit (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
  return res;
}

static BtorBitVector *
sll_bv (BtorMemMgr *mm, const BtorBitVector *a, uint32_t shift)
{
  assert (mm);
  assert (a);

  uint32_t skip, i, j, k;
  BtorBitVector *res;
  BTOR_BV_TYPE v;

  res = btor_bv_new (mm, a->width);
  if (shift >= a->width) return res;

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
  assert (check_bits_sll_dbg (a, res, shift));
  return res;
}

BtorBitVector *
btor_bv_sll (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (btor_util_is_power_of_2 (a->width) || a->len == b->len);
  assert (btor_util_log_2 (a->width) == b->width || a->width == b->width);

  uint64_t shift;
  shift = btor_bv_to_uint64 (b);
  return sll_bv (mm, a, shift);
}

BtorBitVector *
btor_bv_srl (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (btor_util_is_power_of_2 (a->width) || a->len == b->len);
  assert (btor_util_log_2 (a->width) == b->width || a->width == b->width);

  uint32_t skip, i, j, k;
  uint64_t shift;
  BtorBitVector *res;
  BTOR_BV_TYPE v;

  res   = btor_bv_new (mm, a->width);
  shift = btor_bv_to_uint64 (b);
  if (shift >= a->width) return res;

  k    = shift % BTOR_BV_TYPE_BW;
  skip = shift / BTOR_BV_TYPE_BW;

  v = 0;
  for (i = 0, j = skip; i < a->len && j < a->len; i++, j++)
  {
    v            = (k == 0) ? a->bits[i] : v | (a->bits[i] >> k);
    res->bits[j] = v;
    v            = (k == 0) ? a->bits[i] : a->bits[i] << (BTOR_BV_TYPE_BW - k);
  }

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_mul (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;
  uint64_t x, y;
  BtorBitVector *res, *and, *shift, *add;

  if (a->width <= 64)
  {
    x   = btor_bv_to_uint64 (a);
    y   = btor_bv_to_uint64 (b);
    res = btor_bv_uint64_to_bv (mm, x * y, a->width);
  }
  else
  {
    res = btor_bv_new (mm, a->width);
    for (i = 0; i < a->width; i++)
    {
      if (btor_bv_get_bit (b, i))
        and = btor_bv_copy (mm, a);
      else
        and = btor_bv_new (mm, a->width);
      shift = sll_bv (mm, and, i);
      add   = btor_bv_add (mm, res, shift);
      btor_bv_free (mm, and);
      btor_bv_free (mm, shift);
      btor_bv_free (mm, res);
      res = add;
    }
  }
  return res;
}

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
  assert (a->len == b->len);
  assert (a->width == b->width);

  int64_t i;
  bool is_true;
  uint64_t x, y, z;

  BtorBitVector *neg_b, *quot, *rem, *ult, *eq, *tmp;

  if (a->width <= 64)
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
    quot = btor_bv_uint64_to_bv (mm, x, a->width);
    rem  = btor_bv_uint64_to_bv (mm, y, a->width);
  }
  else
  {
    neg_b = btor_bv_neg (mm, b);
    quot  = btor_bv_new (mm, a->width);
    rem   = btor_bv_new (mm, a->width);

    for (i = a->width - 1; i >= 0; i--)
    {
      tmp = sll_bv (mm, rem, 1);
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

BtorBitVector *
btor_bv_udiv (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  BtorBitVector *res = 0;
  udiv_urem_bv (mm, a, b, &res, 0);
  assert (res);
  return res;
}

BtorBitVector *
btor_bv_urem (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  BtorBitVector *res = 0;
  udiv_urem_bv (mm, a, b, 0, &res);
  assert (res);
  return res;
}

BtorBitVector *
btor_bv_concat (BtorMemMgr *mm, const BtorBitVector *a, const BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);

  int64_t i, j, k;
  BTOR_BV_TYPE v;
  BtorBitVector *res;

  res = btor_bv_new (mm, a->width + b->width);

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

  uint32_t i, j;
  BtorBitVector *res;

  res = btor_bv_new (mm, upper - lower + 1);
  for (i = lower, j = 0; i <= upper; i++)
    btor_bv_set_bit (res, j++, btor_bv_get_bit (bv, i));

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_sext (BtorMemMgr *mm, const BtorBitVector *bv, uint32_t len)
{
  assert (mm);
  assert (bv);
  assert (len > 0);

  BtorBitVector *tmp, *res;

  tmp = btor_bv_get_bit (bv, bv->width - 1) ? btor_bv_ones (mm, len)
                                            : btor_bv_zero (mm, len);
  res = btor_bv_concat (mm, tmp, bv);
  btor_bv_free (mm, tmp);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_uext (BtorMemMgr *mm, const BtorBitVector *bv, uint32_t len)
{
  assert (mm);
  assert (bv);
  assert (len > 0);

  BtorBitVector *res;

  res = btor_bv_new (mm, bv->width + len);
  memcpy (
      res->bits + res->len - bv->len, bv->bits, sizeof (*(bv->bits)) * bv->len);

  return res;
}

BtorBitVector *
btor_bv_ite (BtorMemMgr *mm,
             const BtorBitVector *c,
             const BtorBitVector *t,
             const BtorBitVector *e)
{
  assert (c);
  assert (c->len == 1);
  assert (t);
  assert (t->len > 0);
  assert (e);
  assert (t->len == e->len);
  assert (t->width == e->width);

  BtorBitVector *res;
  BTOR_BV_TYPE cc, nn;
  uint32_t i;

  cc = btor_bv_get_bit (c, 0) ? (~(BTOR_BV_TYPE) 0) : 0;
  nn = ~cc;

  res = btor_bv_new (mm, t->width);
  for (i = 0; i < t->len; i++)
    res->bits[i] = (cc & t->bits[i]) | (nn & e->bits[i]);

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_bv_flipped_bit (BtorMemMgr *mm, const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (bv->len > 0);
  assert (pos < bv->width);

  BtorBitVector *res;

  res = btor_bv_copy (mm, bv);
  btor_bv_set_bit (res, pos, btor_bv_get_bit (res, pos) ? 0 : 1);
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));

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

  uint32_t i;
  BtorBitVector *res;

  res = btor_bv_copy (mm, bv);
  for (i = lower; i <= upper; i++)
    btor_bv_set_bit (res, i, btor_bv_get_bit (res, i) ? 0 : 1);
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
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
  assert (a->len == b->len);
  assert (a->width == b->width);

  bool res;
  BtorBitVector *aext, *bext, *mul, *o;

  res = false;

  if (a->width > 1)
  {
    aext = btor_bv_uext (mm, a, a->width);
    bext = btor_bv_uext (mm, b, b->width);
    mul  = btor_bv_mul (mm, aext, bext);
    o    = btor_bv_slice (mm, mul, mul->width - 1, a->width);
    if (!btor_bv_is_zero (o)) res = true;
    btor_bv_free (mm, aext);
    btor_bv_free (mm, bext);
    btor_bv_free (mm, mul);
    btor_bv_free (mm, o);
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

  uint32_t i;
  BtorBitVector *a, *b, *y, *ly, *ty, *q, *yq, *r, *res;

  /* a = 2^bw
   * b = bv
   * lx * a + ly * b = gcd (a, b) = 1
   * -> lx * a = lx * 2^bw = 0 (2^bw_[bw] = 0)
   * -> ly * b = bv^-1 * bv = 1
   * -> ly is modular inverse of bv */

  a = btor_bv_new (mm, bv->width + 1);
  btor_bv_set_bit (a, a->width - 1, 1); /* 2^bw */

  b = btor_bv_new (mm, bv->width + 1); /* extend to bw of a */
  for (i = 0; i < bv->width; i++)
    btor_bv_set_bit (b, i, btor_bv_get_bit (bv, i));

  y  = btor_bv_one (mm, bv->width + 1);
  ly = btor_bv_new (mm, bv->width + 1);

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
  assert (arity > 0);

  BtorBitVectorTuple *res;

  BTOR_CNEW (mm, res);
  BTOR_CNEWN (mm, res->bv, arity);
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
  for (i = 0; i < t->arity; i++) btor_bv_free (mm, t->bv[i]);

  btor_mem_free (mm, t->bv, sizeof (BtorBitVectorTuple *) * t->arity);
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

  uint32_t i, j = 0, hash = 0;

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

  uint32_t i;
  BtorBitVectorTuple *res;

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
  size_t res;

  res = sizeof (BtorBitVectorTuple) + t->arity * sizeof (BtorBitVector *);
  for (i = 0; i < t->arity; i++) res += btor_bv_size (t->bv[i]);

  return res;
}

/*------------------------------------------------------------------------*/

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

#include "btorbitvec.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconst.h"
#include "btorcore.h"
#include "utils/btorutil.h"

#include <limits.h>

#define BTOR_MASK_REM_BITS(bv)                       \
  ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1) \
   >> (BTOR_BV_TYPE_BW - 1 - (bv->width % BTOR_BV_TYPE_BW)))

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static int
rem_bits_zero_dbg (BtorBitVector *bv)
{
  assert (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
  return 1;
}

static int
check_bits_sll_dbg (BtorBitVector *bv, BtorBitVector *res, int shift)
{
  assert (bv);
  assert (res);
  assert (bv->width == res->width);

  unsigned i;

  for (i = 0; shift + i < bv->width; i++)
    assert (btor_get_bit_bv (bv, i) == btor_get_bit_bv (res, shift + i));

  return 1;
}
#endif

static void
set_rem_bits_to_zero (BtorBitVector *bv)
{
  if ((unsigned) bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_new_bv (BtorMemMgr *mm, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  uint32_t i;
  BtorBitVector *res;

  i = bw / BTOR_BV_TYPE_BW;
  if (bw % BTOR_BV_TYPE_BW > 0) i += 1;

  assert (i > 0);
  res = btor_malloc (mm, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * i);
  BTOR_CLRN (res->bits, i);
  res->len = i;
  assert (res->len);
  res->width = bw;
  return res;
}

// TODO simpler with btor_sub_bv
BtorBitVector *
btor_new_random_range_bv (BtorMemMgr *mm,
                          BtorRNG *rng,
                          uint32_t bw,
                          BtorBitVector *from,
                          BtorBitVector *to)
{
  assert (mm);
  assert (rng);
  assert (bw > 0);
  assert (bw == from->width);
  assert (from->width == to->width);
  assert (btor_compare_bv (from, to) <= 0);

  BtorBitVector *res, *resext, *fromext, *toext, *tmp1, *tmp2;

  /* we allow to = 1...1 */
  fromext = btor_uext_bv (mm, from, 1);
  toext   = btor_uext_bv (mm, to, 1);

  res    = btor_new_random_bv (mm, rng, bw);
  resext = btor_uext_bv (mm, res, 1);
  btor_free_bv (mm, res);

  tmp1 = btor_inc_bv (mm, toext);          // to + 1
  tmp2 = btor_sub_bv (mm, tmp1, fromext);  // to + 1 - from
  btor_free_bv (mm, tmp1);

  tmp1   = resext;
  resext = btor_urem_bv (mm, tmp1, tmp2);  // res %= to + 1 - from
  btor_free_bv (mm, tmp1);

  tmp1   = resext;
  resext = btor_add_bv (mm, tmp1, fromext);  // res += from

  btor_free_bv (mm, tmp1);
  btor_free_bv (mm, tmp2);
  btor_free_bv (mm, fromext);
  btor_free_bv (mm, toext);

  res = btor_slice_bv (mm, resext, from->width - 1, 0);
  btor_free_bv (mm, resext);
  return res;
}

BtorBitVector *
btor_new_random_bit_range_bv (
    BtorMemMgr *mm, BtorRNG *rng, uint32_t bw, uint32_t up, uint32_t lo)
{
  assert (mm);
  assert (rng);
  assert (bw > 0);
  assert (lo <= up);

  uint32_t i;
  BtorBitVector *res;

  res = btor_new_bv (mm, bw);
  for (i = 1; i < res->len; i++)
    res->bits[i] = (BTOR_BV_TYPE) btor_rand_rng (rng);
  res->bits[0] = (BTOR_BV_TYPE) btor_pick_rand_rng (
      rng, 0, ((~0) >> (BTOR_BV_TYPE_BW - bw % BTOR_BV_TYPE_BW)) - 1);

  for (i = 0; i < lo; i++) btor_set_bit_bv (res, i, 0);
  for (i = up + 1; i < res->width; i++) btor_set_bit_bv (res, i, 0);

  set_rem_bits_to_zero (res);

  return res;
}

BtorBitVector *
btor_new_random_bv (BtorMemMgr *mm, BtorRNG *rng, uint32_t bw)
{
  return btor_new_random_bit_range_bv (mm, rng, bw, bw - 1, 0);
}

BtorBitVector *
btor_char_to_bv (BtorMemMgr *mm, char *assignment)
{
  assert (mm);
  assert (assignment);
  assert (strlen (assignment) > 0);

  uint32_t i, j, bit;
  BtorBitVector *res;

  res = btor_new_bv (mm, strlen (assignment));

  for (i = 0; i < res->width; i++)
  {
    j = res->width - 1 - i;
    assert (assignment[j] == '0' || assignment[j] == '1');
    bit = assignment[j] == '0' ? 0 : 1;
    btor_set_bit_bv (res, i, bit);
  }

  return res;
}

BtorBitVector *
btor_uint64_to_bv (BtorMemMgr *mm, uint64_t value, uint32_t bw)
{
  assert (mm);
  assert (bw > 0);

  BtorBitVector *res;

  res = btor_new_bv (mm, bw);
  assert (res->len > 0);
  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_assignment_bv (BtorMemMgr *mm, BtorNode *exp, bool init_x_values)
{
  assert (mm);
  assert (exp);
  assert (init_x_values || BTOR_REAL_ADDR_NODE (exp)->av);
  assert (init_x_values == 0 || init_x_values == 1);

  int i, j, len, bit, inv;
  BtorNode *real_exp;
  BtorBitVector *res;
  BtorAIGVec *av;
  BtorAIGMgr *amgr;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (!real_exp->av)
    return btor_new_bv (mm, btor_get_exp_width (real_exp->btor, real_exp));

  amgr = btor_get_aig_mgr_btor (real_exp->btor);
  av   = real_exp->av;
  len  = av->len;
  res  = btor_new_bv (mm, len);
  inv  = BTOR_IS_INVERTED_NODE (exp);

  for (i = 0, j = len - 1; i < len; i++, j--)
  {
    bit = btor_get_assignment_aig (amgr, av->aigs[j]);
    if (init_x_values && bit == 0) bit = -1;
    if (inv) bit *= -1;
    assert (bit == -1 || bit == 1);
    btor_set_bit_bv (res, i, bit == 1 ? 1 : 0);
  }
  return res;
}

BtorBitVector *
btor_copy_bv (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res;

  res = btor_new_bv (mm, bv->width);
  assert (res->width == bv->width);
  assert (res->len == bv->len);
  memcpy (res->bits, bv->bits, sizeof (*(bv->bits)) * bv->len);
  assert (btor_compare_bv (res, (BtorBitVector *) bv) == 0);
  return res;
}

/*------------------------------------------------------------------------*/

size_t
btor_size_bv (BtorBitVector *bv)
{
  assert (bv);
  return sizeof (BtorBitVector) + bv->len * sizeof (BTOR_BV_TYPE);
}

void
btor_free_bv (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);
  btor_free (mm, bv, sizeof (BtorBitVector) + sizeof (BTOR_BV_TYPE) * bv->len);
}

int
btor_compare_bv (const BtorBitVector *a, const BtorBitVector *b)
{
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  if (i == a->len) return 0;

  if (a->bits[i] > b->bits[i]) return 1;

  assert (a->bits[i] < b->bits[i]);
  return -1;
}

bool
btor_is_zero_bv (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;
  for (i = 0; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
}

bool
btor_is_one_bv (const BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;

  if (bv->bits[bv->len - 1] != 1) return false;
  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return false;
  return true;
}

unsigned int
btor_hash_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, hash = 0;

  for (i = 0; i < bv->len; i++) hash += bv->bits[i] * 7334147u;

  return hash;
}

/*------------------------------------------------------------------------*/

void
btor_print_bv (BtorBitVector *bv)
{
  assert (bv);

  int i;

  for (i = bv->width - 1; i >= 0; i--) printf ("%d", btor_get_bit_bv (bv, i));
  printf ("\n");
}

void
btor_print_all_bv (BtorBitVector *bv)
{
  assert (bv);

  int i;

  for (i = BTOR_BV_TYPE_BW * bv->len - 1; i >= 0; i--)
  {
    if ((unsigned) i == (BTOR_BV_TYPE_BW * bv->len + 1 - bv->width))
      printf ("|");
    if (i > 0 && (BTOR_BV_TYPE_BW * bv->len - 1 - i) % BTOR_BV_TYPE_BW == 0)
      printf (".");
    printf ("%d", btor_get_bit_bv (bv, i));
  }
  printf ("\n");
}

char *
btor_bv_to_char_bv (BtorMemMgr *mm, const BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  int i, bw, bit;
  char *res;

  bw = bv->width;
  BTOR_NEWN (mm, res, bw + 1);
  for (i = 0; i < bw; i++)
  {
    bit             = btor_get_bit_bv (bv, i);
    res[bw - 1 - i] = bit ? '1' : '0';
  }
  res[bw] = '\0';

  return res;
}

uint64_t
btor_bv_to_uint64_bv (BtorBitVector *bv)
{
  assert (bv);
  assert ((unsigned) bv->width <= sizeof (uint64_t) * 8);
  assert (bv->len <= 2);

  uint32_t i;
  uint64_t res;

  res = 0;
  for (i = 0; i < bv->len; i++)
    res |= ((uint64_t) bv->bits[i]) << (BTOR_BV_TYPE_BW * (bv->len - 1 - i));

  return res;
}

int
btor_get_bit_bv (const BtorBitVector *bv, uint32_t pos)
{
  assert (bv);

  uint32_t i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;

  return (bv->bits[bv->len - 1 - i] >> j) & 1;
}

void
btor_set_bit_bv (BtorBitVector *bv, uint32_t pos, uint32_t bit)
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

int
btor_is_true_bv (BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return btor_get_bit_bv (bv, 0);
}

int
btor_is_false_bv (BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return !btor_get_bit_bv (bv, 0);
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_one_bv (BtorMemMgr *mm, int bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res = btor_new_bv (mm, bw);
  btor_set_bit_bv (res, 0, 1);
  return res;
}

BtorBitVector *
btor_ones_bv (BtorMemMgr *mm, int bw)
{
  assert (mm);
  assert (bw);

  BtorBitVector *res, *tmp;

  tmp = btor_new_bv (mm, bw);
  res = btor_not_bv (mm, tmp);
  btor_free_bv (mm, tmp);

  return res;
}

BtorBitVector *
btor_neg_bv (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *not_bv, *one, *neg_b;

  not_bv = btor_not_bv (mm, bv);
  one    = btor_uint64_to_bv (mm, 1, bv->width);
  neg_b  = btor_add_bv (mm, not_bv, one);
  btor_free_bv (mm, not_bv);
  btor_free_bv (mm, one);

  return neg_b;
}

BtorBitVector *
btor_not_bv (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  uint32_t i;
  BtorBitVector *res;

  res = btor_new_bv (mm, bv->width);
  for (i = 0; i < bv->len; i++) res->bits[i] = ~bv->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_xor_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i;
  BtorBitVector *res;

  res = btor_new_bv (mm, a->width);
  for (i = a->len - 1; i >= 0; i--) res->bits[i] = a->bits[i] ^ b->bits[i];

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_inc_bv (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res, *one;

  one = btor_uint64_to_bv (mm, 1, bv->width);
  res = btor_add_bv (mm, bv, one);
  btor_free_bv (mm, one);
  return res;
}

BtorBitVector *
btor_dec_bv (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);

  BtorBitVector *res, *one, *negone;

  one    = btor_uint64_to_bv (mm, 1, bv->width);
  negone = btor_neg_bv (mm, one);
  res    = btor_add_bv (mm, bv, negone);
  btor_free_bv (mm, one);
  btor_free_bv (mm, negone);
  return res;
}

BtorBitVector *
btor_flipped_bit_bv (BtorMemMgr *mm, BtorBitVector *bv, uint32_t pos)
{
  assert (bv);
  assert (bv->len > 0);
  assert (pos < bv->width);

  BtorBitVector *res;

  res = btor_copy_bv (mm, bv);
  btor_set_bit_bv (res, pos, btor_get_bit_bv (res, pos) ? 0 : 1);
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));

  return res;
}

BtorBitVector *
btor_flipped_bit_range_bv (BtorMemMgr *mm,
                           BtorBitVector *bv,
                           uint32_t upper,
                           uint32_t lower)
{
  assert (mm);
  assert (lower <= upper);
  assert (upper < bv->width);

  uint32_t i;
  BtorBitVector *res;

  res = btor_copy_bv (mm, bv);
  for (i = lower; i <= upper; i++)
    btor_set_bit_bv (res, i, btor_get_bit_bv (res, i) ? 0 : 1);
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_add_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i;
  uint64_t x, y, sum;
  BtorBitVector *res;
  BTOR_BV_TYPE carry;

  if (a->width <= 64)
  {
    x   = btor_bv_to_uint64_bv (a);
    y   = btor_bv_to_uint64_bv (b);
    res = btor_uint64_to_bv (mm, x + y, a->width);
  }
  else
  {
    res   = btor_new_bv (mm, a->width);
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
btor_sub_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  BtorBitVector *negb, *res;

  negb = btor_neg_bv (mm, b);
  res  = btor_add_bv (mm, a, negb);
  btor_free_bv (mm, negb);
  return res;
}

BtorBitVector *
btor_and_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i;
  BtorBitVector *res;

  res = btor_new_bv (mm, a->width);
  for (i = a->len - 1; i >= 0; i--) res->bits[i] = a->bits[i] & b->bits[i];

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_eq_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i, bit;
  BtorBitVector *res;

  res = btor_new_bv (mm, 1);
  bit = 1;
  for (i = 0; i < a->len; i++)
  {
    if (a->bits[i] != b->bits[i])
    {
      bit = 0;
      break;
    }
  }
  btor_set_bit_bv (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_ult_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  uint32_t i, bit;
  BtorBitVector *res;

  res = btor_new_bv (mm, 1);
  bit = 1;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  /* a == b */
  if (i == a->len || a->bits[i] >= b->bits[i]) bit = 0;

  btor_set_bit_bv (res, 0, bit);

  assert (rem_bits_zero_dbg (res));
  return res;
}

static BtorBitVector *
sll_bv (BtorMemMgr *mm, BtorBitVector *a, int shift)
{
  assert (mm);
  assert (a);

  int skip, i, j, k;
  BtorBitVector *res;
  BTOR_BV_TYPE v;

  res  = btor_new_bv (mm, a->width);
  k    = shift % BTOR_BV_TYPE_BW;
  skip = shift / BTOR_BV_TYPE_BW;

  v = 0;
  for (i = a->len - 1, j = res->len - 1 - skip; i >= 0 && j >= 0; i--, j--)
  {
    v = (k == 0) ? a->bits[i] : v | (a->bits[i] << k);
    assert (j >= 0);
    res->bits[j] = v;
    v            = (k == 0) ? a->bits[i] : a->bits[i] >> (BTOR_BV_TYPE_BW - k);
  }
  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  assert (check_bits_sll_dbg (a, res, shift));
  return res;
}

BtorBitVector *
btor_sll_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (btor_is_power_of_2_util (a->width));
  assert (btor_log_2_util (a->width) == b->width);

  uint64_t shift;
  shift = btor_bv_to_uint64_bv (b);
  return sll_bv (mm, a, (int) shift);
}

BtorBitVector *
btor_srl_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);

  uint32_t skip, i, j, k;
  uint64_t shift;
  BtorBitVector *res;
  BTOR_BV_TYPE v;

  res   = btor_new_bv (mm, a->width);
  shift = btor_bv_to_uint64_bv (b);
  k     = shift % BTOR_BV_TYPE_BW;
  skip  = shift / BTOR_BV_TYPE_BW;

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
btor_mul_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
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
    x   = btor_bv_to_uint64_bv (a);
    y   = btor_bv_to_uint64_bv (b);
    res = btor_uint64_to_bv (mm, x * y, a->width);
  }
  else
  {
    res = btor_new_bv (mm, a->width);
    for (i = 0; i < a->width; i++)
    {
      if (btor_get_bit_bv (b, i))
        and = btor_copy_bv (mm, a);
      else
        and = btor_new_bv (mm, a->width);
      shift = sll_bv (mm, and, i);
      add   = btor_add_bv (mm, res, shift);
      btor_free_bv (mm, and);
      btor_free_bv (mm, shift);
      btor_free_bv (mm, res);
      res = add;
    }
  }
  return res;
}

static void
udiv_urem_bv (BtorMemMgr *mm,
              BtorBitVector *a,
              BtorBitVector *b,
              BtorBitVector **q,
              BtorBitVector **r)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i, is_true;
  uint64_t x, y, z;

  BtorBitVector *neg_b, *quot, *rem, *ult, *eq, *tmp;

  if (a->width <= 64)
  {
    x = btor_bv_to_uint64_bv (a);
    y = btor_bv_to_uint64_bv (b);
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
    quot = btor_uint64_to_bv (mm, x, a->width);
    rem  = btor_uint64_to_bv (mm, y, a->width);
  }
  else
  {
    neg_b = btor_neg_bv (mm, b);
    quot  = btor_new_bv (mm, a->width);
    rem   = btor_new_bv (mm, a->width);

    for (i = a->width - 1; i >= 0; i--)
    {
      tmp = sll_bv (mm, rem, 1);
      btor_free_bv (mm, rem);
      rem = tmp;
      btor_set_bit_bv (rem, 0, btor_get_bit_bv (a, i));

      ult     = btor_ult_bv (mm, b, rem);
      is_true = btor_is_true_bv (ult);
      btor_free_bv (mm, ult);

      if (is_true) goto UDIV_UREM_SUBTRACT;

      eq      = btor_eq_bv (mm, b, rem);
      is_true = btor_is_true_bv (eq);
      btor_free_bv (mm, eq);

      if (is_true)
      {
      UDIV_UREM_SUBTRACT:
        tmp = btor_add_bv (mm, rem, neg_b);
        btor_free_bv (mm, rem);
        rem = tmp;
        btor_set_bit_bv (quot, i, 1);
      }
    }
    btor_free_bv (mm, neg_b);
  }

  if (q)
    *q = quot;
  else
    btor_free_bv (mm, quot);

  if (r)
    *r = rem;
  else
    btor_free_bv (mm, rem);
}

BtorBitVector *
btor_udiv_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
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
btor_urem_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
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
btor_concat_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
{
  assert (mm);
  assert (a);
  assert (b);

  int i, j, k;
  BTOR_BV_TYPE v;
  BtorBitVector *res;

  res = btor_new_bv (mm, a->width + b->width);

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
btor_slice_bv (BtorMemMgr *mm,
               BtorBitVector *bv,
               uint32_t upper,
               uint32_t lower)
{
  assert (mm);
  assert (bv);

  uint32_t i, j;
  BtorBitVector *res;

  res = btor_new_bv (mm, upper - lower + 1);
  for (i = lower, j = 0; i <= upper; i++)
    btor_set_bit_bv (res, j++, btor_get_bit_bv (bv, i));

  assert (rem_bits_zero_dbg (res));
  return res;
}

BtorBitVector *
btor_sext_bv (BtorMemMgr *mm, BtorBitVector *bv, uint32_t len)
{
  assert (mm);
  assert (bv);
  assert (len > 0);

  int i;
  BtorBitVector *res;

  res = btor_new_bv (mm, bv->width + len);
  memcpy (
      res->bits + res->len - bv->len, bv->bits, sizeof (*(bv->bits)) * bv->len);
  if (btor_get_bit_bv (bv, bv->width - 1))
  {
    i = (bv->width % BTOR_BV_TYPE_BW);
    res->bits[res->len - bv->len] |= (((uint64_t) -1) >> i) << i;
    for (i = res->len - bv->len - 1; i >= 0; i--) res->bits[i] = UINT_MAX;
  }

  return res;
}

BtorBitVector *
btor_uext_bv (BtorMemMgr *mm, BtorBitVector *bv, uint32_t len)
{
  assert (mm);
  assert (bv);
  assert (len > 0);

  BtorBitVector *res;

  res = btor_new_bv (mm, bv->width + len);
  memcpy (
      res->bits + res->len - bv->len, bv->bits, sizeof (*(bv->bits)) * bv->len);

  return res;
}

/*------------------------------------------------------------------------*/

bool
btor_is_umulo_bv (BtorMemMgr *mm, BtorBitVector *a, BtorBitVector *b)
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
    aext = btor_uext_bv (mm, a, a->width);
    bext = btor_uext_bv (mm, b, b->width);
    mul  = btor_mul_bv (mm, aext, bext);
    o    = btor_slice_bv (mm, mul, mul->width - 1, a->width);
    if (!btor_is_zero_bv (o)) res = true;
    btor_free_bv (mm, aext);
    btor_free_bv (mm, bext);
    btor_free_bv (mm, mul);
    btor_free_bv (mm, o);
  }

  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_gcd_ext_bv (Btor *btor,
                 BtorBitVector *bv1,
                 BtorBitVector *bv2,
                 BtorBitVector **fx,
                 BtorBitVector **fy)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (btor_compare_bv (bv1, bv2) <= 0);
  assert (fx);
  assert (fy);

  BtorBitVector *a, *b, *x, *y, *lx, *ly, *gcd      = 0;
  BtorBitVector *zero, *mul, *neg, *tx, *ty, *r, *q = 0;

  zero = btor_new_bv (btor->mm, bv1->width);

  a = btor_copy_bv (btor->mm, bv1);
  b = btor_copy_bv (btor->mm, bv2);

  x = btor_copy_bv (btor->mm, zero);            // 0
  y = btor_flipped_bit_bv (btor->mm, zero, 0);  // 1

  lx = btor_flipped_bit_bv (btor->mm, zero, 0);  // 1
  ly = btor_copy_bv (btor->mm, zero);            // 0

  r = btor_copy_bv (btor->mm, bv1);

  while (btor_compare_bv (b, zero) > 0)
  {
    if (gcd) btor_free_bv (btor->mm, gcd);
    gcd = btor_copy_bv (btor->mm, r);

    btor_free_bv (btor->mm, r);
    r = btor_urem_bv (btor->mm, a, b);  // r = a % b

    if (q) btor_free_bv (btor->mm, q);
    q = btor_udiv_bv (btor->mm, a, b);  // q = a / b

    btor_free_bv (btor->mm, a);
    a = btor_copy_bv (btor->mm, b);  // a = b
    btor_free_bv (btor->mm, b);
    b = btor_copy_bv (btor->mm, r);  // b = r

    tx  = btor_copy_bv (btor->mm, x);  // tx = x
    mul = btor_mul_bv (btor->mm, x, q);
    neg = btor_neg_bv (btor->mm, mul);
    btor_free_bv (btor->mm, x);
    x = btor_add_bv (btor->mm, lx, neg);  // x = lx - x * q
    btor_free_bv (btor->mm, neg);
    btor_free_bv (btor->mm, mul);
    btor_free_bv (btor->mm, lx);
    lx = tx;  // lx = tx

    ty  = btor_copy_bv (btor->mm, y);  // ty = y
    mul = btor_mul_bv (btor->mm, y, q);
    neg = btor_neg_bv (btor->mm, mul);
    btor_free_bv (btor->mm, y);
    y = btor_add_bv (btor->mm, ly, neg);  // y = ly - y * q
    btor_free_bv (btor->mm, neg);
    btor_free_bv (btor->mm, mul);
    btor_free_bv (btor->mm, ly);
    ly = ty;  // ly = ty
  }

  *fx = lx;
  *fy = ly;
  btor_free_bv (btor->mm, r);
  btor_free_bv (btor->mm, q);
  btor_free_bv (btor->mm, a);
  btor_free_bv (btor->mm, b);
  btor_free_bv (btor->mm, x);
  btor_free_bv (btor->mm, y);
  btor_free_bv (btor->mm, zero);
  return gcd;
}

/* Calculate modular inverse for bv by means of the Extended Euclidian
 * Algorithm. Note that c must be odd (the greatest
 * common divisor gcd (c, 2^bw) must be and is in this case always 1).  */
BtorBitVector *
btor_mod_inverse_bv (BtorMemMgr *mm, BtorBitVector *bv)
{
  assert (mm);
  assert (bv);
  assert (btor_get_bit_bv (bv, 0)); /* bv must be odd */

  uint32_t i;
  BtorBitVector *a, *b, *y, *ly, *ty, *q, *yq, *r, *res;

  /* a = 2^bw
   * b = bv
   * lx * a + ly * b = gcd (a, b) = 1
   * -> lx * a = lx * 2^bw = 0 (2^bw_[bw] = 0)
   * -> ly * b = bv^-1 * bv = 1
   * -> ly is modular inverse of bv */

  a = btor_new_bv (mm, bv->width + 1);
  btor_set_bit_bv (a, a->width - 1, 1); /* 2^bw */

  b = btor_new_bv (mm, bv->width + 1); /* extend to bw of a */
  for (i = 0; i < bv->width; i++)
    btor_set_bit_bv (b, i, btor_get_bit_bv (bv, i));

  y  = btor_one_bv (mm, bv->width + 1);
  ly = btor_new_bv (mm, bv->width + 1);

  while (!btor_is_zero_bv (b))
  {
    udiv_urem_bv (mm, a, b, &q, &r);
    btor_free_bv (mm, a);

    a = b;
    b = r;

    ty = y;
    yq = btor_mul_bv (mm, y, q);
    btor_free_bv (mm, q);
    y = btor_sub_bv (mm, ly, yq); /* y = ly - y * q */
    btor_free_bv (mm, yq);

    btor_free_bv (mm, ly);
    ly = ty;
  }

  res = btor_slice_bv (mm, ly, bv->width - 1, 0);

#ifndef NDEBUG
  assert (res->width == bv->width);
  ty = btor_mul_bv (mm, bv, res);
  assert (btor_is_one_bv (ty));
  btor_free_bv (mm, ty);
#endif

  btor_free_bv (mm, ly);
  btor_free_bv (mm, y);
  btor_free_bv (mm, b);
  btor_free_bv (mm, a);

  return res;
}

/*------------------------------------------------------------------------*/

BtorBitVectorTuple *
btor_new_bv_tuple (BtorMemMgr *mm, uint32_t arity)
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
btor_add_to_bv_tuple (BtorMemMgr *mm,
                      BtorBitVectorTuple *t,
                      BtorBitVector *bv,
                      uint32_t pos)
{
  assert (mm);
  assert (t);
  assert (bv);
  assert (pos < t->arity);
  assert (!t->bv[pos]);
  t->bv[pos] = btor_copy_bv (mm, bv);
}

void
btor_free_bv_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t)
{
  assert (mm);
  assert (t);

  uint32_t i;

  for (i = 0; i < t->arity; i++) btor_free_bv (mm, t->bv[i]);
  btor_free (mm, t->bv, sizeof (BtorBitVectorTuple *) * t->arity);
  btor_free (mm, t, sizeof (BtorBitVectorTuple));
}

int
btor_compare_bv_tuple (BtorBitVectorTuple *t0, BtorBitVectorTuple *t1)
{
  assert (t0);
  assert (t1);
  assert (t0->arity == t1->arity);

  uint32_t i;
  int j;

  for (i = 0; i < t0->arity; i++)
  {
    assert (t0->bv[i]);
    assert (t1->bv[i]);
    j = btor_compare_bv (t0->bv[i], t1->bv[i]);
    if (j != 0) return j;
  }

  return 0;
}

uint32_t
btor_hash_bv_tuple (BtorBitVectorTuple *t)
{
  assert (t);

  uint32_t i, hash = 0;

  for (i = 0; i < t->arity; i++)
  {
    assert (t->bv[i]);
    hash += btor_hash_bv (t->bv[i]);
  }

  return hash;
}

BtorBitVectorTuple *
btor_copy_bv_tuple (BtorMemMgr *mm, BtorBitVectorTuple *t)
{
  assert (mm);
  assert (t);

  uint32_t i;
  BtorBitVectorTuple *res;

  res = btor_new_bv_tuple (mm, t->arity);

  for (i = 0; i < t->arity; i++)
  {
    assert (t->bv[i]);
    res->bv[i] = btor_copy_bv (mm, t->bv[i]);
  }

  return res;
}

size_t
btor_size_bv_tuple (BtorBitVectorTuple *t)
{
  assert (t);

  uint32_t i;
  size_t res;

  res = sizeof (BtorBitVectorTuple) + t->arity * sizeof (BtorBitVector *);
  for (i = 0; i < t->arity; i++) res += btor_size_bv (t->bv[i]);

  return res;
}

/*------------------------------------------------------------------------*/

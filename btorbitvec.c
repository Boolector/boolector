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

#ifndef NDEBUG
static int
rem_bits_zero_dbg (BtorBitVector *bv)
{
  assert (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
  return 1;
}

static int
btor_check_bits_sll_dbg (BtorBitVector *bv, BtorBitVector *res, int shift)
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
  res->len   = i;
  res->width = bw;
  return res;
}

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

static void
set_rem_bits_to_zero (BtorBitVector *bv)
{
  if ((unsigned) bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
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

bool
btor_is_true_bv (BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return btor_get_bit_bv (bv, 0);
}

bool
btor_is_false_bv (BtorBitVector *bv)
{
  assert (bv);

  if (bv->width != 1) return 0;
  return !btor_get_bit_bv (bv, 0);
}

bool
btor_is_zero_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;
  for (i = 0; i < bv->len; i++)
    if (bv->bits[i] != 0) return false;
  return true;
}

bool
btor_is_one_bv (BtorBitVector *bv)
{
  assert (bv);

  int i;
  if (bv->bits[bv->len - 1] != 1) return false;
  for (i = bv->len - 2; i >= 0; i--)
    if (bv->bits[i] != 0) return false;
  return true;
}

bool
btor_is_ones_bv (BtorBitVector *bv)
{
  assert (bv);

  int i, n;
  for (i = bv->len - 1; i >= 1; i--)
    if (bv->bits[i] != UINT_MAX) return false;
  if (bv->width == BTOR_BV_TYPE_BW)
    return bv->bits[0] == UINT_MAX;
  else
  {
    n = BTOR_BV_TYPE_BW - bv->width % BTOR_BV_TYPE_BW;
    assert (n > 0);
    if (bv->bits[0] != UINT_MAX >> n) return false;
  }
  return true;
}

int
btor_is_power_of_two_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t i, j;
  int bit;
  bool iszero;

  for (i = 0, j = 0, iszero = true; i < bv->width; i++)
  {
    bit = btor_get_bit_bv (bv, i);
    if (!bit) continue;
    if (bit && !iszero) return -1;
    assert (bit && iszero);
    j      = i;
    iszero = false;
  }
  return j;
}

int
btor_is_small_positive_int_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;

  for (i = 0; i < bv->len - 1; i++)
    if (bv->bits[i] != 0) return -1;
  if (((int32_t) bv->bits[bv->len - 1]) < 0) return -1;
  return bv->bits[bv->len - 1];
}

int
btor_get_num_leading_zeros_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;
  int res;

  for (i = bv->width - 1, res = 0; i < UINT_MAX; i--)
  {
    if (btor_get_bit_bv (bv, i)) break;
    res += 1;
  }

  return res;
}

int
btor_get_num_leading_ones_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t i;
  int res;

  for (i = bv->width - 1, res = 0; i < UINT_MAX; i--)
  {
    if (!btor_get_bit_bv (bv, i)) break;
    res += 1;
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
  assert (btor_check_bits_sll_dbg (a, res, shift));
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

BtorBitVector *
btor_one_bv (BtorMemMgr *mm, uint32_t width)
{
  assert (mm);
  assert (width > 0);

  BtorBitVector *res;

  res = btor_new_bv (mm, width);
  btor_set_bit_bv (res, 0, 1);
  return res;
}

BtorBitVector *
btor_ones_bv (BtorMemMgr *mm, uint32_t width)
{
  assert (mm);
  assert (width > 0);

  BtorBitVector *res, *tmp;

  tmp = btor_new_bv (mm, width);
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

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};

#define NPRIMES ((int) (sizeof hash_primes / sizeof *hash_primes))

uint32_t
btor_hash_bv (BtorBitVector *bv)
{
  assert (bv);

  uint32_t res = 0, i, j;

  for (i = 0, j = 0; i < bv->len; i++)
  {
    res += hash_primes[j++] * bv->bits[i];
    if (j == NPRIMES) j = 0;
  }
  return res;
}

/*------------------------------------------------------------------------*/

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
   *    * b = bv
   *       * lx * a + ly * b = gcd (a, b) = 1
   *          * -> lx * a = lx * 2^bw = 0 (2^bw_[bw] = 0)
   *             * -> ly * b = bv^-1 * bv = 1
   *                * -> ly is modular inverse of bv */

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

BtorSpecialConstBitVector
btor_is_special_const_bv (BtorBitVector *bv)
{
  assert (bv);

  if (btor_is_zero_bv (bv)) return BTOR_SPECIAL_CONST_BV_ZERO;
  if (btor_is_one_bv (bv))
    return bv->width == 1 ? BTOR_SPECIAL_CONST_BV_ONE_ONES
                          : BTOR_SPECIAL_CONST_BV_ONE;
  if (btor_is_ones_bv (bv))
  {
    assert (bv->width > 1);
    return BTOR_SPECIAL_CONST_BV_ONES;
  }
  return BTOR_SPECIAL_CONST_BV_NONE;
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

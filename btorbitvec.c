/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Mathias Preiner.
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
#include "btorutil.h"

#define BTOR_MASK_REM_BITS(bv)                       \
  ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1) \
   >> (BTOR_BV_TYPE_BW - 1 - (bv->width % BTOR_BV_TYPE_BW)))

#ifndef NDEBUG
static int
rem_bits_zero_dbg (BitVector *bv)
{
  assert (bv->width % BTOR_BV_TYPE_BW == 0
          || (bv->bits[0] >> (bv->width % BTOR_BV_TYPE_BW) == 0));
  return 1;
}

static int
check_bits_sll_dbg (BitVector *bv, BitVector *res, int shift)
{
  assert (bv);
  assert (res);
  assert (bv->width == res->width);

  int i;

  for (i = 0; shift + i < bv->width; i++)
    assert (btor_get_bit_bv (bv, i) == btor_get_bit_bv (res, shift + i));

  return 1;
}
#endif

/*------------------------------------------------------------------------*/

BitVectorTuple *
btor_new_bv_tuple (Btor *btor, int arity)
{
  assert (btor);
  assert (arity > 0);

  BitVectorTuple *res;

  BTOR_CNEW (btor->mm, res);
  BTOR_CNEWN (btor->mm, res->bv, arity);
  res->arity = arity;
  return res;
}

void
btor_add_to_bv_tuple (Btor *btor, BitVectorTuple *t, BitVector *bv, int pos)
{
  assert (btor);
  assert (t);
  assert (!BTOR_IS_INVERTED_BV (bv));
  assert (bv);
  assert (pos >= 0);
  assert (pos < t->arity);
  assert (!t->bv[pos]);
  t->bv[pos] = btor_copy_bv (btor, bv);
}

void
btor_free_bv_tuple (Btor *btor, BitVectorTuple *t)
{
  assert (btor);
  assert (t);

  int i;
  for (i = 0; i < t->arity; i++) btor_free_bv (btor, t->bv[i]);

  btor_free (btor->mm, t->bv, sizeof (BitVectorTuple *) * t->arity);
  btor_free (btor->mm, t, sizeof (BitVectorTuple));
}

int
btor_compare_bv_tuple (BitVectorTuple *t0, BitVectorTuple *t1)
{
  assert (t0);
  assert (t1);
  assert (t0->arity == t1->arity);

  int i, j;

  for (i = 0; i < t0->arity; i++)
  {
    assert (t0->bv[i]);
    assert (t1->bv[i]);
    j = btor_compare_bv (t0->bv[i], t1->bv[i]);
    if (j != 0) return j;
  }

  return 0;
}

unsigned int
btor_hash_bv_tuple (BitVectorTuple *t)
{
  assert (t);

  int i;
  unsigned int hash = 0;

  for (i = 0; i < t->arity; i++)
  {
    assert (t->bv[i]);
    hash += btor_hash_bv (t->bv[i]);
  }

  return hash;
}

BitVectorTuple *
btor_copy_bv_tuple (Btor *btor, BitVectorTuple *t)
{
  assert (btor);
  assert (t);

  int i;
  BitVectorTuple *res;

  res = btor_new_bv_tuple (btor, t->arity);

  for (i = 0; i < t->arity; i++)
  {
    assert (t->bv[i]);
    res->bv[i] = btor_copy_bv (btor, t->bv[i]);
  }

  return res;
}

size_t
btor_size_bv_tuple (BitVectorTuple *t)
{
  assert (t);

  int i;
  size_t res;

  res = sizeof (BitVectorTuple) + t->arity * sizeof (BitVector *);
  for (i = 0; i < t->arity; i++) res += btor_size_bv (t->bv[i]);

  return res;
}

/*------------------------------------------------------------------------*/

void
btor_print_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  int i;

  for (i = bv->width - 1; i >= 0; i--) printf ("%d", btor_get_bit_bv (bv, i));
  printf ("\n");
}

void
btor_print_all_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

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

BitVector *
btor_new_bv (Btor *btor, int bw)
{
  assert (btor);
  assert (bw > 0);

  int i;
  BitVector *res;

  i = bw / BTOR_BV_TYPE_BW;
  if (bw % BTOR_BV_TYPE_BW > 0) i += 1;

  assert (i > 0);
  BTOR_CNEW (btor->mm, res);
  BTOR_NEWN (btor->mm, res->bits, i);
  BTOR_CLRN (res->bits, i);
  res->len   = i;
  res->width = bw;
  return res;
}

size_t
btor_size_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));
  return sizeof (BitVector) + bv->len * sizeof (BTOR_BV_TYPE);
}

void
btor_free_bv (Btor *btor, BitVector *bv)
{
  assert (btor);
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));
  btor_free (btor->mm, bv->bits, sizeof (*(bv->bits)) * bv->len);
  btor_free (btor->mm, bv, sizeof (BitVector));
}

int
btor_get_bit_bv (const BitVector *bv, int pos)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  int i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;

  return (bv->bits[bv->len - 1 - i] >> j) & 1;
}

static void
btor_set_bit_bv (BitVector *bv, int pos, int bit)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));
  assert (bv->len > 0);
  assert (bit == 0 || bit == 1);
  assert (pos < bv->width);

  int i, j;

  i = pos / BTOR_BV_TYPE_BW;
  j = pos % BTOR_BV_TYPE_BW;
  assert (i < bv->len);

  if (bit)
    bv->bits[bv->len - 1 - i] |= (1u << j);
  else
    bv->bits[bv->len - 1 - i] &= ~(1u << j);
}

static void
set_rem_bits_to_zero (BitVector *bv)
{
  assert (!BTOR_IS_INVERTED_BV (bv));
  if ((unsigned) bv->width != BTOR_BV_TYPE_BW * bv->len)
    bv->bits[0] &= BTOR_MASK_REM_BITS (bv);
}

uint64_t
btor_bv_to_uint64_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));
  assert ((unsigned) bv->width <= sizeof (uint64_t) * 8);
  assert (bv->len <= 2);

  int i;
  uint64_t res;

  res = 0;
  for (i = 0; i < bv->len; i++)
    res |= ((uint64_t) bv->bits[i]) << (BTOR_BV_TYPE_BW * (bv->len - 1 - i));

  return res;
}

char *
btor_bv_to_char_bv (Btor *btor, const BitVector *bv)
{
  assert (btor);
  assert (bv);

  int i, bw, inv, bit;
  char *res;

  inv = BTOR_IS_INVERTED_BV (bv);
  bv  = BTOR_REAL_ADDR_BV (bv);
  bw  = bv->width;
  BTOR_NEWN (btor->mm, res, bw + 1);
  for (i = 0; i < bw; i++)
  {
    bit             = btor_get_bit_bv (bv, i);
    res[bw - 1 - i] = ((bit && !inv) || (!bit && inv)) ? '1' : '0';
  }
  res[bw] = '\0';

  return res;
}

BitVector *
btor_char_to_bv (Btor *btor, char *assignment)
{
  assert (btor);
  assert (assignment);
  assert (strlen (assignment) > 0);

  int i, j, bit;
  BitVector *res;

  res = btor_new_bv (btor, strlen (assignment));

  for (i = 0; i < res->width; i++)
  {
    j = res->width - 1 - i;
    assert (assignment[j] == '0' || assignment[j] == '1');
    bit = assignment[j] == '0' ? 0 : 1;
    btor_set_bit_bv (res, i, bit);
  }

  return res;
}

int
btor_is_true_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  if (bv->width != 1) return 0;
  return btor_get_bit_bv (bv, 0);
}

int
btor_is_false_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  if (bv->width != 1) return 0;
  return !btor_get_bit_bv (bv, 0);
}

BitVector *
btor_uint64_to_bv (Btor *btor, uint64_t value, int bw)
{
  assert (btor);
  assert (bw > 0);

  BitVector *res;

  res = btor_new_bv (btor, bw);
  assert (res->len > 0);
  res->bits[res->len - 1] = (BTOR_BV_TYPE) value;
  if (res->width > 32)
    res->bits[res->len - 2] = (BTOR_BV_TYPE) (value >> BTOR_BV_TYPE_BW);

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BitVector *
btor_assignment_bv (Btor *btor, BtorNode *exp, int init_x_values)
{
  assert (btor);
  assert (exp);
  assert (init_x_values || BTOR_REAL_ADDR_NODE (exp)->av);
  assert (init_x_values == 0 || init_x_values == 1);

  int i, j, len, bit, inv;
  BtorNode *real_exp;
  BitVector *res;
  BtorAIGVec *av;
  BtorAIGMgr *amgr;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (!real_exp->av) return btor_new_bv (btor, real_exp->len);

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  av   = real_exp->av;
  len  = av->len;
  res  = btor_new_bv (btor, len);
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

BitVector *
btor_copy_bv (Btor *btor, BitVector *bv)
{
  assert (btor);
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  BitVector *res;

  res = btor_new_bv (btor, bv->width);
  assert (res->width == bv->width);
  assert (res->len == bv->len);
  memcpy (res->bits, bv->bits, sizeof (*(bv->bits)) * bv->len);
  assert (btor_compare_bv (res, bv) == 0);
  return res;
}

BitVector *
btor_not_bv (Btor *btor, BitVector *bv)
{
  assert (btor);
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));
  //  btor->evals[0]++;

  int i;
  BitVector *res;

  res = btor_new_bv (btor, bv->width);
  for (i = 0; i < bv->len; i++) res->bits[i] = ~bv->bits[i];

  set_rem_bits_to_zero (res);
  assert (rem_bits_zero_dbg (res));
  return res;
}

BitVector *
btor_add_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a);
  assert (b);
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i;
  uint64_t x, y, sum;
  BitVector *res;
  BTOR_BV_TYPE carry;

  if (a->width <= 64)
  {
    x   = btor_bv_to_uint64_bv (a);
    y   = btor_bv_to_uint64_bv (b);
    res = btor_uint64_to_bv (btor, x + y, a->width);
  }
  else
  {
    res   = btor_new_bv (btor, a->width);
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

BitVector *
btor_and_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);
  //  btor->evals[BTOR_AND_NODE]++;

  int i;
  BitVector *res;

  res = btor_new_bv (btor, a->width);
  for (i = a->len - 1; i >= 0; i--) res->bits[i] = a->bits[i] & b->bits[i];

  assert (rem_bits_zero_dbg (res));
  return res;
}

BitVector *
btor_eq_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);
  //  btor->evals[BTOR_BEQ_NODE]++;

  int i, bit;
  BitVector *res;

  res = btor_new_bv (btor, 1);
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

BitVector *
btor_ult_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);
  //  btor->evals[BTOR_ULT_NODE]++;

  int i, bit;
  BitVector *res;

  res = btor_new_bv (btor, 1);
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

static BitVector *
sll_bv (Btor *btor, BitVector *a, int shift)
{
  assert (btor);
  assert (a);
  assert (!BTOR_IS_INVERTED_BV (a));

  int skip, i, j, k;
  BitVector *res;
  BTOR_BV_TYPE v;

  res  = btor_new_bv (btor, a->width);
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

BitVector *
btor_sll_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (btor_is_power_of_2_util (a->width));
  assert (btor_log_2_util (a->width) == b->width);

  uint64_t shift;
  shift = btor_bv_to_uint64_bv (b);
  return sll_bv (btor, a, (int) shift);
}

BitVector *
btor_srl_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));

  int skip, i, j, k;
  uint64_t shift;
  BitVector *res;
  BTOR_BV_TYPE v;

  res   = btor_new_bv (btor, a->width);
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

BitVector *
btor_mul_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i;
  uint64_t x, y;
  BitVector *res, *and, *shift, *add;

  if (a->width <= 64)
  {
    x   = btor_bv_to_uint64_bv (a);
    y   = btor_bv_to_uint64_bv (b);
    res = btor_uint64_to_bv (btor, x * y, a->width);
  }
  else
  {
    res = btor_new_bv (btor, a->width);
    for (i = 0; i < a->width; i++)
    {
      if (btor_get_bit_bv (b, i))
        and = btor_copy_bv (btor, a);
      else
        and = btor_new_bv (btor, a->width);
      shift = sll_bv (btor, and, i);
      add   = btor_add_bv (btor, res, shift);
      btor_free_bv (btor, and);
      btor_free_bv (btor, shift);
      btor_free_bv (btor, res);
      res = add;
    }
  }
  return res;
}

BitVector *
btor_neg_bv (Btor *btor, BitVector *bv)
{
  assert (btor);
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  BitVector *not_bv, *one, *neg_b;

  not_bv = btor_not_bv (btor, bv);
  one    = btor_uint64_to_bv (btor, 1, bv->width);
  neg_b  = btor_add_bv (btor, not_bv, one);
  btor_free_bv (btor, not_bv);
  btor_free_bv (btor, one);

  return neg_b;
}

static void
udiv_urem_bv (
    Btor *btor, BitVector *a, BitVector *b, BitVector **q, BitVector **r)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i, is_true;
  uint64_t x, y, z;

  BitVector *neg_b, *quot, *rem, *ult, *eq, *tmp;

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
    quot = btor_uint64_to_bv (btor, x, a->width);
    rem  = btor_uint64_to_bv (btor, y, a->width);
  }
  else
  {
    neg_b = btor_neg_bv (btor, b);
    quot  = btor_new_bv (btor, a->width);
    rem   = btor_new_bv (btor, a->width);

    for (i = a->width - 1; i >= 0; i--)
    {
      tmp = sll_bv (btor, rem, 1);
      btor_free_bv (btor, rem);
      rem = tmp;
      btor_set_bit_bv (rem, 0, btor_get_bit_bv (a, i));

      ult     = btor_ult_bv (btor, b, rem);
      is_true = btor_is_true_bv (ult);
      btor_free_bv (btor, ult);

      if (is_true) goto UDIV_UREM_SUBTRACT;

      eq      = btor_eq_bv (btor, b, rem);
      is_true = btor_is_true_bv (eq);
      btor_free_bv (btor, eq);

      if (is_true)
      {
      UDIV_UREM_SUBTRACT:
        tmp = btor_add_bv (btor, rem, neg_b);
        btor_free_bv (btor, rem);
        rem = tmp;
        btor_set_bit_bv (quot, i, 1);
      }
    }
    btor_free_bv (btor, neg_b);
  }

  if (q)
    *q = quot;
  else
    btor_free_bv (btor, quot);

  if (r)
    *r = rem;
  else
    btor_free_bv (btor, rem);
}

BitVector *
btor_udiv_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);

  BitVector *res = 0;
  udiv_urem_bv (btor, a, b, &res, 0);
  assert (res);
  return res;
}

BitVector *
btor_urem_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);

  BitVector *res = 0;
  udiv_urem_bv (btor, a, b, 0, &res);
  assert (res);
  return res;
}

BitVector *
btor_concat_bv (Btor *btor, BitVector *a, BitVector *b)
{
  assert (btor);
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));

  int i, j, k;
  BTOR_BV_TYPE v;
  BitVector *res;

  res = btor_new_bv (btor, a->width + b->width);

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

BitVector *
btor_slice_bv (Btor *btor, BitVector *bv, int upper, int lower)
{
  assert (btor);
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));
  //  btor->evals[BTOR_SLICE_NODE]++;

  int i, j;
  BitVector *res;

  res = btor_new_bv (btor, upper - lower + 1);
  for (i = lower, j = 0; i <= upper; i++)
    btor_set_bit_bv (res, j++, btor_get_bit_bv (bv, i));

  assert (rem_bits_zero_dbg (res));
  return res;
}

int
btor_compare_bv (BitVector *a, BitVector *b)
{
  assert (a);
  assert (b);
  assert (!BTOR_IS_INVERTED_BV (a));
  assert (!BTOR_IS_INVERTED_BV (b));
  assert (a->len == b->len);
  assert (a->width == b->width);

  int i;

  /* find index on which a and b differ */
  for (i = 0; i < a->len && a->bits[i] == b->bits[i]; i++)
    ;

  if (i == a->len) return 0;

  if (a->bits[i] > b->bits[i]) return 1;

  assert (a->bits[i] < b->bits[i]);
  return -1;
}

unsigned int
btor_hash_bv (BitVector *bv)
{
  assert (bv);
  assert (!BTOR_IS_INVERTED_BV (bv));

  int i;
  unsigned int hash = 0;

  for (i = 0; i < bv->len; i++) hash += bv->bits[i] * 7334147u;

  return hash;
}

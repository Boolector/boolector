/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraigvec.h"
#include "btorcore.h"
#include "btoropt.h"
#include "utils/btoraigmap.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static BtorAIGVec *
new_aigvec (BtorAIGVecMgr *avmgr, uint32_t width)
{
  assert (avmgr);
  assert (width > 0);

  BtorAIGVec *result;

  result        = btor_mem_malloc (avmgr->btor->mm,
                            sizeof (BtorAIGVec) + sizeof (BtorAIG *) * width);
  result->width = width;
  avmgr->cur_num_aigvecs++;
  if (avmgr->max_num_aigvecs < avmgr->cur_num_aigvecs)
    avmgr->max_num_aigvecs = avmgr->cur_num_aigvecs;
  return result;
}

BtorAIGVec *
btor_aigvec_const (BtorAIGVecMgr *avmgr, const BtorBitVector *bits)
{
  assert (avmgr);
  assert (bits);

  BtorAIGVec *result;
  uint32_t i, width;
  width = bits->width;
  assert (width > 0);
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] =
        !btor_bv_get_bit (bits, width - 1 - i) ? BTOR_AIG_FALSE : BTOR_AIG_TRUE;
  return result;
}

BtorAIGVec *
btor_aigvec_var (BtorAIGVecMgr *avmgr, uint32_t width)
{
  assert (avmgr);
  assert (width > 0);

  BtorAIGVec *result;
  uint32_t i;

  result = new_aigvec (avmgr, width);
  for (i = 1; i <= width; i++)
    result->aigs[width - i] = btor_aig_var (avmgr->amgr);
  return result;
}

void
btor_aigvec_invert (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  uint32_t i, width;
  (void) avmgr;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  width = av->width;
  for (i = 0; i < width; i++) av->aigs[i] = BTOR_INVERT_AIG (av->aigs[i]);
}

BtorAIGVec *
btor_aigvec_not (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  width  = av->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_not (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_slice (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t upper,
                   uint32_t lower)
{
  BtorAIGVec *result;
  uint32_t i, width, diff, counter;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  assert (upper < av->width);
  assert (lower <= upper);
  counter = 0;
  width   = av->width;
  diff    = upper - lower;
  result  = new_aigvec (avmgr, diff + 1);
  for (i = width - upper - 1; i <= width - upper - 1 + diff; i++)
    result->aigs[counter++] = btor_aig_copy (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_and (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  width  = av1->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_and (avmgr->amgr, av1->aigs[i], av2->aigs[i]);
  return result;
}

static BtorAIG *
lt_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIG *res, *tmp, *term0, *term1;
  uint32_t i, j;

  amgr = avmgr->amgr;
  res  = BTOR_AIG_FALSE;
  for (j = 1, i = av1->width - 1; j <= av1->width; j++, i--)
  {
    term0 = btor_aig_and (amgr, av1->aigs[i], BTOR_INVERT_AIG (av2->aigs[i]));

    tmp = btor_aig_and (amgr, BTOR_INVERT_AIG (term0), res);
    btor_aig_release (amgr, term0);
    btor_aig_release (amgr, res);
    res = tmp;

    term1 = btor_aig_and (amgr, BTOR_INVERT_AIG (av1->aigs[i]), av2->aigs[i]);

    tmp = btor_aig_or (amgr, term1, res);
    btor_aig_release (amgr, term1);
    btor_aig_release (amgr, res);
    res = tmp;
  }

  return res;
}

BtorAIGVec *
btor_aigvec_ult (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  result          = new_aigvec (avmgr, 1);
  result->aigs[0] = lt_aigvec (avmgr, av1, av2);
  return result;
}

BtorAIGVec *
btor_aigvec_eq (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *result_aig, *temp1, *temp2;
  uint32_t i, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  amgr       = avmgr->amgr;
  width      = av1->width;
  result     = new_aigvec (avmgr, 1);
  result_aig = btor_aig_eq (amgr, av1->aigs[0], av2->aigs[0]);
  for (i = 1; i < width; i++)
  {
    temp1 = btor_aig_eq (amgr, av1->aigs[i], av2->aigs[i]);
    temp2 = btor_aig_and (amgr, result_aig, temp1);
    btor_aig_release (amgr, temp1);
    btor_aig_release (amgr, result_aig);
    result_aig = temp2;
  }
  result->aigs[0] = result_aig;
  return result;
}

static BtorAIG *
half_adder (BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG **cout)
{
  BtorAIG *res, *x_and_y, *not_x, *not_y, *not_x_and_not_y, *x_xnor_y;
  x_and_y         = btor_aig_and (amgr, x, y);
  not_x           = BTOR_INVERT_AIG (x);
  not_y           = BTOR_INVERT_AIG (y);
  not_x_and_not_y = btor_aig_and (amgr, not_x, not_y);
  x_xnor_y        = btor_aig_or (amgr, x_and_y, not_x_and_not_y);
  res             = BTOR_INVERT_AIG (x_xnor_y);
  *cout           = x_and_y;
  btor_aig_release (amgr, not_x_and_not_y);
  return res;
}

static BtorAIG *
full_adder (
    BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG *cin, BtorAIG **cout)
{
  BtorAIG *sum, *c1, *c2, *res;
  sum   = half_adder (amgr, x, y, &c1);
  res   = half_adder (amgr, sum, cin, &c2);
  *cout = btor_aig_or (amgr, c1, c2);
  btor_aig_release (amgr, sum);
  btor_aig_release (amgr, c1);
  btor_aig_release (amgr, c2);
  return res;
}

static int32_t
compare_aigvec_lsb_first (BtorAIGVec *a, BtorAIGVec *b)
{
  uint32_t width, i;
  int32_t res;
  assert (a);
  assert (b);
  width = a->width;
  assert (width == b->width);
  res = 0;
  for (i = 0; !res && i < width; i++)
    res = btor_aig_compare (a->aigs[i], b->aigs[i]);
  return res;
}

BtorAIGVec *
btor_aigvec_add (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);

  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *cout, *cin;
  uint32_t i, j;

  if (btor_opt_get (avmgr->btor, BTOR_OPT_SORT_AIGVEC) > 0
      && compare_aigvec_lsb_first (av1, av2) > 0)
  {
    BTOR_SWAP (BtorAIGVec *, av1, av2);
  }

  amgr   = avmgr->amgr;
  result = new_aigvec (avmgr, av1->width);
  cout = cin = BTOR_AIG_FALSE; /* for 'cout' to avoid warning */
  for (j = 1, i = av1->width - 1; j <= av1->width; j++, i--)
  {
    result->aigs[i] = full_adder (amgr, av1->aigs[i], av2->aigs[i], cin, &cout);
    btor_aig_release (amgr, cin);
    cin = cout;
  }
  btor_aig_release (amgr, cout);
  return result;
}

static BtorAIGVec *
sll_n_bits_aigvec (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t n,
                   BtorAIG *shift)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *and1, *and2, *not_shift;
  uint32_t i, j, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  assert (n < av->width);
  if (n == 0) return btor_aigvec_copy (avmgr, av);
  amgr      = avmgr->amgr;
  width     = av->width;
  not_shift = btor_aig_not (amgr, shift);
  result    = new_aigvec (avmgr, width);
  for (i = 0; i < width - n; i++)
  {
    and1            = btor_aig_and (amgr, av->aigs[i], not_shift);
    and2            = btor_aig_and (amgr, av->aigs[i + n], shift);
    result->aigs[i] = btor_aig_or (amgr, and1, and2);
    btor_aig_release (amgr, and1);
    btor_aig_release (amgr, and2);
  }
  for (j = width - n; j < width; j++)
    result->aigs[j] = btor_aig_and (amgr, av->aigs[j], not_shift);
  btor_aig_release (amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_aigvec_sll (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result, *temp;
  uint32_t i, j, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width > 1);
  assert (btor_util_is_power_of_2 (av1->width));
  assert (btor_util_log_2 (av1->width) == av2->width);
  width  = av2->width;
  result = sll_n_bits_aigvec (avmgr, av1, 1, av2->aigs[av2->width - 1]);
  for (j = 2, i = width - 2; j <= width; j++, i--)
  {
    temp   = result;
    result = sll_n_bits_aigvec (
        avmgr, temp, btor_util_pow_2 (width - i - 1), av2->aigs[i]);
    btor_aigvec_release_delete (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
srl_n_bits_aigvec (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t n,
                   BtorAIG *shift)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *and1, *and2, *not_shift;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  assert (n < av->width);
  if (n == 0) return btor_aigvec_copy (avmgr, av);
  amgr      = avmgr->amgr;
  width     = av->width;
  not_shift = btor_aig_not (amgr, shift);
  result    = new_aigvec (avmgr, width);
  for (i = 0; i < n; i++)
    result->aigs[i] = btor_aig_and (amgr, av->aigs[i], not_shift);
  for (i = n; i < width; i++)
  {
    and1            = btor_aig_and (amgr, av->aigs[i], not_shift);
    and2            = btor_aig_and (amgr, av->aigs[i - n], shift);
    result->aigs[i] = btor_aig_or (amgr, and1, and2);
    btor_aig_release (amgr, and1);
    btor_aig_release (amgr, and2);
  }
  btor_aig_release (amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_aigvec_srl (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result, *temp;
  uint32_t i, j, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width > 1);
  assert (btor_util_is_power_of_2 (av1->width));
  assert (btor_util_log_2 (av1->width) == av2->width);
  width  = av2->width;
  result = srl_n_bits_aigvec (avmgr, av1, 1, av2->aigs[av2->width - 1]);
  for (j = 2, i = width - 2; j <= width; j++, i--)
  {
    temp   = result;
    result = srl_n_bits_aigvec (
        avmgr, temp, btor_util_pow_2 (width - i - 1), av2->aigs[i]);
    btor_aigvec_release_delete (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
mul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  BtorAIG *cin, *cout, *and, *tmp;
  BtorAIGMgr *amgr;
  BtorAIGVec *res;
  uint32_t i, j, k, ik, jk, width;

  width = a->width;
  amgr  = btor_aigvec_get_aig_mgr (avmgr);

  assert (width > 0);
  assert (width == b->width);

  if (btor_opt_get (avmgr->btor, BTOR_OPT_SORT_AIGVEC) > 0
      && compare_aigvec_lsb_first (a, b) > 0)
  {
    BTOR_SWAP (BtorAIGVec *, a, b);
  }

  res = new_aigvec (avmgr, width);

  for (k = 0; k < width; k++)
    res->aigs[k] = btor_aig_and (amgr, a->aigs[k], b->aigs[width - 1]);

  for (ik = 2, i = width - 2; ik <= width; ik++, i--)
  {
    cout = BTOR_AIG_FALSE;
    for (jk = 0, j = i; jk <= i; jk++, j--)
    {
      and = btor_aig_and (amgr, a->aigs[width - 1 - i + j], b->aigs[i]);
      tmp = res->aigs[j];
      cin = cout;
      res->aigs[j] = full_adder (amgr, tmp, and, cin, &cout);
      btor_aig_release (amgr, and);
      btor_aig_release (amgr, tmp);
      btor_aig_release (amgr, cin);
    }
    btor_aig_release (amgr, cout);
  }

  return res;
}

BtorAIGVec *
btor_aigvec_mul (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  return mul_aigvec (avmgr, a, b);
}

static void
SC_GATE_CO_aigvec (
    BtorAIGMgr *amgr, BtorAIG **CO, BtorAIG *R, BtorAIG *D, BtorAIG *CI)
{
  BtorAIG *D_or_CI, *D_and_CI, *M;
  D_or_CI  = btor_aig_or (amgr, D, CI);
  D_and_CI = btor_aig_and (amgr, D, CI);
  M        = btor_aig_and (amgr, D_or_CI, R);
  *CO      = btor_aig_or (amgr, M, D_and_CI);
  btor_aig_release (amgr, D_or_CI);
  btor_aig_release (amgr, D_and_CI);
  btor_aig_release (amgr, M);
}

static void
SC_GATE_S_aigvec (BtorAIGMgr *amgr,
                  BtorAIG **S,
                  BtorAIG *R,
                  BtorAIG *D,
                  BtorAIG *CI,
                  BtorAIG *Q)
{
  BtorAIG *D_and_CI, *D_or_CI;
  BtorAIG *T2_or_R, *T2_and_R;
  BtorAIG *T1, *T2;
  D_or_CI  = btor_aig_or (amgr, D, CI);
  D_and_CI = btor_aig_and (amgr, D, CI);
  T1       = btor_aig_and (amgr, D_or_CI, BTOR_INVERT_AIG (D_and_CI));
  T2       = btor_aig_and (amgr, T1, Q);
  T2_or_R  = btor_aig_or (amgr, T2, R);
  T2_and_R = btor_aig_and (amgr, T2, R);
  *S       = btor_aig_and (amgr, T2_or_R, BTOR_INVERT_AIG (T2_and_R));
  btor_aig_release (amgr, T1);
  btor_aig_release (amgr, T2);
  btor_aig_release (amgr, D_and_CI);
  btor_aig_release (amgr, D_or_CI);
  btor_aig_release (amgr, T2_and_R);
  btor_aig_release (amgr, T2_or_R);
}

static void
udiv_urem_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *Ain,
                  BtorAIGVec *Din,
                  BtorAIGVec **Qptr,
                  BtorAIGVec **Rptr)
{
  BtorAIG **A, **nD, ***S, ***C;
  BtorAIGVec *Q, *R;
  BtorAIGMgr *amgr;
  BtorMemMgr *mem;
  uint32_t size, i, j;

  size = Ain->width;
  assert (size > 0);

  amgr = btor_aigvec_get_aig_mgr (avmgr);
  mem  = avmgr->btor->mm;

  BTOR_NEWN (mem, A, size);
  for (i = 0; i < size; i++) A[i] = Ain->aigs[size - 1 - i];

  BTOR_NEWN (mem, nD, size);
  for (i = 0; i < size; i++) nD[i] = BTOR_INVERT_AIG (Din->aigs[size - 1 - i]);

  BTOR_NEWN (mem, S, size + 1);
  for (j = 0; j <= size; j++)
  {
    BTOR_NEWN (mem, S[j], size + 1);
    for (i = 0; i <= size; i++) S[j][i] = BTOR_AIG_FALSE;
  }

  BTOR_NEWN (mem, C, size + 1);
  for (j = 0; j <= size; j++)
  {
    BTOR_NEWN (mem, C[j], size + 1);
    for (i = 0; i <= size; i++) C[j][i] = BTOR_AIG_FALSE;
  }

  R = new_aigvec (avmgr, size);
  Q = new_aigvec (avmgr, size);

  for (j = 0; j <= size - 1; j++)
  {
    S[j][0] = btor_aig_copy (amgr, A[size - j - 1]);
    C[j][0] = BTOR_AIG_TRUE;

    for (i = 0; i <= size - 1; i++)
      SC_GATE_CO_aigvec (amgr, &C[j][i + 1], S[j][i], nD[i], C[j][i]);

    Q->aigs[j] = btor_aig_or (amgr, C[j][size], S[j][size]);

    for (i = 0; i <= size - 1; i++)
      SC_GATE_S_aigvec (
          amgr, &S[j + 1][i + 1], S[j][i], nD[i], C[j][i], Q->aigs[j]);
  }

  for (i = size; i >= 1; i--)
    R->aigs[size - i] = btor_aig_copy (amgr, S[size][i]);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_aig_release (amgr, C[j][i]);
    BTOR_DELETEN (mem, C[j], size + 1);
  }
  BTOR_DELETEN (mem, C, size + 1);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_aig_release (amgr, S[j][i]);
    BTOR_DELETEN (mem, S[j], size + 1);
  }
  BTOR_DELETEN (mem, S, size + 1);

  BTOR_DELETEN (mem, nD, size);
  BTOR_DELETEN (mem, A, size);

  *Qptr = Q;
  *Rptr = R;
}

BtorAIGVec *
btor_aigvec_udiv (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient  = 0;
  BtorAIGVec *remainder = 0;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_aigvec_release_delete (avmgr, remainder);
  return quotient;
}

BtorAIGVec *
btor_aigvec_urem (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient, *remainder;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_aigvec_release_delete (avmgr, quotient);
  return remainder;
}

BtorAIGVec *
btor_aigvec_concat (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  uint32_t i, pos, len_av1, len_av2;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width > 0);
  assert (av2->width > 0);
  assert (INT32_MAX - av1->width >= av2->width);
  pos     = 0;
  amgr    = avmgr->amgr;
  len_av1 = av1->width;
  len_av2 = av2->width;
  result  = new_aigvec (avmgr, len_av1 + len_av2);
  for (i = 0; i < len_av1; i++)
    result->aigs[pos++] = btor_aig_copy (amgr, av1->aigs[i]);
  for (i = 0; i < len_av2; i++)
    result->aigs[pos++] = btor_aig_copy (amgr, av2->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_cond (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *av_cond,
                  BtorAIGVec *av_if,
                  BtorAIGVec *av_else)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av_cond);
  assert (av_if);
  assert (av_else);
  assert (av_cond->width == 1);
  assert (av_if->width == av_else->width);
  assert (av_if->width > 0);
  amgr   = avmgr->amgr;
  width  = av_if->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_cond (
        amgr, av_cond->aigs[0], av_if->aigs[i], av_else->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_copy (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  amgr   = avmgr->amgr;
  width  = av->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_copy (amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_clone (BtorAIGVec *av, BtorAIGVecMgr *avmgr)
{
  assert (av);
  assert (avmgr);

  uint32_t i;
  BtorAIGVec *res;
  BtorAIGMgr *amgr;
  BtorAIG *aig, *caig;

  amgr = avmgr->amgr;
  res  = new_aigvec (avmgr, av->width);
  for (i = 0; i < av->width; i++)
  {
    if (btor_aig_is_const (av->aigs[i]))
      res->aigs[i] = av->aigs[i];
    else
    {
      aig = av->aigs[i];
      assert (BTOR_REAL_ADDR_AIG (aig)->id >= 0);
      assert ((size_t) BTOR_REAL_ADDR_AIG (aig)->id
              < BTOR_COUNT_STACK (amgr->id2aig));
      caig = BTOR_PEEK_STACK (amgr->id2aig, BTOR_REAL_ADDR_AIG (aig)->id);
      assert (caig);
      assert (!btor_aig_is_const (caig));
      if (BTOR_IS_INVERTED_AIG (aig))
        res->aigs[i] = BTOR_INVERT_AIG (caig);
      else
        res->aigs[i] = caig;
      assert (res->aigs[i]);
    }
  }
  return res;
}

void
btor_aigvec_to_sat_tseitin (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  amgr = btor_aigvec_get_aig_mgr (avmgr);
  if (!btor_sat_is_initialized (amgr->smgr)) return;
  width = av->width;
  for (i = 0; i < width; i++) btor_aig_to_sat_tseitin (amgr, av->aigs[i]);
}

void
btor_aigvec_release_delete (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  mm    = avmgr->btor->mm;
  amgr  = avmgr->amgr;
  width = av->width;
  for (i = 0; i < width; i++) btor_aig_release (amgr, av->aigs[i]);
  btor_mem_free (mm, av, sizeof (BtorAIGVec) + sizeof (BtorAIG *) * av->width);
  avmgr->cur_num_aigvecs--;
}

BtorAIGVecMgr *
btor_aigvec_mgr_new (Btor *btor)
{
  assert (btor);

  BtorAIGVecMgr *avmgr;
  BTOR_CNEW (btor->mm, avmgr);
  avmgr->btor = btor;
  avmgr->amgr = btor_aig_mgr_new (btor);
  return avmgr;
}

BtorAIGVecMgr *
btor_aigvec_mgr_clone (Btor *btor, BtorAIGVecMgr *avmgr)
{
  assert (btor);
  assert (avmgr);

  BtorAIGVecMgr *res;
  BTOR_NEW (btor->mm, res);

  res->btor            = btor;
  res->amgr            = btor_aig_mgr_clone (btor, avmgr->amgr);
  res->max_num_aigvecs = avmgr->max_num_aigvecs;
  res->cur_num_aigvecs = avmgr->cur_num_aigvecs;
  return res;
}

void
btor_aigvec_mgr_delete (BtorAIGVecMgr *avmgr)
{
  assert (avmgr);
  btor_aig_mgr_delete (avmgr->amgr);
  BTOR_DELETE (avmgr->btor->mm, avmgr);
}

BtorAIGMgr *
btor_aigvec_get_aig_mgr (const BtorAIGVecMgr *avmgr)
{
  return avmgr ? avmgr->amgr : 0;
}

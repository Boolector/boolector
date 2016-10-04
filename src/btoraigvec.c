/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
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
new_aigvec (BtorAIGVecMgr *avmgr, uint32_t len)
{
  assert (avmgr);
  assert (len > 0);

  BtorAIGVec *result;

  result      = btor_malloc (avmgr->btor->mm,
                        sizeof (BtorAIGVec) + sizeof (BtorAIG *) * len);
  result->len = len;
  avmgr->cur_num_aigvecs++;
  if (avmgr->max_num_aigvecs < avmgr->cur_num_aigvecs)
    avmgr->max_num_aigvecs = avmgr->cur_num_aigvecs;
  return result;
}

BtorAIGVec *
btor_const_aigvec (BtorAIGVecMgr *avmgr, const BtorBitVector *bits)
{
  assert (avmgr);
  assert (bits);

  BtorAIGVec *result;
  int i, len;
  len = bits->width;
  assert (len > 0);
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] =
        !btor_get_bit_bv (bits, len - 1 - i) ? BTOR_AIG_FALSE : BTOR_AIG_TRUE;
  return result;
}

BtorAIGVec *
btor_var_aigvec (BtorAIGVecMgr *avmgr, uint32_t len)
{
  assert (avmgr);
  assert (len > 0);

  BtorAIGVec *result;
  int i;

  result = new_aigvec (avmgr, len);
  for (i = len - 1; i >= 0; i--) result->aigs[i] = btor_var_aig (avmgr->amgr);
  return result;
}

void
btor_invert_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  int i, len;
  (void) avmgr;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  len = av->len;
  for (i = 0; i < len; i++) av->aigs[i] = BTOR_INVERT_AIG (av->aigs[i]);
}

BtorAIGVec *
btor_not_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGVec *result;
  int i, len;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  len    = av->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_not_aig (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_slice_aigvec (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t upper,
                   uint32_t lower)
{
  BtorAIGVec *result;
  unsigned i, len, diff, counter;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  assert (upper < av->len);
  assert (lower <= upper);
  counter = 0;
  len     = av->len;
  diff    = upper - lower;
  result  = new_aigvec (avmgr, diff + 1);
  for (i = len - upper - 1; i <= len - upper - 1 + diff; i++)
    result->aigs[counter++] = btor_copy_aig (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_and_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  int i, len;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len    = av1->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_and_aig (avmgr->amgr, av1->aigs[i], av2->aigs[i]);
  return result;
}

static BtorAIG *
lt_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIG *res, *tmp, *term0, *term1;
  int i;

  amgr = avmgr->amgr;
  res  = BTOR_AIG_FALSE;
  for (i = av1->len - 1; i >= 0; i--)
  {
    term0 = btor_and_aig (amgr, av1->aigs[i], BTOR_INVERT_AIG (av2->aigs[i]));

    tmp = btor_and_aig (amgr, BTOR_INVERT_AIG (term0), res);
    btor_release_aig (amgr, term0);
    btor_release_aig (amgr, res);
    res = tmp;

    term1 = btor_and_aig (amgr, BTOR_INVERT_AIG (av1->aigs[i]), av2->aigs[i]);

    tmp = btor_or_aig (amgr, term1, res);
    btor_release_aig (amgr, term1);
    btor_release_aig (amgr, res);
    res = tmp;
  }

  return res;
}

BtorAIGVec *
btor_ult_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  result          = new_aigvec (avmgr, 1);
  result->aigs[0] = lt_aigvec (avmgr, av1, av2);
  return result;
}

BtorAIGVec *
btor_eq_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *result_aig, *temp1, *temp2;
  int i, len;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  amgr       = avmgr->amgr;
  len        = av1->len;
  result     = new_aigvec (avmgr, 1);
  result_aig = btor_eq_aig (amgr, av1->aigs[0], av2->aigs[0]);
  for (i = 1; i < len; i++)
  {
    temp1 = btor_eq_aig (amgr, av1->aigs[i], av2->aigs[i]);
    temp2 = btor_and_aig (amgr, result_aig, temp1);
    btor_release_aig (amgr, temp1);
    btor_release_aig (amgr, result_aig);
    result_aig = temp2;
  }
  result->aigs[0] = result_aig;
  return result;
}

static BtorAIG *
half_adder (BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG **cout)
{
  BtorAIG *res, *x_and_y, *not_x, *not_y, *not_x_and_not_y, *x_xnor_y;
  x_and_y         = btor_and_aig (amgr, x, y);
  not_x           = BTOR_INVERT_AIG (x);
  not_y           = BTOR_INVERT_AIG (y);
  not_x_and_not_y = btor_and_aig (amgr, not_x, not_y);
  x_xnor_y        = btor_or_aig (amgr, x_and_y, not_x_and_not_y);
  res             = BTOR_INVERT_AIG (x_xnor_y);
  *cout           = x_and_y;
  btor_release_aig (amgr, not_x_and_not_y);
  return res;
}

static BtorAIG *
full_adder (
    BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG *cin, BtorAIG **cout)
{
  BtorAIG *sum, *c1, *c2, *res;
  sum   = half_adder (amgr, x, y, &c1);
  res   = half_adder (amgr, sum, cin, &c2);
  *cout = btor_or_aig (amgr, c1, c2);
  btor_release_aig (amgr, sum);
  btor_release_aig (amgr, c1);
  btor_release_aig (amgr, c2);
  return res;
}

static int
btor_compare_aigvec_lsb_first (BtorAIGVec *a, BtorAIGVec *b)
{
  uint32_t len, i;
  int res;
  assert (a);
  assert (b);
  len = a->len;
  assert (len == b->len);
  res = 0;
  for (i = 0; !res && i < len; i++)
    res = btor_compare_aig (a->aigs[i], b->aigs[i]);
  return res;
}

BtorAIGVec *
btor_add_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len == av2->len);
  assert (av1->len > 0);

  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *cout, *cin;
  int i;

  if (btor_get_opt (avmgr->btor, BTOR_OPT_SORT_AIGVEC) > 0
      && btor_compare_aigvec_lsb_first (av1, av2) > 0)
  {
    BTOR_SWAP (BtorAIGVec *, av1, av2);
  }

  amgr   = avmgr->amgr;
  result = new_aigvec (avmgr, av1->len);
  cout = cin = BTOR_AIG_FALSE; /* for 'cout' to avoid warning */
  for (i = av1->len - 1; i >= 0; i--)
  {
    result->aigs[i] = full_adder (amgr, av1->aigs[i], av2->aigs[i], cin, &cout);
    btor_release_aig (amgr, cin);
    cin = cout;
  }
  btor_release_aig (amgr, cout);
  return result;
}

static BtorAIGVec *
btor_sll_n_bits_aigvec (BtorAIGVecMgr *avmgr,
                        BtorAIGVec *av,
                        uint32_t n,
                        BtorAIG *shift)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *and1, *and2, *not_shift;
  unsigned i, j, len;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  assert (n < av->len);
  if (n == 0) return btor_copy_aigvec (avmgr, av);
  amgr      = avmgr->amgr;
  len       = av->len;
  not_shift = btor_not_aig (amgr, shift);
  result    = new_aigvec (avmgr, len);
  for (i = 0; i < len - n; i++)
  {
    and1            = btor_and_aig (amgr, av->aigs[i], not_shift);
    and2            = btor_and_aig (amgr, av->aigs[i + n], shift);
    result->aigs[i] = btor_or_aig (amgr, and1, and2);
    btor_release_aig (amgr, and1);
    btor_release_aig (amgr, and2);
  }
  for (j = len - n; j < len; j++)
    result->aigs[j] = btor_and_aig (amgr, av->aigs[j], not_shift);
  btor_release_aig (amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_sll_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result, *temp;
  int i, len;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len > 1);
  assert (btor_is_power_of_2_util (av1->len));
  assert (btor_log_2_util (av1->len) == av2->len);
  len    = av2->len;
  result = btor_sll_n_bits_aigvec (avmgr, av1, 1, av2->aigs[av2->len - 1]);
  for (i = len - 2; i >= 0; i--)
  {
    temp   = result;
    result = btor_sll_n_bits_aigvec (
        avmgr, temp, btor_pow_2_util (len - i - 1), av2->aigs[i]);
    btor_release_delete_aigvec (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
btor_srl_n_bits_aigvec (BtorAIGVecMgr *avmgr,
                        BtorAIGVec *av,
                        uint32_t n,
                        BtorAIG *shift)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *and1, *and2, *not_shift;
  unsigned i, len;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  assert (n < av->len);
  if (n == 0) return btor_copy_aigvec (avmgr, av);
  amgr      = avmgr->amgr;
  len       = av->len;
  not_shift = btor_not_aig (amgr, shift);
  result    = new_aigvec (avmgr, len);
  for (i = 0; i < n; i++)
    result->aigs[i] = btor_and_aig (amgr, av->aigs[i], not_shift);
  for (i = n; i < len; i++)
  {
    and1            = btor_and_aig (amgr, av->aigs[i], not_shift);
    and2            = btor_and_aig (amgr, av->aigs[i - n], shift);
    result->aigs[i] = btor_or_aig (amgr, and1, and2);
    btor_release_aig (amgr, and1);
    btor_release_aig (amgr, and2);
  }
  btor_release_aig (amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_srl_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result, *temp;
  int i, len;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len > 1);
  assert (btor_is_power_of_2_util (av1->len));
  assert (btor_log_2_util (av1->len) == av2->len);
  len    = av2->len;
  result = btor_srl_n_bits_aigvec (avmgr, av1, 1, av2->aigs[av2->len - 1]);
  for (i = len - 2; i >= 0; i--)
  {
    temp   = result;
    result = btor_srl_n_bits_aigvec (
        avmgr, temp, btor_pow_2_util (len - i - 1), av2->aigs[i]);
    btor_release_delete_aigvec (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
mul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  BtorAIG *cin, *cout, *and, *tmp;
  BtorAIGMgr *amgr;
  BtorAIGVec *res;
  uint32_t k, len;
  int i, j;

  len  = a->len;
  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);

  assert (len > 0);
  assert (len == b->len);

  if (btor_get_opt (avmgr->btor, BTOR_OPT_SORT_AIGVEC) > 0
      && btor_compare_aigvec_lsb_first (a, b) > 0)
  {
    BTOR_SWAP (BtorAIGVec *, a, b);
  }

  res = new_aigvec (avmgr, len);

  for (k = 0; k < len; k++)
    res->aigs[k] = btor_and_aig (amgr, a->aigs[k], b->aigs[len - 1]);

  for (i = len - 2; i >= 0; i--)
  {
    cout = BTOR_AIG_FALSE;
    for (j = i; j >= 0; j--)
    {
      and          = btor_and_aig (amgr, a->aigs[len - 1 - i + j], b->aigs[i]);
      tmp          = res->aigs[j];
      cin          = cout;
      res->aigs[j] = full_adder (amgr, tmp, and, cin, &cout);
      btor_release_aig (amgr, and);
      btor_release_aig (amgr, tmp);
      btor_release_aig (amgr, cin);
    }
    btor_release_aig (amgr, cout);
  }

  return res;
}

BtorAIGVec *
btor_mul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  return mul_aigvec (avmgr, a, b);
}

static void
btor_SC_GATE_CO_aigvec (
    BtorAIGMgr *amgr, BtorAIG **CO, BtorAIG *R, BtorAIG *D, BtorAIG *CI)
{
  BtorAIG *D_or_CI, *D_and_CI, *M;
  D_or_CI  = btor_or_aig (amgr, D, CI);
  D_and_CI = btor_and_aig (amgr, D, CI);
  M        = btor_and_aig (amgr, D_or_CI, R);
  *CO      = btor_or_aig (amgr, M, D_and_CI);
  btor_release_aig (amgr, D_or_CI);
  btor_release_aig (amgr, D_and_CI);
  btor_release_aig (amgr, M);
}

static void
btor_SC_GATE_S_aigvec (BtorAIGMgr *amgr,
                       BtorAIG **S,
                       BtorAIG *R,
                       BtorAIG *D,
                       BtorAIG *CI,
                       BtorAIG *Q)
{
  BtorAIG *D_and_CI, *D_or_CI;
  BtorAIG *T2_or_R, *T2_and_R;
  BtorAIG *T1, *T2;
  D_or_CI  = btor_or_aig (amgr, D, CI);
  D_and_CI = btor_and_aig (amgr, D, CI);
  T1       = btor_and_aig (amgr, D_or_CI, BTOR_INVERT_AIG (D_and_CI));
  T2       = btor_and_aig (amgr, T1, Q);
  T2_or_R  = btor_or_aig (amgr, T2, R);
  T2_and_R = btor_and_aig (amgr, T2, R);
  *S       = btor_and_aig (amgr, T2_or_R, BTOR_INVERT_AIG (T2_and_R));
  btor_release_aig (amgr, T1);
  btor_release_aig (amgr, T2);
  btor_release_aig (amgr, D_and_CI);
  btor_release_aig (amgr, D_or_CI);
  btor_release_aig (amgr, T2_and_R);
  btor_release_aig (amgr, T2_or_R);
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
  int size, i, j;

  size = Ain->len;
  assert (size > 0);

  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);
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
    S[j][0] = btor_copy_aig (amgr, A[size - j - 1]);
    C[j][0] = BTOR_AIG_TRUE;

    for (i = 0; i <= size - 1; i++)
      btor_SC_GATE_CO_aigvec (amgr, &C[j][i + 1], S[j][i], nD[i], C[j][i]);

    Q->aigs[j] = btor_or_aig (amgr, C[j][size], S[j][size]);

    for (i = 0; i <= size - 1; i++)
      btor_SC_GATE_S_aigvec (
          amgr, &S[j + 1][i + 1], S[j][i], nD[i], C[j][i], Q->aigs[j]);
  }

  for (i = size; i >= 1; i--)
    R->aigs[size - i] = btor_copy_aig (amgr, S[size][i]);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_release_aig (amgr, C[j][i]);
    BTOR_DELETEN (mem, C[j], size + 1);
  }
  BTOR_DELETEN (mem, C, size + 1);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_release_aig (amgr, S[j][i]);
    BTOR_DELETEN (mem, S[j], size + 1);
  }
  BTOR_DELETEN (mem, S, size + 1);

  BTOR_DELETEN (mem, nD, size);
  BTOR_DELETEN (mem, A, size);

  *Qptr = Q;
  *Rptr = R;
}

BtorAIGVec *
btor_udiv_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient  = 0;
  BtorAIGVec *remainder = 0;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_release_delete_aigvec (avmgr, remainder);
  return quotient;
}

BtorAIGVec *
btor_urem_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient, *remainder;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_release_delete_aigvec (avmgr, quotient);
  return remainder;
}

BtorAIGVec *
btor_concat_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  int i, pos, len_av1, len_av2;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->len > 0);
  assert (av2->len > 0);
  assert (INT_MAX - av1->len >= av2->len);
  pos     = 0;
  amgr    = avmgr->amgr;
  len_av1 = av1->len;
  len_av2 = av2->len;
  result  = new_aigvec (avmgr, len_av1 + len_av2);
  for (i = 0; i < len_av1; i++)
    result->aigs[pos++] = btor_copy_aig (amgr, av1->aigs[i]);
  for (i = 0; i < len_av2; i++)
    result->aigs[pos++] = btor_copy_aig (amgr, av2->aigs[i]);
  return result;
}

BtorAIGVec *
btor_cond_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *av_cond,
                  BtorAIGVec *av_if,
                  BtorAIGVec *av_else)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  int i, len;
  assert (avmgr);
  assert (av_cond);
  assert (av_if);
  assert (av_else);
  assert (av_cond->len == 1);
  assert (av_if->len == av_else->len);
  assert (av_if->len > 0);
  amgr   = avmgr->amgr;
  len    = av_if->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_cond_aig (
        amgr, av_cond->aigs[0], av_if->aigs[i], av_else->aigs[i]);
  return result;
}

BtorAIGVec *
btor_copy_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  int i, len;
  assert (avmgr);
  assert (av);
  amgr   = avmgr->amgr;
  len    = av->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++) result->aigs[i] = btor_copy_aig (amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_clone_aigvec (BtorAIGVec *av, BtorAIGVecMgr *avmgr)
{
  assert (av);
  assert (avmgr);

  unsigned i;
  BtorAIGVec *res;
  BtorAIGMgr *amgr;
  BtorAIG *aig, *caig;

  amgr = avmgr->amgr;
  res  = new_aigvec (avmgr, av->len);
  for (i = 0; i < av->len; i++)
  {
    if (BTOR_IS_CONST_AIG (av->aigs[i]))
      res->aigs[i] = av->aigs[i];
    else
    {
      aig = av->aigs[i];
      assert (BTOR_REAL_ADDR_AIG (aig)->id < BTOR_COUNT_STACK (amgr->id2aig));
      caig = BTOR_PEEK_STACK (amgr->id2aig, BTOR_REAL_ADDR_AIG (aig)->id);
      assert (caig);
      assert (!BTOR_IS_CONST_AIG (caig));
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
  int i, len;
  assert (avmgr);
  assert (av);
  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);
  if (!btor_is_initialized_sat (amgr->smgr)) return;
  len = av->len;
  for (i = 0; i < len; i++) btor_aig_to_sat_tseitin (amgr, av->aigs[i]);
}

void
btor_release_delete_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  int i, len;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  mm   = avmgr->btor->mm;
  amgr = avmgr->amgr;
  len  = av->len;
  for (i = 0; i < len; i++) btor_release_aig (amgr, av->aigs[i]);
  btor_free (mm, av, sizeof (BtorAIGVec) + sizeof (BtorAIG *) * av->len);
  avmgr->cur_num_aigvecs--;
}

BtorAIGVecMgr *
btor_new_aigvec_mgr (Btor *btor)
{
  assert (btor);

  BtorAIGVecMgr *avmgr;
  BTOR_CNEW (btor->mm, avmgr);
  avmgr->btor = btor;
  avmgr->amgr = btor_new_aig_mgr (btor);
  return avmgr;
}

BtorAIGVecMgr *
btor_clone_aigvec_mgr (Btor *btor, BtorAIGVecMgr *avmgr)
{
  assert (btor);
  assert (avmgr);

  BtorAIGVecMgr *res;
  BTOR_NEW (btor->mm, res);

  res->btor            = btor;
  res->amgr            = btor_clone_aig_mgr (btor, avmgr->amgr);
  res->max_num_aigvecs = avmgr->max_num_aigvecs;
  res->cur_num_aigvecs = avmgr->cur_num_aigvecs;
  return res;
}

void
btor_delete_aigvec_mgr (BtorAIGVecMgr *avmgr)
{
  assert (avmgr);
  btor_delete_aig_mgr (avmgr->amgr);
  BTOR_DELETE (avmgr->btor->mm, avmgr);
}

BtorAIGMgr *
btor_get_aig_mgr_aigvec_mgr (const BtorAIGVecMgr *avmgr)
{
  return avmgr ? avmgr->amgr : 0;
}

char *
btor_assignment_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr;
  int i, len, cur;
  char *result;
  assert (avmgr);
  assert (av);
  assert (av->len > 0);
  amgr = avmgr->amgr;
  len  = av->len;
  BTOR_NEWN (avmgr->btor->mm, result, len + 1);
  for (i = 0; i < len; i++)
  {
    cur = btor_get_assignment_aig (amgr, av->aigs[i]);
    assert (cur >= -1);
    assert (cur <= 1);
    if (cur == 1)
      result[i] = '1';
    else if (cur == -1)
      result[i] = '0';
    else
      result[i] = 'x';
  }
  result[i] = '\0';
  return result;
}

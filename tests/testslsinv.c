/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbitvec.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btorsls.h"
#include "testrunner.h"
#include "utils/btorutil.h"

static Btor *g_btor;
static BtorMemMgr *g_mm;
static BtorRNG *g_rng;

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#define TEST_SLS_INV_BV(fun, iscon, bw, bve, bvn, eidx) \
  do                                                    \
  {                                                     \
    res = inv_##fun##_bv (g_btor, fun, bvn, bve, eidx); \
    if (iscon)                                          \
      assert (!res);                                    \
    else                                                \
    {                                                   \
      if (eidx)                                         \
        tmp = btor_##fun##_bv (g_mm, bve, res);         \
      else                                              \
        tmp = btor_##fun##_bv (g_mm, res, bve);         \
      assert (!btor_compare_bv (tmp, bvn));             \
      btor_free_bv (g_mm, tmp);                         \
      btor_free_bv (g_mm, res);                         \
    }                                                   \
  } while (0)

#define TEST_SLS_INV_VAL(fun, iscon, bw, ve, vn, eidx)                \
  do                                                                  \
  {                                                                   \
    idx      = eidx ? 0 : 1;                                          \
    bve[idx] = btor_uint64_to_bv (g_mm, ve, bw);                      \
    bv##fun  = btor_uint64_to_bv (g_mm, vn, bw);                      \
    res      = inv_##fun##_bv (g_btor, fun, bv##fun, bve[idx], eidx); \
    if (iscon)                                                        \
      assert (!res);                                                  \
    else                                                              \
    {                                                                 \
      if (eidx)                                                       \
        tmp = btor_##fun##_bv (g_mm, bve[idx], res);                  \
      else                                                            \
        tmp = btor_##fun##_bv (g_mm, res, bve[idx]);                  \
      assert (!btor_compare_bv (tmp, bv##fun));                       \
      btor_free_bv (g_mm, tmp);                                       \
      btor_free_bv (g_mm, res);                                       \
    }                                                                 \
    btor_free_bv (g_btor->mm, bve[idx]);                              \
    btor_free_bv (g_btor->mm, bv##fun);                               \
  } while (0)

#define TEST_SLS_INIT_INV_VAL_CON(fun, bw, ve, eidx)                 \
  do                                                                 \
  {                                                                  \
    idx = eidx ? 0 : 1;                                              \
    BTOR_CNEWN (g_mm, bits, bw + 1);                                 \
    if (!ve)                                                         \
      memset (bits, '0', bw);                                        \
    else                                                             \
    {                                                                \
      tmpbits = btor_decimal_to_const (g_mm, #ve);                   \
      len     = strlen (#ve);                                        \
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0'; \
      btor_freestr (g_mm, tmpbits);                                  \
    }                                                                \
    e[idx] = btor_const_exp (g_btor, bits);                          \
    BTOR_DELETEN (g_mm, bits, bw + 1);                               \
    fun = btor_##fun##_exp (g_btor, e[0], e[1]);                     \
  } while (0)

#define TEST_SLS_FINISH_INV_VAL_CON(fun, eidx) \
  do                                           \
  {                                            \
    idx = eidx ? 0 : 1;                        \
    btor_release_exp (g_btor, fun);            \
    btor_release_exp (g_btor, e[idx]);         \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

void
init_slsinv_tests (void)
{
  g_btor                            = btor_new_btor ();
  g_btor->slv                       = btor_new_sls_solver (g_btor);
  g_btor->options.sls.val           = 1;
  g_btor->options.rewrite_level.val = 0;
  g_mm                              = g_btor->mm;
  g_rng                             = &g_btor->rng;
}

static void
sls_inv_add_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int j;
  BtorNode *add, *e[3];
  BtorBitVector *bvadd, *bve[3], *res, *tmp;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  add  = btor_add_exp (g_btor, e[0], e[1]);

  for (j = 0; j < 5; j++)
  {
    bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
    bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
    bvadd  = btor_new_random_bv (g_mm, g_rng, bw);

    /* find assignment for e[0] */
    TEST_SLS_INV_BV (add, 0, bw, bve[1], bvadd, 0);

    /* find assignment for e[1] */
    TEST_SLS_INV_BV (add, 0, bw, bve[1], bvadd, 1);

    btor_free_bv (g_mm, bvadd);
    btor_free_bv (g_mm, bve[0]);
    btor_free_bv (g_mm, bve[1]);
  }

  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
#endif
}

static void
sls_inv_and_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int i, j;
  BtorNode *and, *e[3], *tmpe[3], *tmpand;
  BtorBitVector *bvand, *bve[3], *res, *one, *bvmax, *tmp;
  char *bits;

  one   = btor_one_bv (g_mm, bw);
  tmp   = btor_new_bv (g_mm, bw);
  bvmax = btor_not_bv (g_mm, tmp);
  btor_free_bv (g_mm, tmp);

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  and  = btor_and_exp (g_btor, e[0], e[1]);

  for (j = 0; j < 5; j++)
  {
    bvand = btor_new_random_bv (g_mm, g_rng, bw);

    bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
    for (i = 0; i < bvand->width; i++)
      if (btor_get_bit_bv (bvand, i)) btor_set_bit_bv (bve[0], i, 1);

    bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
    for (i = 0; i < bvand->width; i++)
      if (btor_get_bit_bv (bvand, i)) btor_set_bit_bv (bve[1], i, 1);

    /* find assignment for e[0] */
    TEST_SLS_INV_BV (and, 0, bw, bve[1], bvand, 0);

    /* find assignment for e[1] */
    TEST_SLS_INV_BV (and, 0, bw, bve[0], bvand, 1);

    btor_free_bv (g_mm, bve[0]);
    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvand);

    /* fixable conflicts */
    bvand  = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmax);
    bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
    bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
    for (i = 0; i < bve[0]->width; i++)
      if (btor_get_bit_bv (bvand, i) && btor_get_bit_bv (bve[0], i))
      {
        btor_set_bit_bv (bve[0], i, 0);
        break;
      }
    for (i = 0; i < bve[1]->width; i++)
      if (btor_get_bit_bv (bvand, i) && btor_get_bit_bv (bve[1], i))
      {
        btor_set_bit_bv (bve[1], i, 0);
        break;
      }
    /* fixable conflict, assignment for e[0] */
    res = inv_and_bv (g_btor, and, bvand, bve[1], 0);
    assert (res);
    for (i = 0; i < bvand->width; i++)
      if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
    btor_free_bv (g_mm, res);
    /* fixable conflict, assignment for e[1] */
    res = inv_and_bv (g_btor, and, bvand, bve[0], 1);
    assert (res);
    for (i = 0; i < bvand->width; i++)
      if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
    btor_free_bv (g_mm, res);

    /* non-fixable conflicts */
    tmpe[0] = e[0];
    tmpe[1] = e[1];
    tmpand  = and;
    /* non-fixable, assignment for e[0] */
    bits = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    and = btor_and_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (and, 1, bw, bve[1], bvand, 0);
    btor_release_exp (g_btor, and);
    btor_release_exp (g_btor, e[1]);
    e[1] = tmpe[1];
    /* non-fixable, assignment for e[1] */
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    and = btor_and_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (and, 1, bw, bve[0], bvand, 1);
    btor_release_exp (g_btor, and);
    btor_release_exp (g_btor, e[0]);
    e[0] = tmpe[0];
    and  = tmpand;

    btor_free_bv (g_mm, bvand);
    btor_free_bv (g_mm, bve[0]);
    btor_free_bv (g_mm, bve[1]);
  }
  btor_release_exp (g_btor, tmpe[0]);
  btor_release_exp (g_btor, tmpe[1]);
  btor_release_exp (g_btor, tmpand);
  btor_free_bv (g_mm, one);
  btor_free_bv (g_mm, bvmax);
#endif
}

static void
sls_inv_eq_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  BtorNode *eq, *e[3];
  BtorBitVector *bveq, *bve[3], *res;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  eq   = btor_eq_exp (g_btor, e[0], e[1]);

  bveq   = btor_new_random_bv (g_mm, g_rng, 1);
  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
  bve[1] = btor_new_random_bv (g_mm, g_rng, bw);

  /* find assignment for e[0],  */
  res = inv_eq_bv (g_btor, eq, bveq, bve[1], 0);
  assert (res);
  assert ((btor_is_zero_bv (bveq) && btor_compare_bv (res, bve[1]))
          || (!btor_is_zero_bv (bveq) && !btor_compare_bv (res, bve[1])));
  btor_free_bv (g_mm, res);

  /* find assignment for e[1] */
  res = inv_eq_bv (g_btor, eq, bveq, bve[0], 1);
  assert (res);
  assert ((btor_is_zero_bv (bveq) && btor_compare_bv (res, bve[0]))
          || (!btor_is_zero_bv (bveq) && !btor_compare_bv (res, bve[0])));
  btor_free_bv (g_mm, res);

  btor_free_bv (g_mm, bveq);
  btor_free_bv (g_mm, bve[0]);
  btor_free_bv (g_mm, bve[1]);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
#endif
}

static void
sls_inv_ult_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int j;
  BtorNode *ult, *e[3], *tmpe[3];
  BtorBitVector *bve[3], *res, *tmp;
  BtorBitVector *tr, *fa, *zero, *bvmax, *one, *neg;
  char *bits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  ult  = btor_ult_exp (g_btor, e[0], e[1]);

  fa    = btor_new_bv (g_mm, 1);
  tr    = btor_not_bv (g_mm, fa);
  zero  = btor_new_bv (g_mm, bw);
  bvmax = btor_not_bv (g_mm, zero);
  one   = btor_one_bv (g_mm, bw);
  neg   = btor_neg_bv (g_mm, one);

  for (j = 0; j < 5; j++)
  {
    /* search assignment for e[0] */
    bve[1] = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmax);
    TEST_SLS_INV_BV (ult, 0, bw, bve[1], tr, 0);
    btor_free_bv (g_mm, bve[1]);
    bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
    TEST_SLS_INV_BV (ult, 0, bw, bve[1], fa, 0);
    btor_free_bv (g_mm, bve[1]);

    /* search assignment for e[1] */
    tmp    = btor_add_bv (g_mm, bvmax, neg);
    bve[0] = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    TEST_SLS_INV_BV (ult, 0, bw, bve[0], tr, 1);
    btor_free_bv (g_mm, bve[0]);
    bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
    TEST_SLS_INV_BV (ult, 0, bw, bve[0], fa, 1);
    btor_free_bv (g_mm, bve[0]);
  }

  /* corner case: e[0] >= 0 */
  TEST_SLS_INV_BV (ult, 0, bw, zero, fa, 0);
  /* corner case: e[0] < 1...1 */
  TEST_SLS_INV_BV (ult, 0, bw, bvmax, tr, 0);
  /* corner case: 0 < e[1] */
  TEST_SLS_INV_BV (ult, 0, bw, zero, tr, 1);
  /* corner case: 1...1 >= e[1] */
  TEST_SLS_INV_BV (ult, 0, bw, bvmax, fa, 1);

  tmpe[0] = e[0];
  tmpe[1] = e[1];
  btor_release_exp (g_btor, ult);

  /* conflict: e[0] < 0 */
  bits = btor_bv_to_char_bv (g_mm, zero);
  e[1] = btor_const_exp (g_btor, bits);
  ult  = btor_ult_exp (g_btor, e[0], e[1]);
  TEST_SLS_INV_BV (ult, 1, bw, zero, tr, 0);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, e[1]);
  e[1] = tmpe[1];
  /* conflict: 0 >= e[1] */
  e[0] = btor_const_exp (g_btor, bits);
  ult  = btor_ult_exp (g_btor, e[0], e[1]);
  TEST_SLS_INV_BV (ult, 1, bw, zero, fa, 1);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, e[0]);
  btor_freestr (g_mm, bits);
  e[0] = tmpe[0];
  /* conflict: e[0] >= 1...1 */
  bits = btor_bv_to_char_bv (g_mm, bvmax);
  e[1] = btor_const_exp (g_btor, bits);
  ult  = btor_ult_exp (g_btor, e[0], e[1]);
  TEST_SLS_INV_BV (ult, 1, bw, bvmax, fa, 0);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, e[1]);
  e[1] = tmpe[1];
  /* conflict: 1...1 < e[1] */
  e[0] = btor_const_exp (g_btor, bits);
  ult  = btor_ult_exp (g_btor, e[0], e[1]);
  TEST_SLS_INV_BV (ult, 1, bw, bvmax, tr, 1);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, e[0]);
  btor_freestr (g_mm, bits);
#if 0
  for (j = 0; j < 5; j++)
    {
      bvult = btor_new_random_bv (g_mm, g_rng, 1);  

      bve[0] = 0;
      do
	{
	  tmp = bve[0];
	  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
	  if (tmp) btor_free_bv (g_mm, tmp);
	}
      while (bw > 1
	     && !btor_compare_bv (ones, bve[0])
	     && btor_is_one_bv (bvult));

      bve[1] = 0;
      do
	{
	  tmp = bve[1];
	  bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
	  if (tmp) btor_free_bv (g_mm, tmp);
	}
      while (bw > 1
	     && btor_is_zero_bv (bve[1]) &&
	     btor_is_one_bv (bvult));

      /* find assignment for e[0] */
      if (bw > 1 || btor_is_zero_bv (bvult) || !btor_is_zero_bv (bve[1]))
	TEST_SLS_INV_BV (ult, 0, bw, bve[1], bvult, 0);

      /* find assignment for e[1] */
      if (bw > 1 || btor_is_zero_bv (bvult) || btor_compare_bv (ones, bve[0]))
	TEST_SLS_INV_BV (ult, 0, bw, bve[0], bvult, 1);

      /* find assignment for 0 < e[1] */
      TEST_SLS_INV_BV (ult, 0, bw, zero, tr, 1);

      /* find assignment for 0 >= e[1] */
      TEST_SLS_INV_BV (ult, 0, bw, zero, fa, 1);

      /* find assignment for e[0] >= 0 */
      TEST_SLS_INV_BV (ult, 0, bw, zero, fa, 0);

      /* find assignment for e[0] < 1..1 */
      TEST_SLS_INV_BV (ult, 0, bw, ones, tr, 0);

      /* find assignment for e[0] >= 1..1 */
      TEST_SLS_INV_BV (ult, 0, bw, ones, fa, 0);

      /* find assignment for 1..1 >= e[1] */
      TEST_SLS_INV_BV (ult, 0, bw, ones, fa, 1);

      tmpe[0] = e[0];
      tmpe[1] = e[1];
      tmpult = ult;

      /* find assignment for e[0] < 0, non-fixable conflict */
      bits = btor_bv_to_char_bv (g_mm, zero);
      e[1] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, bits);
      ult = btor_ult_exp (g_btor, e[0], e[1]);
      TEST_SLS_INV_BV (ult, 1, bw, zero, tr, 0);
      btor_release_exp (g_btor, ult);
      btor_release_exp (g_btor, e[1]);
      e[1] = tmpe[1];

      /* find assignment for 1..1 < e[1], non-fixable conflict */
      bits = btor_bv_to_char_bv (g_mm, ones);
      e[0] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, bits);
      ult = btor_ult_exp (g_btor, e[0], e[1]);
      TEST_SLS_INV_BV (ult, 1, bw, ones, tr, 1);
      btor_release_exp (g_btor, ult);
      btor_release_exp (g_btor, e[0]);
      e[0] = tmpe[0];
      ult = tmpult;

      btor_free_bv (g_mm, bvult);
      btor_free_bv (g_mm, bve[0]);
      btor_free_bv (g_mm, bve[1]);
    }
#endif
  btor_free_bv (g_mm, tr);
  btor_free_bv (g_mm, fa);
  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, bvmax);
  btor_free_bv (g_mm, one);
  btor_free_bv (g_mm, neg);
  btor_release_exp (g_btor, tmpe[0]);
  btor_release_exp (g_btor, tmpe[1]);
#endif
}

static void
sls_inv_sll_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int i, j, r, sbw;
  BtorNode *sll, *e[3], *tmpe[3];
  BtorBitVector *bvsll, *bve[3], *res, *zero, *one, *bvmaxshift, *tmp;
  char *bits;

  sbw  = btor_log_2_util (bw);
  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, sbw, 0);
  sll  = btor_sll_exp (g_btor, e[0], e[1]);

  zero = btor_new_bv (g_mm, bw);
  one  = btor_new_bv (g_mm, bw);
  btor_set_bit_bv (one, 0, 1);

  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
  for (j = 0; j < 10; j++)
  {
    r          = btor_pick_rand_rng (g_rng, 0, bw - 1);
    bvmaxshift = btor_uint64_to_bv (g_mm, r, bw);
    tmp        = btor_new_random_range_bv (g_mm, g_rng, bw, zero, bvmaxshift);
    btor_free_bv (g_mm, bvmaxshift);
    bve[1] = btor_slice_bv (g_mm, tmp, sbw - 1, 0);
    assert (bve[1]->width == sbw);
    btor_free_bv (g_mm, tmp);

    bvsll = btor_sll_bv (g_mm, bve[0], bve[1]);
#ifndef NDEBUG
    r = btor_bv_to_uint64_bv (bve[1]);
    for (i = 0; i < r && i < bvsll->width; i++)
      assert (btor_get_bit_bv (bvsll, i) == 0);
#endif
    /* find assignment for e[0] (value to be shifted) */
    TEST_SLS_INV_BV (sll, 0, bw, bve[1], bvsll, 0);

    /* find assignment for e[1] (shift value) */
    TEST_SLS_INV_BV (sll, 0, bw, bve[0], bvsll, 1);

    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvsll);
  }
  btor_free_bv (g_mm, bve[0]);

  tmpe[0] = e[0];
  tmpe[1] = e[1];
  btor_release_exp (g_btor, sll);

  /* conflict */
  for (j = 0; j < 3; j++)
  {
    bvsll = btor_new_random_bv (g_mm, g_rng, bw);
    r     = btor_pick_rand_rng (g_rng, 1, bw / 4 ? bw / 4 : 1);
    for (i = 0; i < r; i++) btor_set_bit_bv (bvsll, i, 0);
    btor_set_bit_bv (bvsll, r, 1);
    tmp    = btor_uint64_to_bv (g_mm, 1, sbw);
    bve[0] = btor_sll_bv (g_mm, bvsll, tmp);
    btor_free_bv (g_mm, tmp);
    r          = btor_pick_rand_rng (g_rng, 1, bw - 1);
    bvmaxshift = btor_uint64_to_bv (g_mm, r, bw);
    tmp        = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmaxshift);
    btor_free_bv (g_mm, bvmaxshift);
    bve[1] = btor_slice_bv (g_mm, tmp, sbw - 1, 0);
    assert (bve[1]->width == sbw);
    btor_free_bv (g_mm, tmp);

    /* find assignment for e[0] (non-fixable conflict) */
    tmp = btor_copy_bv (g_mm, bvsll);
    r   = btor_bv_to_uint64_bv (bve[1]);
    r   = btor_pick_rand_rng (g_rng, 0, r - 1);
    btor_set_bit_bv (bvsll, r, 1);
    bits = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    sll = btor_sll_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (sll, 1, bw, bve[1], bvsll, 0);
    btor_release_exp (g_btor, e[1]);
    btor_release_exp (g_btor, sll);
    btor_free_bv (g_mm, bvsll);
    bvsll = tmp;
    e[1]  = tmpe[1];

    /* find assignment for e[1] (non-fixable conflict) */
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    sll = btor_sll_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (sll, 1, bw, bve[0], bvsll, 1);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, sll);
    btor_free_bv (g_mm, bvsll);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bve[1]);
    e[0] = tmpe[0];
  }

  /* find assignment for e[1] (non-fixable conflict) */
  if (bw > 2)
  {
    switch (bw)
    {
      case 4:
        bve[0] = btor_char_to_bv (g_mm, "1101");
        bvsll  = btor_char_to_bv (g_mm, "0010");
        e[0]   = btor_const_exp (g_btor, "1101");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 8:
        bve[0] = btor_char_to_bv (g_mm, "11010011");
        bvsll  = btor_char_to_bv (g_mm, "01011100");
        e[0]   = btor_const_exp (g_btor, "11010011");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 16:
        bve[0] = btor_char_to_bv (g_mm, "1011110100110100");
        bvsll  = btor_char_to_bv (g_mm, "1111101001101000");
        e[0]   = btor_const_exp (g_btor, "1011110100110100");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 32:
        bve[0] = btor_char_to_bv (g_mm, "10100101001101011011110100110111");
        bvsll  = btor_char_to_bv (g_mm, "01101001101111011110100110111000");
        e[0]   = btor_const_exp (g_btor, "10100101001101011011110100110111");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 64:
        bve[0] = btor_char_to_bv (
            g_mm,
            "1010010101110101101111010101011010010101111100101111010111011011");
        bvsll = btor_char_to_bv (
            g_mm,
            "1010111010110111101000101100001010111110010111101011101101100000");
        e[0] = btor_const_exp (
            g_btor,
            "1010010101110101101111010101011010010101111100101111010111011011");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      default: break;
    }
    sll = btor_sll_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (sll, 1, bw, bve[0], bvsll, 1);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, sll);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bvsll);
    e[0] = tmpe[0];
  }

  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, one);
  btor_release_exp (g_btor, tmpe[0]);
  btor_release_exp (g_btor, tmpe[1]);
#endif
}

static void
sls_inv_srl_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int i, j, r, sbw;
  BtorNode *srl, *e[3], *tmpe[3];
  BtorBitVector *bvsrl, *bve[3], *res, *zero, *one, *bvmaxshift, *tmp;
  char *bits;

  sbw  = btor_log_2_util (bw);
  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, sbw, 0);
  srl  = btor_srl_exp (g_btor, e[0], e[1]);

  zero = btor_new_bv (g_mm, bw);
  one  = btor_new_bv (g_mm, bw);
  btor_set_bit_bv (one, 0, 1);

  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
  for (j = 0; j < 10; j++)
  {
    r          = btor_pick_rand_rng (g_rng, 0, bw - 1);
    bvmaxshift = btor_uint64_to_bv (g_mm, r, bw);
    tmp        = btor_new_random_range_bv (g_mm, g_rng, bw, zero, bvmaxshift);
    btor_free_bv (g_mm, bvmaxshift);
    bve[1] = btor_slice_bv (g_mm, tmp, sbw - 1, 0);
    assert (bve[1]->width == sbw);
    btor_free_bv (g_mm, tmp);

    bvsrl = btor_srl_bv (g_mm, bve[0], bve[1]);
#ifndef NDEBUG
    r = btor_bv_to_uint64_bv (bve[1]);
    for (i = 0; i < r && i < bvsrl->width; i++)
      assert (btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i) == 0);
#endif
    /* find assignment for e[0] (value to be shifted) */
    TEST_SLS_INV_BV (srl, 0, bw, bve[1], bvsrl, 0);

    /* find assignment for e[1] (shift value) */
    TEST_SLS_INV_BV (srl, 0, bw, bve[0], bvsrl, 1);

    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvsrl);
  }
  btor_free_bv (g_mm, bve[0]);

  tmpe[0] = e[0];
  tmpe[1] = e[1];
  btor_release_exp (g_btor, srl);

  /* conflict */
  for (j = 0; j < 3; j++)
  {
    bvsrl = btor_new_random_bv (g_mm, g_rng, bw);
    r     = btor_pick_rand_rng (g_rng, 1, bw / 4 ? bw / 4 : 1);
    for (i = 0; i < r; i++) btor_set_bit_bv (bvsrl, bvsrl->width - 1 - i, 0);
    btor_set_bit_bv (bvsrl, bvsrl->width - 1 - r, 1);
    tmp    = btor_uint64_to_bv (g_mm, 1, sbw);
    bve[0] = btor_srl_bv (g_mm, bvsrl, tmp);
    btor_free_bv (g_mm, tmp);
    r          = btor_pick_rand_rng (g_rng, 1, bw - 1);
    bvmaxshift = btor_uint64_to_bv (g_mm, r, bw);
    tmp        = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmaxshift);
    btor_free_bv (g_mm, bvmaxshift);
    bve[1] = btor_slice_bv (g_mm, tmp, sbw - 1, 0);
    assert (bve[1]->width == sbw);
    btor_free_bv (g_mm, tmp);

    /* find assignment for e[0] (non-fixable conflict) */
    tmp = btor_copy_bv (g_mm, bvsrl);
    r   = btor_bv_to_uint64_bv (bve[1]);
    r   = btor_pick_rand_rng (g_rng, 0, r - 1);
    btor_set_bit_bv (bvsrl, bvsrl->width - 1 - r, 1);
    bits = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    srl = btor_srl_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (srl, 1, bw, bve[1], bvsrl, 0);
    btor_release_exp (g_btor, e[1]);
    btor_release_exp (g_btor, srl);
    btor_free_bv (g_mm, bvsrl);
    bvsrl = tmp;
    e[1]  = tmpe[1];

    /* find assignment for e[1] (non-fixable conflict) */
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    srl = btor_srl_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (srl, 1, bw, bve[0], bvsrl, 1);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, srl);
    btor_free_bv (g_btor->mm, bvsrl);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bve[1]);
    e[0] = tmpe[0];
  }

  /* find assignment for e[1] (non-fixable conflict) */
  if (bw > 2)
  {
    switch (bw)
    {
      case 4:
        bve[0] = btor_char_to_bv (g_mm, "1101");
        bvsrl  = btor_char_to_bv (g_mm, "0010");
        e[0]   = btor_const_exp (g_btor, "1101");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 8:
        bve[0] = btor_char_to_bv (g_mm, "11010011");
        bvsrl  = btor_char_to_bv (g_mm, "01011100");
        e[0]   = btor_const_exp (g_btor, "11010011");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 16:
        bve[0] = btor_char_to_bv (g_mm, "1011110100110100");
        bvsrl  = btor_char_to_bv (g_mm, "0001111101001101");
        e[0]   = btor_const_exp (g_btor, "1011110100110100");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 32:
        bve[0] = btor_char_to_bv (g_mm, "10100101001101011011110100110111");
        bvsrl  = btor_char_to_bv (g_mm, "01101001101111011110100110111000");
        e[0]   = btor_const_exp (g_btor, "10100101001101011011110100110111");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      case 64:
        bve[0] = btor_char_to_bv (
            g_mm,
            "1010010101110101101111010101011010010101111100101111010111011011");
        bvsrl = btor_char_to_bv (
            g_mm,
            "0001010111010110111101000101100001010111110010111101011101101100");
        e[0] = btor_const_exp (
            g_btor,
            "1010010101110101101111010101011010010101111100101111010111011011");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (btor_get_exp_width (g_btor, e[0]) == bw);
        break;
      default: break;
    }
    srl = btor_srl_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (srl, 1, bw, bve[0], bvsrl, 1);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, srl);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bvsrl);
    e[0] = tmpe[0];
  }

  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, one);
  btor_release_exp (g_btor, tmpe[0]);
  btor_release_exp (g_btor, tmpe[1]);
#endif
}

static void
sls_inv_mul_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int i, len, idx;
  BtorNode *mul, *e[3], *tmpe[3];
  BtorBitVector *bvmul, *bve[3], *res, *tmp;
  char *bits, *tmpbits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  mul  = btor_mul_exp (g_btor, e[0], e[1]);

  /* operand is a divisor of the result, gcd (operand, max value) != 1 */
  switch (bw)
  {
    case 1:
      TEST_SLS_INV_VAL (mul, 0, bw, 1, 1, 1);  // 1 * 1 = 1
      TEST_SLS_INV_VAL (mul, 0, bw, 1, 0, 0);  // 0 * 1 = 0
      break;

    case 7:
      TEST_SLS_INV_VAL (mul, 0, bw, 3, 6, 1);  // 3 * 2 = 6
      TEST_SLS_INV_VAL (mul, 0, bw, 2, 4, 0);  // 2 * 2 = 4
      break;

    case 31:
      TEST_SLS_INV_VAL (mul, 0, bw, 334, 41416, 1);      // 334 * 124 = 41416
      TEST_SLS_INV_VAL (mul, 0, bw, 22222, 1511096, 0);  // 68 * 22222 = 1511096
      break;

    case 33:
      TEST_SLS_INV_VAL (
          mul, 0, bw, 556, 89858496, 1);            // 556 * 161616 = 89858496
      TEST_SLS_INV_VAL (mul, 0, bw, 42, 51828, 0);  // 1234 * 42 = 51828
      break;

    case 45:
      TEST_SLS_INV_VAL (
          mul, 0, bw, 354222444, 3896446884, 1);  // 354222444 * 11 = 3896446884
      TEST_SLS_INV_VAL (mul,
                        0,
                        bw,
                        8293882888,
                        24881648664,
                        0);  // 3 * 8293882888 = 24881648664
      break;

    default: break;
  }

  /* ext euclid, gcd (operand, max value) == 1 */
  switch (bw)
  {
    case 7:
      TEST_SLS_INV_VAL (mul, 0, bw, 5, 11, 1);    // 5 * 79 = 11
      TEST_SLS_INV_VAL (mul, 0, bw, 105, 34, 0);  // 82 * 105 = 34
      break;

    case 31:
      TEST_SLS_INV_VAL (
          mul, 0, bw, 156797, 17846234, 1);  // 156797 * 1197258850 = 17846234
      TEST_SLS_INV_VAL (mul,
                        0,
                        bw,
                        34547367,
                        454656422,
                        0);  // 579931114 * 34547367 = 454656422
      break;

    case 33:
      TEST_SLS_INV_VAL (mul,
                        0,
                        bw,
                        801110083,
                        1602220165,
                        1);  // 801110083 * 3887459223 = 1602220165
      TEST_SLS_INV_VAL (
          mul, 0, bw, 125, 4546522, 0);  // 125 * 5772472418 = 4546522
      break;

    case 45:
      TEST_SLS_INV_VAL (
          mul, 0, bw, 25, 234314345, 1);  // 25 * 21110632625873 = 234314345
      TEST_SLS_INV_VAL (
          mul, 0, bw, 1125, 814546522, 0);  // 25926973578834 * 1125 = 814546522
      break;

    default: break;
  }

  /* conflict */
  tmpe[0] = e[0];
  tmpe[1] = e[1];
  btor_release_exp (g_btor, mul);
  switch (bw)
  {
    case 7:
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 6, 0);
      TEST_SLS_INV_VAL (mul, 1, bw, 6, 8, 0);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 0);
      e[1] = tmpe[1];
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 6, 1);
      TEST_SLS_INV_VAL (mul, 1, bw, 6, 124, 1);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 1);
      break;

    case 31:
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 156798, 0);
      TEST_SLS_INV_VAL (mul, 1, bw, 156798, 17846234, 0);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 0);
      e[1] = tmpe[1];
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 33932, 1);
      TEST_SLS_INV_VAL (mul, 1, bw, 33932, 813457, 1);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 1);
      break;

    case 33:
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 801110082, 0);
      TEST_SLS_INV_VAL (mul, 1, bw, 801110082, 1602220163, 0);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 0);
      e[1] = tmpe[1];
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 33932, 1);
      TEST_SLS_INV_VAL (mul, 1, bw, 33932, 508981, 1);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 1);
      break;

    case 45:
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 9801110082, 0);
      TEST_SLS_INV_VAL (mul, 1, bw, 9801110082, 127414431063, 0);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 0);
      e[1] = tmpe[1];
      TEST_SLS_INIT_INV_VAL_CON (mul, bw, 313932, 1);
      TEST_SLS_INV_VAL (mul, 1, bw, 313932, 7848305, 1);
      TEST_SLS_FINISH_INV_VAL_CON (mul, 1);
      break;

    default: break;
  }

  btor_release_exp (g_btor, tmpe[0]);
  btor_release_exp (g_btor, tmpe[1]);
#endif
}

static void
sls_inv_udiv_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int i, len, idx;
  BtorNode *udiv, *e[3], *tmpe[3];
  BtorBitVector *bvudiv, *bve[3], *res, *tmp;
  char *bits, *tmpbits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  udiv = btor_udiv_exp (g_btor, e[0], e[1]);

  switch (bw)
  {
    case 1:
      TEST_SLS_INV_VAL (udiv, 0, bw, 1, 1, 1);  // 1 / 1 = 1
      TEST_SLS_INV_VAL (udiv, 0, bw, 1, 0, 0);  // 0 / 1 = 0
      break;

    case 7:
      TEST_SLS_INV_VAL (udiv, 0, bw, 6, 3, 1);  // 6 / 2 = 3
      TEST_SLS_INV_VAL (udiv, 0, bw, 2, 2, 0);  // 4 / 2 = 2
      break;

    case 31:
      TEST_SLS_INV_VAL (udiv, 0, bw, 41416, 334, 1);  // 41416 / 124 = 334
      TEST_SLS_INV_VAL (udiv, 0, bw, 68, 22222, 0);   // 1511096 / 68 = 22222
      break;

    case 33:
      TEST_SLS_INV_VAL (
          udiv, 0, bw, 89858496, 556, 1);           // 89858496 / 161616 = 556
      TEST_SLS_INV_VAL (udiv, 0, bw, 1234, 42, 0);  // 51828 / 1234 = 42
      break;

    case 45:
      TEST_SLS_INV_VAL (udiv,
                        0,
                        bw,
                        3896446884,
                        354222444,
                        1);  // 3896446884 / 354222444 = 11
      TEST_SLS_INV_VAL (
          udiv, 0, bw, 3, 8293882888, 0);  // 24881648664 / 3 = 8293882888
      break;

    default: break;
  }

  /* conflict */
  tmpe[0] = e[0];
  tmpe[1] = e[1];
  btor_release_exp (g_btor, udiv);

  switch (bw)
  {
    case 1:
      /* conflict: e[0] / 0 != 1...1 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 0, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: 0 / e[1] != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 1, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      e[0] = tmpe[0];
      break;

    case 7:
      /* conflict: e[0] / 0 != 1...1 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 124, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: 0 / e[1] != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 124, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      e[0] = tmpe[0];
      /* conflict: e[0] / bve = bvudiv, overflow: bve * bvudiv */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 124, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 124, 2, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: bve / e[1] = bvudiv, bvudiv % bve != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 6, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 6, 4, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      break;

    case 31:
      /* conflict: e[0] / 0 != 1...1 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 22222, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: 0 / e[1] != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 22222, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      e[0] = tmpe[0];
      /* conflict: e[0] / bve = bvudiv, overflow: bve * bvudiv */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 123456, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 123456, 22222, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: bve / e[1] = bvudiv, bvudiv % bve != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 41416, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 41416, 333, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      break;

    case 33:
      /* conflict: e[0] / 0 != 1...1 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 4242424242, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: 0 / e[1] != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 4242424242, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      e[0] = tmpe[0];
      /* conflict: e[0] / bve = bvudiv, overflow: bve * bvudiv */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 1234, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 1234, 4242424242, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: bve / e[1] = bvudiv, bvudiv % bve != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 89858496, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 89858496, 555, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      break;

    case 45:
      /* conflict: e[0] / 0 != 1...1 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 8293882888, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: 0 / e[1] != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 0, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 0, 8293882888, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      e[0] = tmpe[0];
      /* conflict: e[0] / bve = bvudiv, overflow: bve * bvudiv */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 333333, 0);
      TEST_SLS_INV_VAL (udiv, 1, bw, 333333, 8293882888, 0);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 0);
      e[1] = tmpe[1];
      /* conflict: bve / e[1] = bvudiv, bvudiv % bve != 0 */
      TEST_SLS_INIT_INV_VAL_CON (udiv, bw, 3896446884, 1);
      TEST_SLS_INV_VAL (udiv, 1, bw, 3896446884, 354222441, 1);
      TEST_SLS_FINISH_INV_VAL_CON (udiv, 1);
      break;

    default: break;
  }

  btor_release_exp (g_btor, tmpe[0]);
  btor_release_exp (g_btor, tmpe[1]);
#endif
}

static void
sls_inv_urem_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int j;
  BtorNode *urem, *e[3], *tmpe, *tmpurem;
  BtorBitVector *bvurem, *bve[3], *res, *tmp, *tmp2, *bvmax, *one, *neg, *zero;
  char *bits;

  e[0]  = btor_var_exp (g_btor, bw, 0);
  e[1]  = btor_var_exp (g_btor, bw, 0);
  urem  = btor_urem_exp (g_btor, e[0], e[1]);
  bvmax = btor_ones_bv (g_mm, bw);
  zero  = btor_new_bv (g_mm, bw);
  one   = btor_one_bv (g_mm, bw);
  neg   = btor_neg_bv (g_mm, one);

  /* search assignment for e[1] */
  for (j = 0; (bw > 1 && j < 5) || j < 1; j++)
  {
    /* bve = bvurem */
    tmp    = btor_add_bv (g_mm, bvmax, neg);
    bve[0] = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    TEST_SLS_INV_BV (urem, 0, bw, bve[0], bve[0], 1);
    btor_free_bv (g_mm, bve[0]);

    /* bve > bvurem */
    bve[0] = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmax);
    tmp    = btor_add_bv (g_mm, bve[0], neg);
    bvurem = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    /* conflict if bve[0] - bvurem <= bvurem */
    tmp  = btor_neg_bv (g_mm, bvurem);
    tmp2 = btor_add_bv (g_mm, bve[0], tmp);
    btor_free_bv (g_mm, tmp);
    if (btor_compare_bv (tmp2, bvurem) > 0)
      TEST_SLS_INV_BV (urem, 0, bw, bve[0], bvurem, 1);
    else
    {
      tmpe    = e[0];
      tmpurem = urem;
      bits    = btor_bv_to_char_bv (g_mm, bve[0]);
      e[0]    = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, bits);
      urem = btor_urem_exp (g_btor, e[0], e[1]);
      TEST_SLS_INV_BV (urem, 1, bw, bve[0], bvurem, 1);
      btor_release_exp (g_btor, e[0]);
      btor_release_exp (g_btor, urem);
      e[0] = tmpe;
      urem = tmpurem;
    }
    btor_free_bv (g_mm, bve[0]);
    btor_free_bv (g_mm, bvurem);
    btor_free_bv (g_mm, tmp2);

    /* conflict: bve < bvurem, bvurem = bvmax */
    tmp    = btor_add_bv (g_mm, bvmax, neg);
    bve[0] = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    TEST_SLS_INV_BV (urem, 1, bw, bve[0], bvmax, 1);
    btor_free_bv (g_mm, bve[0]);

    /* conflict: bve = bvurem = bvmax */
    TEST_SLS_INV_BV (urem, 1, bw, bvmax, bvmax, 1);

    /* conflict: bve < bvurem, e const */
    tmpe    = e[0];
    tmpurem = urem;
    bvurem  = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmax);
    tmp     = btor_add_bv (g_mm, bvurem, neg);
    bve[0]  = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    urem = btor_urem_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (urem, 1, bw, bve[0], bvurem, 1);
    btor_free_bv (g_mm, bve[0]);
    btor_free_bv (g_mm, bvurem);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, urem);

    /* conflict: bve = bvurem = bvmax, e const */
    bits = btor_bv_to_char_bv (g_mm, bvmax);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    urem = btor_urem_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (urem, 1, bw, bvmax, bvmax, 1);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, urem);
    e[0] = tmpe;
    urem = tmpurem;
  }

  /* search assginment for e[0] */
  for (j = 0; (bw > 1 && j < 5) || j < 1; j++)
  {
    /* bve > bvurem */
    bve[1] = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmax);
    tmp    = btor_add_bv (g_mm, bve[1], neg);
    bvurem = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    /* conflict if overflow for bve[1] + bvurem */
    tmp  = btor_neg_bv (g_mm, bvurem);
    tmp2 = btor_add_bv (g_mm, bvmax, tmp);
    btor_free_bv (g_mm, tmp);
    if (btor_compare_bv (tmp2, bvmax) <= 0)
      TEST_SLS_INV_BV (urem, 0, bw, bve[1], bvurem, 0);
    else
    {
      tmpe    = e[1];
      tmpurem = urem;
      bits    = btor_bv_to_char_bv (g_mm, bve[1]);
      e[1]    = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, bits);
      urem = btor_urem_exp (g_btor, e[0], e[1]);
      TEST_SLS_INV_BV (urem, 1, bw, bve[1], bvurem, 0);
      btor_release_exp (g_btor, e[1]);
      btor_release_exp (g_btor, urem);
      e[1] = tmpe;
      urem = tmpurem;
    }
    btor_free_bv (g_mm, tmp2);
    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvurem);

    /* conflict: bve = bvurem, e const */
    tmpe    = e[1];
    tmpurem = urem;
    bve[1]  = btor_new_random_bv (g_mm, g_rng, bw);
    bits    = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1]    = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    urem = btor_urem_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (urem, 1, bw, bve[1], bve[1], 0);
    btor_free_bv (g_mm, bve[1]);
    btor_release_exp (g_btor, e[1]);
    btor_release_exp (g_btor, urem);

    /* conflict: bve < bvurem, e const */
    bvurem = btor_new_random_range_bv (g_mm, g_rng, bw, one, bvmax);
    tmp    = btor_add_bv (g_mm, bvurem, neg);
    bve[1] = btor_new_random_range_bv (g_mm, g_rng, bw, zero, tmp);
    btor_free_bv (g_mm, tmp);
    bits = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    urem = btor_urem_exp (g_btor, e[0], e[1]);
    TEST_SLS_INV_BV (urem, 1, bw, bve[1], bve[1], 0);
    btor_free_bv (g_mm, bvurem);
    btor_free_bv (g_mm, bve[1]);
    btor_release_exp (g_btor, e[1]);
    btor_release_exp (g_btor, urem);
    e[1] = tmpe;
    urem = tmpurem;
  }

  btor_release_exp (g_btor, urem);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
  btor_free_bv (g_mm, bvmax);
  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, one);
  btor_free_bv (g_mm, neg);
#endif
}

static void
sls_inv_concat_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int i, j, ebw, iscon;
  BtorNode *concat, *e[3], *tmpe, *tmpconcat;
  BtorBitVector *bvconcat, *bve[3], *res, *tmp;
  char *bits;

  e[0]   = btor_var_exp (g_btor, bw, 0);
  e[1]   = btor_var_exp (g_btor, bw, 0);
  concat = btor_concat_exp (g_btor, e[0], e[1]);

  for (j = 0; j < 5; j++)
  {
    ebw = btor_pick_rand_rng (g_rng, 1, bw);
    if (btor_pick_rand_rng (g_rng, 0, 1))
    {
      bve[0] = btor_new_random_bv (g_mm, g_rng, ebw);
      bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
    }
    else
    {
      bve[1] = btor_new_random_bv (g_mm, g_rng, ebw);
      bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
    }
    bvconcat = btor_concat_bv (g_mm, bve[0], bve[1]);

    TEST_SLS_INV_BV (concat, 0, bw, bve[1], bvconcat, 0);
    TEST_SLS_INV_BV (concat, 0, bw, bve[0], bvconcat, 1);

    btor_free_bv (g_mm, bvconcat);
    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bve[0]);
  }

  /* conflict */
  for (j = 0; j < 5; j++)
  {
    tmpe      = e[1];
    tmpconcat = concat;
    ebw       = btor_pick_rand_rng (g_rng, 1, bw);
    bve[1]    = btor_new_random_bv (g_mm, g_rng, ebw);
    bvconcat  = btor_new_random_bv (g_mm, g_rng, bw + ebw);
    for (iscon = 0, i = 0; i < bve[1]->width; i++)
      if (btor_get_bit_bv (bve[1], i) != btor_get_bit_bv (bvconcat, i))
      {
        iscon = 1;
        break;
      }
    bits = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    concat = btor_concat_exp (g_btor, e[0], e[1]);
    if (iscon)
      TEST_SLS_INV_BV (concat, 1, bw, bve[1], bvconcat, 0);
    else
      TEST_SLS_INV_BV (concat, 0, bw, bve[1], bvconcat, 0);
    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvconcat);
    btor_release_exp (g_btor, e[1]);
    btor_release_exp (g_btor, concat);
    e[1]   = tmpe;
    concat = tmpconcat;

    tmpe      = e[0];
    tmpconcat = concat;
    ebw       = btor_pick_rand_rng (g_rng, 1, bw);
    bve[0]    = btor_new_random_bv (g_mm, g_rng, ebw);
    bvconcat  = btor_new_random_bv (g_mm, g_rng, bw + ebw);
    for (iscon = 0, i = 0; i < bve[0]->width; i++)
      if (btor_get_bit_bv (bve[0], i)
          != btor_get_bit_bv (bvconcat, bvconcat->width - bve[0]->width + i))
      {
        iscon = 1;
        break;
      }
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    concat = btor_concat_exp (g_btor, e[0], e[1]);
    if (iscon)
      TEST_SLS_INV_BV (concat, 1, bw, bve[0], bvconcat, 1);
    else
      TEST_SLS_INV_BV (concat, 0, bw, bve[0], bvconcat, 1);
    btor_free_bv (g_mm, bve[0]);
    btor_free_bv (g_mm, bvconcat);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, concat);
    e[0]   = tmpe;
    concat = tmpconcat;
  }

  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
  btor_release_exp (g_btor, concat);
#endif
}

static void
sls_inv_slice_bv (int bw)
{
  (void) bw;
#ifndef NDEBUG
  int j, up, lo;
  BtorNode *slice, *e[3];
  BtorBitVector *bvslice, *res, *tmp;

  for (j = 0; j < 5; j++)
  {
    e[0]    = btor_var_exp (g_btor, bw, 0);
    up      = btor_pick_rand_rng (g_rng, 0, bw - 1);
    lo      = btor_pick_rand_rng (g_rng, 0, up);
    slice   = btor_slice_exp (g_btor, e[0], up, lo);
    bvslice = btor_new_random_bv (g_mm, g_rng, up - lo + 1);
    res     = inv_slice_bv (g_btor, slice, bvslice);
    tmp     = btor_slice_bv (g_mm, res, up, lo);
    assert (!btor_compare_bv (tmp, bvslice));
    btor_free_bv (g_mm, tmp);
    btor_free_bv (g_mm, res);
    btor_free_bv (g_mm, bvslice);
    btor_release_exp (g_btor, e[0]);
    btor_release_exp (g_btor, slice);
  }
#endif
}

static void
test_slsinv_add_bv (void)
{
  sls_inv_add_bv (1);
  sls_inv_add_bv (7);
  sls_inv_add_bv (31);
  sls_inv_add_bv (33);
  sls_inv_and_bv (45);
}

static void
test_slsinv_and_bv (void)
{
  sls_inv_and_bv (1);
  sls_inv_and_bv (7);
  sls_inv_and_bv (31);
  sls_inv_and_bv (33);
  sls_inv_and_bv (45);
}

static void
test_slsinv_eq_bv (void)
{
  sls_inv_eq_bv (1);
  sls_inv_eq_bv (7);
  sls_inv_eq_bv (31);
  sls_inv_eq_bv (33);
  sls_inv_eq_bv (45);
}

static void
test_slsinv_ult_bv (void)
{
  sls_inv_ult_bv (1);
  sls_inv_ult_bv (7);
  sls_inv_ult_bv (31);
  sls_inv_ult_bv (33);
  sls_inv_ult_bv (45);
}

static void
test_slsinv_sll_bv (void)
{
  sls_inv_sll_bv (2);
  sls_inv_sll_bv (4);
  sls_inv_sll_bv (8);
  sls_inv_sll_bv (16);
  sls_inv_sll_bv (32);
  sls_inv_sll_bv (64);
}

static void
test_slsinv_srl_bv (void)
{
  sls_inv_srl_bv (2);
  sls_inv_srl_bv (4);
  sls_inv_srl_bv (8);
  sls_inv_srl_bv (16);
  sls_inv_srl_bv (32);
  sls_inv_srl_bv (64);
}

static void
test_slsinv_mul_bv (void)
{
  sls_inv_mul_bv (1);
  sls_inv_mul_bv (7);
  sls_inv_mul_bv (31);
  sls_inv_mul_bv (33);
  sls_inv_mul_bv (45);
}

static void
test_slsinv_udiv_bv (void)
{
  sls_inv_udiv_bv (1);
  sls_inv_udiv_bv (7);
  sls_inv_udiv_bv (31);
  sls_inv_udiv_bv (33);
  sls_inv_udiv_bv (45);
}

static void
test_slsinv_urem_bv (void)
{
  sls_inv_urem_bv (1);
  sls_inv_urem_bv (7);
  sls_inv_urem_bv (31);
  sls_inv_urem_bv (33);
  sls_inv_urem_bv (45);
}

static void
test_slsinv_concat_bv (void)
{
  sls_inv_concat_bv (1);
  sls_inv_concat_bv (7);
  sls_inv_concat_bv (31);
  sls_inv_concat_bv (33);
  sls_inv_concat_bv (45);
}

static void
test_slsinv_slice_bv (void)
{
  sls_inv_slice_bv (1);
  sls_inv_slice_bv (7);
  sls_inv_slice_bv (31);
  sls_inv_slice_bv (33);
  sls_inv_slice_bv (45);
}

void
run_slsinv_tests (int argc, char **argv)
{
  (void) argc;
  (void) argv;
  BTOR_RUN_TEST (slsinv_add_bv);
  BTOR_RUN_TEST (slsinv_and_bv);
  BTOR_RUN_TEST (slsinv_eq_bv);
  BTOR_RUN_TEST (slsinv_ult_bv);
  BTOR_RUN_TEST (slsinv_sll_bv);
  BTOR_RUN_TEST (slsinv_srl_bv);
  BTOR_RUN_TEST (slsinv_mul_bv);
  BTOR_RUN_TEST (slsinv_udiv_bv);
  BTOR_RUN_TEST (slsinv_urem_bv);
  BTOR_RUN_TEST (slsinv_concat_bv);
  BTOR_RUN_TEST (slsinv_slice_bv);
}

void
finish_slsinv_tests (void)
{
  btor_delete_btor (g_btor);
}

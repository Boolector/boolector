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
#include "btorexp.h"
#include "btormodel.h"
#include "btorsls.h"
#include "testrunner.h"
#include "utils/btorutil.h"

static Btor *g_btor;
static BtorMemMgr *g_mm;
static BtorRNG *g_rng;
static BtorPtrHashTable **g_bv_model;

void
init_slsinv_tests (void)
{
  g_btor                            = btor_new_btor ();
  g_btor->options.rewrite_level.val = 0;
  btor_init_fun_model (g_btor, &g_btor->fun_model);
  g_mm       = g_btor->mm;
  g_rng      = &g_btor->rng;
  g_bv_model = &g_btor->bv_model;
}

static void
sls_inv_add_bv (int bw)
{
  BtorNode *add, *e[3];
  BtorBitVector *bvadd, *bve[3], *res, *tmp;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  add  = btor_add_exp (g_btor, e[0], e[1]);

  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
  bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
  bvadd  = btor_new_random_bv (g_mm, g_rng, bw);

  /* find assignment for e[0] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
  assert ((*g_bv_model)->count == 1);
  res = inv_add_bv (g_btor, add, bvadd, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  tmp = btor_add_bv (g_mm, res, bve[1]);
  assert (!btor_compare_bv (tmp, bvadd));
  btor_free_bv (g_mm, tmp);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
  assert ((*g_bv_model)->count == 1);
  res = inv_add_bv (g_btor, add, bvadd, 1);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  tmp = btor_add_bv (g_mm, res, bve[0]);
  assert (!btor_compare_bv (tmp, bvadd));
  btor_free_bv (g_mm, tmp);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  btor_free_bv (g_mm, bvadd);
  btor_free_bv (g_mm, bve[0]);
  btor_free_bv (g_mm, bve[1]);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
}

static void
sls_inv_and_bv (int bw)
{
  int i, j;
  BtorNode *and, *e[3], *tmp;
  BtorBitVector *bvand, *bve[3], *res;
  char *bits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  and  = btor_and_exp (g_btor, e[0], e[1]);

  bvand = btor_new_random_bv (g_mm, g_rng, bw);

  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) btor_set_bit_bv (bve[0], i, 1);

  bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) btor_set_bit_bv (bve[0], i, 1);

  /* find assignment for e[0] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
  assert ((*g_bv_model)->count == 1);
  res = inv_and_bv (g_btor, and, bvand, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
  assert ((*g_bv_model)->count == 1);
  res = inv_and_bv (g_btor, and, bvand, 1);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* conflict */
  for (j = 0; j < 2; j++)
  {
    btor_free_bv (g_mm, bve[j]);
    bve[j] = btor_new_random_bv (g_mm, g_rng, bw);
    for (i = 0; i < bve[j]->width; i++)
    {
      if (btor_get_bit_bv (bvand, i) && btor_get_bit_bv (bve[j], i))
      {
        btor_set_bit_bv (bve[j], i, 0);
        break;
      }
    }
  }
  /* fixable, assignment for e[0] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
  assert ((*g_bv_model)->count == 1);
  res = inv_and_bv (g_btor, and, bvand, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);
  /* fixable, assignment for e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
  res = inv_and_bv (g_btor, and, bvand, 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  tmp = e[1];
  if (!btor_is_zero_bv (bvand))
  {
    /* non-fixable, assignment for e[0] */
    btor_init_bv_model (g_btor, g_bv_model);
    bits = btor_bv_to_char_bv (g_mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    btor_release_exp (g_btor, and);
    and = btor_and_exp (g_btor, e[0], e[1]);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
    assert ((*g_bv_model)->count == 1);
    res = inv_and_bv (g_btor, and, bvand, 0);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);

    /* non-fixable, assignment for e[1] */
    btor_init_bv_model (g_btor, g_bv_model);
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    btor_release_exp (g_btor, e[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    btor_release_exp (g_btor, e[1]);
    e[1] = tmp;
    btor_release_exp (g_btor, and);
    and = btor_and_exp (g_btor, e[0], e[1]);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_and_bv (g_btor, and, bvand, 1);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
  }

  btor_free_bv (g_mm, bvand);
  btor_free_bv (g_mm, bve[0]);
  btor_free_bv (g_mm, bve[1]);
  btor_release_exp (g_btor, and);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
}

static void
sls_inv_eq_bv (int bw)
{
  BtorNode *eq, *e[3];
  BtorBitVector *bveq, *bve[3], *res;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  eq   = btor_eq_exp (g_btor, e[0], e[1]);

  bveq   = btor_new_random_bv (g_mm, g_rng, 1);
  bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
  bve[1] = btor_new_random_bv (g_mm, g_rng, bw);

  /* find assignment for e[0],  */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
  assert ((*g_bv_model)->count == 1);
  res = inv_eq_bv (g_btor, eq, bveq, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert ((btor_is_zero_bv (bveq) && btor_compare_bv (res, bve[1]))
          || (!btor_is_zero_bv (bveq) && !btor_compare_bv (res, bve[1])));
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
  assert ((*g_bv_model)->count == 1);
  res = inv_eq_bv (g_btor, eq, bveq, 1);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert ((btor_is_zero_bv (bveq) && btor_compare_bv (res, bve[0]))
          || (!btor_is_zero_bv (bveq) && !btor_compare_bv (res, bve[0])));
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  btor_free_bv (g_mm, bveq);
  btor_free_bv (g_mm, bve[0]);
  btor_free_bv (g_mm, bve[1]);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
}

static void
sls_inv_ult_bv (int bw)
{
  BtorNode *ult, *e[3], *tmpe;
  BtorBitVector *bvult, *bve[3], *res, *tmp, *tr, *fa, *zero, *ones;
  char *bits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  ult  = btor_ult_exp (g_btor, e[0], e[1]);

  bvult = btor_new_random_bv (g_mm, g_rng, 1);

  fa   = btor_new_bv (g_mm, 1);
  tr   = btor_not_bv (g_mm, fa);
  zero = btor_new_bv (g_mm, bw);
  ones = btor_not_bv (g_mm, zero);

  bve[0] = 0;
  do
  {
    tmp    = bve[0];
    bve[0] = btor_new_random_bv (g_mm, g_rng, bw);
    if (tmp) btor_free_bv (g_mm, tmp);
  } while (bw > 1 && !btor_compare_bv (ones, bve[0]) && btor_is_one_bv (bvult));

  bve[1] = 0;
  do
  {
    tmp    = bve[1];
    bve[1] = btor_new_random_bv (g_mm, g_rng, bw);
    if (tmp) btor_free_bv (g_mm, tmp);
  } while (bw > 1 && btor_is_zero_bv (bve[1]) && btor_is_one_bv (bvult));

  /* find assignment for e[0] */
  if (bw > 1 || btor_is_zero_bv (bvult) || !btor_is_zero_bv (bve[1]))
  {
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
    assert ((*g_bv_model)->count == 1);
    res = inv_ult_bv (g_btor, ult, bvult, 0);
    assert ((*g_bv_model)->count == 1);
    assert (res);
    assert ((btor_is_one_bv (bvult) && btor_compare_bv (res, bve[1]) < 0)
            || (btor_is_zero_bv (bvult) && btor_compare_bv (res, bve[1]) >= 0));
    btor_free_bv (g_mm, res);
    btor_delete_bv_model (g_btor, g_bv_model);
  }

  /* find assignment for e[1] */
  if (bw > 1 || btor_is_zero_bv (bvult) || btor_compare_bv (ones, bve[0]))
  {
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_ult_bv (g_btor, ult, bvult, 1);
    assert ((*g_bv_model)->count == 1);
    assert (res);
    assert ((btor_is_one_bv (bvult) && btor_compare_bv (bve[0], res) < 0)
            || (btor_is_zero_bv (bvult) && btor_compare_bv (bve[0], res) >= 0));
    btor_free_bv (g_mm, res);
    btor_delete_bv_model (g_btor, g_bv_model);
  }

  /* find assignment for 0 < e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], zero);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 1);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert (btor_compare_bv (zero, res) < 0);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for 0 >= e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], zero);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 1);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert (btor_compare_bv (zero, res) >= 0);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for e[0] >= 0 */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], zero);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert (btor_compare_bv (res, zero) >= 0);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for e[0] < 1..1 */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], ones);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert (btor_compare_bv (res, ones) < 0);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for e[0] >= 1..1 */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], ones);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 0);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert (btor_compare_bv (res, ones) >= 0);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for 1..1 >= e[1] */
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], ones);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 1);
  assert ((*g_bv_model)->count == 1);
  assert (res);
  assert (btor_compare_bv (ones, res) >= 0);
  btor_free_bv (g_mm, res);
  btor_delete_bv_model (g_btor, g_bv_model);

  tmpe = e[1];

  /* find assignment for e[0] < 0, non-fixable conflict */
  bits = btor_bv_to_char_bv (g_mm, zero);
  e[1] = btor_const_exp (g_btor, bits);
  btor_freestr (g_mm, bits);
  btor_release_exp (g_btor, ult);
  ult = btor_ult_exp (g_btor, e[0], e[1]);
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[1], zero);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 0);
  assert ((*g_bv_model)->count == 1);
  assert (!res);
  btor_delete_bv_model (g_btor, g_bv_model);

  /* find assignment for 1..1 < e[1], non-fixable conflict */
  bits = btor_bv_to_char_bv (g_mm, ones);
  btor_release_exp (g_btor, e[0]);
  e[0] = btor_const_exp (g_btor, bits);
  btor_freestr (g_mm, bits);
  btor_release_exp (g_btor, e[1]);
  e[1] = tmpe;
  btor_release_exp (g_btor, ult);
  ult = btor_ult_exp (g_btor, e[0], e[1]);
  btor_init_bv_model (g_btor, g_bv_model);
  btor_add_to_bv_model (g_btor, *g_bv_model, e[0], ones);
  assert ((*g_bv_model)->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 1);
  assert ((*g_bv_model)->count == 1);
  assert (!res);
  btor_delete_bv_model (g_btor, g_bv_model);

  btor_free_bv (g_mm, tr);
  btor_free_bv (g_mm, fa);
  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, ones);
  btor_free_bv (g_mm, bvult);
  btor_free_bv (g_mm, bve[0]);
  btor_free_bv (g_mm, bve[1]);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
}

static void
sls_inv_sll_bv (int bw)
{
  int i, j, r, sbw;
  BtorNode *sll, *e[3], *tmpe;
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
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
    assert ((*g_bv_model)->count == 1);
    res = inv_sll_bv (g_btor, sll, bvsll, 0);
    assert ((*g_bv_model)->count == 1);
    assert (res);
    tmp = btor_sll_bv (g_mm, res, bve[1]);
    assert (!btor_compare_bv (tmp, bvsll));
    btor_free_bv (g_mm, tmp);
    btor_free_bv (g_mm, res);
    btor_delete_bv_model (g_btor, g_bv_model);

    /* find assignment for e[1] (shift value) */
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_sll_bv (g_btor, sll, bvsll, 1);
    assert ((*g_bv_model)->count == 1);
    assert (res);
    tmp = btor_sll_bv (g_mm, bve[0], res);
    assert (!btor_compare_bv (tmp, bvsll));
    btor_free_bv (g_mm, tmp);
    btor_free_bv (g_mm, res);
    btor_delete_bv_model (g_btor, g_bv_model);

    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvsll);
  }
  btor_free_bv (g_mm, bve[0]);
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
    tmpe = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    sll = btor_sll_exp (g_btor, e[0], tmpe);
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, tmpe, bve[1]);
    assert ((*g_bv_model)->count == 1);
    res = inv_sll_bv (g_btor, sll, bvsll, 0);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
    btor_release_exp (g_btor, tmpe);
    btor_release_exp (g_btor, sll);
    btor_free_bv (g_mm, bvsll);
    bvsll = tmp;

    /* find assignment for e[1] (non-fixable conflict) */
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    tmpe = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    sll = btor_sll_exp (g_btor, tmpe, e[1]);
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, tmpe, bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_sll_bv (g_btor, sll, bvsll, 1);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
    btor_release_exp (g_btor, tmpe);
    btor_release_exp (g_btor, sll);
    btor_free_bv (g_btor->mm, bvsll);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bve[1]);
  }

  /* find assignment for e[1] (non-fixable conflict) */
  if (bw > 2)
  {
    switch (bw)
    {
      case 4:
        bve[0] = btor_char_to_bv (g_mm, "1101");
        bvsll  = btor_char_to_bv (g_mm, "0010");
        tmpe   = btor_const_exp (g_btor, "1101");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 8:
        bve[0] = btor_char_to_bv (g_mm, "11010011");
        bvsll  = btor_char_to_bv (g_mm, "01011100");
        tmpe   = btor_const_exp (g_btor, "11010011");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 16:
        bve[0] = btor_char_to_bv (g_mm, "1011110100110100");
        bvsll  = btor_char_to_bv (g_mm, "1111101001101000");
        tmpe   = btor_const_exp (g_btor, "1011110100110100");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 32:
        bve[0] = btor_char_to_bv (g_mm, "10100101001101011011110100110111");
        bvsll  = btor_char_to_bv (g_mm, "01101001101111011110100110111000");
        tmpe   = btor_const_exp (g_btor, "10100101001101011011110100110111");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 64:
        bve[0] = btor_char_to_bv (
            g_mm,
            "1010010101110101101111010101011010010101111100101111010111011011");
        bvsll = btor_char_to_bv (
            g_mm,
            "1010111010110111101000101100001010111110010111101011101101100000");
        tmpe = btor_const_exp (
            g_btor,
            "1010010101110101101111010101011010010101111100101111010111011011");
        assert (bve[0]->width == bw);
        assert (bvsll->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      default: break;
    }
    sll = btor_sll_exp (g_btor, tmpe, e[1]);
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, tmpe, bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_sll_bv (g_btor, sll, bvsll, 1);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
    btor_release_exp (g_btor, tmpe);
    btor_release_exp (g_btor, sll);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bvsll);
  }

  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, one);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
}

static void
sls_inv_srl_bv (int bw)
{
  int i, j, r, sbw;
  BtorNode *srl, *e[3], *tmpe;
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
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
    assert ((*g_bv_model)->count == 1);
    res = inv_srl_bv (g_btor, srl, bvsrl, 0);
    assert ((*g_bv_model)->count == 1);
    assert (res);
    tmp = btor_srl_bv (g_mm, res, bve[1]);
    assert (!btor_compare_bv (tmp, bvsrl));
    btor_free_bv (g_mm, tmp);
    btor_free_bv (g_mm, res);
    btor_delete_bv_model (g_btor, g_bv_model);

    /* find assignment for e[1] (shift value) */
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_srl_bv (g_btor, srl, bvsrl, 1);
    assert ((*g_bv_model)->count == 1);
    assert (res);
    tmp = btor_srl_bv (g_mm, bve[0], res);
    assert (!btor_compare_bv (tmp, bvsrl));
    btor_free_bv (g_mm, tmp);
    btor_free_bv (g_mm, res);
    btor_delete_bv_model (g_btor, g_bv_model);

    btor_free_bv (g_mm, bve[1]);
    btor_free_bv (g_mm, bvsrl);
  }
  btor_free_bv (g_mm, bve[0]);
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
    tmpe = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    srl = btor_srl_exp (g_btor, e[0], tmpe);
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, tmpe, bve[1]);
    assert ((*g_bv_model)->count == 1);
    res = inv_srl_bv (g_btor, srl, bvsrl, 0);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
    btor_release_exp (g_btor, tmpe);
    btor_release_exp (g_btor, srl);
    btor_free_bv (g_mm, bvsrl);
    bvsrl = tmp;

    /* find assignment for e[1] (non-fixable conflict) */
    bits = btor_bv_to_char_bv (g_mm, bve[0]);
    tmpe = btor_const_exp (g_btor, bits);
    btor_freestr (g_mm, bits);
    srl = btor_srl_exp (g_btor, tmpe, e[1]);
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, tmpe, bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_srl_bv (g_btor, srl, bvsrl, 1);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
    btor_release_exp (g_btor, tmpe);
    btor_release_exp (g_btor, srl);
    btor_free_bv (g_btor->mm, bvsrl);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bve[1]);
  }

  /* find assignment for e[1] (non-fixable conflict) */
  if (bw > 2)
  {
    switch (bw)
    {
      case 4:
        bve[0] = btor_char_to_bv (g_mm, "1101");
        bvsrl  = btor_char_to_bv (g_mm, "0010");
        tmpe   = btor_const_exp (g_btor, "1101");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 8:
        bve[0] = btor_char_to_bv (g_mm, "11010011");
        bvsrl  = btor_char_to_bv (g_mm, "01011100");
        tmpe   = btor_const_exp (g_btor, "11010011");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 16:
        bve[0] = btor_char_to_bv (g_mm, "1011110100110100");
        bvsrl  = btor_char_to_bv (g_mm, "0001111101001101");
        tmpe   = btor_const_exp (g_btor, "1011110100110100");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 32:
        bve[0] = btor_char_to_bv (g_mm, "10100101001101011011110100110111");
        bvsrl  = btor_char_to_bv (g_mm, "01101001101111011110100110111000");
        tmpe   = btor_const_exp (g_btor, "10100101001101011011110100110111");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      case 64:
        bve[0] = btor_char_to_bv (
            g_mm,
            "1010010101110101101111010101011010010101111100101111010111011011");
        bvsrl = btor_char_to_bv (
            g_mm,
            "0001010111010110111101000101100001010111110010111101011101101100");
        tmpe = btor_const_exp (
            g_btor,
            "1010010101110101101111010101011010010101111100101111010111011011");
        assert (bve[0]->width == bw);
        assert (bvsrl->width == bw);
        assert (BTOR_REAL_ADDR_NODE (tmpe)->len == bw);
        break;
      default: break;
    }
    srl = btor_srl_exp (g_btor, tmpe, e[1]);
    btor_init_bv_model (g_btor, g_bv_model);
    btor_add_to_bv_model (g_btor, *g_bv_model, tmpe, bve[0]);
    assert ((*g_bv_model)->count == 1);
    res = inv_srl_bv (g_btor, srl, bvsrl, 1);
    assert ((*g_bv_model)->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, g_bv_model);
    btor_release_exp (g_btor, tmpe);
    btor_release_exp (g_btor, srl);
    btor_free_bv (g_btor->mm, bve[0]);
    btor_free_bv (g_btor->mm, bvsrl);
  }

  btor_free_bv (g_mm, zero);
  btor_free_bv (g_mm, one);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
}

static void
sls_inv_mul_bv (int bw)
{
  int i, len;
  BtorNode *mul, *e[3], *tmpe;
  BtorBitVector *bvmul, *bve[3], *res, *tmp;
  char *bits, *tmpbits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  mul  = btor_mul_exp (g_btor, e[0], e[1]);

  /* operand is a divisor of the result, gcd (operand, max value) != 1 */
  switch (bw)
  {
    case 7:
      bve[0] = btor_uint64_to_bv (g_mm, 3, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 6, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 2, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 4, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 31:
      bve[0] = btor_uint64_to_bv (g_mm, 334, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 41416, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 22222, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 1511096, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 33:
      bve[0] = btor_uint64_to_bv (g_mm, 556, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 89858496, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 42, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 51828, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 45:
      bve[0] = btor_uint64_to_bv (g_mm, 354222444, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 3896446884, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 8293882888, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 24881648664, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    default: break;
  }

  /* ext euclid, gcd (operand, max value) == 1 */
  switch (bw)
  {
    case 1:
      bve[0] = btor_uint64_to_bv (g_mm, 1, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 1, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 1, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 0, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 7:
      bve[0] = btor_uint64_to_bv (g_mm, 5, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 11, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 105, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 34, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 31:
      bve[0] = btor_uint64_to_bv (g_mm, 156797, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 17846234, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 34547367, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 454656422, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 33:
      bve[0] = btor_uint64_to_bv (g_mm, 801110083, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 1602220166, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 125, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 4546522, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 45:
      bve[0] = btor_uint64_to_bv (g_mm, 25, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 234314345, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, bve[0], res);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);

      bve[1] = btor_uint64_to_bv (g_mm, 1125, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 814546522, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      tmp = btor_mul_bv (g_mm, res, bve[1]);
      assert (!btor_compare_bv (tmp, bvmul));
      btor_free_bv (g_mm, tmp);
      btor_free_bv (g_mm, res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    default: break;
  }

  /* conflict */
  tmpe = e[1];
  switch (bw)
  {
    case 7:
      tmpbits = btor_decimal_to_const (g_mm, "6");
      len     = strlen ("6");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[1] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[1] = btor_uint64_to_bv (g_mm, 6, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 8, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);

      btor_release_exp (g_btor, e[1]);
      e[1] = tmpe;
      btor_release_exp (g_btor, e[0]);
      tmpbits = btor_decimal_to_const (g_mm, "6");
      len     = strlen ("6");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[0] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[0] = btor_uint64_to_bv (g_mm, 6, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 124, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 31:
      tmpbits = btor_decimal_to_const (g_mm, "156798");
      len     = strlen ("156798");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[1] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[1] = btor_uint64_to_bv (g_mm, 156798, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 17846234, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);

      btor_release_exp (g_btor, e[1]);
      e[1] = tmpe;
      btor_release_exp (g_btor, e[0]);
      tmpbits = btor_decimal_to_const (g_mm, "33932");
      len     = strlen ("33932");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[0] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[0] = btor_uint64_to_bv (g_mm, 33932, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 813457, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 33:
      tmpbits = btor_decimal_to_const (g_mm, "801110082");
      len     = strlen ("801110082");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[1] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[1] = btor_uint64_to_bv (g_mm, 801110082, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 1602220163, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);

      btor_release_exp (g_btor, e[1]);
      e[1] = tmpe;
      btor_release_exp (g_btor, e[0]);
      tmpbits = btor_decimal_to_const (g_mm, "33932");
      len     = strlen ("33932");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[0] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[0] = btor_uint64_to_bv (g_mm, 33932, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 508981, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);
      break;

    case 45:
      tmpbits = btor_decimal_to_const (g_mm, "9801110082");
      len     = strlen ("9801110082");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[1] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[1] = btor_uint64_to_bv (g_mm, 9801110082, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 127414431063, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[1], bve[1]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 0);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[1]);
      btor_free_bv (g_btor->mm, bvmul);

      btor_release_exp (g_btor, e[1]);
      e[1] = tmpe;
      btor_release_exp (g_btor, e[0]);
      tmpbits = btor_decimal_to_const (g_mm, "313932");
      len     = strlen ("313932");
      BTOR_CNEWN (g_mm, bits, bw + 1);
      for (i = 0; i < bw; i++) bits[i] = i < len ? tmpbits[i] : '0';
      e[0] = btor_const_exp (g_btor, bits);
      btor_freestr (g_mm, tmpbits);
      BTOR_DELETEN (g_mm, bits, bw + 1);
      btor_release_exp (g_btor, mul);
      mul    = btor_mul_exp (g_btor, e[0], e[1]);
      bve[0] = btor_uint64_to_bv (g_mm, 313932, bw);
      bvmul  = btor_uint64_to_bv (g_mm, 7848305, bw);
      btor_init_bv_model (g_btor, g_bv_model);
      btor_add_to_bv_model (g_btor, *g_bv_model, e[0], bve[0]);
      assert ((*g_bv_model)->count == 1);
      res = inv_mul_bv (g_btor, mul, bvmul, 1);
      assert ((*g_bv_model)->count == 1);
      assert (!res);
      btor_delete_bv_model (g_btor, g_bv_model);
      btor_free_bv (g_btor->mm, bve[0]);
      btor_free_bv (g_btor->mm, bvmul);
      break;
    default: break;
  }

  btor_release_exp (g_btor, mul);
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
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

void
run_slsinv_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (slsinv_add_bv);
  BTOR_RUN_TEST (slsinv_and_bv);
  BTOR_RUN_TEST (slsinv_eq_bv);
  BTOR_RUN_TEST (slsinv_ult_bv);
  BTOR_RUN_TEST (slsinv_sll_bv);
  BTOR_RUN_TEST (slsinv_srl_bv);
  BTOR_RUN_TEST (slsinv_mul_bv);
}

void
finish_slsinv_tests (void)
{
  btor_delete_btor (g_btor);
}

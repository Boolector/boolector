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
#include "btorexp.h"
#include "btormodel.h"
#include "btorsls.h"
#include "testrunner.h"
#include "utils/btorutil.h"

static Btor *g_btor;

void
init_slsinv_tests (void)
{
  g_btor                            = btor_new_btor ();
  g_btor->options.rewrite_level.val = 0;
  btor_init_fun_model (g_btor, &g_btor->fun_model);
}

static void
sls_inv_add_bv (int bw)
{
  BtorNode *add, *e[3];
  BtorBitVector *bvadd, *bve[3], *res, *tmp;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  add  = btor_add_exp (g_btor, e[0], e[1]);

  bve[0] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
  bve[1] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
  bvadd  = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);

  /* find assignment for e[0] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], bve[1]);
  assert (g_btor->bv_model->count == 1);
  res = inv_add_bv (g_btor, add, bvadd, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  tmp = btor_add_bv (g_btor->mm, res, bve[1]);
  assert (!btor_compare_bv (tmp, bvadd));
  btor_free_bv (g_btor->mm, tmp);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], bve[0]);
  assert (g_btor->bv_model->count == 1);
  res = inv_add_bv (g_btor, add, bvadd, 1);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  tmp = btor_add_bv (g_btor->mm, res, bve[0]);
  assert (!btor_compare_bv (tmp, bvadd));
  btor_free_bv (g_btor->mm, tmp);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  btor_free_bv (g_btor->mm, bvadd);
  btor_free_bv (g_btor->mm, bve[0]);
  btor_free_bv (g_btor->mm, bve[1]);
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

  bvand = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);

  bve[0] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) btor_set_bit_bv (bve[0], i, 1);

  bve[1] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) btor_set_bit_bv (bve[0], i, 1);

  /* find assignment for e[0] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], bve[1]);
  assert (g_btor->bv_model->count == 1);
  res = inv_and_bv (g_btor, and, bvand, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], bve[0]);
  assert (g_btor->bv_model->count == 1);
  res = inv_and_bv (g_btor, and, bvand, 1);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* conflict */
  for (j = 0; j < 2; j++)
  {
    btor_free_bv (g_btor->mm, bve[j]);
    bve[j] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
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
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], bve[1]);
  assert (g_btor->bv_model->count == 1);
  res = inv_and_bv (g_btor, and, bvand, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);
  /* fixable, assignment for e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], bve[0]);
  res = inv_and_bv (g_btor, and, bvand, 1);
  assert (res);
  for (i = 0; i < bvand->width; i++)
    if (btor_get_bit_bv (bvand, i)) assert (btor_get_bit_bv (res, i));
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  tmp = e[1];
  if (!btor_is_zero_bv (bvand))
  {
    /* non-fixable, assignment for e[0] */
    btor_init_bv_model (g_btor, &g_btor->bv_model);
    bits = btor_bv_to_char_bv (g_btor->mm, bve[1]);
    e[1] = btor_const_exp (g_btor, bits);
    btor_freestr (g_btor->mm, bits);
    btor_release_exp (g_btor, and);
    and = btor_and_exp (g_btor, e[0], e[1]);
    btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], bve[1]);
    assert (g_btor->bv_model->count == 1);
    res = inv_and_bv (g_btor, and, bvand, 0);
    assert (g_btor->bv_model->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, &g_btor->bv_model);

    /* non-fixable, assignment for e[1] */
    btor_init_bv_model (g_btor, &g_btor->bv_model);
    bits = btor_bv_to_char_bv (g_btor->mm, bve[0]);
    btor_release_exp (g_btor, e[0]);
    e[0] = btor_const_exp (g_btor, bits);
    btor_freestr (g_btor->mm, bits);
    btor_release_exp (g_btor, e[1]);
    e[1] = tmp;
    btor_release_exp (g_btor, and);
    and = btor_and_exp (g_btor, e[0], e[1]);
    btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], bve[0]);
    assert (g_btor->bv_model->count == 1);
    res = inv_and_bv (g_btor, and, bvand, 1);
    assert (g_btor->bv_model->count == 1);
    assert (!res);
    btor_delete_bv_model (g_btor, &g_btor->bv_model);
  }

  btor_free_bv (g_btor->mm, bvand);
  btor_free_bv (g_btor->mm, bve[0]);
  btor_free_bv (g_btor->mm, bve[1]);
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

  bveq   = btor_new_random_bv (g_btor->mm, &g_btor->rng, 1);
  bve[0] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
  bve[1] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);

  /* find assignment for e[0],  */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], bve[1]);
  assert (g_btor->bv_model->count == 1);
  res = inv_eq_bv (g_btor, eq, bveq, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert ((btor_is_zero_bv (bveq) && btor_compare_bv (res, bve[1]))
          || (!btor_is_zero_bv (bveq) && !btor_compare_bv (res, bve[1])));
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], bve[0]);
  assert (g_btor->bv_model->count == 1);
  res = inv_eq_bv (g_btor, eq, bveq, 1);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert ((btor_is_zero_bv (bveq) && btor_compare_bv (res, bve[0]))
          || (!btor_is_zero_bv (bveq) && !btor_compare_bv (res, bve[0])));
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  btor_free_bv (g_btor->mm, bveq);
  btor_free_bv (g_btor->mm, bve[0]);
  btor_free_bv (g_btor->mm, bve[1]);
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

  bvult = btor_new_random_bv (g_btor->mm, &g_btor->rng, 1);

  fa   = btor_new_bv (g_btor->mm, 1);
  tr   = btor_not_bv (g_btor->mm, fa);
  zero = btor_new_bv (g_btor->mm, bw);
  ones = btor_not_bv (g_btor->mm, zero);

  bve[0] = 0;
  do
  {
    tmp    = bve[0];
    bve[0] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
    if (tmp) btor_free_bv (g_btor->mm, tmp);
  } while (bw > 1 && !btor_compare_bv (ones, bve[0]) && btor_is_one_bv (bvult));

  bve[1] = 0;
  do
  {
    tmp    = bve[1];
    bve[1] = btor_new_random_bv (g_btor->mm, &g_btor->rng, bw);
    if (tmp) btor_free_bv (g_btor->mm, tmp);
  } while (bw > 1 && btor_is_zero_bv (bve[1]) && btor_is_one_bv (bvult));

  /* find assignment for e[0] */
  if (bw > 1 || btor_is_zero_bv (bvult) || !btor_is_zero_bv (bve[1]))
  {
    btor_init_bv_model (g_btor, &g_btor->bv_model);
    btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], bve[1]);
    assert (g_btor->bv_model->count == 1);
    res = inv_ult_bv (g_btor, ult, bvult, 0);
    assert (g_btor->bv_model->count == 1);
    assert (res);
    assert ((btor_is_one_bv (bvult) && btor_compare_bv (res, bve[1]) < 0)
            || (btor_is_zero_bv (bvult) && btor_compare_bv (res, bve[1]) >= 0));
    btor_free_bv (g_btor->mm, res);
    btor_delete_bv_model (g_btor, &g_btor->bv_model);
  }

  /* find assignment for e[1] */
  if (bw > 1 || btor_is_zero_bv (bvult) || btor_compare_bv (ones, bve[0]))
  {
    btor_init_bv_model (g_btor, &g_btor->bv_model);
    btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], bve[0]);
    assert (g_btor->bv_model->count == 1);
    res = inv_ult_bv (g_btor, ult, bvult, 1);
    assert (g_btor->bv_model->count == 1);
    assert (res);
    assert ((btor_is_one_bv (bvult) && btor_compare_bv (bve[0], res) < 0)
            || (btor_is_zero_bv (bvult) && btor_compare_bv (bve[0], res) >= 0));
    btor_free_bv (g_btor->mm, res);
    btor_delete_bv_model (g_btor, &g_btor->bv_model);
  }

  /* find assignment for 0 < e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], zero);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 1);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert (btor_compare_bv (zero, res) < 0);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for 0 >= e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], zero);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 1);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert (btor_compare_bv (zero, res) >= 0);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for e[0] >= 0 */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], zero);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert (btor_compare_bv (res, zero) >= 0);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for e[0] < 1..1 */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], ones);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert (btor_compare_bv (res, ones) < 0);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for e[0] >= 1..1 */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], ones);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 0);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert (btor_compare_bv (res, ones) >= 0);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for 1..1 >= e[1] */
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], ones);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, fa, 1);
  assert (g_btor->bv_model->count == 1);
  assert (res);
  assert (btor_compare_bv (ones, res) >= 0);
  btor_free_bv (g_btor->mm, res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  tmpe = e[1];

  /* find assignment for e[0] < 0, non-fixable conflict */
  bits = btor_bv_to_char_bv (g_btor->mm, zero);
  e[1] = btor_const_exp (g_btor, bits);
  btor_freestr (g_btor->mm, bits);
  btor_release_exp (g_btor, ult);
  ult = btor_ult_exp (g_btor, e[0], e[1]);
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[1], zero);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 0);
  assert (g_btor->bv_model->count == 1);
  assert (!res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  /* find assignment for 1..1 < e[1], non-fixable conflict */
  bits = btor_bv_to_char_bv (g_btor->mm, ones);
  btor_release_exp (g_btor, e[0]);
  e[0] = btor_const_exp (g_btor, bits);
  btor_freestr (g_btor->mm, bits);
  btor_release_exp (g_btor, e[1]);
  e[1] = tmpe;
  btor_release_exp (g_btor, ult);
  ult = btor_ult_exp (g_btor, e[0], e[1]);
  btor_init_bv_model (g_btor, &g_btor->bv_model);
  btor_add_to_bv_model (g_btor, g_btor->bv_model, e[0], ones);
  assert (g_btor->bv_model->count == 1);
  res = inv_ult_bv (g_btor, ult, tr, 1);
  assert (g_btor->bv_model->count == 1);
  assert (!res);
  btor_delete_bv_model (g_btor, &g_btor->bv_model);

  btor_free_bv (g_btor->mm, tr);
  btor_free_bv (g_btor->mm, fa);
  btor_free_bv (g_btor->mm, zero);
  btor_free_bv (g_btor->mm, ones);
  btor_free_bv (g_btor->mm, bvult);
  btor_free_bv (g_btor->mm, bve[0]);
  btor_free_bv (g_btor->mm, bve[1]);
  btor_release_exp (g_btor, ult);
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
void
run_slsinv_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (slsinv_add_bv);
  BTOR_RUN_TEST (slsinv_and_bv);
  BTOR_RUN_TEST (slsinv_eq_bv);
  BTOR_RUN_TEST (slsinv_ult_bv);
}

void
finish_slsinv_tests (void)
{
  btor_delete_btor (g_btor);
}

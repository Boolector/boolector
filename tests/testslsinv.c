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
  /* keep track of children (might have changed due to rewriting) */
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
  e[0] = btor_copy_exp (g_btor, add->e[0]);
  e[1] = btor_copy_exp (g_btor, add->e[1]);

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
  BtorNode *and, *e[3], *tmpe;
  BtorBitVector *bvand, *bve[3], *res;
  char *bits;

  e[0] = btor_var_exp (g_btor, bw, 0);
  e[1] = btor_var_exp (g_btor, bw, 0);
  and  = btor_and_exp (g_btor, e[0], e[1]);
  /* keep track of children (might have changed due to rewriting) */
  btor_release_exp (g_btor, e[0]);
  btor_release_exp (g_btor, e[1]);
  e[0] = btor_copy_exp (g_btor, and->e[0]);
  e[1] = btor_copy_exp (g_btor, and->e[1]);

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

  tmpe = e[1];

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
    e[1] = tmpe;
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

void
run_slsinv_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (slsinv_add_bv);
  BTOR_RUN_TEST (slsinv_and_bv);
}

void
finish_slsinv_tests (void)
{
  btor_delete_btor (g_btor);
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"
#include "normalizer/btornormquant.h"
#include "testrunner.h"

#include "dumper/btordumpsmt.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

#define RUN_TEST(TEST)        \
  {                           \
    init_normquant_test ();   \
    BTOR_RUN_TEST (TEST);     \
    finish_normquant_test (); \
  }

static Btor *g_btor = NULL;

static void
init_normquant_test (void)
{
  g_btor = btor_new_btor ();
}

static void
finish_normquant_test (void)
{
  btor_delete_btor (g_btor);
}

void
init_normquant_tests (void)
{
}

void
finish_normquant_tests (void)
{
}

/* -------------------------------------------------------------------------- */

static void
test_normquant_inv_exists (void)
{
  BtorNode *exists, *eqx, *eqy, *x[2], *y[2], *expected, *result;

  x[0]   = btor_param_exp (g_btor, 32, 0);
  x[1]   = btor_param_exp (g_btor, 32, 0);
  eqx    = btor_eq_exp (g_btor, x[0], x[1]);
  exists = btor_exists_n_exp (g_btor, x, 2, eqx);

  y[0]     = btor_param_exp (g_btor, 32, 0);
  y[1]     = btor_param_exp (g_btor, 32, 0);
  eqy      = btor_eq_exp (g_btor, y[0], y[1]);
  expected = btor_forall_n_exp (g_btor, y, 2, BTOR_INVERT_NODE (eqy));

  result =
      btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (exists), 0);
  assert (result == expected);

  btor_release_exp (g_btor, x[0]);
  btor_release_exp (g_btor, x[1]);
  btor_release_exp (g_btor, eqx);
  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, eqy);
  btor_release_exp (g_btor, exists);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}

static void
test_normquant_inv_forall (void)
{
  BtorNode *forall, *eqx, *eqy, *x[2], *y[2], *expected, *result;

  x[0]   = btor_param_exp (g_btor, 32, 0);
  x[1]   = btor_param_exp (g_btor, 32, 0);
  eqx    = btor_eq_exp (g_btor, x[0], x[1]);
  forall = btor_forall_n_exp (g_btor, x, 2, eqx);

  y[0]     = btor_param_exp (g_btor, 32, 0);
  y[1]     = btor_param_exp (g_btor, 32, 0);
  eqy      = btor_eq_exp (g_btor, y[0], y[1]);
  expected = btor_exists_n_exp (g_btor, y, 2, BTOR_INVERT_NODE (eqy));

  result =
      btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (forall), 0);
  assert (result == expected);

  btor_release_exp (g_btor, x[0]);
  btor_release_exp (g_btor, x[1]);
  btor_release_exp (g_btor, eqx);
  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, eqy);
  btor_release_exp (g_btor, forall);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}

static void
test_normquant_inv_exists_nested (void)
{
  BtorNode *forall, *exists, *eqx, *x[2];
  BtorNode *expected, *eqy, *y[2];
  BtorNode *result;

  x[0]   = btor_param_exp (g_btor, 32, 0);
  x[1]   = btor_param_exp (g_btor, 32, 0);
  eqx    = btor_eq_exp (g_btor, x[0], x[1]);
  exists = btor_exists_exp (g_btor, x[0], eqx);
  forall = btor_forall_exp (g_btor, x[1], BTOR_INVERT_NODE (exists));

  y[0]     = btor_param_exp (g_btor, 32, 0);
  y[1]     = btor_param_exp (g_btor, 32, 0);
  eqy      = btor_eq_exp (g_btor, y[0], y[1]);
  expected = btor_forall_n_exp (g_btor, y, 2, BTOR_INVERT_NODE (eqy));

  result = btor_normalize_quantifiers_node (g_btor, forall, 0);
  assert (result == expected);

  btor_release_exp (g_btor, x[0]);
  btor_release_exp (g_btor, x[1]);
  btor_release_exp (g_btor, eqx);
  btor_release_exp (g_btor, exists);
  btor_release_exp (g_btor, forall);
  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, eqy);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}

static void
test_normquant_inv_exists_nested2 (void)
{
  BtorNode *forall, *exists, *eqx, *x[2];
  BtorNode *expected, *eqy, *y[2];
  BtorNode *result;

  x[0]   = btor_param_exp (g_btor, 32, 0);
  x[1]   = btor_param_exp (g_btor, 32, 0);
  eqx    = btor_eq_exp (g_btor, x[0], x[1]);
  exists = btor_exists_exp (g_btor, x[0], eqx);
  forall = btor_forall_exp (g_btor, x[1], BTOR_INVERT_NODE (exists));

  y[0]     = btor_param_exp (g_btor, 32, 0);
  y[1]     = btor_param_exp (g_btor, 32, 0);
  eqy      = btor_eq_exp (g_btor, y[0], y[1]);
  expected = btor_exists_n_exp (g_btor, y, 2, eqy);

  result =
      btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (forall), 0);
  assert (result == expected);

  btor_release_exp (g_btor, x[0]);
  btor_release_exp (g_btor, x[1]);
  btor_release_exp (g_btor, eqx);
  btor_release_exp (g_btor, exists);
  btor_release_exp (g_btor, forall);
  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, eqy);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}

static void
test_normquant_inv_prefix (void)
{
  BtorNode *forall0, *forall1, *exists, *x[3], *and;
  BtorNode *exists0, *expected, *forall, *y[3], *andy;
  BtorNode *result;

  x[0]    = btor_param_exp (g_btor, 1, 0);
  x[1]    = btor_param_exp (g_btor, 1, 0);
  x[2]    = btor_param_exp (g_btor, 1, 0);
  and     = btor_and_n_exp (g_btor, x, 3);
  forall0 = btor_forall_exp (g_btor, x[0], and);
  exists  = btor_exists_exp (g_btor, x[1], forall0);
  forall1 = btor_forall_exp (g_btor, x[2], exists);

  y[0]     = btor_param_exp (g_btor, 1, 0);
  y[1]     = btor_param_exp (g_btor, 1, 0);
  y[2]     = btor_param_exp (g_btor, 1, 0);
  andy     = btor_and_n_exp (g_btor, y, 3);
  exists0  = btor_exists_exp (g_btor, y[0], BTOR_INVERT_NODE (andy));
  forall   = btor_forall_exp (g_btor, y[1], exists0);
  expected = btor_exists_exp (g_btor, y[2], forall);

  result =
      btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (forall1), 0);
  assert (result == expected);

  btor_release_exp (g_btor, x[0]);
  btor_release_exp (g_btor, x[1]);
  btor_release_exp (g_btor, x[2]);
  btor_release_exp (g_btor, and);
  btor_release_exp (g_btor, forall0);
  btor_release_exp (g_btor, exists);
  btor_release_exp (g_btor, forall1);

  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, y[2]);
  btor_release_exp (g_btor, andy);
  btor_release_exp (g_btor, exists0);
  btor_release_exp (g_btor, forall);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}

static void
test_normquant_inv_and_exists (void)
{
  BtorNode *forall, *exists0, *exists1, *and, *x, *y[2], *ult, *ugt;
  BtorNode *expected, *forall0, *forall1, * or, *X, *Y[2], *ugte, *ulte;
  BtorNode *result;

  x       = btor_param_exp (g_btor, 32, 0);
  y[0]    = btor_param_exp (g_btor, 32, 0);
  y[1]    = btor_param_exp (g_btor, 32, 0);
  ugt     = btor_ugt_exp (g_btor, x, y[0]);
  exists0 = btor_exists_exp (g_btor, y[0], ugt);
  ult     = btor_ult_exp (g_btor, x, y[1]);
  exists1 = btor_exists_exp (g_btor, y[1], ult);
  and     = btor_and_exp (g_btor, exists0, exists1);
  forall  = btor_forall_exp (g_btor, x, BTOR_INVERT_NODE (and));

  X        = btor_param_exp (g_btor, 32, 0);
  Y[0]     = btor_param_exp (g_btor, 32, 0);
  Y[1]     = btor_param_exp (g_btor, 32, 0);
  ulte     = btor_ulte_exp (g_btor, X, Y[0]);
  forall0  = btor_forall_exp (g_btor, Y[0], ulte);
  ugte     = btor_ugte_exp (g_btor, X, Y[1]);
  forall1  = btor_forall_exp (g_btor, Y[1], ugte);
  or       = btor_and_exp (g_btor, forall0, forall1);
  expected = btor_forall_exp (g_btor, X, BTOR_INVERT_NODE (or));

  result = btor_normalize_quantifiers_node (g_btor, forall, 0);
  assert (result == expected);

  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, ugt);
  btor_release_exp (g_btor, exists0);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, exists1);
  btor_release_exp (g_btor, and);
  btor_release_exp (g_btor, forall);
  btor_release_exp (g_btor, X);
  btor_release_exp (g_btor, Y[0]);
  btor_release_exp (g_btor, Y[1]);
  btor_release_exp (g_btor, ulte);
  btor_release_exp (g_btor, forall0);
  btor_release_exp (g_btor, ugte);
  btor_release_exp (g_btor, forall1);
  btor_release_exp (g_btor, or);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}

static void
test_normquant_elim_ite (void)
{
  BtorNode *forall, *exists, *x, *y, *v0, *v1, *ult, *ite, *eqx;
  BtorNode *expected, *existsY, *forallY, *X, *Y[2], *Z, *ugte, *ultY;
  BtorNode *eqZX, *eqZv1, *eqZv0, *imp_if, *imp_else, *and0, *and1;
  BtorNode *result, *uf;

  v0     = btor_var_exp (g_btor, 32, "v0");
  v1     = btor_var_exp (g_btor, 32, "v1");
  x      = btor_param_exp (g_btor, 32, 0);
  y      = btor_param_exp (g_btor, 32, 0);
  ult    = btor_ult_exp (g_btor, x, y);
  exists = btor_exists_exp (g_btor, y, ult);
  ite    = btor_cond_exp (g_btor, exists, v0, v1);
  eqx    = btor_eq_exp (g_btor, x, ite);
  forall = btor_forall_exp (g_btor, x, eqx);

  result = btor_normalize_quantifiers_node (g_btor, forall, 0);
  assert (g_btor->ufs->count == 1);
  uf = g_btor->ufs->first->key;

  X    = btor_param_exp (g_btor, 32, 0);
  Y[0] = btor_param_exp (g_btor, 32, 0);
  Y[1] = btor_param_exp (g_btor, 32, 0);
  Z    = btor_apply_exps (g_btor, &X, 1, uf);

  eqZX     = btor_eq_exp (g_btor, X, Z);
  eqZv0    = btor_eq_exp (g_btor, Z, v0);
  eqZv1    = btor_eq_exp (g_btor, Z, v1);
  ultY     = btor_ult_exp (g_btor, X, Y[0]);
  ugte     = btor_ugte_exp (g_btor, X, Y[1]);
  existsY  = btor_exists_exp (g_btor, Y[0], ultY);
  forallY  = btor_forall_exp (g_btor, Y[1], ugte);
  imp_if   = btor_implies_exp (g_btor, forallY, eqZv0);
  imp_else = btor_implies_exp (g_btor, existsY, eqZv1);
  and0     = btor_and_exp (g_btor, imp_if, imp_else);
  and1     = btor_and_exp (g_btor, eqZX, and0);
  expected = btor_forall_exp (g_btor, X, and1);

  assert (result == expected);

  btor_release_exp (g_btor, v0);
  btor_release_exp (g_btor, v1);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, exists);
  btor_release_exp (g_btor, ite);
  btor_release_exp (g_btor, eqx);
  btor_release_exp (g_btor, forall);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, X);
  btor_release_exp (g_btor, Y[0]);
  btor_release_exp (g_btor, Y[1]);
  btor_release_exp (g_btor, Z);
  btor_release_exp (g_btor, eqZX);
  btor_release_exp (g_btor, eqZv0);
  btor_release_exp (g_btor, eqZv1);
  btor_release_exp (g_btor, ultY);
  btor_release_exp (g_btor, ugte);
  btor_release_exp (g_btor, existsY);
  btor_release_exp (g_btor, forallY);
  btor_release_exp (g_btor, imp_if);
  btor_release_exp (g_btor, imp_else);
  btor_release_exp (g_btor, and0);
  btor_release_exp (g_btor, and1);
  btor_release_exp (g_btor, expected);
}

static void
test_normquant_elim_top_ite (void)
{
  BtorNode *exists, *y, *v0, *v1, *v2, *ult, *ite, *eqv;
  BtorNode *expected, *existsY, *forallY, *Y[2], *Z, *ugte, *ultY;
  BtorNode *eqZv2, *eqZv1, *eqZv0, *imp_if, *imp_else, *and0;
  BtorNode *result;

  v0     = btor_var_exp (g_btor, 32, "v0");
  v1     = btor_var_exp (g_btor, 32, "v1");
  v2     = btor_var_exp (g_btor, 32, "v2");
  y      = btor_param_exp (g_btor, 32, 0);
  ult    = btor_ult_exp (g_btor, v2, y);
  exists = btor_exists_exp (g_btor, y, ult);
  ite    = btor_cond_exp (g_btor, exists, v0, v1);
  eqv    = btor_eq_exp (g_btor, v2, ite);

  result = btor_normalize_quantifiers_node (g_btor, eqv, 0);
  assert (g_btor->bv_vars->count == 4);

  Y[0] = btor_param_exp (g_btor, 32, 0);
  Y[1] = btor_param_exp (g_btor, 32, 0);
  Z    = g_btor->bv_vars->last->key;

  eqZv2    = btor_eq_exp (g_btor, v2, Z);
  eqZv0    = btor_eq_exp (g_btor, Z, v0);
  eqZv1    = btor_eq_exp (g_btor, Z, v1);
  ultY     = btor_ult_exp (g_btor, v2, Y[0]);
  ugte     = btor_ugte_exp (g_btor, v2, Y[1]);
  existsY  = btor_exists_exp (g_btor, Y[0], ultY);
  forallY  = btor_forall_exp (g_btor, Y[1], ugte);
  imp_if   = btor_implies_exp (g_btor, forallY, eqZv0);
  imp_else = btor_implies_exp (g_btor, existsY, eqZv1);
  and0     = btor_and_exp (g_btor, imp_if, imp_else);
  expected = btor_and_exp (g_btor, eqZv2, and0);

  assert (result == expected);

  btor_release_exp (g_btor, v0);
  btor_release_exp (g_btor, v1);
  btor_release_exp (g_btor, v2);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, ult);
  btor_release_exp (g_btor, exists);
  btor_release_exp (g_btor, ite);
  btor_release_exp (g_btor, eqv);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, Y[0]);
  btor_release_exp (g_btor, Y[1]);
  btor_release_exp (g_btor, eqZv2);
  btor_release_exp (g_btor, eqZv0);
  btor_release_exp (g_btor, eqZv1);
  btor_release_exp (g_btor, ultY);
  btor_release_exp (g_btor, ugte);
  btor_release_exp (g_btor, existsY);
  btor_release_exp (g_btor, forallY);
  btor_release_exp (g_btor, imp_if);
  btor_release_exp (g_btor, imp_else);
  btor_release_exp (g_btor, and0);
  btor_release_exp (g_btor, expected);
}

void
run_normquant_tests (int argc, char **argv)
{
  RUN_TEST (normquant_inv_exists);
  RUN_TEST (normquant_inv_forall);
  RUN_TEST (normquant_inv_exists_nested);
  RUN_TEST (normquant_inv_exists_nested2);
  RUN_TEST (normquant_inv_prefix);
  RUN_TEST (normquant_inv_and_exists);
  RUN_TEST (normquant_elim_ite);
  RUN_TEST (normquant_elim_top_ite);
}

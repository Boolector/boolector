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

  result = btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (exists));
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

  result = btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (forall));
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

  result = btor_normalize_quantifiers_node (g_btor, forall);
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

  result = btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (forall));
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

  result = btor_normalize_quantifiers_node (g_btor, BTOR_INVERT_NODE (forall1));
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

#if 0
static void
test_normquant_elim_ite (void)
{
  BtorNode *var[2];
  BtorNode *exists, *cond, *eqx[2], *ite, *x[3];
  BtorNode *expected, *eqy[4], *impl[2], *y[4], *and[2];
  BtorNode *result;

  var[0] = btor_var_exp (g_btor, 32, 0);
  var[1] = btor_var_exp (g_btor, 32, 0);

  x[0] = btor_param_exp (g_btor, 32, 0);
  x[1] = btor_param_exp (g_btor, 32, 0);
  x[2] = btor_param_exp (g_btor, 32, 0);
  cond = btor_forall_exp (g_btor, 
  eqx[0] = btor_eq_exp (g_btor, x[0], x[1]);
  ite = btor_cond_exp (g_btor, eqx[0], x[0], var[1]);
  eqx[1] = btor_ult_exp (g_btor, x[2], ite);
  exists = btor_exists_n_exp (g_btor, x, 3, eqx[1]);

  y[0] = btor_param_exp (g_btor, 32, 0);
  y[1] = btor_param_exp (g_btor, 32, 0);
  y[2] = btor_param_exp (g_btor, 32, 0);
  y[3] = btor_param_exp (g_btor, 32, 0);
  eqy[0] = btor_ult_exp (g_btor, y[2], y[3]);
  eqy[1] = btor_eq_exp (g_btor, y[0], y[1]); 
  eqy[2] = btor_eq_exp (g_btor, y[3], y[2]);
  eqy[3] = btor_eq_exp (g_btor, y[3], y[0]);
  impl[0] = btor_implies_exp (g_btor, eqy[1], eqy[2]);
  impl[1] = btor_implies_exp (g_btor, BTOR_INVERT_NODE (eqy[1]), eqy[3]);
  and[0] = btor_and_exp (g_btor, impl[0], impl[1]);
  and[1] = btor_and_exp (g_btor, and[0], eqy[0]); 
  expected = btor_exists_n_exp (g_btor, y, 4, and[1]);

  result = btor_normalize_quantifiers_node (g_btor, exists);
  btor_dump_smt2_node (g_btor, stdout, exists, -1);
  btor_dump_smt2_node (g_btor, stdout, result, -1);
  btor_dump_smt2_node (g_btor, stdout, expected, -1);
  assert (result == expected);

  btor_release_exp (g_btor, x[0]);
  btor_release_exp (g_btor, x[1]);
  btor_release_exp (g_btor, x[2]);
  btor_release_exp (g_btor, eqx[0]);
  btor_release_exp (g_btor, eqx[1]);
  btor_release_exp (g_btor, ite);
  btor_release_exp (g_btor, exists);

  btor_release_exp (g_btor, y[0]);
  btor_release_exp (g_btor, y[1]);
  btor_release_exp (g_btor, y[2]);
  btor_release_exp (g_btor, y[3]);
  btor_release_exp (g_btor, eqy[0]);
  btor_release_exp (g_btor, eqy[1]);
  btor_release_exp (g_btor, eqy[2]);
  btor_release_exp (g_btor, eqy[3]);
  btor_release_exp (g_btor, impl[0]);
  btor_release_exp (g_btor, impl[1]);
  btor_release_exp (g_btor, and[0]);
  btor_release_exp (g_btor, and[1]);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, result);
}
#endif

void
run_normquant_tests (int argc, char **argv)
{
  RUN_TEST (normquant_inv_exists);
  RUN_TEST (normquant_inv_forall);
  RUN_TEST (normquant_inv_exists_nested);
  RUN_TEST (normquant_inv_exists_nested2);
  RUN_TEST (normquant_inv_prefix);
  //  RUN_TEST (normquant_elim_ite);
}

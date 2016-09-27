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

/*
 * exp: \not (\exists x,y . x = y)
 * res: \forall x,y . x != y
 *
 */
static void
test_normquant_inv_exists (void)
{
  BtorNode *exists, *eqx, *eqy, *x[2], *y[2], *expected, *result;

  x[0]   = btor_param_exp (g_btor, 32, "x0");
  x[1]   = btor_param_exp (g_btor, 32, "x1");
  eqx    = btor_eq_exp (g_btor, x[0], x[1]);
  exists = btor_exists_n_exp (g_btor, x, 2, eqx);

  y[0]     = btor_param_exp (g_btor, 32, "y0");
  y[1]     = btor_param_exp (g_btor, 32, "y1");
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

/*
 * exp: \not (\forall x,y . x = y)
 * res: \exists x,y . x != y
 *
 */
static void
test_normquant_inv_forall (void)
{
  BtorNode *forall, *eqx, *eqy, *x[2], *y[2], *expected, *result;

  x[0]   = btor_param_exp (g_btor, 32, 0);
  x[1]   = btor_param_exp (g_btor, 32, 0);
  eqx    = btor_eq_exp (g_btor, x[0], x[1]);
  forall = BTOR_INVERT_NODE (btor_forall_n_exp (g_btor, x, 2, eqx));

  y[0]     = btor_param_exp (g_btor, 32, 0);
  y[1]     = btor_param_exp (g_btor, 32, 0);
  eqy      = btor_eq_exp (g_btor, y[0], y[1]);
  expected = btor_exists_n_exp (g_btor, y, 2, BTOR_INVERT_NODE (eqy));

  result = btor_normalize_quantifiers_node (g_btor, forall, 0);
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

/*
 * exp: \forall x . \not (\exists y . x = y)
 * res: \forall x,y . x != y
 *
 */
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

/*
 * exp: \not (\forall x . \not (\exists y . x = y))
 * res: \exists x, y . x = y
 *
 */
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
  forall = BTOR_INVERT_NODE (
      btor_forall_exp (g_btor, x[1], BTOR_INVERT_NODE (exists)));

  y[0]     = btor_param_exp (g_btor, 32, 0);
  y[1]     = btor_param_exp (g_btor, 32, 0);
  eqy      = btor_eq_exp (g_btor, y[0], y[1]);
  expected = btor_exists_n_exp (g_btor, y, 2, eqy);

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

/*
 * exp: \not (\forall x . \exists y . \forall z . x /\ y /\ z)
 * res: \exists x . \forall y . \exists z . \not (x /\ y /\ z)
 *
 */
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
  forall1 = BTOR_INVERT_NODE (btor_forall_exp (g_btor, x[2], exists));

  y[0]     = btor_param_exp (g_btor, 1, 0);
  y[1]     = btor_param_exp (g_btor, 1, 0);
  y[2]     = btor_param_exp (g_btor, 1, 0);
  andy     = btor_and_n_exp (g_btor, y, 3);
  exists0  = btor_exists_exp (g_btor, y[0], BTOR_INVERT_NODE (andy));
  forall   = btor_forall_exp (g_btor, y[1], exists0);
  expected = btor_exists_exp (g_btor, y[2], forall);

  result = btor_normalize_quantifiers_node (g_btor, forall1, 0);
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

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: \forall x . \not ((\exists y . x > y) /\ (\exists z . x < z))
 *
 * after fixing polarities:
 *
 * res: \forall x . \not ((\forall y . x > y) /\ (\forall z . x < z))
 *
 */
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
  ulte     = btor_ugt_exp (g_btor, X, Y[0]);
  forall0  = btor_forall_exp (g_btor, Y[0], ulte);
  ugte     = btor_ult_exp (g_btor, X, Y[1]);
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

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: \forall x . (\not ((\not \exists y . y > x) /\ x > 0))
 *
 * after eliminating negated quantifiers:
 *
 * res: \forall x . (\not ((\forall y . y <= x) /\ x > 0))
 *
 * after fixing ploarities:
 *
 * res: \forall x . (\not ((\exists y . y <= x) /\ x > 0))
 *
 */
static void
test_normquant_normalize_negated_quant (void)
{
  BtorNode *x, *y, *X, *Y;
  BtorNode *existsY, *YulteX, *Xugt0, *and2;
  BtorNode *forallx, *existsy, *yugtx, *xugt0, *zero, *and;
  BtorNode *result, *expected;

  x       = btor_param_exp (g_btor, 32, "x");
  y       = btor_param_exp (g_btor, 32, "y");
  zero    = btor_zero_exp (g_btor, 32);
  xugt0   = btor_ugt_exp (g_btor, x, zero);
  yugtx   = btor_ugt_exp (g_btor, y, x);
  existsy = btor_exists_exp (g_btor, y, yugtx);
  and     = btor_and_exp (g_btor, BTOR_INVERT_NODE (existsy), xugt0);
  forallx = btor_forall_exp (g_btor, x, BTOR_INVERT_NODE (and));

  result = btor_normalize_quantifiers_node (g_btor, forallx, 0);

  X        = btor_param_exp (g_btor, 32, "X");
  Y        = btor_param_exp (g_btor, 32, "Y");
  Xugt0    = btor_ugt_exp (g_btor, X, zero);
  YulteX   = btor_ulte_exp (g_btor, Y, X);
  existsY  = btor_exists_exp (g_btor, Y, YulteX);
  and2     = btor_and_exp (g_btor, existsY, Xugt0);
  expected = btor_forall_exp (g_btor, X, BTOR_INVERT_NODE (and2));

  assert (result == expected);

  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, X);
  btor_release_exp (g_btor, Y);
  btor_release_exp (g_btor, existsY);
  btor_release_exp (g_btor, YulteX);
  btor_release_exp (g_btor, Xugt0);
  btor_release_exp (g_btor, and2);
  btor_release_exp (g_btor, forallx);
  btor_release_exp (g_btor, existsy);
  btor_release_exp (g_btor, yugtx);
  btor_release_exp (g_btor, xugt0);
  btor_release_exp (g_btor, zero);
  btor_release_exp (g_btor, and);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, expected);
}

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: \forall x . x = (\exists y . x < y) ? v0 : v1
 *
 * after eliminating ITE:
 *
 * res_ite: \exists v0,v1 . \forall x. x = v_ite(x)
 *                     /\ \not ((\exists y . x < y) /\ v_ite(x) != v0)
 *                     /\ \not ((\forall y . x >= y) /\ v_ite(x) != v1)
 *
 * after fixing polarities:
 *
 * res: \exists v0,v1 . \forall x . x = v_ite(x)
 *		    /\ \not ((\forall y . x < y) /\ v_ite(x) != v0)
 *		    /\ \not ((\exists y . x >= y) /\ v_ite(x) != v1)
 *
 */
static void
test_normquant_elim_ite (void)
{
  BtorNode *forall, *exists, *x, *y, *v0, *v1, *ult, *ite, *eqx;
  BtorNode *expected, *existsY, *forallY, *X, *Y[2], *Z, *ugte, *ultY;
  BtorNode *eqZX, *eqZv1, *eqZv0, *imp_if, *imp_else, *and0, *and1;
  BtorNode *result, *uf, *V[2], *forallX;

  v0     = btor_var_exp (g_btor, 32, "v0");
  v1     = btor_var_exp (g_btor, 32, "v1");
  x      = btor_param_exp (g_btor, 32, "x");
  y      = btor_param_exp (g_btor, 32, "y");
  ult    = btor_ult_exp (g_btor, x, y);
  exists = btor_exists_exp (g_btor, y, ult);
  ite    = btor_cond_exp (g_btor, exists, v0, v1);
  eqx    = btor_eq_exp (g_btor, x, ite);
  forall = btor_forall_exp (g_btor, x, eqx);

  result = btor_normalize_quantifiers_node (g_btor, forall, 0);
  /* new UF introduced for ITE */
  assert (g_btor->ufs->count == 1);
  uf = g_btor->ufs->first->key;

  X    = btor_param_exp (g_btor, 32, 0);
  Y[0] = btor_param_exp (g_btor, 32, 0);
  Y[1] = btor_param_exp (g_btor, 32, 0);
  Z    = btor_apply_exps (g_btor, &X, 1, uf);

  V[0]     = btor_param_exp (g_btor, 32, "V0");
  V[1]     = btor_param_exp (g_btor, 32, "V1");
  eqZX     = btor_eq_exp (g_btor, X, Z);
  eqZv0    = btor_eq_exp (g_btor, Z, V[0]);
  eqZv1    = btor_eq_exp (g_btor, Z, V[1]);
  ultY     = btor_ult_exp (g_btor, X, Y[0]);
  ugte     = btor_ugte_exp (g_btor, X, Y[1]);
  forallY  = btor_forall_exp (g_btor, Y[0], ultY);
  existsY  = btor_exists_exp (g_btor, Y[1], ugte);
  imp_if   = btor_and_exp (g_btor, forallY, BTOR_INVERT_NODE (eqZv0));
  imp_else = btor_and_exp (g_btor, existsY, BTOR_INVERT_NODE (eqZv1));
  and0     = btor_and_exp (
      g_btor, BTOR_INVERT_NODE (imp_if), BTOR_INVERT_NODE (imp_else));
  and1     = btor_and_exp (g_btor, eqZX, and0);
  forallX  = btor_forall_exp (g_btor, X, and1);
  expected = btor_exists_n_exp (g_btor, V, 2, forallX);

  assert (result == expected);

  btor_release_exp (g_btor, v0);
  btor_release_exp (g_btor, v1);
  btor_release_exp (g_btor, V[0]);
  btor_release_exp (g_btor, V[1]);
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
  btor_release_exp (g_btor, forallX);
  btor_release_exp (g_btor, expected);
}

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: v2 = (\exists y . v2 < y) ? v0 : v1
 *
 * after eliminating ITE:
 *
 * res: \exists v0,v1,v2,v_ite .
 *	   v2 = v_ite
 *         /\ \not ((\exists y . v2 < y) /\ v_ite != v0)
 *         /\ \not ((\forall y . v2 >= y) /\ v_ite != v!)
 *
 * after fixing polarities:
 *
 * res: \exists v0,v1,v2,v_ite .
 *	   v2 = v_ite
 *	   /\ \not ((\forall y . v2 < y) /\ v_ite != v0)
 *	   /\ \not ((\exists y . v2 >= y) /\ v_ite != v1)
 */
#if 0
static void
test_normquant_elim_top_ite (void)
{
  BtorNode *exists, *y, *v0, *v1, *v2, *ult, *ite, *eqv;
  BtorNode *expected, *existsY, *forallY, *Y[2], *ugte, *ultY;
  BtorNode *eqZv2, *eqZv1, *eqZv0, *imp_if, *imp_else, *and0, *and1;
  BtorNode *result, *V[4];

  v0 = btor_var_exp (g_btor, 32, "v0");
  v1 = btor_var_exp (g_btor, 32, "v1");
  v2 = btor_var_exp (g_btor, 32, "v2");
  y = btor_param_exp (g_btor, 32, "y");
  ult = btor_ult_exp (g_btor, v2, y); 
  exists = btor_exists_exp (g_btor, y, ult);
  ite = btor_cond_exp (g_btor, exists, v0, v1); 
  eqv = btor_eq_exp (g_btor, v2, ite);

  result = btor_normalize_quantifiers_node (g_btor, eqv, 0);

  Y[0] = btor_param_exp (g_btor, 32, "Y0");
  Y[1] = btor_param_exp (g_btor, 32, "Y1");

  V[0] = btor_param_exp (g_btor, 32, "V0");
  V[1] = btor_param_exp (g_btor, 32, "V1");
  V[2] = btor_param_exp (g_btor, 32, "V2");
  V[3] = btor_param_exp (g_btor, 32, "V_ite");
  eqZv2 = btor_eq_exp (g_btor, V[2], V[3]);
  eqZv0 = btor_eq_exp (g_btor, V[3], V[0]); 
  eqZv1 = btor_eq_exp (g_btor, V[3], V[1]);
  ultY = btor_ult_exp (g_btor, V[2], Y[0]);
  ugte = btor_ugte_exp (g_btor, V[2], Y[1]);
  forallY = btor_forall_exp (g_btor, Y[0], ultY);
  existsY = btor_exists_exp (g_btor, Y[1], ugte);
  imp_if = btor_and_exp (g_btor, forallY, BTOR_INVERT_NODE (eqZv0));
  imp_else = btor_and_exp (g_btor, existsY, BTOR_INVERT_NODE (eqZv1));
  and0 = btor_and_exp (g_btor, BTOR_INVERT_NODE (imp_if),
		       BTOR_INVERT_NODE (imp_else));
  and1 = btor_and_exp (g_btor, eqZv2, and0); 
  expected = btor_exists_n_exp (g_btor, V, 4, and1);

  printf ("\n"); btor_dump_smt2_node (g_btor, stdout, result, -1);
  printf ("\n"); btor_dump_smt2_node (g_btor, stdout, expected, -1);
  assert (result == expected);

  btor_release_exp (g_btor, v0);
  btor_release_exp (g_btor, v1);
  btor_release_exp (g_btor, v2);
  btor_release_exp (g_btor, V[0]);
  btor_release_exp (g_btor, V[1]);
  btor_release_exp (g_btor, V[2]);
  btor_release_exp (g_btor, V[3]);
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
  btor_release_exp (g_btor, and1);
  btor_release_exp (g_btor, expected);
}
#endif

/*
 * test quantifier hashing
 *
 * Ex0-Ex1.x0=x1 == Ey0-Ey1.y0=y1
 * Ex0x1.x0=x1 == Ey0y1.y1==y0
 *
 *
 *
 *
 */

void
run_normquant_tests (int argc, char **argv)
{
  RUN_TEST (normquant_inv_exists);
  RUN_TEST (normquant_inv_forall);
  RUN_TEST (normquant_inv_exists_nested);
  RUN_TEST (normquant_inv_exists_nested2);
  RUN_TEST (normquant_inv_prefix);
  RUN_TEST (normquant_inv_and_exists);
  RUN_TEST (normquant_normalize_negated_quant);
  RUN_TEST (normquant_elim_ite);
  // FIXME (ma): this one is disabled for now since hashing of quantifier
  // expressions does not recognize result and expected to be the same
  //  RUN_TEST (normquant_elim_top_ite);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbeta.h"
#include "btorcore.h"
#include "btorexp.h"
#include "testexp.h"
#include "testrunner.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor       = NULL;
static int32_t g_index_bw = 32;
static int32_t g_elem_bw  = 16;
static BtorSortId g_elem_sort;
static BtorSortId g_index_sort;
static BtorSortId g_array_sort;

void
init_lambda_test (void)
{
  g_btor = btor_new ();
  if (g_rwreads) btor_opt_set (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  g_elem_sort  = btor_sort_bv (g_btor, g_elem_bw);
  g_index_sort = btor_sort_bv (g_btor, g_index_bw);
  g_array_sort = btor_sort_array (g_btor, g_index_sort, g_elem_sort);
}

void
finish_lambda_test (void)
{
  btor_sort_release (g_btor, g_elem_sort);
  btor_sort_release (g_btor, g_index_sort);
  btor_sort_release (g_btor, g_array_sort);
  btor_delete (g_btor);
}

void
init_lambda_tests (void)
{
}

static void
assert_parameterized (int32_t argc, ...)
{
  int32_t i;
  va_list ap;
  BtorNode *e;

  va_start (ap, argc);
  for (i = 0; i < argc; i++)
  {
    e = va_arg (ap, BtorNode *);
    assert (btor_node_real_addr (e)->parameterized);
  }
  va_end (ap);
}

static void
assert_not_parameterized (int32_t argc, ...)
{
  int32_t i;
  va_list ap;
  BtorNode *e;

  va_start (ap, argc);
  for (i = 0; i < argc; i++)
  {
    e = va_arg (ap, BtorNode *);
    assert (!btor_node_real_addr (e)->parameterized);
  }
  va_end (ap);
}

static BtorNode *
apply_and_reduce (Btor *btor, BtorNode *args[], int32_t argc, BtorNode *lambda)
{
  assert (btor);
  assert (argc >= 0);
  assert (argc < 1 || args);
  assert (lambda);

  int32_t i;
  BtorNode *result, *cur;
  BtorNodePtrStack unassign;
  BtorMemMgr *mm;

  mm = btor->mm;

  BTOR_INIT_STACK (mm, unassign);

  cur = lambda;
  for (i = 0; i < argc; i++)
  {
    assert (btor_node_is_regular (cur));
    assert (btor_node_is_lambda (cur));
    btor_beta_assign_param (btor, cur, args[i]);
    BTOR_PUSH_STACK (unassign, cur);
    cur = btor_node_real_addr (cur->e[1]);
  }

  result = btor_beta_reduce_full (btor, lambda, 0);

  while (!BTOR_EMPTY_STACK (unassign))
  {
    cur = BTOR_POP_STACK (unassign);
    btor_beta_unassign_params (btor, cur);
  }

  BTOR_RELEASE_STACK (unassign);

  return result;
}

/*---------------------------------------------------------------------------
 * constant lambda tests
 *---------------------------------------------------------------------------*/

static void
test_lambda_const_lambda_const (void)
{
  BtorNode *result;
  BtorNode *x, *c, *i, *lambda;

  init_lambda_test ();

  x      = btor_exp_param (g_btor, g_index_sort, "x");
  c      = btor_exp_bv_zero (g_btor, g_elem_sort);
  i      = btor_exp_var (g_btor, g_index_sort, "i");
  lambda = btor_exp_lambda (g_btor, x, c);

  /* (lambda x . 0) (i) */
  result = apply_and_reduce (g_btor, &i, 1, lambda);
  assert (result == c);
  assert_not_parameterized (1, result);
  btor_node_release (g_btor, result);

  /* (lambda x . 0) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == c);
  assert_parameterized (1, x);
  assert_not_parameterized (4, result, c, i, lambda);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, c);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_const_lambda_var (void)
{
  BtorNode *result;
  BtorNode *x, *a, *i, *lambda;

  init_lambda_test ();

  x      = btor_exp_param (g_btor, g_index_sort, "x");
  a      = btor_exp_var (g_btor, g_elem_sort, "a");
  i      = btor_exp_var (g_btor, g_index_sort, "i");
  lambda = btor_exp_lambda (g_btor, x, a);

  /* (lambda x . a) (i) */
  result = apply_and_reduce (g_btor, &i, 1, lambda);
  assert (result == a);
  assert_not_parameterized (1, result);
  btor_node_release (g_btor, result);

  /* (lambda x . a) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == a);
  assert_parameterized (1, x);
  assert_not_parameterized (4, result, lambda, i, a);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, i);
  finish_lambda_test ();
}

static void
test_lambda_const_lambda_param (void)
{
  BtorNode *result;
  BtorNode *x, *a, *lambda;

  init_lambda_test ();

  x      = btor_exp_param (g_btor, g_elem_sort, "x");
  a      = btor_exp_var (g_btor, g_elem_sort, "a");
  lambda = btor_exp_lambda (g_btor, x, x);

  /* (lambda x . x) (a) */
  result = apply_and_reduce (g_btor, &a, 1, lambda);
  assert (result == a);
  assert_not_parameterized (1, result);
  btor_node_release (g_btor, result);

  /* (lambda x . x) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == lambda);
  assert_parameterized (1, x);
  assert_not_parameterized (3, result, lambda, a);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_const_lambda_negated (void)
{
  BtorNode *result;
  BtorNode *a, *not_a, *x, *not_x, *lambda;

  init_lambda_test ();

  a      = btor_exp_var (g_btor, g_elem_sort, "a");
  not_a  = btor_exp_bv_not (g_btor, a);
  x      = btor_exp_param (g_btor, g_elem_sort, "x");
  not_x  = btor_exp_bv_not (g_btor, x);
  lambda = btor_exp_lambda (g_btor, x, not_x);

  /* (lambda x . not (x)) (not (a)) */
  result = apply_and_reduce (g_btor, &not_a, 1, lambda);
  assert (result == a);
  assert_not_parameterized (1, result);
  btor_node_release (g_btor, result);

  /* (lambda x . not (x)) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == lambda);
  assert_parameterized (2, x, not_x);
  assert_not_parameterized (4, result, lambda, not_a, a);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, not_x);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, not_a);
  btor_node_release (g_btor, a);
  finish_lambda_test ();
}

/* (lambda x . a) () */
static void
test_lambda_unassigned_param (void)
{
  BtorNode *result;
  BtorNode *x, *a, *lambda;

  init_lambda_test ();

  x      = btor_exp_param (g_btor, g_index_sort, "x");
  a      = btor_exp_var (g_btor, g_elem_sort, "a");
  lambda = btor_exp_lambda (g_btor, x, a);
  result = apply_and_reduce (g_btor, 0, 0, lambda);

  assert (result == a);
  assert_parameterized (1, x);
  assert_not_parameterized (3, result, lambda, a);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * unary expression tests
 *---------------------------------------------------------------------------*/

static void
unary_param_exp_test (BtorNode *(*func) (Btor *, BtorNode *) )
{
  BtorNode *result;
  BtorNode *var, *expected, *param, *param_exp, *lambda;
  BtorSortId lambda_index_sort;

  init_lambda_test ();

  lambda_index_sort = g_elem_sort;
  var               = btor_exp_var (g_btor, g_elem_sort, "v1");
  expected          = func (g_btor, var);
  param             = btor_exp_param (g_btor, lambda_index_sort, "p1");
  param_exp         = func (g_btor, param);
  lambda            = btor_exp_lambda (g_btor, param, param_exp);
  result            = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, param, param_exp);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, param);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, var);
  finish_lambda_test ();
}

static void
test_lambda_param_not (void)
{
  unary_param_exp_test (btor_exp_bv_not);
}

static void
test_lambda_param_neg (void)
{
  unary_param_exp_test (btor_exp_bv_neg);
}

static void
test_lambda_param_redor (void)
{
  unary_param_exp_test (btor_exp_bv_redor);
}

static void
test_lambda_param_redxor (void)
{
  unary_param_exp_test (btor_exp_bv_redxor);
}

static void
test_lambda_param_redand (void)
{
  unary_param_exp_test (btor_exp_bv_redand);
}

static void
test_lambda_param_slice (void)
{
  BtorNode *result;
  BtorNode *var, *param, *expected, *slice, *lambda;
  int32_t lower, upper;

  init_lambda_test ();

  lower = g_elem_bw / 2 + 1;
  upper = g_elem_bw - 1;

  var      = btor_exp_var (g_btor, g_elem_sort, "v1");
  param    = btor_exp_param (g_btor, g_elem_sort, "p1");
  expected = btor_exp_bv_slice (g_btor, var, upper, lower);
  slice    = btor_exp_bv_slice (g_btor, param, upper, lower);
  lambda   = btor_exp_lambda (g_btor, param, slice);
  result   = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, param, slice);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, slice);
  btor_node_release (g_btor, param);
  btor_node_release (g_btor, var);
  finish_lambda_test ();
}

static void
param_extension_test (BtorNode *(*func) (Btor *, BtorNode *, uint32_t))
{
  BtorNode *result;
  BtorNode *var, *param, *expected, *param_exp, *lambda;
  BtorSortId lower_sort, upper_sort;
  int32_t lower, upper;

  init_lambda_test ();

  lower      = g_elem_bw / 2 + 1;
  upper      = g_elem_bw - 1;
  lower_sort = btor_sort_bv (g_btor, lower);
  upper_sort = btor_sort_bv (g_btor, upper);

  var       = btor_exp_var (g_btor, lower_sort, "v1");
  param     = btor_exp_param (g_btor, lower_sort, "p1");
  expected  = func (g_btor, var, upper_sort);
  param_exp = func (g_btor, param, upper_sort);
  lambda    = btor_exp_lambda (g_btor, param, param_exp);
  result    = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, param, param_exp);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_sort_release (g_btor, lower_sort);
  btor_sort_release (g_btor, upper_sort);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, param);
  btor_node_release (g_btor, var);
  finish_lambda_test ();
}

static void
test_lambda_param_uext (void)
{
  param_extension_test (btor_exp_bv_uext);
}

static void
test_lambda_param_sext (void)
{
  param_extension_test (btor_exp_bv_sext);
}

/*---------------------------------------------------------------------------
 * binary expression tests
 *---------------------------------------------------------------------------*/

/* (lambda x . bin_exp (x, v2)) (v1) or (lambda x . bin_exp (v1, x)) (v2) */
static void
binary_param_exp_test (int32_t param_pos,
                       BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  assert (param_pos == 0 || param_pos == 1);

  BtorNode *result;
  BtorNode *param_exp, *v1, *v2, *expected, *x;
  BtorSortId v1_sort, v2_sort, x_sort;
  int32_t x_bw, v1_bw, v2_bw;

  init_lambda_test ();

  x_bw  = g_elem_bw;
  v1_bw = g_elem_bw;
  v2_bw = g_elem_bw;

  if (func == btor_exp_implies || func == btor_exp_iff)
  {
    v1_bw = 1;
    v2_bw = 1;
  }
  else if (func == btor_exp_bv_sll || func == btor_exp_bv_srl
           || func == btor_exp_bv_sra || func == btor_exp_bv_rol
           || func == btor_exp_bv_ror)
  {
    v2_bw = btor_util_log_2 (v1_bw);
  }

  x_bw = (param_pos == 0) ? v1_bw : v2_bw;

  v1_sort = btor_sort_bv (g_btor, v1_bw);
  v2_sort = btor_sort_bv (g_btor, v2_bw);
  x_sort  = btor_sort_bv (g_btor, x_bw);

  v1       = btor_exp_var (g_btor, v1_sort, "v1");
  v2       = btor_exp_var (g_btor, v2_sort, "v2");
  expected = func (g_btor, v1, v2);
  x        = btor_exp_param (g_btor, x_sort, "x");

  if (param_pos == 0)
    param_exp = func (g_btor, x, v2);
  else
    param_exp = func (g_btor, v1, x);

  BtorNode *lambda = btor_exp_lambda (g_btor, x, param_exp);

  if (param_pos == 0)
    result = apply_and_reduce (g_btor, &v1, 1, lambda);
  else
    result = apply_and_reduce (g_btor, &v2, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (5, v1, v2, expected, lambda, result);

  btor_sort_release (g_btor, v1_sort);
  btor_sort_release (g_btor, v2_sort);
  btor_sort_release (g_btor, x_sort);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, v2);
  btor_node_release (g_btor, v1);
  finish_lambda_test ();
}

static void
test_lambda_param_implies (void)
{
  binary_param_exp_test (0, btor_exp_implies);
  binary_param_exp_test (1, btor_exp_implies);
}

static void
test_lambda_param_iff (void)
{
  binary_param_exp_test (0, btor_exp_iff);
  binary_param_exp_test (1, btor_exp_iff);
}

static void
test_lambda_param_xor (void)
{
  binary_param_exp_test (0, btor_exp_bv_xor);
  binary_param_exp_test (1, btor_exp_bv_xor);
}

static void
test_lambda_param_xnor (void)
{
  binary_param_exp_test (0, btor_exp_bv_xnor);
  binary_param_exp_test (1, btor_exp_bv_xnor);
}

static void
test_lambda_param_and (void)
{
  binary_param_exp_test (0, btor_exp_bv_and);
  binary_param_exp_test (1, btor_exp_bv_and);
}

static void
test_lambda_param_nand (void)
{
  binary_param_exp_test (0, btor_exp_bv_nand);
  binary_param_exp_test (1, btor_exp_bv_nand);
}

static void
test_lambda_param_or (void)
{
  binary_param_exp_test (0, btor_exp_bv_or);
  binary_param_exp_test (1, btor_exp_bv_or);
}

static void
test_lambda_param_nor (void)
{
  binary_param_exp_test (0, btor_exp_bv_nor);
  binary_param_exp_test (1, btor_exp_bv_nor);
}

static void
test_lambda_param_eq (void)
{
  binary_param_exp_test (0, btor_exp_eq);
  binary_param_exp_test (1, btor_exp_eq);
}

static void
test_lambda_param_ne (void)
{
  binary_param_exp_test (0, btor_exp_ne);
  binary_param_exp_test (1, btor_exp_ne);
}

static void
test_lambda_param_add (void)
{
  binary_param_exp_test (0, btor_exp_bv_add);
  binary_param_exp_test (1, btor_exp_bv_add);
}

static void
test_lambda_param_uaddo (void)
{
  binary_param_exp_test (0, btor_exp_bv_uaddo);
  binary_param_exp_test (1, btor_exp_bv_uaddo);
}

static void
test_lambda_param_saddo (void)
{
  binary_param_exp_test (0, btor_exp_bv_saddo);
  binary_param_exp_test (1, btor_exp_bv_saddo);
}

static void
test_lambda_param_mul (void)
{
  binary_param_exp_test (0, btor_exp_bv_mul);
  binary_param_exp_test (1, btor_exp_bv_mul);
}

static void
test_lambda_param_umulo (void)
{
  binary_param_exp_test (0, btor_exp_bv_umulo);
  binary_param_exp_test (1, btor_exp_bv_umulo);
}

static void
test_lambda_param_smulo (void)
{
  binary_param_exp_test (0, btor_exp_bv_smulo);
  binary_param_exp_test (1, btor_exp_bv_smulo);
}

static void
test_lambda_param_ult (void)
{
  binary_param_exp_test (0, btor_exp_bv_ult);
  binary_param_exp_test (1, btor_exp_bv_ult);
}

static void
test_lambda_param_slt (void)
{
  binary_param_exp_test (0, btor_exp_bv_slt);
  binary_param_exp_test (1, btor_exp_bv_slt);
}

static void
test_lambda_param_ulte (void)
{
  binary_param_exp_test (0, btor_exp_bv_ulte);
  binary_param_exp_test (1, btor_exp_bv_ulte);
}

static void
test_lambda_param_slte (void)
{
  binary_param_exp_test (0, btor_exp_bv_slte);
  binary_param_exp_test (1, btor_exp_bv_slte);
}

static void
test_lambda_param_ugt (void)
{
  binary_param_exp_test (0, btor_exp_bv_ugt);
  binary_param_exp_test (1, btor_exp_bv_ugt);
}

static void
test_lambda_param_sgt (void)
{
  binary_param_exp_test (0, btor_exp_bv_sgt);
  binary_param_exp_test (1, btor_exp_bv_sgt);
}

static void
test_lambda_param_ugte (void)
{
  binary_param_exp_test (0, btor_exp_bv_ugte);
  binary_param_exp_test (1, btor_exp_bv_ugte);
}

static void
test_lambda_param_sgte (void)
{
  binary_param_exp_test (0, btor_exp_bv_sgte);
  binary_param_exp_test (1, btor_exp_bv_sgte);
}

static void
test_lambda_param_sll (void)
{
  binary_param_exp_test (0, btor_exp_bv_sll);
  binary_param_exp_test (1, btor_exp_bv_sll);
}

static void
test_lambda_param_srl (void)
{
  binary_param_exp_test (0, btor_exp_bv_srl);
  binary_param_exp_test (1, btor_exp_bv_srl);
}

static void
test_lambda_param_sra (void)
{
  binary_param_exp_test (0, btor_exp_bv_sra);
  binary_param_exp_test (1, btor_exp_bv_sra);
}

static void
test_lambda_param_rol (void)
{
  binary_param_exp_test (0, btor_exp_bv_rol);
  binary_param_exp_test (1, btor_exp_bv_rol);
}

static void
test_lambda_param_ror (void)
{
  binary_param_exp_test (0, btor_exp_bv_ror);
  binary_param_exp_test (1, btor_exp_bv_ror);
}

static void
test_lambda_param_sub (void)
{
  binary_param_exp_test (0, btor_exp_bv_sub);
  binary_param_exp_test (1, btor_exp_bv_sub);
}

static void
test_lambda_param_usubo (void)
{
  binary_param_exp_test (0, btor_exp_bv_usubo);
  binary_param_exp_test (1, btor_exp_bv_usubo);
}

static void
test_lambda_param_ssubo (void)
{
  binary_param_exp_test (0, btor_exp_bv_ssubo);
  binary_param_exp_test (1, btor_exp_bv_ssubo);
}

static void
test_lambda_param_udiv (void)
{
  binary_param_exp_test (0, btor_exp_bv_udiv);
  binary_param_exp_test (1, btor_exp_bv_udiv);
}

static void
test_lambda_param_sdiv (void)
{
  binary_param_exp_test (0, btor_exp_bv_sdiv);
  binary_param_exp_test (1, btor_exp_bv_sdiv);
}

static void
test_lambda_param_sdivo (void)
{
  binary_param_exp_test (0, btor_exp_bv_sdivo);
  binary_param_exp_test (1, btor_exp_bv_sdivo);
}

static void
test_lambda_param_urem (void)
{
  binary_param_exp_test (0, btor_exp_bv_urem);
  binary_param_exp_test (1, btor_exp_bv_urem);
}

static void
test_lambda_param_srem (void)
{
  binary_param_exp_test (0, btor_exp_bv_srem);
  binary_param_exp_test (1, btor_exp_bv_srem);
}

static void
test_lambda_param_smod (void)
{
  binary_param_exp_test (0, btor_exp_bv_smod);
  binary_param_exp_test (1, btor_exp_bv_smod);
}

static void
test_lambda_param_concat (void)
{
  binary_param_exp_test (0, btor_exp_bv_concat);
  binary_param_exp_test (1, btor_exp_bv_concat);
}

/* (lambda x . read(a, x)) (i) */
static void
test_lambda_param_read (void)
{
  BtorNode *result;
  BtorNode *x, *i, *a, *expected, *read, *lambda;

  init_lambda_test ();

  x        = btor_exp_param (g_btor, g_index_sort, "x");
  i        = btor_exp_var (g_btor, g_index_sort, "i");
  a        = btor_exp_array (g_btor, g_array_sort, "a");
  expected = btor_exp_read (g_btor, a, i);
  read     = btor_exp_read (g_btor, a, x);
  lambda   = btor_exp_lambda (g_btor, x, read);
  result   = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, read);
  assert_not_parameterized (5, result, lambda, expected, a, i);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, read);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * ternary expression tests
 *---------------------------------------------------------------------------*/

/* (lambda x . write (a, i, x)) (e) */
static void
test_lambda_param_write1 (void)
{
  BtorNode *result;
  BtorNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  init_lambda_test ();

  i         = btor_exp_var (g_btor, g_index_sort, "i");
  e         = btor_exp_var (g_btor, g_elem_sort, "e");
  a         = btor_exp_array (g_btor, g_array_sort, "a");
  expected  = btor_exp_lambda_write (g_btor, a, i, e);
  x         = btor_exp_param (g_btor, g_elem_sort, "x");
  param_exp = btor_exp_lambda_write (g_btor, a, i, x);
  lambda    = btor_exp_lambda (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &e, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, a, e, i);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, e);
  btor_node_release (g_btor, i);
  finish_lambda_test ();
}

/* (lambda x . write (a, x, e)) (i) */
static void
test_lambda_param_write2 (void)
{
  BtorNode *result;
  BtorNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  init_lambda_test ();

  i         = btor_exp_var (g_btor, g_index_sort, "i");
  e         = btor_exp_var (g_btor, g_elem_sort, "e");
  a         = btor_exp_array (g_btor, g_array_sort, "a");
  expected  = btor_exp_lambda_write (g_btor, a, i, e);
  x         = btor_exp_param (g_btor, g_index_sort, "p");
  param_exp = btor_exp_lambda_write (g_btor, a, x, e);
  lambda    = btor_exp_lambda (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, a, e, i);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, e);
  btor_node_release (g_btor, i);
  finish_lambda_test ();
}

/* (lambda x . x ? v2 : v3) (v1) */
static void
test_lambda_param_bcond1 (void)
{
  BtorNode *result;
  BtorNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BtorSortId sort;

  init_lambda_test ();

  sort      = btor_sort_bv (g_btor, 1);
  v1        = btor_exp_var (g_btor, sort, "v1");
  x         = btor_exp_param (g_btor, sort, "x");
  v2        = btor_exp_var (g_btor, g_elem_sort, "v2");
  v3        = btor_exp_var (g_btor, g_elem_sort, "v3");
  expected  = btor_exp_cond (g_btor, v1, v2, v3);
  param_exp = btor_exp_cond (g_btor, x, v2, v3);
  lambda    = btor_exp_lambda (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &v1, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, v3);
  btor_node_release (g_btor, v2);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, v1);
  finish_lambda_test ();
}

/* (lambda x . v1 ? x : v3) (v2) */
static void
test_lambda_param_bcond2 (void)
{
  BtorNode *result;
  BtorNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BtorSortId sort;

  init_lambda_test ();

  sort      = btor_sort_bv (g_btor, 1);
  v1        = btor_exp_var (g_btor, sort, "v1");
  x         = btor_exp_param (g_btor, g_elem_sort, "x");
  v2        = btor_exp_var (g_btor, g_elem_sort, "v2");
  v3        = btor_exp_var (g_btor, g_elem_sort, "v3");
  expected  = btor_exp_cond (g_btor, v1, v2, v3);
  param_exp = btor_exp_cond (g_btor, v1, x, v3);
  lambda    = btor_exp_lambda (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &v2, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, v3);
  btor_node_release (g_btor, v2);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, v1);
  finish_lambda_test ();
}

/* (lambda x . v1 ? v2 : x) (v3) */
static void
test_lambda_param_bcond3 (void)
{
  BtorNode *result;
  BtorNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BtorSortId sort;

  init_lambda_test ();

  sort      = btor_sort_bv (g_btor, 1);
  v1        = btor_exp_var (g_btor, sort, "v1");
  x         = btor_exp_param (g_btor, g_elem_sort, "x");
  v2        = btor_exp_var (g_btor, g_elem_sort, "v2");
  v3        = btor_exp_var (g_btor, g_elem_sort, "v3");
  expected  = btor_exp_cond (g_btor, v1, v2, v3);
  param_exp = btor_exp_cond (g_btor, v1, v2, x);
  lambda    = btor_exp_lambda (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &v3, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, v3);
  btor_node_release (g_btor, v2);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, v1);
  finish_lambda_test ();
}

/* NOTE: right now, we have to use a read on the array condition as lambdas
 * return bit-vectors only. */
static void
test_lambda_param_acond (void)
{
  BtorNode *result;
  BtorNode *var, *index, *e_if, *e_else, *expected_acond, *expected,
      *expected_cond;
  BtorNode *param, *param_cond, *param_acond, *param_exp, *lambda;

  init_lambda_test ();

  var            = btor_exp_var (g_btor, g_index_sort, "v1");
  index          = btor_exp_var (g_btor, g_index_sort, "i");
  expected_cond  = btor_exp_eq (g_btor, var, index);
  e_if           = btor_exp_array (g_btor, g_array_sort, "a1");
  e_else         = btor_exp_array (g_btor, g_array_sort, "a2");
  expected_acond = btor_exp_cond (g_btor, expected_cond, e_if, e_else);
  expected       = btor_exp_read (g_btor, expected_acond, var);

  param       = btor_exp_param (g_btor, g_index_sort, "p");
  param_cond  = btor_exp_eq (g_btor, param, index);
  param_acond = btor_exp_cond (g_btor, param_cond, e_if, e_else);
  param_exp   = btor_exp_read (g_btor, param_acond, param);
  lambda      = btor_exp_lambda (g_btor, param, param_exp);
  result      = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (4, param, param_cond, param_acond, param_exp);
  assert_not_parameterized (4, result, lambda, expected, expected_acond);
  assert_not_parameterized (5, e_else, e_if, expected_cond, index, var);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, param_exp);
  btor_node_release (g_btor, param_acond);
  btor_node_release (g_btor, param_cond);
  btor_node_release (g_btor, param);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, expected_acond);
  btor_node_release (g_btor, e_else);
  btor_node_release (g_btor, e_if);
  btor_node_release (g_btor, expected_cond);
  btor_node_release (g_btor, index);
  btor_node_release (g_btor, var);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

/* (lambda x . read ((lambda y . y), x)) */
static void
test_lambda_bounded_reduce1 (void)
{
  BtorNode *result;
  BtorNode *x, *y, *l2, *r, *l1, *v, *expected;

  init_lambda_test ();

  x  = btor_exp_param (g_btor, g_index_sort, "x");
  y  = btor_exp_param (g_btor, g_index_sort, "y");
  l2 = btor_exp_lambda (g_btor, y, y);
  r  = btor_exp_apply_n (g_btor, l2, &x, 1);
  l1 = btor_exp_lambda (g_btor, x, r);
  v  = btor_exp_var (g_btor, g_index_sort, "v");

  expected = btor_exp_apply_n (g_btor, l2, &v, 1);

  /* bound 2: stop at second lambda */
  btor_beta_assign_param (g_btor, l1, v);
  result = btor_beta_reduce_bounded (g_btor, l1, 2);
  btor_beta_unassign_params (g_btor, l1);

  assert (result == expected);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, expected);

  /* bound 3: stop at third lambda */
  btor_beta_assign_param (g_btor, l1, v);
  result = btor_beta_reduce_bounded (g_btor, l1, 3);
  btor_beta_unassign_params (g_btor, l1);

  assert (result == v);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, v);
  btor_node_release (g_btor, l1);
  btor_node_release (g_btor, r);
  btor_node_release (g_btor, l2);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_bounded_reduce2 (void)
{
  BtorNode *result;
  BtorNode *x, *i, *eq, *l, *j, *expected;

  init_lambda_test ();

  x        = btor_exp_param (g_btor, g_index_sort, "x");
  i        = btor_exp_var (g_btor, g_index_sort, "i");
  eq       = btor_exp_eq (g_btor, x, i);
  l        = btor_exp_lambda (g_btor, x, eq);
  j        = btor_exp_var (g_btor, g_index_sort, "j");
  expected = btor_exp_eq (g_btor, i, j);

  btor_beta_assign_param (g_btor, l, j);
  result = btor_beta_reduce_bounded (g_btor, l, 0);
  assert (result == expected);
  btor_node_release (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l, 1);
  assert (result == l);
  btor_node_release (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, eq, 1);
  assert (result == expected);
  btor_node_release (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l, 2);
  assert (result == expected);
  btor_beta_unassign_params (g_btor, l);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, j);
  btor_node_release (g_btor, l);
  btor_node_release (g_btor, eq);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_bounded_reduce3 (void)
{
  BtorNode *result;
  BtorNode *x, *y, *l1, *a, *l2, *i, *expected;

  init_lambda_test ();

  x        = btor_exp_param (g_btor, g_index_sort, "x");
  y        = btor_exp_param (g_btor, g_index_sort, "y");
  l1       = btor_exp_lambda (g_btor, x, x);
  a        = btor_exp_apply_n (g_btor, l1, &y, 1);
  l2       = btor_exp_lambda (g_btor, y, a);
  i        = btor_exp_var (g_btor, g_index_sort, "i");
  expected = btor_exp_apply_n (g_btor, l1, &i, 1);

  btor_beta_assign_param (g_btor, l2, i);
  result = btor_beta_reduce_bounded (g_btor, l2, 1);
  assert (result == l2);
  btor_node_release (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l2, 2);
  assert (result == expected);
  btor_node_release (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l2, 3);
  assert (result == i);
  btor_beta_unassign_params (g_btor, l2);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, l2);
  btor_node_release (g_btor, l1);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, x);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

static void
test_lambda_reduce_write1 (void)
{
  BtorNode *result;
  BtorNode *a, *i, *e, *param, *read, *eq, *cond, *lambda;

  init_lambda_test ();
  a      = btor_exp_array (g_btor, g_array_sort, "a");
  i      = btor_exp_var (g_btor, g_index_sort, "i");
  e      = btor_exp_var (g_btor, g_elem_sort, "e");
  param  = btor_exp_param (g_btor, g_index_sort, "p");
  read   = btor_exp_read (g_btor, a, param);
  eq     = btor_exp_eq (g_btor, param, i);
  cond   = btor_exp_cond (g_btor, eq, e, read);
  lambda = btor_exp_lambda (g_btor, param, cond);
  result = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == e);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, cond);
  btor_node_release (g_btor, eq);
  btor_node_release (g_btor, read);
  btor_node_release (g_btor, param);
  btor_node_release (g_btor, e);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, a);
  finish_lambda_test ();
}

static void
test_lambda_reduce_write2 (void)
{
  BtorNode *result;
  BtorNode *a, *i, *e, *param, *read, *expected, *eq, *cond, *lambda;

  init_lambda_test ();

  a        = btor_exp_array (g_btor, g_array_sort, "a");
  i        = btor_exp_var (g_btor, g_index_sort, "i");
  e        = btor_exp_var (g_btor, g_elem_sort, "e");
  param    = btor_exp_param (g_btor, g_index_sort, "p");
  read     = btor_exp_read (g_btor, a, param);
  expected = btor_exp_read (g_btor, a, i);
  eq       = btor_exp_ne (g_btor, param, i);
  cond     = btor_exp_cond (g_btor, eq, e, read);
  lambda   = btor_exp_lambda (g_btor, param, cond);
  result   = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == expected);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda);
  btor_node_release (g_btor, cond);
  btor_node_release (g_btor, eq);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, read);
  btor_node_release (g_btor, param);
  btor_node_release (g_btor, e);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, a);
  finish_lambda_test ();
}

static void
test_lambda_reduce_nested_writes (void)
{
  BtorNode *result;
  BtorNode *i, *a, *e2, *w2, *e1, *w1;

  init_lambda_test ();

  i = btor_exp_var (g_btor, g_index_sort, "i");
  /* w2 = write (a, i, e2) */
  a  = btor_exp_array (g_btor, g_array_sort, "a");
  e2 = btor_exp_var (g_btor, g_elem_sort, "e2");
  w2 = btor_exp_lambda_write (g_btor, a, i, e2);
  /* w1 = write (w1, not i, e1) */
  e1     = btor_exp_var (g_btor, g_elem_sort, "e1");
  w1     = btor_exp_lambda_write (g_btor, w2, btor_node_invert (i), e1);
  result = apply_and_reduce (g_btor, &i, 1, w1);

  assert (result == e2);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, w1);
  btor_node_release (g_btor, e1);
  btor_node_release (g_btor, w2);
  btor_node_release (g_btor, e2);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, i);
  finish_lambda_test ();
}

/* (lambda x . (lambda y . (x + y))) (a b) */
static void
test_lambda_reduce_nested_lambdas_add1 (void)
{
  BtorNode *result;
  BtorNode *a, *b, *expected, *x, *y, *add, *fun;

  init_lambda_test ();

  a                   = btor_exp_var (g_btor, g_elem_sort, "a");
  b                   = btor_exp_var (g_btor, g_elem_sort, "b");
  BtorNode *args[2]   = {a, b};
  expected            = btor_exp_bv_add (g_btor, a, b);
  x                   = btor_exp_param (g_btor, g_elem_sort, "x");
  y                   = btor_exp_param (g_btor, g_elem_sort, "y");
  BtorNode *params[2] = {x, y};
  add                 = btor_exp_bv_add (g_btor, x, y);
  fun                 = btor_exp_fun (g_btor, params, 2, add);

  result = apply_and_reduce (g_btor, args, 2, fun);
  assert (result == expected);
  btor_node_release (g_btor, result);

  BtorNode *apply = btor_exp_apply_n (g_btor, fun, args, 2);
  result          = btor_beta_reduce_full (g_btor, apply, 0);
  assert (result == expected);

  btor_node_release (g_btor, apply);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, fun);
  btor_node_release (g_btor, add);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, b);
  btor_node_release (g_btor, a);
  finish_lambda_test ();
}

/* (lambda x . (x + read(lambda y . y, b))) (a) */
static void
test_lambda_reduce_nested_lambdas_add2 (void)
{
  BtorNode *result;
  BtorNode *a, *b, *expected, *x, *y, *lambda1, *lambda2, *app, *add;
  BtorSortId lambda_index_sort;

  init_lambda_test ();

  lambda_index_sort = g_elem_sort;
  a                 = btor_exp_var (g_btor, g_elem_sort, "a");
  b                 = btor_exp_var (g_btor, g_elem_sort, "b");
  expected          = btor_exp_bv_add (g_btor, a, b);
  x                 = btor_exp_param (g_btor, lambda_index_sort, "x");
  y                 = btor_exp_param (g_btor, lambda_index_sort, "y");
  lambda2           = btor_exp_lambda (g_btor, y, y);
  app               = btor_exp_apply_n (g_btor, lambda2, &b, 1);
  add               = btor_exp_bv_add (g_btor, x, app);
  lambda1           = btor_exp_lambda (g_btor, x, add);
  result            = apply_and_reduce (g_btor, &a, 1, lambda1);

  assert (result == expected);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, lambda1);
  btor_node_release (g_btor, add);
  btor_node_release (g_btor, app);
  btor_node_release (g_btor, lambda2);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, b);
  btor_node_release (g_btor, a);
  finish_lambda_test ();
}

/* (lambda x . not (read (lambda y . y, x + var))) (a) */
static void
test_lambda_reduce_nested_lambdas_read (void)
{
  BtorNode *result;
  BtorNode *a, *var, *y, *lambda1, *lambda2, *x, *add, *app, *napp;
  BtorNode *expected, *expected_add;

  init_lambda_test ();

  var     = btor_exp_var (g_btor, g_elem_sort, "var");
  y       = btor_exp_param (g_btor, g_elem_sort, "y");
  lambda2 = btor_exp_lambda (g_btor, y, y);
  x       = btor_exp_param (g_btor, g_elem_sort, "x");
  add     = btor_exp_bv_add (g_btor, x, var);
  app     = btor_exp_apply_n (g_btor, lambda2, &add, 1);
  napp    = btor_exp_bv_not (g_btor, app);
  lambda1 = btor_exp_lambda (g_btor, x, napp);
  a       = btor_exp_var (g_btor, g_elem_sort, "a");
  /* exptected not (a + var) */
  expected_add = btor_exp_bv_add (g_btor, a, var);
  expected     = btor_exp_bv_not (g_btor, expected_add);
  result       = apply_and_reduce (g_btor, &a, 1, lambda1);

  assert (result == expected);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, expected);
  btor_node_release (g_btor, expected_add);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, lambda1);
  btor_node_release (g_btor, napp);
  btor_node_release (g_btor, app);
  btor_node_release (g_btor, add);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, lambda2);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, var);
  finish_lambda_test ();
}

/* (lambda x1 . (lambda x2 . ... (lambda x1000 . var))) (i1 ... i1000) */
static void
test_lambda_reduce_nested_lambdas_const_n1000 (void)
{
  BtorNode *result;
  BtorNode **params, **indices, *var, *fun;
  int32_t i, nesting_lvl;
  size_t size;

  init_lambda_test ();

  nesting_lvl = 1000;
  size        = nesting_lvl * sizeof (BtorNode *);
  var         = btor_exp_var (g_btor, g_elem_sort, 0);

  params  = btor_mem_malloc (g_btor->mm, size);
  indices = btor_mem_malloc (g_btor->mm, size);

  for (i = nesting_lvl - 1; i >= 0; i--)
  {
    indices[i] = btor_exp_var (g_btor, g_index_sort, 0);
    params[i]  = btor_exp_param (g_btor, g_index_sort, 0);
  }
  fun = btor_exp_fun (g_btor, params, nesting_lvl, var);

  result = apply_and_reduce (g_btor, indices, nesting_lvl, fun);
  assert (result == var);
  btor_node_release (g_btor, result);

  BtorNode *apply = btor_exp_apply_n (g_btor, fun, indices, nesting_lvl);
  result          = btor_beta_reduce_full (g_btor, apply, 0);
  assert (result == var);

  for (i = 0; i < nesting_lvl; i++)
  {
    btor_node_release (g_btor, params[i]);
    btor_node_release (g_btor, indices[i]);
  }

  btor_mem_free (g_btor->mm, params, size);
  btor_mem_free (g_btor->mm, indices, size);

  btor_node_release (g_btor, fun);
  btor_node_release (g_btor, apply);
  btor_node_release (g_btor, result);
  btor_node_release (g_btor, var);
  finish_lambda_test ();
}

static void
test_lambda_hashing_1 (void)
{
  BtorNode *w0, *w1, *i, *e, *a;
  BtorSortId array_sort, sort;

  init_lambda_test ();

  sort       = btor_sort_bv (g_btor, 32);
  array_sort = btor_sort_array (g_btor, sort, sort);

  a  = btor_exp_array (g_btor, array_sort, 0);
  i  = btor_exp_var (g_btor, sort, 0);
  e  = btor_exp_var (g_btor, sort, 0);
  w0 = btor_exp_lambda_write (g_btor, a, i, e);
  w1 = btor_exp_lambda_write (g_btor, a, i, e);
  assert (w0 == w1);

  btor_sort_release (g_btor, array_sort);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, a);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, e);
  btor_node_release (g_btor, w0);
  btor_node_release (g_btor, w1);
  finish_lambda_test ();
}

static void
test_lambda_hashing_2 (void)
{
  BtorNode *ite0, *ite1, *i, *e, *a0, *a1, *eq;
  BtorSortId array_sort, sort;

  init_lambda_test ();

  sort       = btor_sort_bv (g_btor, 32);
  array_sort = btor_sort_array (g_btor, sort, sort);

  a0   = btor_exp_array (g_btor, array_sort, 0);
  a1   = btor_exp_array (g_btor, array_sort, 0);
  i    = btor_exp_var (g_btor, sort, 0);
  e    = btor_exp_var (g_btor, sort, 0);
  eq   = btor_exp_eq (g_btor, i, e);
  ite0 = btor_exp_cond (g_btor, eq, a0, a1);
  ite1 = btor_exp_cond (g_btor, eq, a0, a1);
  assert (ite0 == ite1);

  btor_node_release (g_btor, ite1);
  ite1 = btor_exp_cond (g_btor, btor_node_invert (eq), a1, a0);
  assert (ite0 == ite1);

  btor_sort_release (g_btor, array_sort);
  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, a0);
  btor_node_release (g_btor, a1);
  btor_node_release (g_btor, i);
  btor_node_release (g_btor, e);
  btor_node_release (g_btor, eq);
  btor_node_release (g_btor, ite0);
  btor_node_release (g_btor, ite1);
  finish_lambda_test ();
}

/* check if hashing considers commutativity */
static void
test_lambda_hashing_3 (void)
{
  BtorNode *l0, *l1, *v, *p0, *p1, *eq0, *eq1;
  BtorSortId sort;

  init_lambda_test ();

  sort = btor_sort_bv (g_btor, 32);

  /* NOTE: order p0, v, p1 is important here */
  p0 = btor_exp_param (g_btor, sort, 0);
  v  = btor_exp_var (g_btor, sort, 0);
  p1 = btor_exp_param (g_btor, sort, 0);

  eq0 = btor_exp_eq (g_btor, p0, v);
  eq1 = btor_exp_eq (g_btor, v, p1);

  l0 = btor_exp_lambda (g_btor, p0, eq0);
  l1 = btor_exp_lambda (g_btor, p1, eq1);
  assert (l0 == l1);

  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, p0);
  btor_node_release (g_btor, p1);
  btor_node_release (g_btor, v);
  btor_node_release (g_btor, eq0);
  btor_node_release (g_btor, eq1);
  btor_node_release (g_btor, l0);
  btor_node_release (g_btor, l1);
  finish_lambda_test ();
}

static void
test_lambda_hashing_4 (void)
{
  BtorNode *f0, *f1, *p0[2], *p1[2], *eq0, *eq1;
  BtorSortId sort;

  init_lambda_test ();

  sort = btor_sort_bv (g_btor, 32);

  p0[0] = btor_exp_param (g_btor, sort, 0);
  p0[1] = btor_exp_param (g_btor, sort, 0);
  p1[0] = btor_exp_param (g_btor, sort, 0);
  p1[1] = btor_exp_param (g_btor, sort, 0);

  eq0 = btor_exp_eq (g_btor, p0[0], p0[1]);
  eq1 = btor_exp_eq (g_btor, p1[0], p1[1]);

  f0 = btor_exp_fun (g_btor, p0, 2, eq0);
  f1 = btor_exp_fun (g_btor, p1, 2, eq1);
  assert (f0 == f1);

  btor_sort_release (g_btor, sort);
  btor_node_release (g_btor, p0[0]);
  btor_node_release (g_btor, p0[1]);
  btor_node_release (g_btor, p1[0]);
  btor_node_release (g_btor, p1[1]);
  btor_node_release (g_btor, eq0);
  btor_node_release (g_btor, eq1);
  btor_node_release (g_btor, f0);
  btor_node_release (g_btor, f1);
  finish_lambda_test ();
}

static void
test_quantifier_hashing_1 (void)
{
  init_lambda_test ();

  BtorNode *x0, *y0, *eq0, *f0, *e0;
  BtorNode *x1, *y1, *eq1, *f1, *e1;
  BtorSortId sort;

  sort = btor_sort_bv (g_btor, 32);
  x0   = btor_exp_param (g_btor, sort, 0);
  y0   = btor_exp_param (g_btor, sort, 0);
  eq0  = btor_exp_eq (g_btor, x0, y0);
  f0   = btor_exp_forall (g_btor, y0, eq0);
  e0   = btor_exp_exists (g_btor, x0, f0);

  x1  = btor_exp_param (g_btor, sort, 0);
  y1  = btor_exp_param (g_btor, sort, 0);
  eq1 = btor_exp_eq (g_btor, x1, y1);
  f1  = btor_exp_forall (g_btor, y1, eq1);
  e1  = btor_exp_exists (g_btor, x1, f1);
  assert (e0 == e1);

  btor_node_release (g_btor, x0);
  btor_node_release (g_btor, y0);
  btor_node_release (g_btor, eq0);
  btor_node_release (g_btor, f0);
  btor_node_release (g_btor, e0);
  btor_node_release (g_btor, x1);
  btor_node_release (g_btor, y1);
  btor_node_release (g_btor, eq1);
  btor_node_release (g_btor, f1);
  btor_node_release (g_btor, e1);
  btor_sort_release (g_btor, sort);
  finish_lambda_test ();
}

static void
test_quantifier_hashing_2 (void)
{
  init_lambda_test ();

  BtorNode *x0, *x1, *x2, *x3, *y0, *y1, *y2, *y3;
  BtorNode *a0, *a1, *a2, *a3, *a4, *a5, *a6, *r0;
  BtorNode *f0, *e0, *f1, *e1, *f2, *e2, *f3, *e3;
  BtorNode *x10, *x11, *x12, *x13, *y10, *y11, *y12, *y13;
  BtorNode *a10, *a11, *a12, *a13, *a14, *a15, *a16, *r10;
  BtorNode *f10, *e10, *f11, *e11, *f12, *e12, *f13, *e13;
  BtorSortId sort;

  sort = btor_sort_bv (g_btor, 32);
  x0   = btor_exp_param (g_btor, sort, 0);
  x1   = btor_exp_param (g_btor, sort, 0);
  x2   = btor_exp_param (g_btor, sort, 0);
  x3   = btor_exp_param (g_btor, sort, 0);
  y0   = btor_exp_param (g_btor, sort, 0);
  y1   = btor_exp_param (g_btor, sort, 0);
  y2   = btor_exp_param (g_btor, sort, 0);
  y3   = btor_exp_param (g_btor, sort, 0);

  a0 = btor_exp_bv_and (g_btor, x0, y0);
  a1 = btor_exp_bv_and (g_btor, a0, x1);
  a2 = btor_exp_bv_and (g_btor, a1, y1);
  a3 = btor_exp_bv_and (g_btor, a2, x2);
  a4 = btor_exp_bv_and (g_btor, a3, y2);
  a5 = btor_exp_bv_and (g_btor, a4, x3);
  a6 = btor_exp_bv_and (g_btor, a5, y3);
  r0 = btor_exp_bv_redor (g_btor, a6);
  f0 = btor_exp_forall (g_btor, x0, r0);
  e0 = btor_exp_exists (g_btor, y0, f0);
  e1 = btor_exp_exists (g_btor, y1, e0);
  f1 = btor_exp_forall (g_btor, x1, e1);
  f2 = btor_exp_forall (g_btor, x2, f1);
  e2 = btor_exp_exists (g_btor, y2, f2);
  f3 = btor_exp_forall (g_btor, x3, e2);
  e3 = btor_exp_exists (g_btor, y3, f3);

  x10 = btor_exp_param (g_btor, sort, 0);
  x11 = btor_exp_param (g_btor, sort, 0);
  x12 = btor_exp_param (g_btor, sort, 0);
  x13 = btor_exp_param (g_btor, sort, 0);
  y10 = btor_exp_param (g_btor, sort, 0);
  y11 = btor_exp_param (g_btor, sort, 0);
  y12 = btor_exp_param (g_btor, sort, 0);
  y13 = btor_exp_param (g_btor, sort, 0);

  a10 = btor_exp_bv_and (g_btor, x10, y10);
  a11 = btor_exp_bv_and (g_btor, a10, x11);
  a12 = btor_exp_bv_and (g_btor, a11, y11);
  a13 = btor_exp_bv_and (g_btor, a12, x12);
  a14 = btor_exp_bv_and (g_btor, a13, y12);
  a15 = btor_exp_bv_and (g_btor, a14, x13);
  a16 = btor_exp_bv_and (g_btor, a15, y13);
  r10 = btor_exp_bv_redor (g_btor, a16);
  f10 = btor_exp_forall (g_btor, x10, r10);
  e10 = btor_exp_exists (g_btor, y10, f10);
  e11 = btor_exp_exists (g_btor, y11, e10);
  f11 = btor_exp_forall (g_btor, x11, e11);
  f12 = btor_exp_forall (g_btor, x12, f11);
  e12 = btor_exp_exists (g_btor, y12, f12);
  f13 = btor_exp_forall (g_btor, x13, e12);
  e13 = btor_exp_exists (g_btor, y13, f13);

  assert (e3 == e13);

  btor_node_release (g_btor, x0);
  btor_node_release (g_btor, x1);
  btor_node_release (g_btor, x2);
  btor_node_release (g_btor, x3);
  btor_node_release (g_btor, y0);
  btor_node_release (g_btor, y1);
  btor_node_release (g_btor, y2);
  btor_node_release (g_btor, y3);
  btor_node_release (g_btor, a0);
  btor_node_release (g_btor, a1);
  btor_node_release (g_btor, a2);
  btor_node_release (g_btor, a3);
  btor_node_release (g_btor, a4);
  btor_node_release (g_btor, a5);
  btor_node_release (g_btor, a6);
  btor_node_release (g_btor, r0);
  btor_node_release (g_btor, f0);
  btor_node_release (g_btor, e0);
  btor_node_release (g_btor, e1);
  btor_node_release (g_btor, f1);
  btor_node_release (g_btor, f2);
  btor_node_release (g_btor, e2);
  btor_node_release (g_btor, f3);
  btor_node_release (g_btor, e3);
  btor_node_release (g_btor, x10);
  btor_node_release (g_btor, x11);
  btor_node_release (g_btor, x12);
  btor_node_release (g_btor, x13);
  btor_node_release (g_btor, y10);
  btor_node_release (g_btor, y11);
  btor_node_release (g_btor, y12);
  btor_node_release (g_btor, y13);
  btor_node_release (g_btor, a10);
  btor_node_release (g_btor, a11);
  btor_node_release (g_btor, a12);
  btor_node_release (g_btor, a13);
  btor_node_release (g_btor, a14);
  btor_node_release (g_btor, a15);
  btor_node_release (g_btor, a16);
  btor_node_release (g_btor, r10);
  btor_node_release (g_btor, f10);
  btor_node_release (g_btor, e10);
  btor_node_release (g_btor, e11);
  btor_node_release (g_btor, f11);
  btor_node_release (g_btor, f12);
  btor_node_release (g_btor, e12);
  btor_node_release (g_btor, f13);
  btor_node_release (g_btor, e13);
  btor_sort_release (g_btor, sort);
  finish_lambda_test ();
}

#if 0
/* (lambda x . (lambda y . (x + y))) (a) */
static void
test_lambda_partial_reduce_nested_lambdas_add1 (void)
{
  BtorNode *result;
  BtorNode *a, *x, *y, *add, *params[2] = {x, y}, *fun;

  init_lambda_test ();

  a = btor_exp_var (g_btor, g_elem_sort, "a");
  x = btor_exp_param (g_btor, g_elem_sort, "x");
  y = btor_exp_param (g_btor, g_elem_sort, "y");
  add = btor_exp_bv_add (g_btor, x, y);
  fun = btor_exp_fun (g_btor, params, 2, add); 
  result = apply_and_reduce (g_btor, 1, &a, fun);

  /* expected: lambda y' . (a + y') */
  assert (btor_node_is_lambda (result));
  assert (result != fun->e[1]);
  assert (result->e[0] != fun->e[1]->e[0]);
  assert (btor_node_real_addr (result->e[1])->kind == BTOR_BV_ADD_NODE);
  assert (btor_node_real_addr (result->e[1])->e[0] == a);
  assert (btor_node_real_addr (result->e[1])->e[1] == result->e[0]);

  btor_node_release (g_btor, result);
  btor_node_release (g_btor, fun);
  btor_node_release (g_btor, add);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, a);
  finish_lambda_test ();
}
#endif

/*---------------------------------------------------------------------------
 * additional tests
 *---------------------------------------------------------------------------*/

static void
test_lambda_define_fun (void)
{
  int32_t i;
  int32_t nesting_lvl = 1000;
  size_t size;
  BtorNode **params, **lambdas, **ands, *left, *right, *expected, *result;

  init_lambda_test ();

  size    = nesting_lvl * sizeof (BtorNode *);
  params  = btor_mem_malloc (g_btor->mm, size);
  lambdas = btor_mem_malloc (g_btor->mm, size);
  ands    = btor_mem_malloc (g_btor->mm, size - sizeof (BtorNode *));

  for (i = 0; i < nesting_lvl; i++)
    params[i] = btor_exp_param (g_btor, g_elem_sort, 0);

  assert (nesting_lvl > 1);
  left  = params[0];
  right = params[1];
  for (i = 0; i < nesting_lvl - 1; i++)
  {
    ands[i] = btor_exp_bv_and (g_btor, left, right);

    if (i + 2 < nesting_lvl)
    {
      left  = params[i + 2];
      right = ands[i];
    }
  }

  /* build expected */
  expected = ands[nesting_lvl - 2];
  for (i = nesting_lvl - 1; i >= 0; i--)
  {
    assert (expected);
    lambdas[i] = btor_exp_lambda (g_btor, params[i], expected);
    expected   = lambdas[i];
  }

  result = btor_exp_fun (g_btor, params, nesting_lvl, ands[nesting_lvl - 2]);

  assert (result == expected);

  for (i = 0; i < nesting_lvl; i++)
  {
    btor_node_release (g_btor, lambdas[i]);
    btor_node_release (g_btor, params[i]);

    if (i < nesting_lvl - 1) btor_node_release (g_btor, ands[i]);
  }

  btor_mem_free (g_btor->mm, params, size);
  btor_mem_free (g_btor->mm, lambdas, size);
  btor_mem_free (g_btor->mm, ands, size - sizeof (BtorNode *));
  btor_node_release (g_btor, result);
  finish_lambda_test ();
}

void
run_lambda_tests (int32_t argc, char **argv)
{
  /* constant lambda tests */
  BTOR_RUN_TEST (lambda_const_lambda_const);
  BTOR_RUN_TEST (lambda_const_lambda_var);
  BTOR_RUN_TEST (lambda_const_lambda_param);
  BTOR_RUN_TEST (lambda_const_lambda_negated);
  BTOR_RUN_TEST (lambda_unassigned_param);
  /* unary exp tests */
  BTOR_RUN_TEST (lambda_param_not);
  BTOR_RUN_TEST (lambda_param_neg);
  BTOR_RUN_TEST (lambda_param_redor);
  BTOR_RUN_TEST (lambda_param_redxor);
  BTOR_RUN_TEST (lambda_param_redand);
  BTOR_RUN_TEST (lambda_param_slice);
  BTOR_RUN_TEST (lambda_param_uext);
  BTOR_RUN_TEST (lambda_param_sext);
  /* binary exp tests */
  BTOR_RUN_TEST (lambda_param_implies);
  BTOR_RUN_TEST (lambda_param_iff);
  BTOR_RUN_TEST (lambda_param_xor);
  BTOR_RUN_TEST (lambda_param_xnor);
  BTOR_RUN_TEST (lambda_param_and);
  BTOR_RUN_TEST (lambda_param_nand);
  BTOR_RUN_TEST (lambda_param_or);
  BTOR_RUN_TEST (lambda_param_nor);
  BTOR_RUN_TEST (lambda_param_eq);
  BTOR_RUN_TEST (lambda_param_ne);
  BTOR_RUN_TEST (lambda_param_add);
  BTOR_RUN_TEST (lambda_param_uaddo);
  BTOR_RUN_TEST (lambda_param_saddo);
  BTOR_RUN_TEST (lambda_param_mul);
  BTOR_RUN_TEST (lambda_param_umulo);
  BTOR_RUN_TEST (lambda_param_smulo);
  BTOR_RUN_TEST (lambda_param_ult);
  BTOR_RUN_TEST (lambda_param_slt);
  BTOR_RUN_TEST (lambda_param_ulte);
  BTOR_RUN_TEST (lambda_param_slte);
  BTOR_RUN_TEST (lambda_param_ugt);
  BTOR_RUN_TEST (lambda_param_sgt);
  BTOR_RUN_TEST (lambda_param_ugte);
  BTOR_RUN_TEST (lambda_param_sgte);
  BTOR_RUN_TEST (lambda_param_sll);
  BTOR_RUN_TEST (lambda_param_srl);
  BTOR_RUN_TEST (lambda_param_sra);
  BTOR_RUN_TEST (lambda_param_rol);
  BTOR_RUN_TEST (lambda_param_ror);
  BTOR_RUN_TEST (lambda_param_sub);
  BTOR_RUN_TEST (lambda_param_usubo);
  BTOR_RUN_TEST (lambda_param_ssubo);
  BTOR_RUN_TEST (lambda_param_udiv);
  BTOR_RUN_TEST (lambda_param_sdiv);
  BTOR_RUN_TEST (lambda_param_sdivo);
  BTOR_RUN_TEST (lambda_param_urem);
  BTOR_RUN_TEST (lambda_param_srem);
  BTOR_RUN_TEST (lambda_param_smod);
  BTOR_RUN_TEST (lambda_param_concat);
  BTOR_RUN_TEST (lambda_param_read);
  /* ternary exp tests */
  BTOR_RUN_TEST (lambda_param_write1);
  BTOR_RUN_TEST (lambda_param_write2);
  BTOR_RUN_TEST (lambda_param_bcond1);
  BTOR_RUN_TEST (lambda_param_bcond2);
  BTOR_RUN_TEST (lambda_param_bcond3);
  BTOR_RUN_TEST (lambda_param_acond);

  /* bounded reduction tests */
  BTOR_RUN_TEST (lambda_bounded_reduce1);
  BTOR_RUN_TEST (lambda_bounded_reduce2);
  BTOR_RUN_TEST (lambda_bounded_reduce3);

  /* full reduction tests (with reduced expressions) */
  BTOR_RUN_TEST (lambda_reduce_write1);
  BTOR_RUN_TEST (lambda_reduce_write2);
  BTOR_RUN_TEST (lambda_reduce_nested_writes);
  BTOR_RUN_TEST (lambda_reduce_nested_lambdas_add1);
  BTOR_RUN_TEST (lambda_reduce_nested_lambdas_add2);
  BTOR_RUN_TEST (lambda_reduce_nested_lambdas_read);
  BTOR_RUN_TEST (lambda_reduce_nested_lambdas_const_n1000);

  /* lambda hashing tests */
  BTOR_RUN_TEST (lambda_hashing_1);
  BTOR_RUN_TEST (lambda_hashing_2);
  BTOR_RUN_TEST (lambda_hashing_3);
  BTOR_RUN_TEST (lambda_hashing_4);

  /* binder hashing tests */
  BTOR_RUN_TEST (quantifier_hashing_1);
  BTOR_RUN_TEST (quantifier_hashing_2);

  /* partial reduction tests */
  // TODO: should we really support this? use case?
  //  BTOR_RUN_TEST (lambda_partial_reduce_nested_lambdas_add1);

  /* additional tests */
  BTOR_RUN_TEST (lambda_define_fun);
}

void
finish_lambda_tests (void)
{
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbeta.h"
#include "btorcore.h"
#include "testexp.h"
#include "testrunner.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor   = NULL;
static int g_index_bw = 32;
static int g_elem_bw  = 16;
static BtorSortId g_elem_sort;
static BtorSortId g_index_sort;
static BtorSortId g_array_sort;

void
init_lambda_test (void)
{
  g_btor = btor_new_btor ();
  if (g_rwreads) btor_opt_set (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  btor_opt_set (g_btor, BTOR_OPT_FUN_STORE_LAMBDAS, 1);
  g_elem_sort  = btor_sort_bitvec (g_btor, g_elem_bw);
  g_index_sort = btor_sort_bitvec (g_btor, g_index_bw);
  g_array_sort = btor_sort_array (g_btor, g_index_sort, g_elem_sort);
}

void
finish_lambda_test (void)
{
  btor_sort_release (g_btor, g_elem_sort);
  btor_sort_release (g_btor, g_index_sort);
  btor_sort_release (g_btor, g_array_sort);
  btor_delete_btor (g_btor);
}

void
init_lambda_tests (void)
{
}

static void
assert_parameterized (int argc, ...)
{
  int i;
  va_list ap;
  BtorNode *e;

  va_start (ap, argc);
  for (i = 0; i < argc; i++)
  {
    e = va_arg (ap, BtorNode *);
    assert (BTOR_REAL_ADDR_NODE (e)->parameterized);
  }
  va_end (ap);
}

static void
assert_not_parameterized (int argc, ...)
{
  int i;
  va_list ap;
  BtorNode *e;

  va_start (ap, argc);
  for (i = 0; i < argc; i++)
  {
    e = va_arg (ap, BtorNode *);
    assert (!BTOR_REAL_ADDR_NODE (e)->parameterized);
  }
  va_end (ap);
}

static BtorNode *
apply_and_reduce (Btor *btor, BtorNode *args[], int argc, BtorNode *lambda)
{
  assert (btor);
  assert (argc >= 0);
  assert (argc < 1 || args);
  assert (lambda);

  int i;
  BtorNode *result, *cur;
  BtorNodePtrStack unassign;
  BtorMemMgr *mm;

  mm = btor->mm;

  BTOR_INIT_STACK (mm, unassign);

  cur = lambda;
  for (i = 0; i < argc; i++)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (btor_is_lambda_node (cur));
    btor_beta_assign_param (btor, cur, args[i]);
    BTOR_PUSH_STACK (unassign, cur);
    cur = BTOR_REAL_ADDR_NODE (cur->e[1]);
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

  x      = btor_param_exp (g_btor, g_index_sort, "x");
  c      = btor_zero_exp (g_btor, g_elem_sort);
  i      = btor_var_exp (g_btor, g_index_sort, "i");
  lambda = btor_lambda_exp (g_btor, x, c);

  /* (lambda x . 0) (i) */
  result = apply_and_reduce (g_btor, &i, 1, lambda);
  assert (result == c);
  assert_not_parameterized (1, result);
  btor_release_exp (g_btor, result);

  /* (lambda x . 0) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == c);
  assert_parameterized (1, x);
  assert_not_parameterized (4, result, c, i, lambda);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, c);
  btor_release_exp (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_const_lambda_var (void)
{
  BtorNode *result;
  BtorNode *x, *a, *i, *lambda;

  init_lambda_test ();

  x      = btor_param_exp (g_btor, g_index_sort, "x");
  a      = btor_var_exp (g_btor, g_elem_sort, "a");
  i      = btor_var_exp (g_btor, g_index_sort, "i");
  lambda = btor_lambda_exp (g_btor, x, a);

  /* (lambda x . a) (i) */
  result = apply_and_reduce (g_btor, &i, 1, lambda);
  assert (result == a);
  assert_not_parameterized (1, result);
  btor_release_exp (g_btor, result);

  /* (lambda x . a) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == a);
  assert_parameterized (1, x);
  assert_not_parameterized (4, result, lambda, i, a);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, i);
  finish_lambda_test ();
}

static void
test_lambda_const_lambda_param (void)
{
  BtorNode *result;
  BtorNode *x, *a, *lambda;

  init_lambda_test ();

  x      = btor_param_exp (g_btor, g_elem_sort, "x");
  a      = btor_var_exp (g_btor, g_elem_sort, "a");
  lambda = btor_lambda_exp (g_btor, x, x);

  /* (lambda x . x) (a) */
  result = apply_and_reduce (g_btor, &a, 1, lambda);
  assert (result == a);
  assert_not_parameterized (1, result);
  btor_release_exp (g_btor, result);

  /* (lambda x . x) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == lambda);
  assert_parameterized (1, x);
  assert_not_parameterized (3, result, lambda, a);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_const_lambda_negated (void)
{
  BtorNode *result;
  BtorNode *a, *not_a, *x, *not_x, *lambda;

  init_lambda_test ();

  a      = btor_var_exp (g_btor, g_elem_sort, "a");
  not_a  = btor_not_exp (g_btor, a);
  x      = btor_param_exp (g_btor, g_elem_sort, "x");
  not_x  = btor_not_exp (g_btor, x);
  lambda = btor_lambda_exp (g_btor, x, not_x);

  /* (lambda x . not (x)) (not (a)) */
  result = apply_and_reduce (g_btor, &not_a, 1, lambda);
  assert (result == a);
  assert_not_parameterized (1, result);
  btor_release_exp (g_btor, result);

  /* (lambda x . not (x)) () */
  result = apply_and_reduce (g_btor, 0, 0, lambda);
  assert (result == lambda);
  assert_parameterized (2, x, not_x);
  assert_not_parameterized (4, result, lambda, not_a, a);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, not_x);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, not_a);
  btor_release_exp (g_btor, a);
  finish_lambda_test ();
}

/* (lambda x . a) () */
static void
test_lambda_unassigned_param (void)
{
  BtorNode *result;
  BtorNode *x, *a, *lambda;

  init_lambda_test ();

  x      = btor_param_exp (g_btor, g_index_sort, "x");
  a      = btor_var_exp (g_btor, g_elem_sort, "a");
  lambda = btor_lambda_exp (g_btor, x, a);
  result = apply_and_reduce (g_btor, 0, 0, lambda);

  assert (result == a);
  assert_parameterized (1, x);
  assert_not_parameterized (3, result, lambda, a);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, x);
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
  var               = btor_var_exp (g_btor, g_elem_sort, "v1");
  expected          = func (g_btor, var);
  param             = btor_param_exp (g_btor, lambda_index_sort, "p1");
  param_exp         = func (g_btor, param);
  lambda            = btor_lambda_exp (g_btor, param, param_exp);
  result            = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, param, param_exp);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
test_lambda_param_not (void)
{
  unary_param_exp_test (btor_not_exp);
}

static void
test_lambda_param_neg (void)
{
  unary_param_exp_test (btor_neg_exp);
}

static void
test_lambda_param_redor (void)
{
  unary_param_exp_test (btor_redor_exp);
}

static void
test_lambda_param_redxor (void)
{
  unary_param_exp_test (btor_redxor_exp);
}

static void
test_lambda_param_redand (void)
{
  unary_param_exp_test (btor_redand_exp);
}

static void
test_lambda_param_slice (void)
{
  BtorNode *result;
  BtorNode *var, *param, *expected, *slice, *lambda;
  int lower, upper;

  init_lambda_test ();

  lower = g_elem_bw / 2 + 1;
  upper = g_elem_bw - 1;

  var      = btor_var_exp (g_btor, g_elem_sort, "v1");
  param    = btor_param_exp (g_btor, g_elem_sort, "p1");
  expected = btor_slice_exp (g_btor, var, upper, lower);
  slice    = btor_slice_exp (g_btor, param, upper, lower);
  lambda   = btor_lambda_exp (g_btor, param, slice);
  result   = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, param, slice);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, slice);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
param_extension_test (BtorNode *(*func) (Btor *, BtorNode *, uint32_t))
{
  BtorNode *result;
  BtorNode *var, *param, *expected, *param_exp, *lambda;
  BtorSortId lower_sort, upper_sort;
  int lower, upper;

  init_lambda_test ();

  lower      = g_elem_bw / 2 + 1;
  upper      = g_elem_bw - 1;
  lower_sort = btor_sort_bitvec (g_btor, lower);
  upper_sort = btor_sort_bitvec (g_btor, upper);

  var       = btor_var_exp (g_btor, lower_sort, "v1");
  param     = btor_param_exp (g_btor, lower_sort, "p1");
  expected  = func (g_btor, var, upper_sort);
  param_exp = func (g_btor, param, upper_sort);
  lambda    = btor_lambda_exp (g_btor, param, param_exp);
  result    = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, param, param_exp);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_sort_release (g_btor, lower_sort);
  btor_sort_release (g_btor, upper_sort);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
test_lambda_param_uext (void)
{
  param_extension_test (btor_uext_exp);
}

static void
test_lambda_param_sext (void)
{
  param_extension_test (btor_sext_exp);
}

/*---------------------------------------------------------------------------
 * binary expression tests
 *---------------------------------------------------------------------------*/

/* (lambda x . bin_exp (x, v2)) (v1) or (lambda x . bin_exp (v1, x)) (v2) */
static void
binary_param_exp_test (int param_pos,
                       BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  assert (param_pos == 0 || param_pos == 1);

  BtorNode *result;
  BtorNode *param_exp, *v1, *v2, *expected, *x;
  BtorSortId v1_sort, v2_sort, x_sort;
  int x_bw, v1_bw, v2_bw;

  init_lambda_test ();

  x_bw  = g_elem_bw;
  v1_bw = g_elem_bw;
  v2_bw = g_elem_bw;

  if (func == btor_implies_exp || func == btor_iff_exp)
  {
    v1_bw = 1;
    v2_bw = 1;
  }
  else if (func == btor_sll_exp || func == btor_srl_exp || func == btor_sra_exp
           || func == btor_rol_exp || func == btor_ror_exp)
  {
    v2_bw = btor_util_log_2 (v1_bw);
  }

  x_bw = (param_pos == 0) ? v1_bw : v2_bw;

  v1_sort = btor_sort_bitvec (g_btor, v1_bw);
  v2_sort = btor_sort_bitvec (g_btor, v2_bw);
  x_sort  = btor_sort_bitvec (g_btor, x_bw);

  v1       = btor_var_exp (g_btor, v1_sort, "v1");
  v2       = btor_var_exp (g_btor, v2_sort, "v2");
  expected = func (g_btor, v1, v2);
  x        = btor_param_exp (g_btor, x_sort, "x");

  if (param_pos == 0)
    param_exp = func (g_btor, x, v2);
  else
    param_exp = func (g_btor, v1, x);

  BtorNode *lambda = btor_lambda_exp (g_btor, x, param_exp);

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
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, v2);
  btor_release_exp (g_btor, v1);
  finish_lambda_test ();
}

static void
test_lambda_param_implies (void)
{
  binary_param_exp_test (0, btor_implies_exp);
  binary_param_exp_test (1, btor_implies_exp);
}

static void
test_lambda_param_iff (void)
{
  binary_param_exp_test (0, btor_iff_exp);
  binary_param_exp_test (1, btor_iff_exp);
}

static void
test_lambda_param_xor (void)
{
  binary_param_exp_test (0, btor_xor_exp);
  binary_param_exp_test (1, btor_xor_exp);
}

static void
test_lambda_param_xnor (void)
{
  binary_param_exp_test (0, btor_xnor_exp);
  binary_param_exp_test (1, btor_xnor_exp);
}

static void
test_lambda_param_and (void)
{
  binary_param_exp_test (0, btor_and_exp);
  binary_param_exp_test (1, btor_and_exp);
}

static void
test_lambda_param_nand (void)
{
  binary_param_exp_test (0, btor_nand_exp);
  binary_param_exp_test (1, btor_nand_exp);
}

static void
test_lambda_param_or (void)
{
  binary_param_exp_test (0, btor_or_exp);
  binary_param_exp_test (1, btor_or_exp);
}

static void
test_lambda_param_nor (void)
{
  binary_param_exp_test (0, btor_nor_exp);
  binary_param_exp_test (1, btor_nor_exp);
}

static void
test_lambda_param_eq (void)
{
  binary_param_exp_test (0, btor_eq_exp);
  binary_param_exp_test (1, btor_eq_exp);
}

static void
test_lambda_param_ne (void)
{
  binary_param_exp_test (0, btor_ne_exp);
  binary_param_exp_test (1, btor_ne_exp);
}

static void
test_lambda_param_add (void)
{
  binary_param_exp_test (0, btor_add_exp);
  binary_param_exp_test (1, btor_add_exp);
}

static void
test_lambda_param_uaddo (void)
{
  binary_param_exp_test (0, btor_uaddo_exp);
  binary_param_exp_test (1, btor_uaddo_exp);
}

static void
test_lambda_param_saddo (void)
{
  binary_param_exp_test (0, btor_saddo_exp);
  binary_param_exp_test (1, btor_saddo_exp);
}

static void
test_lambda_param_mul (void)
{
  binary_param_exp_test (0, btor_mul_exp);
  binary_param_exp_test (1, btor_mul_exp);
}

static void
test_lambda_param_umulo (void)
{
  binary_param_exp_test (0, btor_umulo_exp);
  binary_param_exp_test (1, btor_umulo_exp);
}

static void
test_lambda_param_smulo (void)
{
  binary_param_exp_test (0, btor_smulo_exp);
  binary_param_exp_test (1, btor_smulo_exp);
}

static void
test_lambda_param_ult (void)
{
  binary_param_exp_test (0, btor_ult_exp);
  binary_param_exp_test (1, btor_ult_exp);
}

static void
test_lambda_param_slt (void)
{
  binary_param_exp_test (0, btor_slt_exp);
  binary_param_exp_test (1, btor_slt_exp);
}

static void
test_lambda_param_ulte (void)
{
  binary_param_exp_test (0, btor_ulte_exp);
  binary_param_exp_test (1, btor_ulte_exp);
}

static void
test_lambda_param_slte (void)
{
  binary_param_exp_test (0, btor_slte_exp);
  binary_param_exp_test (1, btor_slte_exp);
}

static void
test_lambda_param_ugt (void)
{
  binary_param_exp_test (0, btor_ugt_exp);
  binary_param_exp_test (1, btor_ugt_exp);
}

static void
test_lambda_param_sgt (void)
{
  binary_param_exp_test (0, btor_sgt_exp);
  binary_param_exp_test (1, btor_sgt_exp);
}

static void
test_lambda_param_ugte (void)
{
  binary_param_exp_test (0, btor_ugte_exp);
  binary_param_exp_test (1, btor_ugte_exp);
}

static void
test_lambda_param_sgte (void)
{
  binary_param_exp_test (0, btor_sgte_exp);
  binary_param_exp_test (1, btor_sgte_exp);
}

static void
test_lambda_param_sll (void)
{
  binary_param_exp_test (0, btor_sll_exp);
  binary_param_exp_test (1, btor_sll_exp);
}

static void
test_lambda_param_srl (void)
{
  binary_param_exp_test (0, btor_srl_exp);
  binary_param_exp_test (1, btor_srl_exp);
}

static void
test_lambda_param_sra (void)
{
  binary_param_exp_test (0, btor_sra_exp);
  binary_param_exp_test (1, btor_sra_exp);
}

static void
test_lambda_param_rol (void)
{
  binary_param_exp_test (0, btor_rol_exp);
  binary_param_exp_test (1, btor_rol_exp);
}

static void
test_lambda_param_ror (void)
{
  binary_param_exp_test (0, btor_ror_exp);
  binary_param_exp_test (1, btor_ror_exp);
}

static void
test_lambda_param_sub (void)
{
  binary_param_exp_test (0, btor_sub_exp);
  binary_param_exp_test (1, btor_sub_exp);
}

static void
test_lambda_param_usubo (void)
{
  binary_param_exp_test (0, btor_usubo_exp);
  binary_param_exp_test (1, btor_usubo_exp);
}

static void
test_lambda_param_ssubo (void)
{
  binary_param_exp_test (0, btor_ssubo_exp);
  binary_param_exp_test (1, btor_ssubo_exp);
}

static void
test_lambda_param_udiv (void)
{
  binary_param_exp_test (0, btor_udiv_exp);
  binary_param_exp_test (1, btor_udiv_exp);
}

static void
test_lambda_param_sdiv (void)
{
  binary_param_exp_test (0, btor_sdiv_exp);
  binary_param_exp_test (1, btor_sdiv_exp);
}

static void
test_lambda_param_sdivo (void)
{
  binary_param_exp_test (0, btor_sdivo_exp);
  binary_param_exp_test (1, btor_sdivo_exp);
}

static void
test_lambda_param_urem (void)
{
  binary_param_exp_test (0, btor_urem_exp);
  binary_param_exp_test (1, btor_urem_exp);
}

static void
test_lambda_param_srem (void)
{
  binary_param_exp_test (0, btor_srem_exp);
  binary_param_exp_test (1, btor_srem_exp);
}

static void
test_lambda_param_smod (void)
{
  binary_param_exp_test (0, btor_smod_exp);
  binary_param_exp_test (1, btor_smod_exp);
}

static void
test_lambda_param_concat (void)
{
  binary_param_exp_test (0, btor_concat_exp);
  binary_param_exp_test (1, btor_concat_exp);
}

/* (lambda x . read(a, x)) (i) */
static void
test_lambda_param_read (void)
{
  BtorNode *result;
  BtorNode *x, *i, *a, *expected, *read, *lambda;

  init_lambda_test ();

  x        = btor_param_exp (g_btor, g_index_sort, "x");
  i        = btor_var_exp (g_btor, g_index_sort, "i");
  a        = btor_array_exp (g_btor, g_array_sort, "a");
  expected = btor_read_exp (g_btor, a, i);
  read     = btor_read_exp (g_btor, a, x);
  lambda   = btor_lambda_exp (g_btor, x, read);
  result   = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, read);
  assert_not_parameterized (5, result, lambda, expected, a, i);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, read);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, x);
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

  i         = btor_var_exp (g_btor, g_index_sort, "i");
  e         = btor_var_exp (g_btor, g_elem_sort, "e");
  a         = btor_array_exp (g_btor, g_array_sort, "a");
  expected  = btor_write_exp (g_btor, a, i, e);
  x         = btor_param_exp (g_btor, g_elem_sort, "x");
  param_exp = btor_write_exp (g_btor, a, i, x);
  lambda    = btor_lambda_exp (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &e, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, a, e, i);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, i);
  finish_lambda_test ();
}

/* (lambda x . write (a, x, e)) (i) */
static void
test_lambda_param_write2 (void)
{
  BtorNode *result;
  BtorNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  init_lambda_test ();

  i         = btor_var_exp (g_btor, g_index_sort, "i");
  e         = btor_var_exp (g_btor, g_elem_sort, "e");
  a         = btor_array_exp (g_btor, g_array_sort, "a");
  expected  = btor_write_exp (g_btor, a, i, e);
  x         = btor_param_exp (g_btor, g_index_sort, "p");
  param_exp = btor_write_exp (g_btor, a, x, e);
  lambda    = btor_lambda_exp (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, a, e, i);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, i);
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

  sort      = btor_sort_bitvec (g_btor, 1);
  v1        = btor_var_exp (g_btor, sort, "v1");
  x         = btor_param_exp (g_btor, sort, "x");
  v2        = btor_var_exp (g_btor, g_elem_sort, "v2");
  v3        = btor_var_exp (g_btor, g_elem_sort, "v3");
  expected  = btor_cond_exp (g_btor, v1, v2, v3);
  param_exp = btor_cond_exp (g_btor, x, v2, v3);
  lambda    = btor_lambda_exp (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &v1, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, v3);
  btor_release_exp (g_btor, v2);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, v1);
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

  sort      = btor_sort_bitvec (g_btor, 1);
  v1        = btor_var_exp (g_btor, sort, "v1");
  x         = btor_param_exp (g_btor, g_elem_sort, "x");
  v2        = btor_var_exp (g_btor, g_elem_sort, "v2");
  v3        = btor_var_exp (g_btor, g_elem_sort, "v3");
  expected  = btor_cond_exp (g_btor, v1, v2, v3);
  param_exp = btor_cond_exp (g_btor, v1, x, v3);
  lambda    = btor_lambda_exp (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &v2, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, v3);
  btor_release_exp (g_btor, v2);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, v1);
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

  sort      = btor_sort_bitvec (g_btor, 1);
  v1        = btor_var_exp (g_btor, sort, "v1");
  x         = btor_param_exp (g_btor, g_elem_sort, "x");
  v2        = btor_var_exp (g_btor, g_elem_sort, "v2");
  v3        = btor_var_exp (g_btor, g_elem_sort, "v3");
  expected  = btor_cond_exp (g_btor, v1, v2, v3);
  param_exp = btor_cond_exp (g_btor, v1, v2, x);
  lambda    = btor_lambda_exp (g_btor, x, param_exp);
  result    = apply_and_reduce (g_btor, &v3, 1, lambda);

  assert (result == expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, v3);
  btor_release_exp (g_btor, v2);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, v1);
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

  var            = btor_var_exp (g_btor, g_index_sort, "v1");
  index          = btor_var_exp (g_btor, g_index_sort, "i");
  expected_cond  = btor_eq_exp (g_btor, var, index);
  e_if           = btor_array_exp (g_btor, g_array_sort, "a1");
  e_else         = btor_array_exp (g_btor, g_array_sort, "a2");
  expected_acond = btor_cond_exp (g_btor, expected_cond, e_if, e_else);
  expected       = btor_read_exp (g_btor, expected_acond, var);

  param       = btor_param_exp (g_btor, g_index_sort, "p");
  param_cond  = btor_eq_exp (g_btor, param, index);
  param_acond = btor_cond_exp (g_btor, param_cond, e_if, e_else);
  param_exp   = btor_read_exp (g_btor, param_acond, param);
  lambda      = btor_lambda_exp (g_btor, param, param_exp);
  result      = apply_and_reduce (g_btor, &var, 1, lambda);

  assert (result == expected);
  assert_parameterized (4, param, param_cond, param_acond, param_exp);
  assert_not_parameterized (4, result, lambda, expected, expected_acond);
  assert_not_parameterized (5, e_else, e_if, expected_cond, index, var);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param_acond);
  btor_release_exp (g_btor, param_cond);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, expected_acond);
  btor_release_exp (g_btor, e_else);
  btor_release_exp (g_btor, e_if);
  btor_release_exp (g_btor, expected_cond);
  btor_release_exp (g_btor, index);
  btor_release_exp (g_btor, var);
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

  x  = btor_param_exp (g_btor, g_index_sort, "x");
  y  = btor_param_exp (g_btor, g_index_sort, "y");
  l2 = btor_lambda_exp (g_btor, y, y);
  r  = btor_apply_exps (g_btor, &x, 1, l2);
  l1 = btor_lambda_exp (g_btor, x, r);
  v  = btor_var_exp (g_btor, g_index_sort, "v");

  expected = btor_apply_exps (g_btor, &v, 1, l2);

  /* bound 2: stop at second lambda */
  btor_beta_assign_param (g_btor, l1, v);
  result = btor_beta_reduce_bounded (g_btor, l1, 2);
  btor_beta_unassign_params (g_btor, l1);

  assert (result == expected);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, expected);

  /* bound 3: stop at third lambda */
  btor_beta_assign_param (g_btor, l1, v);
  result = btor_beta_reduce_bounded (g_btor, l1, 3);
  btor_beta_unassign_params (g_btor, l1);

  assert (result == v);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, v);
  btor_release_exp (g_btor, l1);
  btor_release_exp (g_btor, r);
  btor_release_exp (g_btor, l2);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_bounded_reduce2 (void)
{
  BtorNode *result;
  BtorNode *x, *i, *eq, *l, *j, *expected;

  init_lambda_test ();

  x        = btor_param_exp (g_btor, g_index_sort, "x");
  i        = btor_var_exp (g_btor, g_index_sort, "i");
  eq       = btor_eq_exp (g_btor, x, i);
  l        = btor_lambda_exp (g_btor, x, eq);
  j        = btor_var_exp (g_btor, g_index_sort, "j");
  expected = btor_eq_exp (g_btor, i, j);

  btor_beta_assign_param (g_btor, l, j);
  result = btor_beta_reduce_bounded (g_btor, l, 0);
  assert (result == expected);
  btor_release_exp (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l, 1);
  assert (result == l);
  btor_release_exp (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, eq, 1);
  assert (result == expected);
  btor_release_exp (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l, 2);
  assert (result == expected);
  btor_beta_unassign_params (g_btor, l);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, j);
  btor_release_exp (g_btor, l);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, x);
  finish_lambda_test ();
}

static void
test_lambda_bounded_reduce3 (void)
{
  BtorNode *result;
  BtorNode *x, *y, *l1, *a, *l2, *i, *expected;

  init_lambda_test ();

  x        = btor_param_exp (g_btor, g_index_sort, "x");
  y        = btor_param_exp (g_btor, g_index_sort, "y");
  l1       = btor_lambda_exp (g_btor, x, x);
  a        = btor_apply_exps (g_btor, &y, 1, l1);
  l2       = btor_lambda_exp (g_btor, y, a);
  i        = btor_var_exp (g_btor, g_index_sort, "i");
  expected = btor_apply_exps (g_btor, &i, 1, l1);

  btor_beta_assign_param (g_btor, l2, i);
  result = btor_beta_reduce_bounded (g_btor, l2, 1);
  assert (result == l2);
  btor_release_exp (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l2, 2);
  assert (result == expected);
  btor_release_exp (g_btor, result);

  result = btor_beta_reduce_bounded (g_btor, l2, 3);
  assert (result == i);
  btor_beta_unassign_params (g_btor, l2);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, l2);
  btor_release_exp (g_btor, l1);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, x);
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
  a      = btor_array_exp (g_btor, g_array_sort, "a");
  i      = btor_var_exp (g_btor, g_index_sort, "i");
  e      = btor_var_exp (g_btor, g_elem_sort, "e");
  param  = btor_param_exp (g_btor, g_index_sort, "p");
  read   = btor_read_exp (g_btor, a, param);
  eq     = btor_eq_exp (g_btor, param, i);
  cond   = btor_cond_exp (g_btor, eq, e, read);
  lambda = btor_lambda_exp (g_btor, param, cond);
  result = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == e);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, cond);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, read);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, a);
  finish_lambda_test ();
}

static void
test_lambda_reduce_write2 (void)
{
  BtorNode *result;
  BtorNode *a, *i, *e, *param, *read, *expected, *eq, *cond, *lambda;

  init_lambda_test ();

  a        = btor_array_exp (g_btor, g_array_sort, "a");
  i        = btor_var_exp (g_btor, g_index_sort, "i");
  e        = btor_var_exp (g_btor, g_elem_sort, "e");
  param    = btor_param_exp (g_btor, g_index_sort, "p");
  read     = btor_read_exp (g_btor, a, param);
  expected = btor_read_exp (g_btor, a, i);
  eq       = btor_ne_exp (g_btor, param, i);
  cond     = btor_cond_exp (g_btor, eq, e, read);
  lambda   = btor_lambda_exp (g_btor, param, cond);
  result   = apply_and_reduce (g_btor, &i, 1, lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, cond);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, read);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, a);
  finish_lambda_test ();
}

static void
test_lambda_reduce_nested_writes (void)
{
  BtorNode *result;
  BtorNode *i, *a, *e2, *w2, *e1, *w1;

  init_lambda_test ();

  i = btor_var_exp (g_btor, g_index_sort, "i");
  /* w2 = write (a, i, e2) */
  a  = btor_array_exp (g_btor, g_array_sort, "a");
  e2 = btor_var_exp (g_btor, g_elem_sort, "e2");
  w2 = btor_write_exp (g_btor, a, i, e2);
  /* w1 = write (w1, not i, e1) */
  e1     = btor_var_exp (g_btor, g_elem_sort, "e1");
  w1     = btor_write_exp (g_btor, w2, BTOR_INVERT_NODE (i), e1);
  result = apply_and_reduce (g_btor, &i, 1, w1);

  assert (result == e2);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, w1);
  btor_release_exp (g_btor, e1);
  btor_release_exp (g_btor, w2);
  btor_release_exp (g_btor, e2);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, i);
  finish_lambda_test ();
}

/* (lambda x . (lambda y . (x + y))) (a b) */
static void
test_lambda_reduce_nested_lambdas_add1 (void)
{
  BtorNode *result;
  BtorNode *a, *b, *expected, *x, *y, *add, *fun;

  init_lambda_test ();

  a                   = btor_var_exp (g_btor, g_elem_sort, "a");
  b                   = btor_var_exp (g_btor, g_elem_sort, "b");
  BtorNode *args[2]   = {a, b};
  expected            = btor_add_exp (g_btor, a, b);
  x                   = btor_param_exp (g_btor, g_elem_sort, "x");
  y                   = btor_param_exp (g_btor, g_elem_sort, "y");
  BtorNode *params[2] = {x, y};
  add                 = btor_add_exp (g_btor, x, y);
  fun                 = btor_fun_exp (g_btor, params, 2, add);

  result = apply_and_reduce (g_btor, args, 2, fun);
  assert (result == expected);
  btor_release_exp (g_btor, result);

  BtorNode *apply = btor_apply_exps (g_btor, args, 2, fun);
  result          = btor_beta_reduce_full (g_btor, apply, 0);
  assert (result == expected);

  btor_release_exp (g_btor, apply);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, fun);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, b);
  btor_release_exp (g_btor, a);
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
  a                 = btor_var_exp (g_btor, g_elem_sort, "a");
  b                 = btor_var_exp (g_btor, g_elem_sort, "b");
  expected          = btor_add_exp (g_btor, a, b);
  x                 = btor_param_exp (g_btor, lambda_index_sort, "x");
  y                 = btor_param_exp (g_btor, lambda_index_sort, "y");
  lambda2           = btor_lambda_exp (g_btor, y, y);
  app               = btor_apply_exps (g_btor, &b, 1, lambda2);
  add               = btor_add_exp (g_btor, x, app);
  lambda1           = btor_lambda_exp (g_btor, x, add);
  result            = apply_and_reduce (g_btor, &a, 1, lambda1);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda1);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, app);
  btor_release_exp (g_btor, lambda2);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, b);
  btor_release_exp (g_btor, a);
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

  var     = btor_var_exp (g_btor, g_elem_sort, "var");
  y       = btor_param_exp (g_btor, g_elem_sort, "y");
  lambda2 = btor_lambda_exp (g_btor, y, y);
  x       = btor_param_exp (g_btor, g_elem_sort, "x");
  add     = btor_add_exp (g_btor, x, var);
  app     = btor_apply_exps (g_btor, &add, 1, lambda2);
  napp    = btor_not_exp (g_btor, app);
  lambda1 = btor_lambda_exp (g_btor, x, napp);
  a       = btor_var_exp (g_btor, g_elem_sort, "a");
  /* exptected not (a + var) */
  expected_add = btor_add_exp (g_btor, a, var);
  expected     = btor_not_exp (g_btor, expected_add);
  result       = apply_and_reduce (g_btor, &a, 1, lambda1);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, expected_add);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, lambda1);
  btor_release_exp (g_btor, napp);
  btor_release_exp (g_btor, app);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, lambda2);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

/* (lambda x1 . (lambda x2 . ... (lambda x1000 . var))) (i1 ... i1000) */
static void
test_lambda_reduce_nested_lambdas_const_n1000 (void)
{
  BtorNode *result;
  BtorNode **params, **indices, *var, *fun;
  int i, nesting_lvl;
  size_t size;

  init_lambda_test ();

  nesting_lvl = 1000;
  size        = nesting_lvl * sizeof (BtorNode *);
  var         = btor_var_exp (g_btor, g_elem_sort, 0);

  params  = btor_mem_malloc (g_btor->mm, size);
  indices = btor_mem_malloc (g_btor->mm, size);

  for (i = nesting_lvl - 1; i >= 0; i--)
  {
    indices[i] = btor_var_exp (g_btor, g_index_sort, 0);
    params[i]  = btor_param_exp (g_btor, g_index_sort, 0);
  }
  fun = btor_fun_exp (g_btor, params, nesting_lvl, var);

  result = apply_and_reduce (g_btor, indices, nesting_lvl, fun);
  assert (result == var);
  btor_release_exp (g_btor, result);

  BtorNode *apply = btor_apply_exps (g_btor, indices, nesting_lvl, fun);
  result          = btor_beta_reduce_full (g_btor, apply, 0);
  assert (result == var);

  for (i = 0; i < nesting_lvl; i++)
  {
    btor_release_exp (g_btor, params[i]);
    btor_release_exp (g_btor, indices[i]);
  }

  btor_mem_free (g_btor->mm, params, size);
  btor_mem_free (g_btor->mm, indices, size);

  btor_release_exp (g_btor, fun);
  btor_release_exp (g_btor, apply);
  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
test_lambda_hashing_1 (void)
{
  BtorNode *w0, *w1, *i, *e, *a;
  BtorSortId array_sort, sort;

  init_lambda_test ();

  sort       = btor_sort_bitvec (g_btor, 32);
  array_sort = btor_sort_array (g_btor, sort, sort);

  a  = btor_array_exp (g_btor, array_sort, 0);
  i  = btor_var_exp (g_btor, sort, 0);
  e  = btor_var_exp (g_btor, sort, 0);
  w0 = btor_write_exp (g_btor, a, i, e);
  w1 = btor_write_exp (g_btor, a, i, e);
  assert (w0 == w1);

  btor_sort_release (g_btor, array_sort);
  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, w0);
  btor_release_exp (g_btor, w1);
  finish_lambda_test ();
}

static void
test_lambda_hashing_2 (void)
{
  BtorNode *ite0, *ite1, *i, *e, *a0, *a1, *eq;
  BtorSortId array_sort, sort;

  init_lambda_test ();

  sort       = btor_sort_bitvec (g_btor, 32);
  array_sort = btor_sort_array (g_btor, sort, sort);

  a0   = btor_array_exp (g_btor, array_sort, 0);
  a1   = btor_array_exp (g_btor, array_sort, 0);
  i    = btor_var_exp (g_btor, sort, 0);
  e    = btor_var_exp (g_btor, sort, 0);
  eq   = btor_eq_exp (g_btor, i, e);
  ite0 = btor_cond_exp (g_btor, eq, a0, a1);
  ite1 = btor_cond_exp (g_btor, eq, a0, a1);
  assert (ite0 == ite1);

  btor_release_exp (g_btor, ite1);
  ite1 = btor_cond_exp (g_btor, BTOR_INVERT_NODE (eq), a1, a0);
  assert (ite0 == ite1);

  btor_sort_release (g_btor, array_sort);
  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, a0);
  btor_release_exp (g_btor, a1);
  btor_release_exp (g_btor, i);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, ite0);
  btor_release_exp (g_btor, ite1);
  finish_lambda_test ();
}

/* check if hashing considers commutativity */
static void
test_lambda_hashing_3 (void)
{
  BtorNode *l0, *l1, *v, *p0, *p1, *eq0, *eq1;
  BtorSortId sort;

  init_lambda_test ();

  sort = btor_sort_bitvec (g_btor, 32);

  /* NOTE: order p0, v, p1 is important here */
  p0 = btor_param_exp (g_btor, sort, 0);
  v  = btor_var_exp (g_btor, sort, 0);
  p1 = btor_param_exp (g_btor, sort, 0);

  eq0 = btor_eq_exp (g_btor, p0, v);
  eq1 = btor_eq_exp (g_btor, v, p1);

  l0 = btor_lambda_exp (g_btor, p0, eq0);
  l1 = btor_lambda_exp (g_btor, p1, eq1);
  assert (l0 == l1);

  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, p0);
  btor_release_exp (g_btor, p1);
  btor_release_exp (g_btor, v);
  btor_release_exp (g_btor, eq0);
  btor_release_exp (g_btor, eq1);
  btor_release_exp (g_btor, l0);
  btor_release_exp (g_btor, l1);
  finish_lambda_test ();
}

static void
test_lambda_hashing_4 (void)
{
  BtorNode *f0, *f1, *p0[2], *p1[2], *eq0, *eq1;
  BtorSortId sort;

  init_lambda_test ();

  sort = btor_sort_bitvec (g_btor, 32);

  p0[0] = btor_param_exp (g_btor, sort, 0);
  p0[1] = btor_param_exp (g_btor, sort, 0);
  p1[0] = btor_param_exp (g_btor, sort, 0);
  p1[1] = btor_param_exp (g_btor, sort, 0);

  eq0 = btor_eq_exp (g_btor, p0[0], p0[1]);
  eq1 = btor_eq_exp (g_btor, p1[0], p1[1]);

  f0 = btor_fun_exp (g_btor, p0, 2, eq0);
  f1 = btor_fun_exp (g_btor, p1, 2, eq1);
  assert (f0 == f1);

  btor_sort_release (g_btor, sort);
  btor_release_exp (g_btor, p0[0]);
  btor_release_exp (g_btor, p0[1]);
  btor_release_exp (g_btor, p1[0]);
  btor_release_exp (g_btor, p1[1]);
  btor_release_exp (g_btor, eq0);
  btor_release_exp (g_btor, eq1);
  btor_release_exp (g_btor, f0);
  btor_release_exp (g_btor, f1);
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

  a = btor_var_exp (g_btor, g_elem_sort, "a");
  x = btor_param_exp (g_btor, g_elem_sort, "x");
  y = btor_param_exp (g_btor, g_elem_sort, "y");
  add = btor_add_exp (g_btor, x, y);
  fun = btor_fun_exp (g_btor, params, 2, add); 
  result = apply_and_reduce (g_btor, 1, &a, fun);

  /* expected: lambda y' . (a + y') */
  assert (btor_is_lambda_node (result));
  assert (result != fun->e[1]);
  assert (result->e[0] != fun->e[1]->e[0]);
  assert (BTOR_REAL_ADDR_NODE (result->e[1])->kind == BTOR_ADD_NODE);
  assert (BTOR_REAL_ADDR_NODE (result->e[1])->e[0] == a);
  assert (BTOR_REAL_ADDR_NODE (result->e[1])->e[1] == result->e[0]);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, fun);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, y);
  btor_release_exp (g_btor, x);
  btor_release_exp (g_btor, a);
  finish_lambda_test ();
}
#endif

/*---------------------------------------------------------------------------
 * additional tests
 *---------------------------------------------------------------------------*/

static void
test_lambda_define_fun (void)
{
  int i;
  int nesting_lvl = 1000;
  size_t size;
  BtorNode **params, **lambdas, **ands, *left, *right, *expected, *result;

  init_lambda_test ();

  size    = nesting_lvl * sizeof (BtorNode *);
  params  = btor_mem_malloc (g_btor->mm, size);
  lambdas = btor_mem_malloc (g_btor->mm, size);
  ands    = btor_mem_malloc (g_btor->mm, size - sizeof (BtorNode *));

  for (i = 0; i < nesting_lvl; i++)
    params[i] = btor_param_exp (g_btor, g_elem_sort, 0);

  assert (nesting_lvl > 1);
  left  = params[0];
  right = params[1];
  for (i = 0; i < nesting_lvl - 1; i++)
  {
    ands[i] = btor_and_exp (g_btor, left, right);

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
    lambdas[i] = btor_lambda_exp (g_btor, params[i], expected);
    expected   = lambdas[i];
  }

  result = btor_fun_exp (g_btor, params, nesting_lvl, ands[nesting_lvl - 2]);

  assert (result == expected);

  for (i = 0; i < nesting_lvl; i++)
  {
    btor_release_exp (g_btor, lambdas[i]);
    btor_release_exp (g_btor, params[i]);

    if (i < nesting_lvl - 1) btor_release_exp (g_btor, ands[i]);
  }

  btor_mem_free (g_btor->mm, params, size);
  btor_mem_free (g_btor->mm, lambdas, size);
  btor_mem_free (g_btor->mm, ands, size - sizeof (BtorNode *));
  btor_release_exp (g_btor, result);
  finish_lambda_test ();
}

void
run_lambda_tests (int argc, char **argv)
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

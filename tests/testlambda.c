#include "btorexp.h"
#include "testexp.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor   = NULL;
static int g_index_bw = 32;
static int g_elem_bw  = 16;

void
init_lambda_test (void)
{
  g_btor                 = btor_new_btor ();
  g_btor->rewrite_writes = 0;
}

void
finish_lambda_test (void)
{
  btor_delete_btor (g_btor);
}

void
init_lambda_tests (void)
{
}

/*---------------------------------------------------------------------------
 * constant lambda tests
 *---------------------------------------------------------------------------*/

static void
test_const_lambda_const (void)
{
  init_lambda_test ();
  BtorNode *param     = btor_param_exp (g_btor, g_index_bw, "p1");
  BtorNode *const_exp = btor_zero_exp (g_btor, g_elem_bw);
  BtorNode *index     = btor_var_exp (g_btor, g_index_bw, "i1");
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, const_exp);

  btor_assign_param (lambda, index);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == const_exp);

  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, const_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, index);
  btor_release_exp (g_btor, result);
  finish_lambda_test ();
}

static void
test_const_lambda_var (void)
{
  init_lambda_test ();
  BtorNode *param   = btor_param_exp (g_btor, g_index_bw, "p1");
  BtorNode *var_exp = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *index   = btor_var_exp (g_btor, g_index_bw, "i1");
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, var_exp);

  btor_assign_param (lambda, index);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == var_exp);

  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, var_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, index);
  btor_release_exp (g_btor, result);
  finish_lambda_test ();
}

static void
test_const_lambda_param (void)
{
  init_lambda_test ();
  BtorNode *param   = btor_param_exp (g_btor, g_elem_bw, "p1");
  BtorNode *var_exp = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_elem_bw, param, param);

  btor_assign_param (lambda, var_exp);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == var_exp);

  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, var_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, result);
  finish_lambda_test ();
}

static void
test_unassigned_param (void)
{
  init_lambda_test ();
  BtorNode *param   = btor_param_exp (g_btor, g_index_bw, "p1");
  BtorNode *var_exp = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, var_exp);

  BtorNode *result = btor_beta_reduce (g_btor, lambda);

  assert (result == lambda);

  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, var_exp);
  btor_release_exp (g_btor, param);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * unary expression tests
 *---------------------------------------------------------------------------*/

static void
unary_param_exp_test (BtorNode *(*func) (Btor *, BtorNode *) )
{
  init_lambda_test ();
  BtorNode *var       = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *expected  = func (g_btor, var);
  BtorNode *param     = btor_param_exp (g_btor, g_elem_bw, "p1");
  BtorNode *param_exp = func (g_btor, param);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, var);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
test_param_not (void)
{
  unary_param_exp_test (btor_not_exp);
}

static void
test_param_neg (void)
{
  unary_param_exp_test (btor_neg_exp);
}

static void
test_param_redor (void)
{
  unary_param_exp_test (btor_redor_exp);
}

static void
test_param_redxor (void)
{
  unary_param_exp_test (btor_redxor_exp);
}

static void
test_param_redand (void)
{
  unary_param_exp_test (btor_redand_exp);
}

static void
test_param_slice (void)
{
  init_lambda_test ();
  int lower          = g_elem_bw / 2 + 1;
  int upper          = g_elem_bw - 1;
  BtorNode *var      = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *param    = btor_param_exp (g_btor, g_elem_bw, "p1");
  BtorNode *expected = btor_slice_exp (g_btor, var, upper, lower);
  BtorNode *slice    = btor_slice_exp (g_btor, param, upper, lower);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, slice);

  btor_assign_param (lambda, var);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, slice);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
param_extension_test (BtorNode *(*func) (Btor *, BtorNode *, int) )
{
  init_lambda_test ();
  int lower           = g_elem_bw / 2 + 1;
  int upper           = g_elem_bw - 1;
  BtorNode *var       = btor_var_exp (g_btor, lower, "v1");
  BtorNode *param     = btor_param_exp (g_btor, lower, "p1");
  BtorNode *expected  = func (g_btor, var, upper);
  BtorNode *param_exp = func (g_btor, param, upper);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, var);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

static void
test_param_uext (void)
{
  param_extension_test (btor_uext_exp);
}

static void
test_param_sext (void)
{
  param_extension_test (btor_sext_exp);
}

/*---------------------------------------------------------------------------
 * binary expression tests
 *---------------------------------------------------------------------------*/

static void
binary_param_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
{
  init_lambda_test ();
  BtorNode *var1      = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *var2      = btor_var_exp (g_btor, g_elem_bw, "v2");
  BtorNode *expected  = func (g_btor, var1, var2);
  BtorNode *param     = btor_param_exp (g_btor, g_elem_bw, "p1");
  BtorNode *param_exp = func (g_btor, var1, param);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, var2);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, var2);
  btor_release_exp (g_btor, var1);
  finish_lambda_test ();
}

static void
test_param_implies (void)
{
  binary_param_exp_test (btor_implies_exp);
}

static void
test_param_iff (void)
{
  binary_param_exp_test (btor_iff_exp);
}

static void
test_param_xor (void)
{
  binary_param_exp_test (btor_xor_exp);
}

static void
test_param_xnor (void)
{
  binary_param_exp_test (btor_xnor_exp);
}

static void
test_param_and (void)
{
  binary_param_exp_test (btor_and_exp);
}

static void
test_param_nand (void)
{
  binary_param_exp_test (btor_nand_exp);
}

static void
test_param_or (void)
{
  binary_param_exp_test (btor_or_exp);
}

static void
test_param_nor (void)
{
  binary_param_exp_test (btor_nor_exp);
}

static void
test_param_eq (void)
{
  binary_param_exp_test (btor_eq_exp);
}

static void
test_param_ne (void)
{
  binary_param_exp_test (btor_ne_exp);
}

static void
test_param_add (void)
{
  binary_param_exp_test (btor_add_exp);
}

static void
test_param_uaddo (void)
{
  binary_param_exp_test (btor_uaddo_exp);
}

static void
test_param_saddo (void)
{
  binary_param_exp_test (btor_saddo_exp);
}

static void
test_param_mul (void)
{
  binary_param_exp_test (btor_mul_exp);
}

static void
test_param_umulo (void)
{
  binary_param_exp_test (btor_umulo_exp);
}

static void
test_param_smulo (void)
{
  binary_param_exp_test (btor_smulo_exp);
}

static void
test_param_ult (void)
{
  binary_param_exp_test (btor_ult_exp);
}

static void
test_param_slt (void)
{
  binary_param_exp_test (btor_slt_exp);
}

static void
test_param_ulte (void)
{
  binary_param_exp_test (btor_ulte_exp);
}

static void
test_param_slte (void)
{
  binary_param_exp_test (btor_slte_exp);
}

static void
test_param_ugt (void)
{
  binary_param_exp_test (btor_ugt_exp);
}

static void
test_param_sgt (void)
{
  binary_param_exp_test (btor_sgt_exp);
}

static void
test_param_ugte (void)
{
  binary_param_exp_test (btor_ugte_exp);
}

static void
test_param_sgte (void)
{
  binary_param_exp_test (btor_sgte_exp);
}

static void
test_param_sll (void)
{
  binary_param_exp_test (btor_sll_exp);
}

static void
test_param_srl (void)
{
  binary_param_exp_test (btor_srl_exp);
}

static void
test_param_sra (void)
{
  binary_param_exp_test (btor_sra_exp);
}

static void
test_param_rol (void)
{
  binary_param_exp_test (btor_rol_exp);
}

static void
test_param_ror (void)
{
  binary_param_exp_test (btor_ror_exp);
}

static void
test_param_sub (void)
{
  binary_param_exp_test (btor_sub_exp);
}

static void
test_param_usubo (void)
{
  binary_param_exp_test (btor_usubo_exp);
}

static void
test_param_ssubo (void)
{
  binary_param_exp_test (btor_ssubo_exp);
}

static void
test_param_udiv (void)
{
  binary_param_exp_test (btor_udiv_exp);
}

static void
test_param_sdiv (void)
{
  binary_param_exp_test (btor_sdiv_exp);
}

static void
test_param_sdivo (void)
{
  binary_param_exp_test (btor_sdivo_exp);
}

static void
test_param_urem (void)
{
  binary_param_exp_test (btor_urem_exp);
}

static void
test_param_srem (void)
{
  binary_param_exp_test (btor_srem_exp);
}

static void
test_param_smod (void)
{
  binary_param_exp_test (btor_smod_exp);
}

static void
test_param_concat (void)
{
  binary_param_exp_test (btor_concat_exp);
}

static void
test_param_read (void)
{
  init_lambda_test ();
  BtorNode *param    = btor_param_exp (g_btor, g_index_bw, "p1");
  BtorNode *index    = btor_var_exp (g_btor, g_elem_bw, "index");
  BtorNode *array    = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "array");
  BtorNode *expected = btor_read_exp (g_btor, array, index);
  BtorNode *read     = btor_read_exp (g_btor, array, param);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, read);

  btor_assign_param (lambda, index);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, read);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, array);
  btor_release_exp (g_btor, index);
  btor_release_exp (g_btor, param);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * ternary expression tests
 *---------------------------------------------------------------------------*/

static void
test_param_write1 (void)
{
  init_lambda_test ();
  BtorNode *i         = btor_var_exp (g_btor, g_index_bw, "i");
  BtorNode *e         = btor_var_exp (g_btor, g_elem_bw, "e");
  BtorNode *a         = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a");
  BtorNode *expected  = btor_write_exp (g_btor, a, i, e);
  BtorNode *param     = btor_param_exp (g_btor, g_elem_bw, "p");
  BtorNode *param_exp = btor_write_exp (g_btor, a, i, param);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, e);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, i);
  finish_lambda_test ();
}

static void
test_param_write2 (void)
{
  init_lambda_test ();
  BtorNode *i         = btor_var_exp (g_btor, g_index_bw, "i");
  BtorNode *e         = btor_var_exp (g_btor, g_elem_bw, "e");
  BtorNode *a         = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a");
  BtorNode *expected  = btor_write_exp (g_btor, a, i, e);
  BtorNode *param     = btor_param_exp (g_btor, g_index_bw, "p");
  BtorNode *param_exp = btor_write_exp (g_btor, a, param, e);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, e);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, e);
  btor_release_exp (g_btor, i);
  finish_lambda_test ();
}

static void
test_param_bcond (void)
{
  init_lambda_test ();
  BtorNode *var       = btor_var_exp (g_btor, 1, "v1");
  BtorNode *param     = btor_param_exp (g_btor, 1, "p");
  BtorNode *e_if      = btor_var_exp (g_btor, g_elem_bw, "v2");
  BtorNode *e_else    = btor_var_exp (g_btor, g_elem_bw, "v3");
  BtorNode *expected  = btor_cond_exp (g_btor, var, e_if, e_else);
  BtorNode *param_exp = btor_cond_exp (g_btor, param, e_if, e_else);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, var);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, e_else);
  btor_release_exp (g_btor, e_if);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

/* NOTE: right now, we have to use a read on the array condition as lambdas
 * return bit-vectors only. */
static void
test_param_acond (void)
{
  init_lambda_test ();
  BtorNode *var           = btor_var_exp (g_btor, g_index_bw, "v1");
  BtorNode *index         = btor_var_exp (g_btor, g_index_bw, "i");
  BtorNode *expected_cond = btor_eq_exp (g_btor, var, index);
  BtorNode *e_if   = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a1");
  BtorNode *e_else = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a2");
  BtorNode *expected_acond =
      btor_cond_exp (g_btor, expected_cond, e_if, e_else);
  BtorNode *expected = btor_read_exp (g_btor, expected_acond, var);

  BtorNode *param       = btor_param_exp (g_btor, g_index_bw, "p");
  BtorNode *param_cond  = btor_eq_exp (g_btor, param, index);
  BtorNode *param_acond = btor_cond_exp (g_btor, param_cond, e_if, e_else);
  BtorNode *param_exp   = btor_read_exp (g_btor, param_acond, param);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, param_exp);

  btor_assign_param (lambda, var);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda);
  btor_release_exp (g_btor, param_exp);
  btor_release_exp (g_btor, param_acond);
  btor_release_exp (g_btor, param_cond);
  btor_release_exp (g_btor, param);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, e_else);
  btor_release_exp (g_btor, e_if);
  btor_release_exp (g_btor, expected_cond);
  btor_release_exp (g_btor, index);
  btor_release_exp (g_btor, var);
  finish_lambda_test ();
}

// TODO: arrays as arguments (not possible yet)

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

static void
test_reduce_write1 (void)
{
  init_lambda_test ();
  BtorNode *a     = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a");
  BtorNode *i     = btor_var_exp (g_btor, g_index_bw, "i");
  BtorNode *e     = btor_var_exp (g_btor, g_elem_bw, "e");
  BtorNode *param = btor_param_exp (g_btor, g_index_bw, "p");
  BtorNode *read  = btor_read_exp (g_btor, a, param);
  BtorNode *eq    = btor_eq_exp (g_btor, param, i);
  BtorNode *cond  = btor_cond_exp (g_btor, eq, e, read);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, cond);

  btor_assign_param (lambda, i);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

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
test_reduce_write2 (void)
{
  init_lambda_test ();
  BtorNode *a        = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a");
  BtorNode *i        = btor_var_exp (g_btor, g_index_bw, "i");
  BtorNode *e        = btor_var_exp (g_btor, g_elem_bw, "e");
  BtorNode *param    = btor_param_exp (g_btor, g_index_bw, "p");
  BtorNode *read     = btor_read_exp (g_btor, a, param);
  BtorNode *expected = btor_read_exp (g_btor, a, i);
  BtorNode *eq       = btor_ne_exp (g_btor, param, i);
  BtorNode *cond     = btor_cond_exp (g_btor, eq, e, read);
  BtorNode *lambda =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param, cond);

  btor_assign_param (lambda, i);
  BtorNode *result = btor_beta_reduce (g_btor, lambda);
  btor_unassign_param (lambda);

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
test_reduce_nested_writes (void)
{
  init_lambda_test ();
  BtorNode *i = btor_var_exp (g_btor, g_index_bw, "i");
  /* w1 = write (a, i, e2) */
  BtorNode *a      = btor_array_exp (g_btor, g_elem_bw, g_index_bw, "a");
  BtorNode *e2     = btor_var_exp (g_btor, g_elem_bw, "e2");
  BtorNode *param2 = btor_param_exp (g_btor, g_index_bw, "p2");
  BtorNode *read2  = btor_read_exp (g_btor, a, param2);
  BtorNode *eq2    = btor_eq_exp (g_btor, param2, i);
  BtorNode *cond2  = btor_cond_exp (g_btor, eq2, e2, read2);
  BtorNode *lambda2 =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param2, cond2);
  /* w2 = write (w1, not i, e1) */
  BtorNode *e1     = btor_var_exp (g_btor, g_elem_bw, "e1");
  BtorNode *param1 = btor_param_exp (g_btor, g_index_bw, "p1");
  BtorNode *read1  = btor_read_exp (g_btor, lambda2, param1);
  BtorNode *eq1    = btor_ne_exp (g_btor, param1, i);
  BtorNode *cond1  = btor_cond_exp (g_btor, eq1, e1, read1);
  BtorNode *lambda1 =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param1, cond1);

  btor_assign_param (lambda1, i);
  BtorNode *result = btor_beta_reduce (g_btor, lambda1);
  btor_unassign_param (lambda1);

  assert (result == e2);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda1);
  btor_release_exp (g_btor, cond1);
  btor_release_exp (g_btor, eq1);
  btor_release_exp (g_btor, read1);
  btor_release_exp (g_btor, param1);
  btor_release_exp (g_btor, e1);
  btor_release_exp (g_btor, lambda2);
  btor_release_exp (g_btor, cond2);
  btor_release_exp (g_btor, eq2);
  btor_release_exp (g_btor, read2);
  btor_release_exp (g_btor, param2);
  btor_release_exp (g_btor, e2);
  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, i);
  finish_lambda_test ();
}

/* lambda x . (lambda y . (x + y)) */
static void
test_reduce_nested_lambdas_add1 (void)
{
  init_lambda_test ();
  BtorNode *var1     = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *var2     = btor_var_exp (g_btor, g_elem_bw, "v2");
  BtorNode *expected = btor_add_exp (g_btor, var1, var2);
  BtorNode *param1   = btor_param_exp (g_btor, g_elem_bw, "p1");
  BtorNode *param2   = btor_param_exp (g_btor, g_elem_bw, "p2");
  BtorNode *add      = btor_add_exp (g_btor, param1, param2);
  BtorNode *lambda2 =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param2, add);
  BtorNode *lambda1 =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param1, lambda2);

  btor_assign_param (lambda2, var2);
  btor_assign_param (lambda1, var1);
  BtorNode *result = btor_beta_reduce (g_btor, lambda1);
  btor_unassign_param (lambda2);
  btor_unassign_param (lambda1);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda1);
  btor_release_exp (g_btor, lambda2);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, param2);
  btor_release_exp (g_btor, param1);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, var2);
  btor_release_exp (g_btor, var1);
  finish_lambda_test ();
}

// FIXME: x + read (lambda) (else it's x + array)
/* lambda x . (x + lambda y . y) */
static void
test_reduce_nested_lambdas_add2 (void)
{
  init_lambda_test ();
  BtorNode *var1     = btor_var_exp (g_btor, g_elem_bw, "v1");
  BtorNode *var2     = btor_var_exp (g_btor, g_elem_bw, "v2");
  BtorNode *expected = btor_add_exp (g_btor, var1, var2);
  BtorNode *param1   = btor_param_exp (g_btor, g_elem_bw, "p1");
  BtorNode *param2   = btor_param_exp (g_btor, g_elem_bw, "p2");
  BtorNode *lambda2 =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param2, param2);
  BtorNode *add = btor_add_exp (g_btor, param1, lambda2);
  BtorNode *lambda1 =
      btor_lambda_exp (g_btor, g_elem_bw, g_index_bw, param1, add);

  btor_assign_param (lambda2, var2);
  btor_assign_param (lambda1, var1);
  BtorNode *result = btor_beta_reduce (g_btor, lambda1);
  btor_unassign_param (lambda2);
  btor_unassign_param (lambda1);

  assert (result == expected);

  btor_release_exp (g_btor, result);
  btor_release_exp (g_btor, lambda1);
  btor_release_exp (g_btor, lambda2);
  btor_release_exp (g_btor, add);
  btor_release_exp (g_btor, param2);
  btor_release_exp (g_btor, param1);
  btor_release_exp (g_btor, expected);
  btor_release_exp (g_btor, var2);
  btor_release_exp (g_btor, var1);
  finish_lambda_test ();
}

/*---------------------------------------------------------------------------
 * additional tests
 *---------------------------------------------------------------------------*/

void
run_lambda_tests (int argc, char **argv)
{
  /* constant lambda tests */
  BTOR_RUN_TEST (const_lambda_const);
  BTOR_RUN_TEST (const_lambda_var);
  BTOR_RUN_TEST (const_lambda_param);
  BTOR_RUN_TEST (unassigned_param);
  /* unary exp tests */
  BTOR_RUN_TEST (param_not);
  BTOR_RUN_TEST (param_neg);
  BTOR_RUN_TEST (param_redor);
  BTOR_RUN_TEST (param_redxor);
  BTOR_RUN_TEST (param_redand);
  BTOR_RUN_TEST (param_slice);
  BTOR_RUN_TEST (param_uext);
  BTOR_RUN_TEST (param_sext);
  /* binary exp tests */
  BTOR_RUN_TEST (param_implies);
  BTOR_RUN_TEST (param_iff);
  BTOR_RUN_TEST (param_xor);
  BTOR_RUN_TEST (param_xnor);
  BTOR_RUN_TEST (param_and);
  BTOR_RUN_TEST (param_nand);
  BTOR_RUN_TEST (param_or);
  BTOR_RUN_TEST (param_nor);
  BTOR_RUN_TEST (param_eq);
  BTOR_RUN_TEST (param_ne);
  BTOR_RUN_TEST (param_add);
  BTOR_RUN_TEST (param_uaddo);
  BTOR_RUN_TEST (param_saddo);
  BTOR_RUN_TEST (param_mul);
  BTOR_RUN_TEST (param_umulo);
  BTOR_RUN_TEST (param_smulo);
  BTOR_RUN_TEST (param_ult);
  BTOR_RUN_TEST (param_slt);
  BTOR_RUN_TEST (param_ulte);
  BTOR_RUN_TEST (param_slte);
  BTOR_RUN_TEST (param_ugt);
  BTOR_RUN_TEST (param_sgt);
  BTOR_RUN_TEST (param_ugte);
  BTOR_RUN_TEST (param_sgte);
  BTOR_RUN_TEST (param_sll);
  BTOR_RUN_TEST (param_srl);
  BTOR_RUN_TEST (param_sra);
  BTOR_RUN_TEST (param_rol);
  BTOR_RUN_TEST (param_ror);
  BTOR_RUN_TEST (param_sub);
  BTOR_RUN_TEST (param_usubo);
  BTOR_RUN_TEST (param_ssubo);
  BTOR_RUN_TEST (param_udiv);
  BTOR_RUN_TEST (param_sdiv);
  BTOR_RUN_TEST (param_sdivo);
  BTOR_RUN_TEST (param_urem);
  BTOR_RUN_TEST (param_srem);
  BTOR_RUN_TEST (param_smod);
  BTOR_RUN_TEST (param_concat);
  BTOR_RUN_TEST (param_read);
  /* ternary exp tests */
  BTOR_RUN_TEST (param_write1);
  BTOR_RUN_TEST (param_write2);
  BTOR_RUN_TEST (param_bcond);
  BTOR_RUN_TEST (param_acond);

  /* full reduction tests (with reduced expressions) */
  BTOR_RUN_TEST (reduce_write1);
  BTOR_RUN_TEST (reduce_write2);
  BTOR_RUN_TEST (reduce_nested_writes);

  /* partial reduction tests */

  /* additional tests */
  BTOR_RUN_TEST (reduce_nested_lambdas_add1);
  // FIXME: BTOR_RUN_TEST (reduce_nested_lambdas_add2);
}

void
finish_lambda_tests (void)
{
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btorbeta.h"
#include "btorcore.h"
#include "btorexp.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"
}

class TestLambda : public TestBtor
{
 protected:
  void SetUp () override
  {
    TestBtor::SetUp ();
    d_elem_sort  = btor_sort_bv (d_btor, s_elem_bw);
    d_index_sort = btor_sort_bv (d_btor, s_index_bw);
    d_array_sort = btor_sort_array (d_btor, d_index_sort, d_elem_sort);
  }

  void TearDown () override
  {
    if (d_elem_sort)
    {
      btor_sort_release (d_btor, d_elem_sort);
      d_elem_sort = 0;
    }
    if (d_index_sort)
    {
      btor_sort_release (d_btor, d_index_sort);
      d_index_sort = 0;
    }
    if (d_array_sort)
    {
      btor_sort_release (d_btor, d_array_sort);
      d_array_sort = 0;
    }
    TestBtor::TearDown ();
  }

  void assert_parameterized (int32_t argc, ...)
  {
    int32_t i;
    va_list ap;
    BtorNode *e;

    va_start (ap, argc);
    for (i = 0; i < argc; i++)
    {
      e = va_arg (ap, BtorNode *);
      ASSERT_TRUE (btor_node_real_addr (e)->parameterized);
    }
    va_end (ap);
  }

  void assert_not_parameterized (int32_t argc, ...)
  {
    int32_t i;
    va_list ap;
    BtorNode *e;

    va_start (ap, argc);
    for (i = 0; i < argc; i++)
    {
      e = va_arg (ap, BtorNode *);
      ASSERT_FALSE (btor_node_real_addr (e)->parameterized);
    }
    va_end (ap);
  }

  BtorNode *apply_and_reduce (Btor *btor,
                              BtorNode *args[],
                              int32_t argc,
                              BtorNode *lambda)
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

  void unary_param_exp_test (BtorNode *(*func) (Btor *, BtorNode *) )
  {
    BtorNode *result;
    BtorNode *var, *expected, *param, *param_exp, *lambda;
    BtorSortId lambda_index_sort;

    lambda_index_sort = d_elem_sort;
    var               = btor_exp_var (d_btor, d_elem_sort, "v1");
    expected          = func (d_btor, var);
    param             = btor_exp_param (d_btor, lambda_index_sort, "p1");
    param_exp         = func (d_btor, param);
    lambda            = btor_exp_lambda (d_btor, param, param_exp);
    result            = apply_and_reduce (d_btor, &var, 1, lambda);

    ASSERT_EQ (result, expected);
    assert_parameterized (2, param, param_exp);
    assert_not_parameterized (4, var, expected, lambda, result);

    btor_node_release (d_btor, result);
    btor_node_release (d_btor, lambda);
    btor_node_release (d_btor, param_exp);
    btor_node_release (d_btor, param);
    btor_node_release (d_btor, expected);
    btor_node_release (d_btor, var);
  }

  void param_extension_test (BtorNode *(*func) (Btor *, BtorNode *, uint32_t))
  {
    BtorNode *result;
    BtorNode *var, *param, *expected, *param_exp, *lambda;
    BtorSortId lower_sort, upper_sort;
    int32_t lower, upper;

    lower      = s_elem_bw / 2 + 1;
    upper      = s_elem_bw - 1;
    lower_sort = btor_sort_bv (d_btor, lower);
    upper_sort = btor_sort_bv (d_btor, upper);

    var       = btor_exp_var (d_btor, lower_sort, "v1");
    param     = btor_exp_param (d_btor, lower_sort, "p1");
    expected  = func (d_btor, var, upper_sort);
    param_exp = func (d_btor, param, upper_sort);
    lambda    = btor_exp_lambda (d_btor, param, param_exp);
    result    = apply_and_reduce (d_btor, &var, 1, lambda);

    ASSERT_EQ (result, expected);
    assert_parameterized (2, param, param_exp);
    assert_not_parameterized (4, var, expected, lambda, result);

    btor_sort_release (d_btor, lower_sort);
    btor_sort_release (d_btor, upper_sort);
    btor_node_release (d_btor, result);
    btor_node_release (d_btor, lambda);
    btor_node_release (d_btor, expected);
    btor_node_release (d_btor, param_exp);
    btor_node_release (d_btor, param);
    btor_node_release (d_btor, var);
  }

  /* (lambda x . bin_exp (x, v2)) (v1) or (lambda x . bin_exp (v1, x)) (v2) */
  void binary_param_exp_test (
      int32_t param_pos, BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
  {
    assert (param_pos == 0 || param_pos == 1);

    BtorNode *result;
    BtorNode *param_exp, *v1, *v2, *expected, *x;
    BtorSortId v1_sort, v2_sort, x_sort;
    int32_t x_bw, v1_bw, v2_bw;

    v1_bw = s_elem_bw;
    v2_bw = s_elem_bw;

    if (func == btor_exp_implies || func == btor_exp_iff)
    {
      v1_bw = 1;
      v2_bw = 1;
    }

    x_bw = (param_pos == 0) ? v1_bw : v2_bw;

    v1_sort = btor_sort_bv (d_btor, v1_bw);
    v2_sort = btor_sort_bv (d_btor, v2_bw);
    x_sort  = btor_sort_bv (d_btor, x_bw);

    v1       = btor_exp_var (d_btor, v1_sort, "v1");
    v2       = btor_exp_var (d_btor, v2_sort, "v2");
    expected = func (d_btor, v1, v2);
    x        = btor_exp_param (d_btor, x_sort, "x");

    if (param_pos == 0)
      param_exp = func (d_btor, x, v2);
    else
      param_exp = func (d_btor, v1, x);

    BtorNode *lambda = btor_exp_lambda (d_btor, x, param_exp);

    if (param_pos == 0)
      result = apply_and_reduce (d_btor, &v1, 1, lambda);
    else
      result = apply_and_reduce (d_btor, &v2, 1, lambda);

    ASSERT_EQ (result, expected);
    assert_parameterized (2, x, param_exp);
    assert_not_parameterized (5, v1, v2, expected, lambda, result);

    btor_sort_release (d_btor, v1_sort);
    btor_sort_release (d_btor, v2_sort);
    btor_sort_release (d_btor, x_sort);
    btor_node_release (d_btor, result);
    btor_node_release (d_btor, lambda);
    btor_node_release (d_btor, param_exp);
    btor_node_release (d_btor, x);
    btor_node_release (d_btor, expected);
    btor_node_release (d_btor, v2);
    btor_node_release (d_btor, v1);
  }

  static constexpr int32_t s_index_bw = 32;
  static constexpr int32_t s_elem_bw  = 16;

  BtorIntHashTable *d_htable = nullptr;
  BtorSortId d_elem_sort     = 0;
  BtorSortId d_index_sort    = 0;
  BtorSortId d_array_sort    = 0;
};

/*---------------------------------------------------------------------------
 * constant lambda tests
 *---------------------------------------------------------------------------*/

TEST_F (TestLambda, const_lambda_const)
{
  BtorNode *result;
  BtorNode *x, *c, *i, *lambda;

  x      = btor_exp_param (d_btor, d_index_sort, "x");
  c      = btor_exp_bv_zero (d_btor, d_elem_sort);
  i      = btor_exp_var (d_btor, d_index_sort, "i");
  lambda = btor_exp_lambda (d_btor, x, c);

  /* (lambda x . 0) (i) */
  result = apply_and_reduce (d_btor, &i, 1, lambda);
  ASSERT_EQ (result, c);
  assert_not_parameterized (1, result);
  btor_node_release (d_btor, result);

  /* (lambda x . 0) () */
  result = apply_and_reduce (d_btor, 0, 0, lambda);
  ASSERT_EQ (result, c);
  assert_parameterized (1, x);
  assert_not_parameterized (4, result, c, i, lambda);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, c);
  btor_node_release (d_btor, x);
}

TEST_F (TestLambda, const_lambda_var)
{
  BtorNode *result;
  BtorNode *x, *a, *i, *lambda;

  x      = btor_exp_param (d_btor, d_index_sort, "x");
  a      = btor_exp_var (d_btor, d_elem_sort, "a");
  i      = btor_exp_var (d_btor, d_index_sort, "i");
  lambda = btor_exp_lambda (d_btor, x, a);

  /* (lambda x . a) (i) */
  result = apply_and_reduce (d_btor, &i, 1, lambda);
  ASSERT_EQ (result, a);
  assert_not_parameterized (1, result);
  btor_node_release (d_btor, result);

  /* (lambda x . a) () */
  result = apply_and_reduce (d_btor, 0, 0, lambda);
  ASSERT_EQ (result, a);
  assert_parameterized (1, x);
  assert_not_parameterized (4, result, lambda, i, a);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, i);
}

TEST_F (TestLambda, const_lambda_param)
{
  BtorNode *result;
  BtorNode *x, *a, *lambda;

  x      = btor_exp_param (d_btor, d_elem_sort, "x");
  a      = btor_exp_var (d_btor, d_elem_sort, "a");
  lambda = btor_exp_lambda (d_btor, x, x);

  /* (lambda x . x) (a) */
  result = apply_and_reduce (d_btor, &a, 1, lambda);
  ASSERT_EQ (result, a);
  assert_not_parameterized (1, result);
  btor_node_release (d_btor, result);

  /* (lambda x . x) () */
  result = apply_and_reduce (d_btor, 0, 0, lambda);
  ASSERT_EQ (result, lambda);
  assert_parameterized (1, x);
  assert_not_parameterized (3, result, lambda, a);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, x);
}

TEST_F (TestLambda, const_lambda_negated)
{
  BtorNode *result;
  BtorNode *a, *not_a, *x, *not_x, *lambda;

  a      = btor_exp_var (d_btor, d_elem_sort, "a");
  not_a  = btor_exp_bv_not (d_btor, a);
  x      = btor_exp_param (d_btor, d_elem_sort, "x");
  not_x  = btor_exp_bv_not (d_btor, x);
  lambda = btor_exp_lambda (d_btor, x, not_x);

  /* (lambda x . not (x)) (not (a)) */
  result = apply_and_reduce (d_btor, &not_a, 1, lambda);
  ASSERT_EQ (result, a);
  assert_not_parameterized (1, result);
  btor_node_release (d_btor, result);

  /* (lambda x . not (x)) () */
  result = apply_and_reduce (d_btor, 0, 0, lambda);
  ASSERT_EQ (result, lambda);
  assert_parameterized (2, x, not_x);
  assert_not_parameterized (4, result, lambda, not_a, a);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, not_x);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, not_a);
  btor_node_release (d_btor, a);
}

/* (lambda x . a) () */
TEST_F (TestLambda, unassigned_param)
{
  BtorNode *result;
  BtorNode *x, *a, *lambda;

  x      = btor_exp_param (d_btor, d_index_sort, "x");
  a      = btor_exp_var (d_btor, d_elem_sort, "a");
  lambda = btor_exp_lambda (d_btor, x, a);
  result = apply_and_reduce (d_btor, 0, 0, lambda);

  ASSERT_EQ (result, a);
  assert_parameterized (1, x);
  assert_not_parameterized (3, result, lambda, a);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, x);
}

/*---------------------------------------------------------------------------
 * unary expression tests
 *---------------------------------------------------------------------------*/

TEST_F (TestLambda, param_not) { unary_param_exp_test (btor_exp_bv_not); }

TEST_F (TestLambda, param_neg) { unary_param_exp_test (btor_exp_bv_neg); }

TEST_F (TestLambda, param_redor) { unary_param_exp_test (btor_exp_bv_redor); }

TEST_F (TestLambda, param_redxor) { unary_param_exp_test (btor_exp_bv_redxor); }

TEST_F (TestLambda, param_redand) { unary_param_exp_test (btor_exp_bv_redand); }

TEST_F (TestLambda, param_slice)
{
  BtorNode *result;
  BtorNode *var, *param, *expected, *slice, *lambda;
  int32_t lower, upper;

  lower = s_elem_bw / 2 + 1;
  upper = s_elem_bw - 1;

  var      = btor_exp_var (d_btor, d_elem_sort, "v1");
  param    = btor_exp_param (d_btor, d_elem_sort, "p1");
  expected = btor_exp_bv_slice (d_btor, var, upper, lower);
  slice    = btor_exp_bv_slice (d_btor, param, upper, lower);
  lambda   = btor_exp_lambda (d_btor, param, slice);
  result   = apply_and_reduce (d_btor, &var, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, param, slice);
  assert_not_parameterized (4, var, expected, lambda, result);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, slice);
  btor_node_release (d_btor, param);
  btor_node_release (d_btor, var);
}

TEST_F (TestLambda, param_uext) { param_extension_test (btor_exp_bv_uext); }

TEST_F (TestLambda, param_sext) { param_extension_test (btor_exp_bv_sext); }

/*---------------------------------------------------------------------------
 * binary expression tests
 *---------------------------------------------------------------------------*/

TEST_F (TestLambda, param_implies)
{
  binary_param_exp_test (0, btor_exp_implies);
  binary_param_exp_test (1, btor_exp_implies);
}

TEST_F (TestLambda, param_iff)
{
  binary_param_exp_test (0, btor_exp_iff);
  binary_param_exp_test (1, btor_exp_iff);
}

TEST_F (TestLambda, param_xor)
{
  binary_param_exp_test (0, btor_exp_bv_xor);
  binary_param_exp_test (1, btor_exp_bv_xor);
}

TEST_F (TestLambda, param_xnor)
{
  binary_param_exp_test (0, btor_exp_bv_xnor);
  binary_param_exp_test (1, btor_exp_bv_xnor);
}

TEST_F (TestLambda, param_and)
{
  binary_param_exp_test (0, btor_exp_bv_and);
  binary_param_exp_test (1, btor_exp_bv_and);
}

TEST_F (TestLambda, param_nand)
{
  binary_param_exp_test (0, btor_exp_bv_nand);
  binary_param_exp_test (1, btor_exp_bv_nand);
}

TEST_F (TestLambda, param_or)
{
  binary_param_exp_test (0, btor_exp_bv_or);
  binary_param_exp_test (1, btor_exp_bv_or);
}

TEST_F (TestLambda, param_nor)
{
  binary_param_exp_test (0, btor_exp_bv_nor);
  binary_param_exp_test (1, btor_exp_bv_nor);
}

TEST_F (TestLambda, param_eq)
{
  binary_param_exp_test (0, btor_exp_eq);
  binary_param_exp_test (1, btor_exp_eq);
}

TEST_F (TestLambda, param_ne)
{
  binary_param_exp_test (0, btor_exp_ne);
  binary_param_exp_test (1, btor_exp_ne);
}

TEST_F (TestLambda, param_add)
{
  binary_param_exp_test (0, btor_exp_bv_add);
  binary_param_exp_test (1, btor_exp_bv_add);
}

TEST_F (TestLambda, param_uaddo)
{
  binary_param_exp_test (0, btor_exp_bv_uaddo);
  binary_param_exp_test (1, btor_exp_bv_uaddo);
}

TEST_F (TestLambda, param_saddo)
{
  binary_param_exp_test (0, btor_exp_bv_saddo);
  binary_param_exp_test (1, btor_exp_bv_saddo);
}

TEST_F (TestLambda, param_mul)
{
  binary_param_exp_test (0, btor_exp_bv_mul);
  binary_param_exp_test (1, btor_exp_bv_mul);
}

TEST_F (TestLambda, param_umulo)
{
  binary_param_exp_test (0, btor_exp_bv_umulo);
  binary_param_exp_test (1, btor_exp_bv_umulo);
}

TEST_F (TestLambda, param_smulo)
{
  binary_param_exp_test (0, btor_exp_bv_smulo);
  binary_param_exp_test (1, btor_exp_bv_smulo);
}

TEST_F (TestLambda, param_ult)
{
  binary_param_exp_test (0, btor_exp_bv_ult);
  binary_param_exp_test (1, btor_exp_bv_ult);
}

TEST_F (TestLambda, param_slt)
{
  binary_param_exp_test (0, btor_exp_bv_slt);
  binary_param_exp_test (1, btor_exp_bv_slt);
}

TEST_F (TestLambda, param_ulte)
{
  binary_param_exp_test (0, btor_exp_bv_ulte);
  binary_param_exp_test (1, btor_exp_bv_ulte);
}

TEST_F (TestLambda, param_slte)
{
  binary_param_exp_test (0, btor_exp_bv_slte);
  binary_param_exp_test (1, btor_exp_bv_slte);
}

TEST_F (TestLambda, param_ugt)
{
  binary_param_exp_test (0, btor_exp_bv_ugt);
  binary_param_exp_test (1, btor_exp_bv_ugt);
}

TEST_F (TestLambda, param_sgt)
{
  binary_param_exp_test (0, btor_exp_bv_sgt);
  binary_param_exp_test (1, btor_exp_bv_sgt);
}

TEST_F (TestLambda, param_ugte)
{
  binary_param_exp_test (0, btor_exp_bv_ugte);
  binary_param_exp_test (1, btor_exp_bv_ugte);
}

TEST_F (TestLambda, param_sgte)
{
  binary_param_exp_test (0, btor_exp_bv_sgte);
  binary_param_exp_test (1, btor_exp_bv_sgte);
}

TEST_F (TestLambda, param_sll)
{
  binary_param_exp_test (0, btor_exp_bv_sll);
  binary_param_exp_test (1, btor_exp_bv_sll);
}

TEST_F (TestLambda, param_srl)
{
  binary_param_exp_test (0, btor_exp_bv_srl);
  binary_param_exp_test (1, btor_exp_bv_srl);
}

TEST_F (TestLambda, param_sra)
{
  binary_param_exp_test (0, btor_exp_bv_sra);
  binary_param_exp_test (1, btor_exp_bv_sra);
}

TEST_F (TestLambda, param_rol)
{
  binary_param_exp_test (0, btor_exp_bv_rol);
  binary_param_exp_test (1, btor_exp_bv_rol);
}

TEST_F (TestLambda, param_ror)
{
  binary_param_exp_test (0, btor_exp_bv_ror);
  binary_param_exp_test (1, btor_exp_bv_ror);
}

TEST_F (TestLambda, param_sub)
{
  binary_param_exp_test (0, btor_exp_bv_sub);
  binary_param_exp_test (1, btor_exp_bv_sub);
}

TEST_F (TestLambda, param_usubo)
{
  binary_param_exp_test (0, btor_exp_bv_usubo);
  binary_param_exp_test (1, btor_exp_bv_usubo);
}

TEST_F (TestLambda, param_ssubo)
{
  binary_param_exp_test (0, btor_exp_bv_ssubo);
  binary_param_exp_test (1, btor_exp_bv_ssubo);
}

TEST_F (TestLambda, param_udiv)
{
  binary_param_exp_test (0, btor_exp_bv_udiv);
  binary_param_exp_test (1, btor_exp_bv_udiv);
}

TEST_F (TestLambda, param_sdiv)
{
  binary_param_exp_test (0, btor_exp_bv_sdiv);
  binary_param_exp_test (1, btor_exp_bv_sdiv);
}

TEST_F (TestLambda, param_sdivo)
{
  binary_param_exp_test (0, btor_exp_bv_sdivo);
  binary_param_exp_test (1, btor_exp_bv_sdivo);
}

TEST_F (TestLambda, param_urem)
{
  binary_param_exp_test (0, btor_exp_bv_urem);
  binary_param_exp_test (1, btor_exp_bv_urem);
}

TEST_F (TestLambda, param_srem)
{
  binary_param_exp_test (0, btor_exp_bv_srem);
  binary_param_exp_test (1, btor_exp_bv_srem);
}

TEST_F (TestLambda, param_smod)
{
  binary_param_exp_test (0, btor_exp_bv_smod);
  binary_param_exp_test (1, btor_exp_bv_smod);
}

TEST_F (TestLambda, param_concat)
{
  binary_param_exp_test (0, btor_exp_bv_concat);
  binary_param_exp_test (1, btor_exp_bv_concat);
}

/* (lambda x . read(a, x)) (i) */
TEST_F (TestLambda, param_read)
{
  BtorNode *result;
  BtorNode *x, *i, *a, *expected, *read, *lambda;

  x        = btor_exp_param (d_btor, d_index_sort, "x");
  i        = btor_exp_var (d_btor, d_index_sort, "i");
  a        = btor_exp_array (d_btor, d_array_sort, "a");
  expected = btor_exp_read (d_btor, a, i);
  read     = btor_exp_read (d_btor, a, x);
  lambda   = btor_exp_lambda (d_btor, x, read);
  result   = apply_and_reduce (d_btor, &i, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, x, read);
  assert_not_parameterized (5, result, lambda, expected, a, i);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, read);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, x);
}

/*---------------------------------------------------------------------------
 * ternary expression tests
 *---------------------------------------------------------------------------*/

// !!! currently broken as we do not support lambda hashing yet
/* (lambda x . write (a, i, x)) (e) */
TEST_F (TestLambda, DISABLED_param_write1)
{
  BtorNode *result;
  BtorNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  i         = btor_exp_var (d_btor, d_index_sort, "i");
  e         = btor_exp_var (d_btor, d_elem_sort, "e");
  a         = btor_exp_array (d_btor, d_array_sort, "a");
  expected  = btor_exp_lambda_write (d_btor, a, i, e);
  x         = btor_exp_param (d_btor, d_elem_sort, "x");
  param_exp = btor_exp_lambda_write (d_btor, a, i, x);
  lambda    = btor_exp_lambda (d_btor, x, param_exp);
  result    = apply_and_reduce (d_btor, &e, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, a, e, i);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, param_exp);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, e);
  btor_node_release (d_btor, i);
}

// !!! currently broken as we do not support lambda hashing yet
/* (lambda x . write (a, x, e)) (i) */
TEST_F (TestLambda, DISABLED_param_write2)
{
  BtorNode *result;
  BtorNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  i         = btor_exp_var (d_btor, d_index_sort, "i");
  e         = btor_exp_var (d_btor, d_elem_sort, "e");
  a         = btor_exp_array (d_btor, d_array_sort, "a");
  expected  = btor_exp_lambda_write (d_btor, a, i, e);
  x         = btor_exp_param (d_btor, d_index_sort, "p");
  param_exp = btor_exp_lambda_write (d_btor, a, x, e);
  lambda    = btor_exp_lambda (d_btor, x, param_exp);
  result    = apply_and_reduce (d_btor, &i, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, a, e, i);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, param_exp);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, e);
  btor_node_release (d_btor, i);
}

/* (lambda x . x ? v2 : v3) (v1) */
TEST_F (TestLambda, param_bcond1)
{
  BtorNode *result;
  BtorNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BtorSortId sort;

  sort      = btor_sort_bv (d_btor, 1);
  v1        = btor_exp_var (d_btor, sort, "v1");
  x         = btor_exp_param (d_btor, sort, "x");
  v2        = btor_exp_var (d_btor, d_elem_sort, "v2");
  v3        = btor_exp_var (d_btor, d_elem_sort, "v3");
  expected  = btor_exp_cond (d_btor, v1, v2, v3);
  param_exp = btor_exp_cond (d_btor, x, v2, v3);
  lambda    = btor_exp_lambda (d_btor, x, param_exp);
  result    = apply_and_reduce (d_btor, &v1, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, param_exp);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, v3);
  btor_node_release (d_btor, v2);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, v1);
}

/* (lambda x . v1 ? x : v3) (v2) */
TEST_F (TestLambda, param_bcond2)
{
  BtorNode *result;
  BtorNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BtorSortId sort;

  sort      = btor_sort_bv (d_btor, 1);
  v1        = btor_exp_var (d_btor, sort, "v1");
  x         = btor_exp_param (d_btor, d_elem_sort, "x");
  v2        = btor_exp_var (d_btor, d_elem_sort, "v2");
  v3        = btor_exp_var (d_btor, d_elem_sort, "v3");
  expected  = btor_exp_cond (d_btor, v1, v2, v3);
  param_exp = btor_exp_cond (d_btor, v1, x, v3);
  lambda    = btor_exp_lambda (d_btor, x, param_exp);
  result    = apply_and_reduce (d_btor, &v2, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, param_exp);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, v3);
  btor_node_release (d_btor, v2);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, v1);
}

/* (lambda x . v1 ? v2 : x) (v3) */
TEST_F (TestLambda, param_bcond3)
{
  BtorNode *result;
  BtorNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BtorSortId sort;

  sort      = btor_sort_bv (d_btor, 1);
  v1        = btor_exp_var (d_btor, sort, "v1");
  x         = btor_exp_param (d_btor, d_elem_sort, "x");
  v2        = btor_exp_var (d_btor, d_elem_sort, "v2");
  v3        = btor_exp_var (d_btor, d_elem_sort, "v3");
  expected  = btor_exp_cond (d_btor, v1, v2, v3);
  param_exp = btor_exp_cond (d_btor, v1, v2, x);
  lambda    = btor_exp_lambda (d_btor, x, param_exp);
  result    = apply_and_reduce (d_btor, &v3, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (2, x, param_exp);
  assert_not_parameterized (6, result, lambda, expected, v3, v2, v1);

  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, param_exp);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, v3);
  btor_node_release (d_btor, v2);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, v1);
}

/* NOTE: right now, we have to use a read on the array condition as lambdas
 * return bit-vectors only. */
TEST_F (TestLambda, param_acond)
{
  BtorNode *result;
  BtorNode *var, *index, *e_if, *e_else, *expected_acond, *expected,
      *expected_cond;
  BtorNode *param, *param_cond, *param_acond, *param_exp, *lambda;

  var            = btor_exp_var (d_btor, d_index_sort, "v1");
  index          = btor_exp_var (d_btor, d_index_sort, "i");
  expected_cond  = btor_exp_eq (d_btor, var, index);
  e_if           = btor_exp_array (d_btor, d_array_sort, "a1");
  e_else         = btor_exp_array (d_btor, d_array_sort, "a2");
  expected_acond = btor_exp_cond (d_btor, expected_cond, e_if, e_else);
  expected       = btor_exp_read (d_btor, expected_acond, var);

  param       = btor_exp_param (d_btor, d_index_sort, "p");
  param_cond  = btor_exp_eq (d_btor, param, index);
  param_acond = btor_exp_cond (d_btor, param_cond, e_if, e_else);
  param_exp   = btor_exp_read (d_btor, param_acond, param);
  lambda      = btor_exp_lambda (d_btor, param, param_exp);
  result      = apply_and_reduce (d_btor, &var, 1, lambda);

  ASSERT_EQ (result, expected);
  assert_parameterized (4, param, param_cond, param_acond, param_exp);
  assert_not_parameterized (4, result, lambda, expected, expected_acond);
  assert_not_parameterized (5, e_else, e_if, expected_cond, index, var);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, param_exp);
  btor_node_release (d_btor, param_acond);
  btor_node_release (d_btor, param_cond);
  btor_node_release (d_btor, param);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, expected_acond);
  btor_node_release (d_btor, e_else);
  btor_node_release (d_btor, e_if);
  btor_node_release (d_btor, expected_cond);
  btor_node_release (d_btor, index);
  btor_node_release (d_btor, var);
}

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

/* (lambda x . read ((lambda y . y), x)) */
TEST_F (TestLambda, bounded_reduce1)
{
  BtorNode *result;
  BtorNode *x, *y, *l2, *r, *l1, *v, *expected;

  x  = btor_exp_param (d_btor, d_index_sort, "x");
  y  = btor_exp_param (d_btor, d_index_sort, "y");
  l2 = btor_exp_lambda (d_btor, y, y);
  r  = btor_exp_apply_n (d_btor, l2, &x, 1);
  l1 = btor_exp_lambda (d_btor, x, r);
  v  = btor_exp_var (d_btor, d_index_sort, "v");

  expected = btor_exp_apply_n (d_btor, l2, &v, 1);

  /* bound 2: stop at second lambda */
  btor_beta_assign_param (d_btor, l1, v);
  result = btor_beta_reduce_bounded (d_btor, l1, 2);
  btor_beta_unassign_params (d_btor, l1);

  ASSERT_EQ (result, expected);
  btor_node_release (d_btor, result);
  btor_node_release (d_btor, expected);

  /* bound 3: stop at third lambda */
  btor_beta_assign_param (d_btor, l1, v);
  result = btor_beta_reduce_bounded (d_btor, l1, 3);
  btor_beta_unassign_params (d_btor, l1);

  ASSERT_EQ (result, v);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, v);
  btor_node_release (d_btor, l1);
  btor_node_release (d_btor, r);
  btor_node_release (d_btor, l2);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, x);
}

TEST_F (TestLambda, bounded_reduce2)
{
  BtorNode *result;
  BtorNode *x, *i, *eq, *l, *j, *expected;

  x        = btor_exp_param (d_btor, d_index_sort, "x");
  i        = btor_exp_var (d_btor, d_index_sort, "i");
  eq       = btor_exp_eq (d_btor, x, i);
  l        = btor_exp_lambda (d_btor, x, eq);
  j        = btor_exp_var (d_btor, d_index_sort, "j");
  expected = btor_exp_eq (d_btor, i, j);

  btor_beta_assign_param (d_btor, l, j);
  result = btor_beta_reduce_bounded (d_btor, l, 0);
  ASSERT_EQ (result, expected);
  btor_node_release (d_btor, result);

  result = btor_beta_reduce_bounded (d_btor, l, 1);
  ASSERT_EQ (result, l);
  btor_node_release (d_btor, result);

  result = btor_beta_reduce_bounded (d_btor, eq, 1);
  ASSERT_EQ (result, expected);
  btor_node_release (d_btor, result);

  result = btor_beta_reduce_bounded (d_btor, l, 2);
  ASSERT_EQ (result, expected);
  btor_beta_unassign_params (d_btor, l);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, j);
  btor_node_release (d_btor, l);
  btor_node_release (d_btor, eq);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, x);
}

TEST_F (TestLambda, bounded_reduce3)
{
  BtorNode *result;
  BtorNode *x, *y, *l1, *a, *l2, *i, *expected;

  x        = btor_exp_param (d_btor, d_index_sort, "x");
  y        = btor_exp_param (d_btor, d_index_sort, "y");
  l1       = btor_exp_lambda (d_btor, x, x);
  a        = btor_exp_apply_n (d_btor, l1, &y, 1);
  l2       = btor_exp_lambda (d_btor, y, a);
  i        = btor_exp_var (d_btor, d_index_sort, "i");
  expected = btor_exp_apply_n (d_btor, l1, &i, 1);

  btor_beta_assign_param (d_btor, l2, i);
  result = btor_beta_reduce_bounded (d_btor, l2, 1);
  ASSERT_EQ (result, l2);
  btor_node_release (d_btor, result);

  result = btor_beta_reduce_bounded (d_btor, l2, 2);
  ASSERT_EQ (result, expected);
  btor_node_release (d_btor, result);

  result = btor_beta_reduce_bounded (d_btor, l2, 3);
  ASSERT_EQ (result, i);
  btor_beta_unassign_params (d_btor, l2);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, l2);
  btor_node_release (d_btor, l1);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, x);
}

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

TEST_F (TestLambda, reduce_write1)
{
  BtorNode *result;
  BtorNode *a, *i, *e, *param, *read, *eq, *cond, *lambda;

  a      = btor_exp_array (d_btor, d_array_sort, "a");
  i      = btor_exp_var (d_btor, d_index_sort, "i");
  e      = btor_exp_var (d_btor, d_elem_sort, "e");
  param  = btor_exp_param (d_btor, d_index_sort, "p");
  read   = btor_exp_read (d_btor, a, param);
  eq     = btor_exp_eq (d_btor, param, i);
  cond   = btor_exp_cond (d_btor, eq, e, read);
  lambda = btor_exp_lambda (d_btor, param, cond);
  result = apply_and_reduce (d_btor, &i, 1, lambda);

  ASSERT_EQ (result, e);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, cond);
  btor_node_release (d_btor, eq);
  btor_node_release (d_btor, read);
  btor_node_release (d_btor, param);
  btor_node_release (d_btor, e);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, a);
}

TEST_F (TestLambda, reduce_write2)
{
  BtorNode *result;
  BtorNode *a, *i, *e, *param, *read, *expected, *eq, *cond, *lambda;

  a        = btor_exp_array (d_btor, d_array_sort, "a");
  i        = btor_exp_var (d_btor, d_index_sort, "i");
  e        = btor_exp_var (d_btor, d_elem_sort, "e");
  param    = btor_exp_param (d_btor, d_index_sort, "p");
  read     = btor_exp_read (d_btor, a, param);
  expected = btor_exp_read (d_btor, a, i);
  eq       = btor_exp_ne (d_btor, param, i);
  cond     = btor_exp_cond (d_btor, eq, e, read);
  lambda   = btor_exp_lambda (d_btor, param, cond);
  result   = apply_and_reduce (d_btor, &i, 1, lambda);

  ASSERT_EQ (result, expected);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda);
  btor_node_release (d_btor, cond);
  btor_node_release (d_btor, eq);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, read);
  btor_node_release (d_btor, param);
  btor_node_release (d_btor, e);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, a);
}

TEST_F (TestLambda, reduce_nested_writes)
{
  BtorNode *result;
  BtorNode *i, *a, *e2, *w2, *e1, *w1;

  i = btor_exp_var (d_btor, d_index_sort, "i");
  /* w2 = write (a, i, e2) */
  a  = btor_exp_array (d_btor, d_array_sort, "a");
  e2 = btor_exp_var (d_btor, d_elem_sort, "e2");
  w2 = btor_exp_lambda_write (d_btor, a, i, e2);
  /* w1 = write (w1, not i, e1) */
  e1     = btor_exp_var (d_btor, d_elem_sort, "e1");
  w1     = btor_exp_lambda_write (d_btor, w2, btor_node_invert (i), e1);
  result = apply_and_reduce (d_btor, &i, 1, w1);

  ASSERT_EQ (result, e2);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, w1);
  btor_node_release (d_btor, e1);
  btor_node_release (d_btor, w2);
  btor_node_release (d_btor, e2);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, i);
}

/* (lambda x . (lambda y . (x + y))) (a b) */
TEST_F (TestLambda, reduce_nested_lambdas_add1)
{
  BtorNode *result;
  BtorNode *a, *b, *expected, *x, *y, *add, *fun;

  a                   = btor_exp_var (d_btor, d_elem_sort, "a");
  b                   = btor_exp_var (d_btor, d_elem_sort, "b");
  BtorNode *args[2]   = {a, b};
  expected            = btor_exp_bv_add (d_btor, a, b);
  x                   = btor_exp_param (d_btor, d_elem_sort, "x");
  y                   = btor_exp_param (d_btor, d_elem_sort, "y");
  BtorNode *params[2] = {x, y};
  add                 = btor_exp_bv_add (d_btor, x, y);
  fun                 = btor_exp_fun (d_btor, params, 2, add);

  result = apply_and_reduce (d_btor, args, 2, fun);
  ASSERT_EQ (result, expected);
  btor_node_release (d_btor, result);

  BtorNode *apply = btor_exp_apply_n (d_btor, fun, args, 2);
  result          = btor_beta_reduce_full (d_btor, apply, 0);
  ASSERT_EQ (result, expected);

  btor_node_release (d_btor, apply);
  btor_node_release (d_btor, result);
  btor_node_release (d_btor, fun);
  btor_node_release (d_btor, add);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, b);
  btor_node_release (d_btor, a);
}

/* (lambda x . (x + read(lambda y . y, b))) (a) */
TEST_F (TestLambda, reduce_nested_lambdas_add2)
{
  BtorNode *result;
  BtorNode *a, *b, *expected, *x, *y, *lambda1, *lambda2, *app, *add;
  BtorSortId lambda_index_sort;

  lambda_index_sort = d_elem_sort;
  a                 = btor_exp_var (d_btor, d_elem_sort, "a");
  b                 = btor_exp_var (d_btor, d_elem_sort, "b");
  expected          = btor_exp_bv_add (d_btor, a, b);
  x                 = btor_exp_param (d_btor, lambda_index_sort, "x");
  y                 = btor_exp_param (d_btor, lambda_index_sort, "y");
  lambda2           = btor_exp_lambda (d_btor, y, y);
  app               = btor_exp_apply_n (d_btor, lambda2, &b, 1);
  add               = btor_exp_bv_add (d_btor, x, app);
  lambda1           = btor_exp_lambda (d_btor, x, add);
  result            = apply_and_reduce (d_btor, &a, 1, lambda1);

  ASSERT_EQ (result, expected);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, lambda1);
  btor_node_release (d_btor, add);
  btor_node_release (d_btor, app);
  btor_node_release (d_btor, lambda2);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, b);
  btor_node_release (d_btor, a);
}

/* (lambda x . not (read (lambda y . y, x + var))) (a) */
TEST_F (TestLambda, reduce_nested_lambdas_read)
{
  BtorNode *result;
  BtorNode *a, *var, *y, *lambda1, *lambda2, *x, *add, *app, *napp;
  BtorNode *expected, *expected_add;

  var     = btor_exp_var (d_btor, d_elem_sort, "var");
  y       = btor_exp_param (d_btor, d_elem_sort, "y");
  lambda2 = btor_exp_lambda (d_btor, y, y);
  x       = btor_exp_param (d_btor, d_elem_sort, "x");
  add     = btor_exp_bv_add (d_btor, x, var);
  app     = btor_exp_apply_n (d_btor, lambda2, &add, 1);
  napp    = btor_exp_bv_not (d_btor, app);
  lambda1 = btor_exp_lambda (d_btor, x, napp);
  a       = btor_exp_var (d_btor, d_elem_sort, "a");
  /* exptected not (a + var) */
  expected_add = btor_exp_bv_add (d_btor, a, var);
  expected     = btor_exp_bv_not (d_btor, expected_add);
  result       = apply_and_reduce (d_btor, &a, 1, lambda1);

  ASSERT_EQ (result, expected);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, expected);
  btor_node_release (d_btor, expected_add);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, lambda1);
  btor_node_release (d_btor, napp);
  btor_node_release (d_btor, app);
  btor_node_release (d_btor, add);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, lambda2);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, var);
}

/* (lambda x1 . (lambda x2 . ... (lambda x1000 . var))) (i1 ... i1000) */
TEST_F (TestLambda, reduce_nested_lambdas_const_n1000)
{
  BtorNode *result;
  BtorNode **params, **indices, *var, *fun;
  int32_t i, nesting_lvl;
  size_t size;

  nesting_lvl = 1000;
  size        = nesting_lvl * sizeof (BtorNode *);
  var         = btor_exp_var (d_btor, d_elem_sort, 0);

  params  = (BtorNode **) btor_mem_malloc (d_btor->mm, size);
  indices = (BtorNode **) btor_mem_malloc (d_btor->mm, size);

  for (i = nesting_lvl - 1; i >= 0; i--)
  {
    indices[i] = btor_exp_var (d_btor, d_index_sort, 0);
    params[i]  = btor_exp_param (d_btor, d_index_sort, 0);
  }
  fun = btor_exp_fun (d_btor, params, nesting_lvl, var);

  result = apply_and_reduce (d_btor, indices, nesting_lvl, fun);
  ASSERT_EQ (result, var);
  btor_node_release (d_btor, result);

  BtorNode *apply = btor_exp_apply_n (d_btor, fun, indices, nesting_lvl);
  result          = btor_beta_reduce_full (d_btor, apply, 0);
  ASSERT_EQ (result, var);

  for (i = 0; i < nesting_lvl; i++)
  {
    btor_node_release (d_btor, params[i]);
    btor_node_release (d_btor, indices[i]);
  }

  btor_mem_free (d_btor->mm, params, size);
  btor_mem_free (d_btor->mm, indices, size);

  btor_node_release (d_btor, fun);
  btor_node_release (d_btor, apply);
  btor_node_release (d_btor, result);
  btor_node_release (d_btor, var);
}

TEST_F (TestLambda, hashing1)
{
  BtorNode *w0, *w1, *i, *e, *a;
  BtorSortId array_sort, sort;

  sort       = btor_sort_bv (d_btor, 32);
  array_sort = btor_sort_array (d_btor, sort, sort);

  a  = btor_exp_array (d_btor, array_sort, 0);
  i  = btor_exp_var (d_btor, sort, 0);
  e  = btor_exp_var (d_btor, sort, 0);
  w0 = btor_exp_lambda_write (d_btor, a, i, e);
  w1 = btor_exp_lambda_write (d_btor, a, i, e);
  ASSERT_EQ (w0, w1);

  btor_sort_release (d_btor, array_sort);
  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, a);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, e);
  btor_node_release (d_btor, w0);
  btor_node_release (d_btor, w1);
}

TEST_F (TestLambda, hashing2)
{
  BtorNode *ite0, *ite1, *i, *e, *a0, *a1, *eq;
  BtorSortId array_sort, sort;

  sort       = btor_sort_bv (d_btor, 32);
  array_sort = btor_sort_array (d_btor, sort, sort);

  a0   = btor_exp_array (d_btor, array_sort, 0);
  a1   = btor_exp_array (d_btor, array_sort, 0);
  i    = btor_exp_var (d_btor, sort, 0);
  e    = btor_exp_var (d_btor, sort, 0);
  eq   = btor_exp_eq (d_btor, i, e);
  ite0 = btor_exp_cond (d_btor, eq, a0, a1);
  ite1 = btor_exp_cond (d_btor, eq, a0, a1);
  ASSERT_EQ (ite0, ite1);

  btor_node_release (d_btor, ite1);
  ite1 = btor_exp_cond (d_btor, btor_node_invert (eq), a1, a0);
  ASSERT_EQ (ite0, ite1);

  btor_sort_release (d_btor, array_sort);
  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, a0);
  btor_node_release (d_btor, a1);
  btor_node_release (d_btor, i);
  btor_node_release (d_btor, e);
  btor_node_release (d_btor, eq);
  btor_node_release (d_btor, ite0);
  btor_node_release (d_btor, ite1);
}

/* check if hashing considers commutativity */
TEST_F (TestLambda, hashing3)
{
  BtorNode *l0, *l1, *v, *p0, *p1, *eq0, *eq1;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 32);

  /* NOTE: order p0, v, p1 is important here */
  p0 = btor_exp_param (d_btor, sort, 0);
  v  = btor_exp_var (d_btor, sort, 0);
  p1 = btor_exp_param (d_btor, sort, 0);

  eq0 = btor_exp_eq (d_btor, p0, v);
  eq1 = btor_exp_eq (d_btor, v, p1);

  l0 = btor_exp_lambda (d_btor, p0, eq0);
  l1 = btor_exp_lambda (d_btor, p1, eq1);
  ASSERT_EQ (l0, l1);

  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, p0);
  btor_node_release (d_btor, p1);
  btor_node_release (d_btor, v);
  btor_node_release (d_btor, eq0);
  btor_node_release (d_btor, eq1);
  btor_node_release (d_btor, l0);
  btor_node_release (d_btor, l1);
}

TEST_F (TestLambda, hashing4)
{
  BtorNode *f0, *f1, *p0[2], *p1[2], *eq0, *eq1;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 32);

  p0[0] = btor_exp_param (d_btor, sort, 0);
  p0[1] = btor_exp_param (d_btor, sort, 0);
  p1[0] = btor_exp_param (d_btor, sort, 0);
  p1[1] = btor_exp_param (d_btor, sort, 0);

  eq0 = btor_exp_eq (d_btor, p0[0], p0[1]);
  eq1 = btor_exp_eq (d_btor, p1[0], p1[1]);

  f0 = btor_exp_fun (d_btor, p0, 2, eq0);
  f1 = btor_exp_fun (d_btor, p1, 2, eq1);
  ASSERT_EQ (f0, f1);

  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, p0[0]);
  btor_node_release (d_btor, p0[1]);
  btor_node_release (d_btor, p1[0]);
  btor_node_release (d_btor, p1[1]);
  btor_node_release (d_btor, eq0);
  btor_node_release (d_btor, eq1);
  btor_node_release (d_btor, f0);
  btor_node_release (d_btor, f1);
}

TEST_F (TestLambda, quantifier_hashing1)
{
  BtorNode *x0, *y0, *eq0, *f0, *e0;
  BtorNode *x1, *y1, *eq1, *f1, *e1;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 32);
  x0   = btor_exp_param (d_btor, sort, 0);
  y0   = btor_exp_param (d_btor, sort, 0);
  eq0  = btor_exp_eq (d_btor, x0, y0);
  f0   = btor_exp_forall (d_btor, y0, eq0);
  e0   = btor_exp_exists (d_btor, x0, f0);

  x1  = btor_exp_param (d_btor, sort, 0);
  y1  = btor_exp_param (d_btor, sort, 0);
  eq1 = btor_exp_eq (d_btor, x1, y1);
  f1  = btor_exp_forall (d_btor, y1, eq1);
  e1  = btor_exp_exists (d_btor, x1, f1);
  ASSERT_EQ (e0, e1);

  btor_node_release (d_btor, x0);
  btor_node_release (d_btor, y0);
  btor_node_release (d_btor, eq0);
  btor_node_release (d_btor, f0);
  btor_node_release (d_btor, e0);
  btor_node_release (d_btor, x1);
  btor_node_release (d_btor, y1);
  btor_node_release (d_btor, eq1);
  btor_node_release (d_btor, f1);
  btor_node_release (d_btor, e1);
  btor_sort_release (d_btor, sort);
}

TEST_F (TestLambda, quantifier_hashing2)
{
  BtorNode *x0, *x1, *x2, *x3, *y0, *y1, *y2, *y3;
  BtorNode *a0, *a1, *a2, *a3, *a4, *a5, *a6, *r0;
  BtorNode *f0, *e0, *f1, *e1, *f2, *e2, *f3, *e3;
  BtorNode *x10, *x11, *x12, *x13, *y10, *y11, *y12, *y13;
  BtorNode *a10, *a11, *a12, *a13, *a14, *a15, *a16, *r10;
  BtorNode *f10, *e10, *f11, *e11, *f12, *e12, *f13, *e13;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 32);
  x0   = btor_exp_param (d_btor, sort, 0);
  x1   = btor_exp_param (d_btor, sort, 0);
  x2   = btor_exp_param (d_btor, sort, 0);
  x3   = btor_exp_param (d_btor, sort, 0);
  y0   = btor_exp_param (d_btor, sort, 0);
  y1   = btor_exp_param (d_btor, sort, 0);
  y2   = btor_exp_param (d_btor, sort, 0);
  y3   = btor_exp_param (d_btor, sort, 0);

  a0 = btor_exp_bv_and (d_btor, x0, y0);
  a1 = btor_exp_bv_and (d_btor, a0, x1);
  a2 = btor_exp_bv_and (d_btor, a1, y1);
  a3 = btor_exp_bv_and (d_btor, a2, x2);
  a4 = btor_exp_bv_and (d_btor, a3, y2);
  a5 = btor_exp_bv_and (d_btor, a4, x3);
  a6 = btor_exp_bv_and (d_btor, a5, y3);
  r0 = btor_exp_bv_redor (d_btor, a6);
  f0 = btor_exp_forall (d_btor, x0, r0);
  e0 = btor_exp_exists (d_btor, y0, f0);
  e1 = btor_exp_exists (d_btor, y1, e0);
  f1 = btor_exp_forall (d_btor, x1, e1);
  f2 = btor_exp_forall (d_btor, x2, f1);
  e2 = btor_exp_exists (d_btor, y2, f2);
  f3 = btor_exp_forall (d_btor, x3, e2);
  e3 = btor_exp_exists (d_btor, y3, f3);

  x10 = btor_exp_param (d_btor, sort, 0);
  x11 = btor_exp_param (d_btor, sort, 0);
  x12 = btor_exp_param (d_btor, sort, 0);
  x13 = btor_exp_param (d_btor, sort, 0);
  y10 = btor_exp_param (d_btor, sort, 0);
  y11 = btor_exp_param (d_btor, sort, 0);
  y12 = btor_exp_param (d_btor, sort, 0);
  y13 = btor_exp_param (d_btor, sort, 0);

  a10 = btor_exp_bv_and (d_btor, x10, y10);
  a11 = btor_exp_bv_and (d_btor, a10, x11);
  a12 = btor_exp_bv_and (d_btor, a11, y11);
  a13 = btor_exp_bv_and (d_btor, a12, x12);
  a14 = btor_exp_bv_and (d_btor, a13, y12);
  a15 = btor_exp_bv_and (d_btor, a14, x13);
  a16 = btor_exp_bv_and (d_btor, a15, y13);
  r10 = btor_exp_bv_redor (d_btor, a16);
  f10 = btor_exp_forall (d_btor, x10, r10);
  e10 = btor_exp_exists (d_btor, y10, f10);
  e11 = btor_exp_exists (d_btor, y11, e10);
  f11 = btor_exp_forall (d_btor, x11, e11);
  f12 = btor_exp_forall (d_btor, x12, f11);
  e12 = btor_exp_exists (d_btor, y12, f12);
  f13 = btor_exp_forall (d_btor, x13, e12);
  e13 = btor_exp_exists (d_btor, y13, f13);

  ASSERT_EQ (e3, e13);

  btor_node_release (d_btor, x0);
  btor_node_release (d_btor, x1);
  btor_node_release (d_btor, x2);
  btor_node_release (d_btor, x3);
  btor_node_release (d_btor, y0);
  btor_node_release (d_btor, y1);
  btor_node_release (d_btor, y2);
  btor_node_release (d_btor, y3);
  btor_node_release (d_btor, a0);
  btor_node_release (d_btor, a1);
  btor_node_release (d_btor, a2);
  btor_node_release (d_btor, a3);
  btor_node_release (d_btor, a4);
  btor_node_release (d_btor, a5);
  btor_node_release (d_btor, a6);
  btor_node_release (d_btor, r0);
  btor_node_release (d_btor, f0);
  btor_node_release (d_btor, e0);
  btor_node_release (d_btor, e1);
  btor_node_release (d_btor, f1);
  btor_node_release (d_btor, f2);
  btor_node_release (d_btor, e2);
  btor_node_release (d_btor, f3);
  btor_node_release (d_btor, e3);
  btor_node_release (d_btor, x10);
  btor_node_release (d_btor, x11);
  btor_node_release (d_btor, x12);
  btor_node_release (d_btor, x13);
  btor_node_release (d_btor, y10);
  btor_node_release (d_btor, y11);
  btor_node_release (d_btor, y12);
  btor_node_release (d_btor, y13);
  btor_node_release (d_btor, a10);
  btor_node_release (d_btor, a11);
  btor_node_release (d_btor, a12);
  btor_node_release (d_btor, a13);
  btor_node_release (d_btor, a14);
  btor_node_release (d_btor, a15);
  btor_node_release (d_btor, a16);
  btor_node_release (d_btor, r10);
  btor_node_release (d_btor, f10);
  btor_node_release (d_btor, e10);
  btor_node_release (d_btor, e11);
  btor_node_release (d_btor, f11);
  btor_node_release (d_btor, f12);
  btor_node_release (d_btor, e12);
  btor_node_release (d_btor, f13);
  btor_node_release (d_btor, e13);
  btor_sort_release (d_btor, sort);
}

#if 0
/* (lambda x . (lambda y . (x + y))) (a) */
TEST_F (TestLambda, partial_reduce_nested_lambdas_add1)
{
  BtorNode *result;
  BtorNode *a, *x, *y, *add, *params[2] = {x, y}, *fun;

  a = btor_exp_var (d_btor, d_elem_sort, "a");
  x = btor_exp_param (d_btor, d_elem_sort, "x");
  y = btor_exp_param (d_btor, d_elem_sort, "y");
  add = btor_exp_bv_add (d_btor, x, y);
  fun = btor_exp_fun (d_btor, params, 2, add); 
  result = apply_and_reduce (d_btor, 1, &a, fun);

  /* expected: lambda y' . (a + y') */
  ASSERT_TRUE (btor_node_is_lambda (result));
  ASSERT_NE (result, fun->e[1]);
  ASSERT_NE (result->e[0], fun->e[1]->e[0]);
  ASSERT_EQ (btor_node_real_addr (result->e[1])->kind, BTOR_BV_ADD_NODE);
  ASSERT_EQ (btor_node_real_addr (result->e[1])->e[0], a);
  ASSERT_EQ (btor_node_real_addr (result->e[1])->e[1], result->e[0]);

  btor_node_release (d_btor, result);
  btor_node_release (d_btor, fun);
  btor_node_release (d_btor, add);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, a);
}
#endif

/*---------------------------------------------------------------------------
 * additional tests
 *---------------------------------------------------------------------------*/

TEST_F (TestLambda, define_fun)
{
  int32_t i;
  int32_t nesting_lvl = 1000;
  size_t size;
  BtorNode **params, **lambdas, **ands, *left, *right, *expected, *result;

  size    = nesting_lvl * sizeof (BtorNode *);
  params  = (BtorNode **) btor_mem_malloc (d_btor->mm, size);
  lambdas = (BtorNode **) btor_mem_malloc (d_btor->mm, size);
  ands = (BtorNode **) btor_mem_malloc (d_btor->mm, size - sizeof (BtorNode *));

  for (i = 0; i < nesting_lvl; i++)
    params[i] = btor_exp_param (d_btor, d_elem_sort, 0);

  ASSERT_GT (nesting_lvl, 1);
  left  = params[0];
  right = params[1];
  for (i = 0; i < nesting_lvl - 1; i++)
  {
    ands[i] = btor_exp_bv_and (d_btor, left, right);

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
    ASSERT_NE (expected, nullptr);
    lambdas[i] = btor_exp_lambda (d_btor, params[i], expected);
    expected   = lambdas[i];
  }

  result = btor_exp_fun (d_btor, params, nesting_lvl, ands[nesting_lvl - 2]);

  ASSERT_EQ (result, expected);

  for (i = 0; i < nesting_lvl; i++)
  {
    btor_node_release (d_btor, lambdas[i]);
    btor_node_release (d_btor, params[i]);

    if (i < nesting_lvl - 1) btor_node_release (d_btor, ands[i]);
  }

  btor_mem_free (d_btor->mm, params, size);
  btor_mem_free (d_btor->mm, lambdas, size);
  btor_mem_free (d_btor->mm, ands, size - sizeof (BtorNode *));
  btor_node_release (d_btor, result);
}

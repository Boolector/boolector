/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorexp.h"

#include "btorcore.h"
#include "btordbg.h"
#include "btorrewrite.h"

#include <limits.h>

BtorNode *
btor_const_exp (Btor *btor, const BtorBitVector *bits)
{
  return btor_node_create_const (btor, bits);
}

static BtorNode *
int_min_exp (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv = btor_bv_new (btor->mm, width);
  btor_bv_set_bit (bv, bv->width - 1, 1);
  result = btor_const_exp (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_zero_exp (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bitvec (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bitvec_get_width (btor, sort);
  bv     = btor_bv_new (btor->mm, width);
  result = btor_const_exp (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_ones_exp (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bitvec (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bitvec_get_width (btor, sort);
  bv     = btor_bv_ones (btor->mm, width);
  result = btor_const_exp (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_one_exp (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bitvec (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bitvec_get_width (btor, sort);
  bv     = btor_bv_one (btor->mm, width);
  result = btor_const_exp (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_int_exp (Btor *btor, int32_t i, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bitvec (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bitvec_get_width (btor, sort);
  bv     = btor_bv_int64_to_bv (btor->mm, i, width);
  result = btor_const_exp (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_unsigned_exp (Btor *btor, uint32_t u, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bitvec (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bitvec_get_width (btor, sort);
  bv     = btor_bv_uint64_to_bv (btor->mm, u, width);
  result = btor_const_exp (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_true_exp (Btor *btor)
{
  assert (btor);

  BtorSortId sort;
  BtorNode *result;

  sort   = btor_sort_bitvec (btor, 1);
  result = btor_one_exp (btor, sort);
  btor_sort_release (btor, sort);
  return result;
}

BtorNode *
btor_false_exp (Btor *btor)
{
  assert (btor);

  BtorSortId sort;
  BtorNode *result;

  sort   = btor_sort_bitvec (btor, 1);
  result = btor_zero_exp (btor, sort);
  btor_sort_release (btor, sort);
  return result;
}

BtorNode *
btor_var_exp (Btor *btor, BtorSortId sort, const char *symbol)
{
  return btor_node_create_var (btor, sort, symbol);
}

BtorNode *
btor_param_exp (Btor *btor, BtorSortId sort, const char *symbol)
{
  return btor_node_create_param (btor, sort, symbol);
}

BtorNode *
btor_array_exp (Btor *btor, BtorSortId sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_fun (btor, sort));
  assert (
      btor_sort_tuple_get_arity (btor, btor_sort_fun_get_domain (btor, sort))
      == 1);

  BtorNode *exp;

  exp           = btor_uf_exp (btor, sort, symbol);
  exp->is_array = 1;

  return exp;
}

BtorNode *
btor_uf_exp (Btor *btor, BtorSortId sort, const char *symbol)
{
  return btor_node_create_uf (btor, sort, symbol);
}

BtorNode *
btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (e_param));
  assert (btor == e_param->btor);
  assert (btor_is_param_node (e_param));
  assert (!BTOR_REAL_ADDR_NODE (e_param)->simplified);
  assert (e_exp);
  assert (btor == BTOR_REAL_ADDR_NODE (e_exp)->btor);

  BtorNode *result;
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_LAMBDA_NODE, e_param, e_exp);
  else
    result = btor_lambda_exp_node (btor, e_param, e_exp);
  assert (btor_is_fun_node (result));
  return result;
}

BtorNode *
btor_fun_exp (Btor *btor, BtorNode *params[], uint32_t paramc, BtorNode *exp)
{
  assert (btor);
  assert (paramc > 0);
  assert (params);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  assert (!btor_is_uf_node (exp));

  uint32_t i, j;
  BtorNode *fun      = btor_simplify_exp (btor, exp);
  BtorNode *prev_fun = 0;

  for (i = 1; i <= paramc; i++)
  {
    j = paramc - i;
    assert (params[j]);
    assert (btor == BTOR_REAL_ADDR_NODE (params[j])->btor);
    assert (btor_is_param_node (params[j]));
    fun = btor_lambda_exp (btor, params[j], fun);
    if (prev_fun) btor_release_exp (btor, prev_fun);
    prev_fun = fun;
  }

  return fun;
}

BtorNode *
btor_args_exp (Btor *btor, BtorNode *args[], uint32_t argc)
{
  return btor_node_create_args (btor, args, argc);
}

BtorNode *
btor_apply_exp (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor == BTOR_REAL_ADDR_NODE (fun)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (args)->btor);

  fun  = btor_simplify_exp (btor, fun);
  args = btor_simplify_exp (btor, args);
  assert (btor_is_fun_node (fun));
  assert (btor_is_args_node (args));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_binary_exp (btor, BTOR_APPLY_NODE, fun, args);

  return btor_apply_exp_node (btor, fun, args);
}

BtorNode *
btor_apply_exps (Btor *btor, BtorNode *fun, BtorNode *args[], uint32_t argc)
{
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);

  BtorNode *exp, *_args;

  _args = btor_args_exp (btor, args, argc);
  fun   = btor_simplify_exp (btor, fun);
  _args = btor_simplify_exp (btor, _args);

  exp = btor_apply_exp (btor, fun, _args);
  btor_release_exp (btor, _args);

  return exp;
}

BtorNode *
btor_not_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  (void) btor;
  btor_copy_exp (btor, exp);
  return BTOR_INVERT_NODE (exp);
}

BtorNode *
btor_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_ADD_NODE, e0, e1);
  else
    result = btor_add_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_neg_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *one;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));
  one    = btor_one_exp (btor, btor_exp_get_sort_id (exp));
  result = btor_add_exp (btor, BTOR_INVERT_NODE (exp), one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_slice_exp (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_slice_exp (btor, exp, upper, lower);
  else
    result = btor_slice_exp_node (btor, exp, upper, lower);

  assert (result);
  return result;
}

BtorNode *
btor_or_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (
      btor_and_exp (btor, BTOR_INVERT_NODE (e0), BTOR_INVERT_NODE (e1)));
}

BtorNode *
btor_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
  {
    if (btor_is_fun_node (e0))
      result = btor_rewrite_binary_exp (btor, BTOR_FUN_EQ_NODE, e0, e1);
    else
      result = btor_rewrite_binary_exp (btor, BTOR_BV_EQ_NODE, e0, e1);
  }
  else
    result = btor_eq_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_AND_NODE, e0, e1);
  else
    result = btor_and_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

#if 0
static BtorNode *
create_bin_n_exp (Btor * btor,
		  BtorNode * (*func) (Btor *, BtorNode *, BtorNode *),
		  BtorNode * args[],
		  uint32_t argc)
{
  uint32_t i;
  BtorNode *result, *tmp, *arg;

  result = 0;
  for (i = 0; i < argc; i++)
    {
      arg = args[i];
      if (result)
	{
	  tmp = func (btor, arg, result);
	  btor_release_exp (btor, result);
	  result = tmp;
	}
      else
	result = btor_copy_exp (btor,  arg);
    }
  assert (result);
  return result;
}

BtorNode *
btor_and_n_exp (Btor * btor, BtorNode * args[], uint32_t argc)
{
  return create_bin_n_exp (btor, btor_and_exp, args, argc);
}
#endif

BtorNode *
btor_xor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, * or, *and;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  or     = btor_or_exp (btor, e0, e1);
  and    = btor_and_exp (btor, e0, e1);
  result = btor_and_exp (btor, or, BTOR_INVERT_NODE (and));
  btor_release_exp (btor, or);
  btor_release_exp (btor, and);
  return result;
}

BtorNode *
btor_xnor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_xor_exp (btor, e0, e1));
}

BtorNode *
btor_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_CONCAT_NODE, e0, e1);
  else
    result = btor_concat_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_cond_exp (Btor *btor, BtorNode *e_cond, BtorNode *e_if, BtorNode *e_else)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_cond)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_if)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_else)->btor);

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_ternary_exp (
        btor, BTOR_COND_NODE, e_cond, e_if, e_else);

  return btor_cond_exp_node (btor, e_cond, e_if, e_else);
}

BtorNode *
btor_redor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  zero   = btor_zero_exp (btor, btor_exp_get_sort_id (exp));
  result = BTOR_INVERT_NODE (btor_eq_exp (btor, exp, zero));
  btor_release_exp (btor, zero);
  return result;
}

BtorNode *
btor_redxor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *slice, *xor;
  uint32_t i, width;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  width = btor_get_exp_width (btor, exp);

  result = btor_slice_exp (btor, exp, 0, 0);
  for (i = 1; i < width; i++)
  {
    slice = btor_slice_exp (btor, exp, i, i);
    xor   = btor_xor_exp (btor, result, slice);
    btor_release_exp (btor, slice);
    btor_release_exp (btor, result);
    result = xor;
  }
  return result;
}

BtorNode *
btor_redand_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *ones;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  ones   = btor_ones_exp (btor, btor_exp_get_sort_id (exp));
  result = btor_eq_exp (btor, exp, ones);
  btor_release_exp (btor, ones);
  return result;
}

BtorNode *
btor_uext_exp (Btor *btor, BtorNode *exp, uint32_t width)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero;
  BtorSortId sort;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp));

  if (width == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (width > 0);
    sort = btor_sort_bitvec (btor, width);
    zero = btor_zero_exp (btor, sort);
    btor_sort_release (btor, sort);
    result = btor_concat_exp (btor, zero, exp);
    btor_release_exp (btor, zero);
  }
  return result;
}

BtorNode *
btor_sext_exp (Btor *btor, BtorNode *exp, uint32_t width)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero, *ones, *neg, *cond;
  uint32_t exp_width;
  BtorSortId sort;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp));

  if (width == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (width > 0);
    sort = btor_sort_bitvec (btor, width);
    zero = btor_zero_exp (btor, sort);
    ones = btor_ones_exp (btor, sort);
    btor_sort_release (btor, sort);
    exp_width = btor_get_exp_width (btor, exp);
    neg       = btor_slice_exp (btor, exp, exp_width - 1, exp_width - 1);
    cond      = btor_cond_exp (btor, neg, ones, zero);
    result    = btor_concat_exp (btor, cond, exp);
    btor_release_exp (btor, zero);
    btor_release_exp (btor, ones);
    btor_release_exp (btor, neg);
    btor_release_exp (btor, cond);
  }
  return result;
}

BtorNode *
btor_nand_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_and_exp (btor, e0, e1));
}

BtorNode *
btor_nor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_or_exp (btor, e0, e1));
}

BtorNode *
btor_implies_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor_get_exp_width (btor, e0) == 1);
  return BTOR_INVERT_NODE (btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1)));
}

BtorNode *
btor_iff_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor_get_exp_width (btor, e0) == 1);
  return btor_eq_exp (btor, e0, e1);
}

BtorNode *
btor_ne_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_eq_exp (btor, e0, e1));
}

BtorNode *
btor_uaddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *add;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width   = btor_get_exp_width (btor, e0);
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, e1, 1);
  add     = btor_add_exp (btor, uext_e1, uext_e2);
  result  = btor_slice_exp (btor, add, width, width);
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, add);
  return result;
}

BtorNode *
btor_saddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *sign_result;
  BtorNode *add, *and1, *and2, *or1, *or2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width       = btor_get_exp_width (btor, e0);
  sign_e1     = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e2     = btor_slice_exp (btor, e1, width - 1, width - 1);
  add         = btor_add_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, add, width - 1, width - 1);
  and1        = btor_and_exp (btor, sign_e1, sign_e2);
  or1         = btor_and_exp (btor, and1, BTOR_INVERT_NODE (sign_result));
  and2        = btor_and_exp (
      btor, BTOR_INVERT_NODE (sign_e1), BTOR_INVERT_NODE (sign_e2));
  or2    = btor_and_exp (btor, and2, sign_result);
  result = btor_or_exp (btor, or1, or2);
  btor_release_exp (btor, and1);
  btor_release_exp (btor, and2);
  btor_release_exp (btor, or1);
  btor_release_exp (btor, or2);
  btor_release_exp (btor, add);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, sign_result);
  return result;
}

BtorNode *
btor_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_MUL_NODE, e0, e1);
  else
    result = btor_mul_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_umulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *mul, *slice, *and, * or, **temps_e2;
  BtorSortId sort;
  uint32_t i, width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);
  if (width == 1)
  {
    sort   = btor_sort_bitvec (btor, 1);
    result = btor_zero_exp (btor, sort);
    btor_sort_release (btor, sort);
    return result;
  }
  BTOR_NEWN (btor->mm, temps_e2, width - 1);
  temps_e2[0] = btor_slice_exp (btor, e1, width - 1, width - 1);
  for (i = 1; i < width - 1; i++)
  {
    slice       = btor_slice_exp (btor, e1, width - 1 - i, width - 1 - i);
    temps_e2[i] = btor_or_exp (btor, temps_e2[i - 1], slice);
    btor_release_exp (btor, slice);
  }
  slice  = btor_slice_exp (btor, e0, 1, 1);
  result = btor_and_exp (btor, slice, temps_e2[0]);
  btor_release_exp (btor, slice);
  for (i = 1; i < width - 1; i++)
  {
    slice = btor_slice_exp (btor, e0, i + 1, i + 1);
    and   = btor_and_exp (btor, slice, temps_e2[i]);
    or    = btor_or_exp (btor, result, and);
    btor_release_exp (btor, slice);
    btor_release_exp (btor, and);
    btor_release_exp (btor, result);
    result = or ;
  }
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, e1, 1);
  mul     = btor_mul_exp (btor, uext_e1, uext_e2);
  slice   = btor_slice_exp (btor, mul, width, width);
  or      = btor_or_exp (btor, result, slice);
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, mul);
  btor_release_exp (btor, slice);
  btor_release_exp (btor, result);
  result = or ;
  for (i = 0; i < width - 1; i++) btor_release_exp (btor, temps_e2[i]);
  BTOR_DELETEN (btor->mm, temps_e2, width - 1);
  return result;
}

BtorNode *
btor_smulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sext_e1, *sext_e2, *sign_e1, *sign_e2, *sext_sign_e1;
  BtorNode *sext_sign_e2, *xor_sign_e1, *xor_sign_e2, *mul, *slice, *slice_n;
  BtorNode *slice_n_minus_1, *xor, *and, * or, **temps_e2;
  uint32_t i, width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);
  if (width == 1) return btor_and_exp (btor, e0, e1);
  if (width == 2)
  {
    sext_e1         = btor_sext_exp (btor, e0, 1);
    sext_e2         = btor_sext_exp (btor, e1, 1);
    mul             = btor_mul_exp (btor, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (btor, mul, width, width);
    slice_n_minus_1 = btor_slice_exp (btor, mul, width - 1, width - 1);
    result          = btor_xor_exp (btor, slice_n, slice_n_minus_1);
    btor_release_exp (btor, sext_e1);
    btor_release_exp (btor, sext_e2);
    btor_release_exp (btor, mul);
    btor_release_exp (btor, slice_n);
    btor_release_exp (btor, slice_n_minus_1);
  }
  else
  {
    sign_e1      = btor_slice_exp (btor, e0, width - 1, width - 1);
    sign_e2      = btor_slice_exp (btor, e1, width - 1, width - 1);
    sext_sign_e1 = btor_sext_exp (btor, sign_e1, width - 1);
    sext_sign_e2 = btor_sext_exp (btor, sign_e2, width - 1);
    xor_sign_e1  = btor_xor_exp (btor, e0, sext_sign_e1);
    xor_sign_e2  = btor_xor_exp (btor, e1, sext_sign_e2);
    BTOR_NEWN (btor->mm, temps_e2, width - 2);
    temps_e2[0] = btor_slice_exp (btor, xor_sign_e2, width - 2, width - 2);
    for (i = 1; i < width - 2; i++)
    {
      slice = btor_slice_exp (btor, xor_sign_e2, width - 2 - i, width - 2 - i);
      temps_e2[i] = btor_or_exp (btor, temps_e2[i - 1], slice);
      btor_release_exp (btor, slice);
    }
    slice  = btor_slice_exp (btor, xor_sign_e1, 1, 1);
    result = btor_and_exp (btor, slice, temps_e2[0]);
    btor_release_exp (btor, slice);
    for (i = 1; i < width - 2; i++)
    {
      slice = btor_slice_exp (btor, xor_sign_e1, i + 1, i + 1);
      and   = btor_and_exp (btor, slice, temps_e2[i]);
      or    = btor_or_exp (btor, result, and);
      btor_release_exp (btor, slice);
      btor_release_exp (btor, and);
      btor_release_exp (btor, result);
      result = or ;
    }
    sext_e1         = btor_sext_exp (btor, e0, 1);
    sext_e2         = btor_sext_exp (btor, e1, 1);
    mul             = btor_mul_exp (btor, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (btor, mul, width, width);
    slice_n_minus_1 = btor_slice_exp (btor, mul, width - 1, width - 1);
    xor             = btor_xor_exp (btor, slice_n, slice_n_minus_1);
    or              = btor_or_exp (btor, result, xor);
    btor_release_exp (btor, sext_e1);
    btor_release_exp (btor, sext_e2);
    btor_release_exp (btor, sign_e1);
    btor_release_exp (btor, sign_e2);
    btor_release_exp (btor, sext_sign_e1);
    btor_release_exp (btor, sext_sign_e2);
    btor_release_exp (btor, xor_sign_e1);
    btor_release_exp (btor, xor_sign_e2);
    btor_release_exp (btor, mul);
    btor_release_exp (btor, slice_n);
    btor_release_exp (btor, slice_n_minus_1);
    btor_release_exp (btor, xor);
    btor_release_exp (btor, result);
    result = or ;
    for (i = 0; i < width - 2; i++) btor_release_exp (btor, temps_e2[i]);
    BTOR_DELETEN (btor->mm, temps_e2, width - 2);
  }
  return result;
}

BtorNode *
btor_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_ULT_NODE, e0, e1);
  else
    result = btor_ult_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_slt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *determined_by_sign, *eq_sign, *ult, *eq_sign_and_ult;
  BtorNode *res, *s0, *s1, *r0, *r1, *l, *r;

  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);
  if (width == 1) return btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1));
  s0                 = btor_slice_exp (btor, e0, width - 1, width - 1);
  s1                 = btor_slice_exp (btor, e1, width - 1, width - 1);
  r0                 = btor_slice_exp (btor, e0, width - 2, 0);
  r1                 = btor_slice_exp (btor, e1, width - 2, 0);
  ult                = btor_ult_exp (btor, r0, r1);
  determined_by_sign = btor_and_exp (btor, s0, BTOR_INVERT_NODE (s1));
  l                  = btor_copy_exp (btor, determined_by_sign);
  r                  = btor_and_exp (btor, BTOR_INVERT_NODE (s0), s1);
  eq_sign = btor_and_exp (btor, BTOR_INVERT_NODE (l), BTOR_INVERT_NODE (r));
  eq_sign_and_ult = btor_and_exp (btor, eq_sign, ult);
  res             = btor_or_exp (btor, determined_by_sign, eq_sign_and_ult);
  btor_release_exp (btor, s0);
  btor_release_exp (btor, s1);
  btor_release_exp (btor, r0);
  btor_release_exp (btor, r1);
  btor_release_exp (btor, ult);
  btor_release_exp (btor, determined_by_sign);
  btor_release_exp (btor, l);
  btor_release_exp (btor, r);
  btor_release_exp (btor, eq_sign);
  btor_release_exp (btor, eq_sign_and_ult);
  return res;
}

BtorNode *
btor_ulte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *ult;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  ult    = btor_ult_exp (btor, e1, e0);
  result = btor_not_exp (btor, ult);
  btor_release_exp (btor, ult);
  return result;
}

BtorNode *
btor_slte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *slt;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  slt    = btor_slt_exp (btor, e1, e0);
  result = btor_not_exp (btor, slt);
  btor_release_exp (btor, slt);
  return result;
}

BtorNode *
btor_ugt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_ult_exp (btor, e1, e0);
}

BtorNode *
btor_sgt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_slt_exp (btor, e1, e0);
}

BtorNode *
btor_ugte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *ult;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  ult    = btor_ult_exp (btor, e0, e1);
  result = btor_not_exp (btor, ult);
  btor_release_exp (btor, ult);
  return result;
}

BtorNode *
btor_sgte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *slt;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  slt    = btor_slt_exp (btor, e0, e1);
  result = btor_not_exp (btor, slt);
  btor_release_exp (btor, slt);
  return result;
}

BtorNode *
btor_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_SLL_NODE, e0, e1);
  else
    result = btor_sll_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_SRL_NODE, e0, e1);
  else
    result = btor_srl_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_sra_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *srl1, *srl2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  width   = btor_get_exp_width (btor, e0);
  sign_e1 = btor_slice_exp (btor, e0, width - 1, width - 1);
  srl1    = btor_srl_exp (btor, e0, e1);
  srl2    = btor_srl_exp (btor, BTOR_INVERT_NODE (e0), e1);
  result  = btor_cond_exp (btor, sign_e1, BTOR_INVERT_NODE (srl2), srl1);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, srl1);
  btor_release_exp (btor, srl2);
  return result;
}

BtorNode *
btor_rol_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sll, *neg_e2, *srl;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  sll    = btor_sll_exp (btor, e0, e1);
  neg_e2 = btor_neg_exp (btor, e1);
  srl    = btor_srl_exp (btor, e0, neg_e2);
  result = btor_or_exp (btor, sll, srl);
  btor_release_exp (btor, sll);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, srl);
  return result;
}

BtorNode *
btor_ror_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *srl, *neg_e2, *sll;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  srl    = btor_srl_exp (btor, e0, e1);
  neg_e2 = btor_neg_exp (btor, e1);
  sll    = btor_sll_exp (btor, e0, neg_e2);
  result = btor_or_exp (btor, srl, sll);
  btor_release_exp (btor, srl);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, sll);
  return result;
}

BtorNode *
btor_sub_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *neg_e2;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  neg_e2 = btor_neg_exp (btor, e1);
  result = btor_add_exp (btor, e0, neg_e2);
  btor_release_exp (btor, neg_e2);
  return result;
}

BtorNode *
btor_usubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *add1, *add2, *one;
  BtorSortId sort;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width   = btor_get_exp_width (btor, e0);
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, BTOR_INVERT_NODE (e1), 1);
  assert (width < INT_MAX);
  sort = btor_sort_bitvec (btor, width + 1);
  one  = btor_one_exp (btor, sort);
  btor_sort_release (btor, sort);
  add1   = btor_add_exp (btor, uext_e2, one);
  add2   = btor_add_exp (btor, uext_e1, add1);
  result = BTOR_INVERT_NODE (btor_slice_exp (btor, add2, width, width));
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, add1);
  btor_release_exp (btor, add2);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_ssubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *sign_result;
  BtorNode *sub, *and1, *and2, *or1, *or2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width       = btor_get_exp_width (btor, e0);
  sign_e1     = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e2     = btor_slice_exp (btor, e1, width - 1, width - 1);
  sub         = btor_sub_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, sub, width - 1, width - 1);
  and1        = btor_and_exp (btor, BTOR_INVERT_NODE (sign_e1), sign_e2);
  or1         = btor_and_exp (btor, and1, sign_result);
  and2        = btor_and_exp (btor, sign_e1, BTOR_INVERT_NODE (sign_e2));
  or2         = btor_and_exp (btor, and2, BTOR_INVERT_NODE (sign_result));
  result      = btor_or_exp (btor, or1, or2);
  btor_release_exp (btor, and1);
  btor_release_exp (btor, and2);
  btor_release_exp (btor, or1);
  btor_release_exp (btor, or2);
  btor_release_exp (btor, sub);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, sign_result);
  return result;
}

BtorNode *
btor_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_UDIV_NODE, e0, e1);
  else
    result = btor_udiv_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_sdiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *xor, *neg_e1, *neg_e2;
  BtorNode *cond_e1, *cond_e2, *udiv, *neg_udiv;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);

  if (width == 1)
    return BTOR_INVERT_NODE (btor_and_exp (btor, BTOR_INVERT_NODE (e0), e1));

  sign_e1 = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e2 = btor_slice_exp (btor, e1, width - 1, width - 1);
  /* xor: must result be signed? */
  xor    = btor_xor_exp (btor, sign_e1, sign_e2);
  neg_e1 = btor_neg_exp (btor, e0);
  neg_e2 = btor_neg_exp (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_cond_exp (btor, sign_e1, neg_e1, e0);
  cond_e2  = btor_cond_exp (btor, sign_e2, neg_e2, e1);
  udiv     = btor_udiv_exp (btor, cond_e1, cond_e2);
  neg_udiv = btor_neg_exp (btor, udiv);
  /* sign result if necessary */
  result = btor_cond_exp (btor, xor, neg_udiv, udiv);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, xor);
  btor_release_exp (btor, neg_e1);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, cond_e1);
  btor_release_exp (btor, cond_e2);
  btor_release_exp (btor, udiv);
  btor_release_exp (btor, neg_udiv);
  return result;
}

BtorNode *
btor_sdivo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *int_min, *ones, *eq1, *eq2;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  int_min = int_min_exp (btor, btor_get_exp_width (btor, e0));
  ones    = btor_ones_exp (btor, btor_exp_get_sort_id (e1));
  eq1     = btor_eq_exp (btor, e0, int_min);
  eq2     = btor_eq_exp (btor, e1, ones);
  result  = btor_and_exp (btor, eq1, eq2);
  btor_release_exp (btor, int_min);
  btor_release_exp (btor, ones);
  btor_release_exp (btor, eq1);
  btor_release_exp (btor, eq2);
  return result;
}

BtorNode *
btor_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_UREM_NODE, e0, e1);
  else
    result = btor_urem_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_srem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1;
  BtorNode *cond_e0, *cond_e1, *urem, *neg_urem;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);

  if (width == 1) return btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1));

  sign_e0 = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e1 = btor_slice_exp (btor, e1, width - 1, width - 1);
  neg_e0  = btor_neg_exp (btor, e0);
  neg_e1  = btor_neg_exp (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e0  = btor_cond_exp (btor, sign_e0, neg_e0, e0);
  cond_e1  = btor_cond_exp (btor, sign_e1, neg_e1, e1);
  urem     = btor_urem_exp (btor, cond_e0, cond_e1);
  neg_urem = btor_neg_exp (btor, urem);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = btor_cond_exp (btor, sign_e0, neg_urem, urem);
  btor_release_exp (btor, sign_e0);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, neg_e0);
  btor_release_exp (btor, neg_e1);
  btor_release_exp (btor, cond_e0);
  btor_release_exp (btor, cond_e1);
  btor_release_exp (btor, urem);
  btor_release_exp (btor, neg_urem);
  return result;
}

BtorNode *
btor_smod_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1, *cond_e0, *cond_e1;
  BtorNode *neg_e0_and_e1, *neg_e0_and_neg_e1, *zero, *e0_zero;
  BtorNode *neg_urem, *add1, *add2, *or1, *or2, *e0_and_e1, *e0_and_neg_e1;
  BtorNode *cond_case1, *cond_case2, *cond_case3, *cond_case4, *urem;
  BtorNode *urem_zero, *gadd1, *gadd2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width     = btor_get_exp_width (btor, e0);
  zero      = btor_zero_exp (btor, btor_exp_get_sort_id (e0));
  e0_zero   = btor_eq_exp (btor, zero, e0);
  sign_e0   = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e1   = btor_slice_exp (btor, e1, width - 1, width - 1);
  neg_e0    = btor_neg_exp (btor, e0);
  neg_e1    = btor_neg_exp (btor, e1);
  e0_and_e1 = btor_and_exp (
      btor, BTOR_INVERT_NODE (sign_e0), BTOR_INVERT_NODE (sign_e1));
  e0_and_neg_e1     = btor_and_exp (btor, BTOR_INVERT_NODE (sign_e0), sign_e1);
  neg_e0_and_e1     = btor_and_exp (btor, sign_e0, BTOR_INVERT_NODE (sign_e1));
  neg_e0_and_neg_e1 = btor_and_exp (btor, sign_e0, sign_e1);
  /* normalize e0 and e1 if necessary */
  cond_e0    = btor_cond_exp (btor, sign_e0, neg_e0, e0);
  cond_e1    = btor_cond_exp (btor, sign_e1, neg_e1, e1);
  urem       = btor_urem_exp (btor, cond_e0, cond_e1);
  urem_zero  = btor_eq_exp (btor, urem, zero);
  neg_urem   = btor_neg_exp (btor, urem);
  add1       = btor_add_exp (btor, neg_urem, e1);
  add2       = btor_add_exp (btor, urem, e1);
  gadd1      = btor_cond_exp (btor, urem_zero, zero, add1);
  gadd2      = btor_cond_exp (btor, urem_zero, zero, add2);
  cond_case1 = btor_cond_exp (btor, e0_and_e1, urem, zero);
  cond_case2 = btor_cond_exp (btor, neg_e0_and_e1, gadd1, zero);
  cond_case3 = btor_cond_exp (btor, e0_and_neg_e1, gadd2, zero);
  cond_case4 = btor_cond_exp (btor, neg_e0_and_neg_e1, neg_urem, zero);
  or1        = btor_or_exp (btor, cond_case1, cond_case2);
  or2        = btor_or_exp (btor, cond_case3, cond_case4);
  result     = btor_or_exp (btor, or1, or2);
  btor_release_exp (btor, zero);
  btor_release_exp (btor, e0_zero);
  btor_release_exp (btor, sign_e0);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, neg_e0);
  btor_release_exp (btor, neg_e1);
  btor_release_exp (btor, cond_e0);
  btor_release_exp (btor, cond_e1);
  btor_release_exp (btor, urem_zero);
  btor_release_exp (btor, cond_case1);
  btor_release_exp (btor, cond_case2);
  btor_release_exp (btor, cond_case3);
  btor_release_exp (btor, cond_case4);
  btor_release_exp (btor, urem);
  btor_release_exp (btor, neg_urem);
  btor_release_exp (btor, add1);
  btor_release_exp (btor, add2);
  btor_release_exp (btor, gadd1);
  btor_release_exp (btor, gadd2);
  btor_release_exp (btor, or1);
  btor_release_exp (btor, or2);
  btor_release_exp (btor, e0_and_e1);
  btor_release_exp (btor, neg_e0_and_e1);
  btor_release_exp (btor, e0_and_neg_e1);
  btor_release_exp (btor, neg_e0_and_neg_e1);
  return result;
}

BtorNode *
btor_read_exp (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_index)->btor);

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));
  return btor_apply_exps (btor, e_array, &e_index, 1);
}

BtorNode *
btor_write_exp (Btor *btor,
                BtorNode *e_array,
                BtorNode *e_index,
                BtorNode *e_value)
{
  assert (btor);
  assert (btor_is_array_node (btor_simplify_exp (btor, e_array)));
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_index)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_value)->btor);

  BtorNode *param, *e_cond, *e_if, *e_else, *bvcond, *args;
  BtorLambdaNode *lambda;
  BtorPtrHashBucket *b;

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));

  param  = btor_param_exp (btor, btor_exp_get_sort_id (e_index), 0);
  e_cond = btor_eq_exp (btor, param, e_index);
  e_if   = btor_copy_exp (btor, e_value);
  e_else = btor_read_exp (btor, e_array, param);
  bvcond = btor_cond_exp (btor, e_cond, e_if, e_else);
  lambda = (BtorLambdaNode *) btor_lambda_exp (btor, param, bvcond);
  if (!lambda->static_rho)
  {
    lambda->static_rho =
        btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_hash_exp_by_id,
                                (BtorCmpPtr) btor_compare_exp_by_id);
    args           = btor_args_exp (btor, &e_index, 1);
    b              = btor_hashptr_table_add (lambda->static_rho, args);
    b->data.as_ptr = btor_copy_exp (btor, e_value);
  }
  //#ifndef NDEBUG
  //  else
  //    {
  //      if (lambda->static_rho->count == 1)
  //	{
  //	  assert ((args = lambda->static_rho->first->key)
  //		  && args->e[0] == e_index);
  //	  assert (((BtorNode *) lambda->static_rho->first->data.as_ptr)
  //		  == e_value);
  //	}
  //      else
  //	{
  //	  BtorPtrHashTableIterator it;
  //	  btor_iter_hashptr_init (&it, lambda->static_rho);
  //	  while (btor_iter_hashptr_has_next (&it))
  //	    {
  //	      assert (it.bucket->data.as_ptr == e_value);
  //	      (void) btor_iter_hashptr_next (&it);
  //	    }
  //	}
  //    }
  //#endif

  btor_release_exp (btor, e_if);
  btor_release_exp (btor, e_else);
  btor_release_exp (btor, e_cond);
  btor_release_exp (btor, bvcond);
  btor_release_exp (btor, param);

  lambda->is_array = 1;
  return (BtorNode *) lambda;
}

BtorNode *
btor_inc_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, btor_exp_get_sort_id (exp));
  result = btor_add_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_dec_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, btor_exp_get_sort_id (exp));
  result = btor_sub_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_create_exp (Btor *btor, BtorNodeKind kind, BtorNode *e[], uint32_t arity)
{
  assert (arity > 0);
  assert (arity <= 3);

  switch (kind)
  {
    case BTOR_AND_NODE:
      assert (arity == 2);
      return btor_and_exp (btor, e[0], e[1]);
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE:
      assert (arity == 2);
      return btor_eq_exp (btor, e[0], e[1]);
    case BTOR_ADD_NODE:
      assert (arity == 2);
      return btor_add_exp (btor, e[0], e[1]);
    case BTOR_MUL_NODE:
      assert (arity == 2);
      return btor_mul_exp (btor, e[0], e[1]);
    case BTOR_ULT_NODE:
      assert (arity == 2);
      return btor_ult_exp (btor, e[0], e[1]);
    case BTOR_SLL_NODE:
      assert (arity == 2);
      return btor_sll_exp (btor, e[0], e[1]);
    case BTOR_SRL_NODE:
      assert (arity == 2);
      return btor_srl_exp (btor, e[0], e[1]);
    case BTOR_UDIV_NODE:
      assert (arity == 2);
      return btor_udiv_exp (btor, e[0], e[1]);
    case BTOR_UREM_NODE:
      assert (arity == 2);
      return btor_urem_exp (btor, e[0], e[1]);
    case BTOR_CONCAT_NODE:
      assert (arity == 2);
      return btor_concat_exp (btor, e[0], e[1]);
    case BTOR_APPLY_NODE:
      assert (arity == 2);
      return btor_apply_exp (btor, e[0], e[1]);
    case BTOR_LAMBDA_NODE:
      assert (arity == 2);
      return btor_lambda_exp (btor, e[0], e[1]);
    case BTOR_COND_NODE:
      assert (arity == 3);
      return btor_cond_exp (btor, e[0], e[1], e[2]);
    default:
      assert (kind == BTOR_ARGS_NODE);
      return btor_args_exp (btor, e, arity);
  }
  return 0;
}

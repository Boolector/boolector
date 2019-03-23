/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorexp.h"

#include "btorcore.h"
#include "btordbg.h"
#include "btorrewrite.h"

#include <limits.h>

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_create (Btor *btor, BtorNodeKind kind, BtorNode *e[], uint32_t arity)
{
  assert (arity > 0);
  assert (arity <= 3);

  switch (kind)
  {
    case BTOR_BV_AND_NODE:
      assert (arity == 2);
      return btor_exp_bv_and (btor, e[0], e[1]);
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE:
      assert (arity == 2);
      return btor_exp_eq (btor, e[0], e[1]);
    case BTOR_BV_ADD_NODE:
      assert (arity == 2);
      return btor_exp_bv_add (btor, e[0], e[1]);
    case BTOR_BV_MUL_NODE:
      assert (arity == 2);
      return btor_exp_bv_mul (btor, e[0], e[1]);
    case BTOR_BV_ULT_NODE:
      assert (arity == 2);
      return btor_exp_bv_ult (btor, e[0], e[1]);
    case BTOR_BV_SLL_NODE:
      assert (arity == 2);
      return btor_exp_bv_sll (btor, e[0], e[1]);
    case BTOR_BV_SRL_NODE:
      assert (arity == 2);
      return btor_exp_bv_srl (btor, e[0], e[1]);
    case BTOR_BV_UDIV_NODE:
      assert (arity == 2);
      return btor_exp_bv_udiv (btor, e[0], e[1]);
    case BTOR_BV_UREM_NODE:
      assert (arity == 2);
      return btor_exp_bv_urem (btor, e[0], e[1]);
    case BTOR_BV_CONCAT_NODE:
      assert (arity == 2);
      return btor_exp_bv_concat (btor, e[0], e[1]);
    case BTOR_APPLY_NODE:
      assert (arity == 2);
      return btor_exp_apply (btor, e[0], e[1]);
    case BTOR_LAMBDA_NODE:
      assert (arity == 2);
      return btor_exp_lambda (btor, e[0], e[1]);
    case BTOR_EXISTS_NODE:
      assert (arity == 2);
      return btor_exp_exists (btor, e[0], e[1]);
    case BTOR_FORALL_NODE:
      assert (arity == 2);
      return btor_exp_forall (btor, e[0], e[1]);
    case BTOR_COND_NODE:
      assert (arity == 3);
      return btor_exp_cond (btor, e[0], e[1], e[2]);
    case BTOR_UPDATE_NODE:
      assert (arity == 3);
      return btor_exp_update (btor, e[0], e[1], e[2]);
    default:
      assert (kind == BTOR_ARGS_NODE);
      return btor_exp_args (btor, e, arity);
  }
  return 0;
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_var (Btor *btor, BtorSortId sort, const char *symbol)
{
  return btor_node_create_var (btor, sort, symbol);
}

BtorNode *
btor_exp_param (Btor *btor, BtorSortId sort, const char *symbol)
{
  return btor_node_create_param (btor, sort, symbol);
}

BtorNode *
btor_exp_array (Btor *btor, BtorSortId sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_fun (btor, sort));
  assert (
      btor_sort_tuple_get_arity (btor, btor_sort_fun_get_domain (btor, sort))
      == 1);

  BtorNode *exp;

  exp           = btor_exp_uf (btor, sort, symbol);
  exp->is_array = 1;

  return exp;
}

BtorNode *
btor_exp_uf (Btor *btor, BtorSortId sort, const char *symbol)
{
  return btor_node_create_uf (btor, sort, symbol);
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_true (Btor *btor)
{
  assert (btor);

  BtorSortId sort;
  BtorNode *result;

  sort   = btor_sort_bv (btor, 1);
  result = btor_exp_bv_one (btor, sort);
  btor_sort_release (btor, sort);
  return result;
}

BtorNode *
btor_exp_false (Btor *btor)
{
  assert (btor);

  BtorSortId sort;
  BtorNode *result;

  sort   = btor_sort_bv (btor, 1);
  result = btor_exp_bv_zero (btor, sort);
  btor_sort_release (btor, sort);
  return result;
}

BtorNode *
btor_exp_implies (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  assert (btor_node_bv_get_width (btor, e0) == 1);
  return btor_node_invert (btor_exp_bv_and (btor, e0, btor_node_invert (e1)));
}

BtorNode *
btor_exp_iff (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  assert (btor_node_bv_get_width (btor, e0) == 1);
  return btor_exp_eq (btor, e0, e1);
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_eq_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
  {
    if (btor_node_is_fun (e0))
      result = btor_rewrite_binary_exp (btor, BTOR_FUN_EQ_NODE, e0, e1);
    else
      result = btor_rewrite_binary_exp (btor, BTOR_BV_EQ_NODE, e0, e1);
  }
  else
    result = btor_node_create_eq (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_ne (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_eq_exp (btor, e0, e1));
  return btor_node_invert (btor_exp_eq (btor, e0, e1));
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_cond (Btor *btor, BtorNode *e_cond, BtorNode *e_if, BtorNode *e_else)
{
  assert (btor == btor_node_real_addr (e_cond)->btor);
  assert (btor == btor_node_real_addr (e_if)->btor);
  assert (btor == btor_node_real_addr (e_else)->btor);

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_ternary_exp (
        btor, BTOR_COND_NODE, e_cond, e_if, e_else);

  return btor_node_create_cond (btor, e_cond, e_if, e_else);
}

BtorNode *
btor_exp_bv_const (Btor *btor, const BtorBitVector *bits)
{
  return btor_node_create_bv_const (btor, bits);
}

/*------------------------------------------------------------------------*/

static BtorNode *
int_min_exp (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv = btor_bv_new (btor->mm, width);
  btor_bv_set_bit (bv, bv->width - 1, 1);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_zero (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_new (btor->mm, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_ones (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_ones (btor->mm, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_one (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_one (btor->mm, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_min_signed (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_min_signed (btor->mm, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_max_signed (Btor *btor, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_max_signed (btor->mm, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_int (Btor *btor, int32_t i, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_int64_to_bv (btor->mm, i, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

BtorNode *
btor_exp_bv_unsigned (Btor *btor, uint32_t u, BtorSortId sort)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));

  uint32_t width;
  BtorNode *result;
  BtorBitVector *bv;

  width  = btor_sort_bv_get_width (btor, sort);
  bv     = btor_bv_uint64_to_bv (btor->mm, u, width);
  result = btor_exp_bv_const (btor, bv);
  btor_bv_free (btor->mm, bv);
  return result;
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_bv_not (Btor *btor, BtorNode *exp)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));

  (void) btor;
  btor_node_copy (btor, exp);
  return btor_node_invert (exp);
}

BtorNode *
btor_exp_bv_neg (Btor *btor, BtorNode *exp)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result, *one;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));
  one    = btor_exp_bv_one (btor, btor_node_get_sort_id (exp));
  result = btor_exp_bv_add (btor, btor_node_invert (exp), one);
  btor_node_release (btor, one);
  return result;
}

BtorNode *
btor_exp_bv_redor (Btor *btor, BtorNode *exp)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result, *zero;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));

  zero   = btor_exp_bv_zero (btor, btor_node_get_sort_id (exp));
  result = btor_node_invert (btor_exp_eq (btor, exp, zero));
  btor_node_release (btor, zero);
  return result;
}

BtorNode *
btor_exp_bv_redxor (Btor *btor, BtorNode *exp)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result, *slice, *xor;
  uint32_t i, width;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));

  width = btor_node_bv_get_width (btor, exp);

  result = btor_exp_bv_slice (btor, exp, 0, 0);
  for (i = 1; i < width; i++)
  {
    slice = btor_exp_bv_slice (btor, exp, i, i);
    xor   = btor_exp_bv_xor (btor, result, slice);
    btor_node_release (btor, slice);
    btor_node_release (btor, result);
    result = xor;
  }
  return result;
}

BtorNode *
btor_exp_bv_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_slice_exp (btor, exp, upper, lower));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_slice_exp (btor, exp, upper, lower);
  else
    result = btor_node_create_bv_slice (btor, exp, upper, lower);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_redand (Btor *btor, BtorNode *exp)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result, *ones;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));

  ones   = btor_exp_bv_ones (btor, btor_node_get_sort_id (exp));
  result = btor_exp_eq (btor, exp, ones);
  btor_node_release (btor, ones);
  return result;
}

BtorNode *
btor_exp_bv_uext (Btor *btor, BtorNode *exp, uint32_t width)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result, *zero;
  BtorSortId sort;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_ext_exp (btor, exp));

  if (width == 0)
    result = btor_node_copy (btor, exp);
  else
  {
    assert (width > 0);
    sort = btor_sort_bv (btor, width);
    zero = btor_exp_bv_zero (btor, sort);
    btor_sort_release (btor, sort);
    result = btor_exp_bv_concat (btor, zero, exp);
    btor_node_release (btor, zero);
  }
  return result;
}

BtorNode *
btor_exp_bv_sext (Btor *btor, BtorNode *exp, uint32_t width)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *result, *zero, *ones, *neg, *cond;
  uint32_t exp_width;
  BtorSortId sort;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_ext_exp (btor, exp));

  if (width == 0)
    result = btor_node_copy (btor, exp);
  else
  {
    assert (width > 0);
    sort = btor_sort_bv (btor, width);
    zero = btor_exp_bv_zero (btor, sort);
    ones = btor_exp_bv_ones (btor, sort);
    btor_sort_release (btor, sort);
    exp_width = btor_node_bv_get_width (btor, exp);
    neg       = btor_exp_bv_slice (btor, exp, exp_width - 1, exp_width - 1);
    cond      = btor_exp_cond (btor, neg, ones, zero);
    result    = btor_exp_bv_concat (btor, cond, exp);
    btor_node_release (btor, zero);
    btor_node_release (btor, ones);
    btor_node_release (btor, neg);
    btor_node_release (btor, cond);
  }
  return result;
}

BtorNode *
btor_exp_bv_xor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, * or, *and;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  or     = btor_exp_bv_or (btor, e0, e1);
  and    = btor_exp_bv_and (btor, e0, e1);
  result = btor_exp_bv_and (btor, or, btor_node_invert (and));
  btor_node_release (btor, or);
  btor_node_release (btor, and);
  return result;
}

BtorNode *
btor_exp_bv_xnor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  return btor_node_invert (btor_exp_bv_xor (btor, e0, e1));
}

BtorNode *
btor_exp_bv_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_AND_NODE, e0, e1);
  else
    result = btor_node_create_bv_and (btor, e0, e1);

  assert (result);
  return result;
}

static BtorNode *
create_bin_n_exp (Btor *btor,
                  BtorNode *(*func) (Btor *, BtorNode *, BtorNode *),
                  BtorNode *args[],
                  uint32_t argc)
{
  assert (argc > 0);

  uint32_t i;
  BtorNode *result, *tmp, *arg;

  result = 0;
  for (i = 0; i < argc; i++)
  {
    arg = args[i];
    if (result)
    {
      tmp = func (btor, arg, result);
      btor_node_release (btor, result);
      result = tmp;
    }
    else
      result = btor_node_copy (btor, arg);
  }
  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_and_n (Btor *btor, BtorNode *args[], uint32_t argc)
{
  return create_bin_n_exp (btor, btor_exp_bv_and, args, argc);
}

BtorNode *
btor_exp_bv_nand (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  return btor_node_invert (btor_exp_bv_and (btor, e0, e1));
}

BtorNode *
btor_exp_bv_or (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  return btor_node_invert (
      btor_exp_bv_and (btor, btor_node_invert (e0), btor_node_invert (e1)));
}

BtorNode *
btor_exp_bv_nor (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  return btor_node_invert (btor_exp_bv_or (btor, e0, e1));
}
BtorNode *
btor_exp_bv_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_ADD_NODE, e0, e1);
  else
    result = btor_node_create_bv_add (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_uaddo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *add;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width   = btor_node_bv_get_width (btor, e0);
  uext_e1 = btor_exp_bv_uext (btor, e0, 1);
  uext_e2 = btor_exp_bv_uext (btor, e1, 1);
  add     = btor_exp_bv_add (btor, uext_e1, uext_e2);
  result  = btor_exp_bv_slice (btor, add, width, width);
  btor_node_release (btor, uext_e1);
  btor_node_release (btor, uext_e2);
  btor_node_release (btor, add);
  return result;
}

BtorNode *
btor_exp_bv_saddo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *sign_result;
  BtorNode *add, *and1, *and2, *or1, *or2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width       = btor_node_bv_get_width (btor, e0);
  sign_e1     = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  sign_e2     = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  add         = btor_exp_bv_add (btor, e0, e1);
  sign_result = btor_exp_bv_slice (btor, add, width - 1, width - 1);
  and1        = btor_exp_bv_and (btor, sign_e1, sign_e2);
  or1         = btor_exp_bv_and (btor, and1, btor_node_invert (sign_result));
  and2        = btor_exp_bv_and (
      btor, btor_node_invert (sign_e1), btor_node_invert (sign_e2));
  or2    = btor_exp_bv_and (btor, and2, sign_result);
  result = btor_exp_bv_or (btor, or1, or2);
  btor_node_release (btor, and1);
  btor_node_release (btor, and2);
  btor_node_release (btor, or1);
  btor_node_release (btor, or2);
  btor_node_release (btor, add);
  btor_node_release (btor, sign_e1);
  btor_node_release (btor, sign_e2);
  btor_node_release (btor, sign_result);
  return result;
}

BtorNode *
btor_exp_bv_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_MUL_NODE, e0, e1);
  else
    result = btor_node_create_bv_mul (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_umulo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *mul, *slice, *and, * or, **temps_e2;
  BtorSortId sort;
  uint32_t i, width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width = btor_node_bv_get_width (btor, e0);
  if (width == 1)
  {
    sort   = btor_sort_bv (btor, 1);
    result = btor_exp_bv_zero (btor, sort);
    btor_sort_release (btor, sort);
    return result;
  }
  BTOR_NEWN (btor->mm, temps_e2, width - 1);
  temps_e2[0] = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  for (i = 1; i < width - 1; i++)
  {
    slice       = btor_exp_bv_slice (btor, e1, width - 1 - i, width - 1 - i);
    temps_e2[i] = btor_exp_bv_or (btor, temps_e2[i - 1], slice);
    btor_node_release (btor, slice);
  }
  slice  = btor_exp_bv_slice (btor, e0, 1, 1);
  result = btor_exp_bv_and (btor, slice, temps_e2[0]);
  btor_node_release (btor, slice);
  for (i = 1; i < width - 1; i++)
  {
    slice = btor_exp_bv_slice (btor, e0, i + 1, i + 1);
    and   = btor_exp_bv_and (btor, slice, temps_e2[i]);
    or    = btor_exp_bv_or (btor, result, and);
    btor_node_release (btor, slice);
    btor_node_release (btor, and);
    btor_node_release (btor, result);
    result = or ;
  }
  uext_e1 = btor_exp_bv_uext (btor, e0, 1);
  uext_e2 = btor_exp_bv_uext (btor, e1, 1);
  mul     = btor_exp_bv_mul (btor, uext_e1, uext_e2);
  slice   = btor_exp_bv_slice (btor, mul, width, width);
  or      = btor_exp_bv_or (btor, result, slice);
  btor_node_release (btor, uext_e1);
  btor_node_release (btor, uext_e2);
  btor_node_release (btor, mul);
  btor_node_release (btor, slice);
  btor_node_release (btor, result);
  result = or ;
  for (i = 0; i < width - 1; i++) btor_node_release (btor, temps_e2[i]);
  BTOR_DELETEN (btor->mm, temps_e2, width - 1);
  return result;
}

BtorNode *
btor_exp_bv_smulo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sext_e1, *sext_e2, *sign_e1, *sign_e2, *sext_sign_e1;
  BtorNode *sext_sign_e2, *xor_sign_e1, *xor_sign_e2, *mul, *slice, *slice_n;
  BtorNode *slice_n_minus_1, *xor, *and, * or, **temps_e2;
  uint32_t i, width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width = btor_node_bv_get_width (btor, e0);
  if (width == 1) return btor_exp_bv_and (btor, e0, e1);
  if (width == 2)
  {
    sext_e1         = btor_exp_bv_sext (btor, e0, 1);
    sext_e2         = btor_exp_bv_sext (btor, e1, 1);
    mul             = btor_exp_bv_mul (btor, sext_e1, sext_e2);
    slice_n         = btor_exp_bv_slice (btor, mul, width, width);
    slice_n_minus_1 = btor_exp_bv_slice (btor, mul, width - 1, width - 1);
    result          = btor_exp_bv_xor (btor, slice_n, slice_n_minus_1);
    btor_node_release (btor, sext_e1);
    btor_node_release (btor, sext_e2);
    btor_node_release (btor, mul);
    btor_node_release (btor, slice_n);
    btor_node_release (btor, slice_n_minus_1);
  }
  else
  {
    sign_e1      = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
    sign_e2      = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
    sext_sign_e1 = btor_exp_bv_sext (btor, sign_e1, width - 1);
    sext_sign_e2 = btor_exp_bv_sext (btor, sign_e2, width - 1);
    xor_sign_e1  = btor_exp_bv_xor (btor, e0, sext_sign_e1);
    xor_sign_e2  = btor_exp_bv_xor (btor, e1, sext_sign_e2);
    BTOR_NEWN (btor->mm, temps_e2, width - 2);
    temps_e2[0] = btor_exp_bv_slice (btor, xor_sign_e2, width - 2, width - 2);
    for (i = 1; i < width - 2; i++)
    {
      slice =
          btor_exp_bv_slice (btor, xor_sign_e2, width - 2 - i, width - 2 - i);
      temps_e2[i] = btor_exp_bv_or (btor, temps_e2[i - 1], slice);
      btor_node_release (btor, slice);
    }
    slice  = btor_exp_bv_slice (btor, xor_sign_e1, 1, 1);
    result = btor_exp_bv_and (btor, slice, temps_e2[0]);
    btor_node_release (btor, slice);
    for (i = 1; i < width - 2; i++)
    {
      slice = btor_exp_bv_slice (btor, xor_sign_e1, i + 1, i + 1);
      and   = btor_exp_bv_and (btor, slice, temps_e2[i]);
      or    = btor_exp_bv_or (btor, result, and);
      btor_node_release (btor, slice);
      btor_node_release (btor, and);
      btor_node_release (btor, result);
      result = or ;
    }
    sext_e1         = btor_exp_bv_sext (btor, e0, 1);
    sext_e2         = btor_exp_bv_sext (btor, e1, 1);
    mul             = btor_exp_bv_mul (btor, sext_e1, sext_e2);
    slice_n         = btor_exp_bv_slice (btor, mul, width, width);
    slice_n_minus_1 = btor_exp_bv_slice (btor, mul, width - 1, width - 1);
    xor             = btor_exp_bv_xor (btor, slice_n, slice_n_minus_1);
    or              = btor_exp_bv_or (btor, result, xor);
    btor_node_release (btor, sext_e1);
    btor_node_release (btor, sext_e2);
    btor_node_release (btor, sign_e1);
    btor_node_release (btor, sign_e2);
    btor_node_release (btor, sext_sign_e1);
    btor_node_release (btor, sext_sign_e2);
    btor_node_release (btor, xor_sign_e1);
    btor_node_release (btor, xor_sign_e2);
    btor_node_release (btor, mul);
    btor_node_release (btor, slice_n);
    btor_node_release (btor, slice_n_minus_1);
    btor_node_release (btor, xor);
    btor_node_release (btor, result);
    result = or ;
    for (i = 0; i < width - 2; i++) btor_node_release (btor, temps_e2[i]);
    BTOR_DELETEN (btor->mm, temps_e2, width - 2);
  }
  return result;
}

BtorNode *
btor_exp_bv_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_ULT_NODE, e0, e1);
  else
    result = btor_node_create_bv_ult (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_slt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *determined_by_sign, *eq_sign, *ult, *eq_sign_and_ult;
  BtorNode *res, *s0, *s1, *r0, *r1, *l, *r;

  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width = btor_node_bv_get_width (btor, e0);
  if (width == 1) return btor_exp_bv_and (btor, e0, btor_node_invert (e1));
  s0                 = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  s1                 = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  r0                 = btor_exp_bv_slice (btor, e0, width - 2, 0);
  r1                 = btor_exp_bv_slice (btor, e1, width - 2, 0);
  ult                = btor_exp_bv_ult (btor, r0, r1);
  determined_by_sign = btor_exp_bv_and (btor, s0, btor_node_invert (s1));
  l                  = btor_node_copy (btor, determined_by_sign);
  r                  = btor_exp_bv_and (btor, btor_node_invert (s0), s1);
  eq_sign = btor_exp_bv_and (btor, btor_node_invert (l), btor_node_invert (r));
  eq_sign_and_ult = btor_exp_bv_and (btor, eq_sign, ult);
  res             = btor_exp_bv_or (btor, determined_by_sign, eq_sign_and_ult);
  btor_node_release (btor, s0);
  btor_node_release (btor, s1);
  btor_node_release (btor, r0);
  btor_node_release (btor, r1);
  btor_node_release (btor, ult);
  btor_node_release (btor, determined_by_sign);
  btor_node_release (btor, l);
  btor_node_release (btor, r);
  btor_node_release (btor, eq_sign);
  btor_node_release (btor, eq_sign_and_ult);
  return res;
}

BtorNode *
btor_exp_bv_ulte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *ult;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  ult    = btor_exp_bv_ult (btor, e1, e0);
  result = btor_exp_bv_not (btor, ult);
  btor_node_release (btor, ult);
  return result;
}

BtorNode *
btor_exp_bv_slte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *slt;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  slt    = btor_exp_bv_slt (btor, e1, e0);
  result = btor_exp_bv_not (btor, slt);
  btor_node_release (btor, slt);
  return result;
}

BtorNode *
btor_exp_bv_ugt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  return btor_exp_bv_ult (btor, e1, e0);
}

BtorNode *
btor_exp_bv_sgt (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));
  return btor_exp_bv_slt (btor, e1, e0);
}

BtorNode *
btor_exp_bv_ugte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *ult;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  ult    = btor_exp_bv_ult (btor, e0, e1);
  result = btor_exp_bv_not (btor, ult);
  btor_node_release (btor, ult);
  return result;
}

BtorNode *
btor_exp_bv_sgte (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *slt;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  slt    = btor_exp_bv_slt (btor, e0, e1);
  result = btor_exp_bv_not (btor, slt);
  btor_node_release (btor, slt);
  return result;
}

BtorNode *
btor_exp_bv_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_SLL_NODE, e0, e1);
  else
    result = btor_node_create_bv_sll (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_SRL_NODE, e0, e1);
  else
    result = btor_node_create_bv_srl (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_sra (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sign_e1, *srl1, *srl2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  width   = btor_node_bv_get_width (btor, e0);
  sign_e1 = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  srl1    = btor_exp_bv_srl (btor, e0, e1);
  srl2    = btor_exp_bv_srl (btor, btor_node_invert (e0), e1);
  result  = btor_exp_cond (btor, sign_e1, btor_node_invert (srl2), srl1);
  btor_node_release (btor, sign_e1);
  btor_node_release (btor, srl1);
  btor_node_release (btor, srl2);
  return result;
}

BtorNode *
btor_exp_bv_rol (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sll, *neg_e2, *srl;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  sll    = btor_exp_bv_sll (btor, e0, e1);
  neg_e2 = btor_exp_bv_neg (btor, e1);
  srl    = btor_exp_bv_srl (btor, e0, neg_e2);
  result = btor_exp_bv_or (btor, sll, srl);
  btor_node_release (btor, sll);
  btor_node_release (btor, neg_e2);
  btor_node_release (btor, srl);
  return result;
}

BtorNode *
btor_exp_bv_ror (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *srl, *neg_e2, *sll;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  srl    = btor_exp_bv_srl (btor, e0, e1);
  neg_e2 = btor_exp_bv_neg (btor, e1);
  sll    = btor_exp_bv_sll (btor, e0, neg_e2);
  result = btor_exp_bv_or (btor, srl, sll);
  btor_node_release (btor, srl);
  btor_node_release (btor, neg_e2);
  btor_node_release (btor, sll);
  return result;
}

BtorNode *
btor_exp_bv_sub (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *neg_e2;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  neg_e2 = btor_exp_bv_neg (btor, e1);
  result = btor_exp_bv_add (btor, e0, neg_e2);
  btor_node_release (btor, neg_e2);
  return result;
}

BtorNode *
btor_exp_bv_usubo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *add1, *add2, *one;
  BtorSortId sort;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width   = btor_node_bv_get_width (btor, e0);
  uext_e1 = btor_exp_bv_uext (btor, e0, 1);
  uext_e2 = btor_exp_bv_uext (btor, btor_node_invert (e1), 1);
  assert (width < INT32_MAX);
  sort = btor_sort_bv (btor, width + 1);
  one  = btor_exp_bv_one (btor, sort);
  btor_sort_release (btor, sort);
  add1   = btor_exp_bv_add (btor, uext_e2, one);
  add2   = btor_exp_bv_add (btor, uext_e1, add1);
  result = btor_node_invert (btor_exp_bv_slice (btor, add2, width, width));
  btor_node_release (btor, uext_e1);
  btor_node_release (btor, uext_e2);
  btor_node_release (btor, add1);
  btor_node_release (btor, add2);
  btor_node_release (btor, one);
  return result;
}

BtorNode *
btor_exp_bv_ssubo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *sign_result;
  BtorNode *sub, *and1, *and2, *or1, *or2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width       = btor_node_bv_get_width (btor, e0);
  sign_e1     = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  sign_e2     = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  sub         = btor_exp_bv_sub (btor, e0, e1);
  sign_result = btor_exp_bv_slice (btor, sub, width - 1, width - 1);
  and1        = btor_exp_bv_and (btor, btor_node_invert (sign_e1), sign_e2);
  or1         = btor_exp_bv_and (btor, and1, sign_result);
  and2        = btor_exp_bv_and (btor, sign_e1, btor_node_invert (sign_e2));
  or2         = btor_exp_bv_and (btor, and2, btor_node_invert (sign_result));
  result      = btor_exp_bv_or (btor, or1, or2);
  btor_node_release (btor, and1);
  btor_node_release (btor, and2);
  btor_node_release (btor, or1);
  btor_node_release (btor, or2);
  btor_node_release (btor, sub);
  btor_node_release (btor, sign_e1);
  btor_node_release (btor, sign_e2);
  btor_node_release (btor, sign_result);
  return result;
}

BtorNode *
btor_exp_bv_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_UDIV_NODE, e0, e1);
  else
    result = btor_node_create_bv_udiv (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_sdiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *xor, *neg_e1, *neg_e2;
  BtorNode *cond_e1, *cond_e2, *udiv, *neg_udiv;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width = btor_node_bv_get_width (btor, e0);

  if (width == 1)
    return btor_node_invert (btor_exp_bv_and (btor, btor_node_invert (e0), e1));

  sign_e1 = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  sign_e2 = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  /* xor: must result be signed? */
  xor    = btor_exp_bv_xor (btor, sign_e1, sign_e2);
  neg_e1 = btor_exp_bv_neg (btor, e0);
  neg_e2 = btor_exp_bv_neg (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_exp_cond (btor, sign_e1, neg_e1, e0);
  cond_e2  = btor_exp_cond (btor, sign_e2, neg_e2, e1);
  udiv     = btor_exp_bv_udiv (btor, cond_e1, cond_e2);
  neg_udiv = btor_exp_bv_neg (btor, udiv);
  /* sign result if necessary */
  result = btor_exp_cond (btor, xor, neg_udiv, udiv);
  btor_node_release (btor, sign_e1);
  btor_node_release (btor, sign_e2);
  btor_node_release (btor, xor);
  btor_node_release (btor, neg_e1);
  btor_node_release (btor, neg_e2);
  btor_node_release (btor, cond_e1);
  btor_node_release (btor, cond_e2);
  btor_node_release (btor, udiv);
  btor_node_release (btor, neg_udiv);
  return result;
}

BtorNode *
btor_exp_bv_sdivo (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *int_min, *ones, *eq1, *eq2;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  int_min = int_min_exp (btor, btor_node_bv_get_width (btor, e0));
  ones    = btor_exp_bv_ones (btor, btor_node_get_sort_id (e1));
  eq1     = btor_exp_eq (btor, e0, int_min);
  eq2     = btor_exp_eq (btor, e1, ones);
  result  = btor_exp_bv_and (btor, eq1, eq2);
  btor_node_release (btor, int_min);
  btor_node_release (btor, ones);
  btor_node_release (btor, eq1);
  btor_node_release (btor, eq2);
  return result;
}

BtorNode *
btor_exp_bv_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_UREM_NODE, e0, e1);
  else
    result = btor_node_create_bv_urem (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_srem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1;
  BtorNode *cond_e0, *cond_e1, *urem, *neg_urem;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width = btor_node_bv_get_width (btor, e0);

  if (width == 1) return btor_exp_bv_and (btor, e0, btor_node_invert (e1));

  sign_e0 = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  sign_e1 = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  neg_e0  = btor_exp_bv_neg (btor, e0);
  neg_e1  = btor_exp_bv_neg (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e0  = btor_exp_cond (btor, sign_e0, neg_e0, e0);
  cond_e1  = btor_exp_cond (btor, sign_e1, neg_e1, e1);
  urem     = btor_exp_bv_urem (btor, cond_e0, cond_e1);
  neg_urem = btor_exp_bv_neg (btor, urem);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = btor_exp_cond (btor, sign_e0, neg_urem, urem);
  btor_node_release (btor, sign_e0);
  btor_node_release (btor, sign_e1);
  btor_node_release (btor, neg_e0);
  btor_node_release (btor, neg_e1);
  btor_node_release (btor, cond_e0);
  btor_node_release (btor, cond_e1);
  btor_node_release (btor, urem);
  btor_node_release (btor, neg_urem);
  return result;
}

BtorNode *
btor_exp_bv_smod (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1, *cond_e0, *cond_e1;
  BtorNode *neg_e0_and_e1, *neg_e0_and_neg_e1, *zero, *e0_zero;
  BtorNode *neg_urem, *add1, *add2, *or1, *or2, *e0_and_e1, *e0_and_neg_e1;
  BtorNode *cond_case1, *cond_case2, *cond_case3, *cond_case4, *urem;
  BtorNode *urem_zero, *gadd1, *gadd2;
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  width     = btor_node_bv_get_width (btor, e0);
  zero      = btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
  e0_zero   = btor_exp_eq (btor, zero, e0);
  sign_e0   = btor_exp_bv_slice (btor, e0, width - 1, width - 1);
  sign_e1   = btor_exp_bv_slice (btor, e1, width - 1, width - 1);
  neg_e0    = btor_exp_bv_neg (btor, e0);
  neg_e1    = btor_exp_bv_neg (btor, e1);
  e0_and_e1 = btor_exp_bv_and (
      btor, btor_node_invert (sign_e0), btor_node_invert (sign_e1));
  e0_and_neg_e1 = btor_exp_bv_and (btor, btor_node_invert (sign_e0), sign_e1);
  neg_e0_and_e1 = btor_exp_bv_and (btor, sign_e0, btor_node_invert (sign_e1));
  neg_e0_and_neg_e1 = btor_exp_bv_and (btor, sign_e0, sign_e1);
  /* normalize e0 and e1 if necessary */
  cond_e0    = btor_exp_cond (btor, sign_e0, neg_e0, e0);
  cond_e1    = btor_exp_cond (btor, sign_e1, neg_e1, e1);
  urem       = btor_exp_bv_urem (btor, cond_e0, cond_e1);
  urem_zero  = btor_exp_eq (btor, urem, zero);
  neg_urem   = btor_exp_bv_neg (btor, urem);
  add1       = btor_exp_bv_add (btor, neg_urem, e1);
  add2       = btor_exp_bv_add (btor, urem, e1);
  gadd1      = btor_exp_cond (btor, urem_zero, zero, add1);
  gadd2      = btor_exp_cond (btor, urem_zero, zero, add2);
  cond_case1 = btor_exp_cond (btor, e0_and_e1, urem, zero);
  cond_case2 = btor_exp_cond (btor, neg_e0_and_e1, gadd1, zero);
  cond_case3 = btor_exp_cond (btor, e0_and_neg_e1, gadd2, zero);
  cond_case4 = btor_exp_cond (btor, neg_e0_and_neg_e1, neg_urem, zero);
  or1        = btor_exp_bv_or (btor, cond_case1, cond_case2);
  or2        = btor_exp_bv_or (btor, cond_case3, cond_case4);
  result     = btor_exp_bv_or (btor, or1, or2);
  btor_node_release (btor, zero);
  btor_node_release (btor, e0_zero);
  btor_node_release (btor, sign_e0);
  btor_node_release (btor, sign_e1);
  btor_node_release (btor, neg_e0);
  btor_node_release (btor, neg_e1);
  btor_node_release (btor, cond_e0);
  btor_node_release (btor, cond_e1);
  btor_node_release (btor, urem_zero);
  btor_node_release (btor, cond_case1);
  btor_node_release (btor, cond_case2);
  btor_node_release (btor, cond_case3);
  btor_node_release (btor, cond_case4);
  btor_node_release (btor, urem);
  btor_node_release (btor, neg_urem);
  btor_node_release (btor, add1);
  btor_node_release (btor, add2);
  btor_node_release (btor, gadd1);
  btor_node_release (btor, gadd2);
  btor_node_release (btor, or1);
  btor_node_release (btor, or2);
  btor_node_release (btor, e0_and_e1);
  btor_node_release (btor, neg_e0_and_e1);
  btor_node_release (btor, e0_and_neg_e1);
  btor_node_release (btor, neg_e0_and_neg_e1);
  return result;
}

BtorNode *
btor_exp_bv_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (btor == btor_node_real_addr (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_concat_exp (btor, e0, e1));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_BV_CONCAT_NODE, e0, e1);
  else
    result = btor_node_create_bv_concat (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_repeat (Btor *btor, BtorNode *exp, uint32_t n)
{
  assert (btor == btor_node_real_addr (exp)->btor);
  assert (((uint32_t) UINT32_MAX / n) >= btor_node_bv_get_width (btor, exp));

  BtorNode *result, *tmp;
  uint32_t i;

  result = btor_node_copy (btor, exp);
  for (i = 1; i < n; i++)
  {
    tmp    = result;
    result = btor_exp_bv_concat (btor, tmp, exp);
    btor_node_release (btor, tmp);
  }
  assert (result);
  return result;
}

BtorNode *
btor_exp_bv_inc (Btor *btor, BtorNode *exp)
{
  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));

  one    = btor_exp_bv_one (btor, btor_node_get_sort_id (exp));
  result = btor_exp_bv_add (btor, exp, one);
  btor_node_release (btor, one);
  return result;
}

BtorNode *
btor_exp_bv_dec (Btor *btor, BtorNode *exp)
{
  assert (btor == btor_node_real_addr (exp)->btor);

  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));

  one    = btor_exp_bv_one (btor, btor_node_get_sort_id (exp));
  result = btor_exp_bv_sub (btor, exp, one);
  btor_node_release (btor, one);
  return result;
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_read (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
  assert (btor == btor_node_real_addr (e_array)->btor);
  assert (btor == btor_node_real_addr (e_index)->btor);

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  assert (btor_dbg_precond_read_exp (btor, e_array, e_index));
  return btor_exp_apply_n (btor, e_array, &e_index, 1);
}

BtorNode *
btor_exp_write (Btor *btor,
                BtorNode *e_array,
                BtorNode *e_index,
                BtorNode *e_value)
{
  assert (btor);
  assert (btor_node_is_array (btor_simplify_exp (btor, e_array)));
  assert (btor == btor_node_real_addr (e_array)->btor);
  assert (btor == btor_node_real_addr (e_index)->btor);
  assert (btor == btor_node_real_addr (e_value)->btor);

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  assert (btor_dbg_precond_write_exp (btor, e_array, e_index, e_value));

  if (btor_opt_get (btor, BTOR_OPT_FUN_STORE_LAMBDAS)
      || btor_node_real_addr (e_index)->parameterized
      || btor_node_real_addr (e_value)->parameterized)
  {
    return btor_exp_lambda_write (btor, e_array, e_index, e_value);
  }
  else
  {
    BtorNode *args = btor_exp_args (btor, &e_index, 1);
    BtorNode *res  = btor_exp_update (btor, e_array, args, e_value);
    btor_node_release (btor, args);
    res->is_array = 1;
    return res;
  }
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_exp_fun (Btor *btor, BtorNode *params[], uint32_t paramc, BtorNode *exp)
{
  assert (btor);
  assert (paramc > 0);
  assert (params);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);
  assert (!btor_node_is_uf (exp));

  uint32_t i, j;
  BtorNode *fun      = btor_simplify_exp (btor, exp);
  BtorNode *prev_fun = 0;

  for (i = 1; i <= paramc; i++)
  {
    j = paramc - i;
    assert (params[j]);
    assert (btor == btor_node_real_addr (params[j])->btor);
    assert (btor_node_is_param (params[j]));
    fun = btor_exp_lambda (btor, params[j], fun);
    if (prev_fun) btor_node_release (btor, prev_fun);
    prev_fun = fun;
  }

  return fun;
}

BtorNode *
btor_exp_apply (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor == btor_node_real_addr (fun)->btor);
  assert (btor == btor_node_real_addr (args)->btor);

  fun  = btor_simplify_exp (btor, fun);
  args = btor_simplify_exp (btor, args);
  assert (btor_node_is_fun (fun));
  assert (btor_node_is_args (args));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_binary_exp (btor, BTOR_APPLY_NODE, fun, args);

  return btor_node_create_apply (btor, fun, args);
}

BtorNode *
btor_exp_apply_n (Btor *btor, BtorNode *fun, BtorNode *args[], uint32_t argc)
{
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);

  BtorNode *exp, *_args;

  _args = btor_exp_args (btor, args, argc);
  fun   = btor_simplify_exp (btor, fun);
  _args = btor_simplify_exp (btor, _args);

  exp = btor_exp_apply (btor, fun, _args);
  btor_node_release (btor, _args);

  return exp;
}

BtorNode *
btor_exp_args (Btor *btor, BtorNode *args[], uint32_t argc)
{
  return btor_node_create_args (btor, args, argc);
}

BtorNode *
btor_exp_update (Btor *btor, BtorNode *fun, BtorNode *args, BtorNode *value)
{
  return btor_node_create_update (btor, fun, args, value);
}

BtorNode *
btor_exp_lambda (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (btor_node_is_regular (e_param));
  assert (btor == e_param->btor);
  assert (btor_node_is_param (e_param));
  assert (!btor_node_real_addr (e_param)->simplified);
  assert (e_exp);
  assert (btor == btor_node_real_addr (e_exp)->btor);

  BtorNode *result;
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_LAMBDA_NODE, e_param, e_exp);
  else
    result = btor_node_create_lambda (btor, e_param, e_exp);
  assert (btor_node_is_fun (result));
  return result;
}

BtorNode *
btor_exp_lambda_write (Btor *btor,
                       BtorNode *e_array,
                       BtorNode *e_index,
                       BtorNode *e_value)
{
  BtorNode *param, *e_cond, *e_if, *e_else, *bvcond, *args;
  BtorLambdaNode *lambda;
  BtorPtrHashBucket *b;

  param  = btor_exp_param (btor, btor_node_get_sort_id (e_index), 0);
  e_cond = btor_exp_eq (btor, param, e_index);
  e_if   = btor_node_copy (btor, e_value);
  e_else = btor_exp_read (btor, e_array, param);
  bvcond = btor_exp_cond (btor, e_cond, e_if, e_else);
  lambda = (BtorLambdaNode *) btor_exp_lambda (btor, param, bvcond);
  if (!lambda->static_rho)
  {
    lambda->static_rho =
        btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    args           = btor_exp_args (btor, &e_index, 1);
    b              = btor_hashptr_table_add (lambda->static_rho, args);
    b->data.as_ptr = btor_node_copy (btor, e_value);
  }
  btor_node_release (btor, e_if);
  btor_node_release (btor, e_else);
  btor_node_release (btor, e_cond);
  btor_node_release (btor, bvcond);
  btor_node_release (btor, param);

  lambda->is_array = 1;
  return (BtorNode *) lambda;
}

/*------------------------------------------------------------------------*/

static BtorNode *
quantifier_exp (Btor *btor, BtorNodeKind kind, BtorNode *param, BtorNode *body)
{
  assert (btor);
  assert (kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE);
  assert (param);

  param = btor_simplify_exp (btor, param);
  body  = btor_simplify_exp (btor, body);

  assert (btor_node_is_regular (param));
  assert (btor_node_is_param (param));
  assert (body);
  assert (btor_sort_is_bool (btor, btor_node_real_addr (body)->sort_id));
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_binary_exp (btor, kind, param, body);
  return btor_node_create_quantifier (btor, kind, param, body);
}

static BtorNode *
quantifier_n_exp (Btor *btor,
                  BtorNodeKind kind,
                  BtorNode *params[],
                  uint32_t n,
                  BtorNode *body)
{
  assert (btor);
  assert (kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE);
  assert (params);
  assert (n > 0);
  assert (body);
  assert (btor == btor_node_real_addr (body)->btor);

  uint32_t i, j;
  BtorNode *res, *tmp;

  res = btor_node_copy (btor, body);
  for (j = 1, i = n - 1; j <= n; j++, i--)
  {
    assert (params[i]);
    assert (btor == btor_node_real_addr (params[i])->btor);
    assert (btor_node_is_param (params[i]));
    tmp = quantifier_exp (btor, kind, params[i], res);
    btor_node_release (btor, res);
    res = tmp;
  }
  return res;
}

BtorNode *
btor_exp_forall (Btor *btor, BtorNode *param, BtorNode *body)
{
  return quantifier_exp (btor, BTOR_FORALL_NODE, param, body);
}

BtorNode *
btor_exp_forall_n (Btor *btor, BtorNode *params[], uint32_t n, BtorNode *body)
{
  return quantifier_n_exp (btor, BTOR_FORALL_NODE, params, n, body);
}

BtorNode *
btor_exp_exists (Btor *btor, BtorNode *param, BtorNode *body)
{
  return quantifier_exp (btor, BTOR_EXISTS_NODE, param, body);
}

BtorNode *
btor_exp_exists_n (Btor *btor, BtorNode *params[], uint32_t n, BtorNode *body)
{
  return quantifier_n_exp (btor, BTOR_EXISTS_NODE, params, n, body);
}


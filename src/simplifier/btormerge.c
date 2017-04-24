/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btormerge.h"
#include "btorbeta.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorlog.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

//#ifndef NDEBUG
// static bool
// btor_check_static_rho_equal_dbg (BtorPtrHashTable * t0, BtorPtrHashTable *
// t1)
//{
//  assert (t0);
//  assert (t1);
//  assert (t0->count == t1->count);
//
//  BtorPtrHashTableIterator it;
//  BtorPtrHashBucket *b;
//  BtorNode *value, *args;
//
//  btor_init_ptr_hash_table_iterator (&it, t0);
//  while (btor_has_next_ptr_hash_table_iterator (&it))
//    {
//      value = it.bucket->data.as_ptr;
//      args = btor_next_ptr_hash_table_iterator (&it);
//      assert (args->arity == 1);
//      b = btor_get_ptr_hash_table (t1, args);
//      assert (b);
//      assert (b->data.as_ptr == value);
//    }
//  return true;
//}
//#endif

static void
delete_static_rho (Btor *btor, BtorPtrHashTable *static_rho)
{
  BtorPtrHashTableIterator it;

  btor_init_ptr_hash_table_iterator (&it, static_rho);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    btor_release_exp (btor, it.bucket->data.as_ptr);
    btor_release_exp (btor, btor_next_ptr_hash_table_iterator (&it));
  }
  btor_delete_ptr_hash_table (static_rho);
}

static void
add_to_static_rho (Btor *btor, BtorPtrHashTable *to, BtorPtrHashTable *from)
{
  BtorNode *data, *key;
  BtorPtrHashTableIterator it;

  if (!from) return;

  btor_init_ptr_hash_table_iterator (&it, from);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    data = it.bucket->data.as_ptr;
    key  = btor_next_ptr_hash_table_iterator (&it);
    if (btor_get_ptr_hash_table (to, key)) continue;
    btor_add_ptr_hash_table (to, btor_copy_exp (btor, key))->data.as_ptr =
        btor_copy_exp (btor, data);
  }
}

void
btor_merge_lambdas (Btor *btor)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0);

  unsigned num_merged_lambdas = 0;
  int i;
  double start, delta;
  BtorNode *cur, *lambda, *subst, *parent, *param, *body;
  BtorMemMgr *mm;
  BtorPtrHashTableIterator it;
  BtorNodeIterator nit;
  BtorNodePtrStack stack, visit, params;
  BtorPtrHashTable *merge_lambdas, *static_rho;
  BtorIntHashTable *mark, *mark_lambda;

  if (btor->lambdas->count == 0) return;

  start = btor_time_stamp ();
  mm    = btor->mm;

  mark        = btor_new_int_hash_table (mm);
  mark_lambda = btor_new_int_hash_table (mm);
  btor_init_substitutions (btor);
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, params);

  /* collect candidates for merging */
  btor_init_ptr_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    lambda = btor_next_ptr_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    /* found top lambda */
    parent = BTOR_REAL_ADDR_NODE (lambda->first_parent);
    if (lambda->parents > 1
        || lambda->parents == 0
        /* case lambda->parents == 1 */
        || (!parent->parameterized
            && (btor_is_apply_node (parent) || btor_is_fun_eq_node (parent))))
    {
      BTOR_PUSH_STACK (stack, lambda);
      continue;
    }
  }

  while (!BTOR_EMPTY_STACK (stack))
  {
    lambda = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    if (btor_contains_int_hash_table (mark_lambda, lambda->id)) continue;

    btor_add_int_hash_table (mark_lambda, lambda->id);
    /* search downwards and look for lambdas that can be merged */
    BTOR_RESET_STACK (visit);
    BTOR_PUSH_STACK (visit, btor_lambda_get_body (lambda));
    merge_lambdas =
        btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    btor_add_ptr_hash_table (merge_lambdas, lambda);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (btor_contains_int_hash_table (mark, cur->id)
          || (!btor_is_lambda_node (cur) && !cur->parameterized)
          || !cur->lambda_below)
        continue;

      if (btor_is_lambda_node (cur))
      {
        /* lambdas with more than one parents cannot be merged */
        if (cur->parents > 1)
        {
          /* try to merge lambdas starting from 'cur' */
          BTOR_PUSH_STACK (stack, cur);
          continue;
        }

        /* we can only merge lambdas that have all a static_rho or
         * none of them has one */
        if (!btor_lambda_get_static_rho (cur)
                != !btor_lambda_get_static_rho (lambda)
            /* we can only merge lambdas that either represent arrays
             * or not */
            || cur->is_array != lambda->is_array)
        {
          /* try to merge lambdas starting from 'cur' */
          BTOR_PUSH_STACK (stack, cur);
          continue;
        }

        if (!btor_get_ptr_hash_table (merge_lambdas, cur))
          btor_add_ptr_hash_table (merge_lambdas, cur);
        BTOR_PUSH_STACK (visit, btor_lambda_get_body (cur));
      }
      else
      {
        for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
      }
      btor_add_int_hash_table (mark, cur->id);
    }

    /* no lambdas to merge found */
    if (merge_lambdas->count <= 1)
    {
      btor_delete_ptr_hash_table (merge_lambdas);
      continue;
    }

    /* assign parameters of top-most lambda with fresh parameters */
    btor_init_lambda_iterator (&nit, lambda);
    while (btor_has_next_lambda_iterator (&nit))
    {
      cur   = btor_next_lambda_iterator (&nit);
      param = btor_param_exp (btor, btor_exp_get_sort_id (cur->e[0]), 0);
      BTOR_PUSH_STACK (params, param);
      btor_beta_assign_param (btor, cur, param);
    }
    /* merge lambdas that are in 'merge_lambdas' table */
    body = btor_beta_reduce_merge (
        btor, btor_lambda_get_body (lambda), merge_lambdas);
    btor_beta_unassign_params (btor, lambda);
    subst = btor_fun_exp (btor, params.start, BTOR_COUNT_STACK (params), body);
    if (lambda->is_array) subst->is_array = 1;
    btor_release_exp (btor, body);

    /* generate static_rho from merged lambdas' static_rhos */
    assert (merge_lambdas->count > 0);
    num_merged_lambdas += merge_lambdas->count;
    static_rho = btor_new_ptr_hash_table (mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
    if (btor_lambda_get_static_rho (lambda))
    {
      btor_init_ptr_hash_table_iterator (&it, merge_lambdas);
      while (btor_has_next_ptr_hash_table_iterator (&it))
      {
        cur = btor_next_ptr_hash_table_iterator (&it);
        add_to_static_rho (btor, static_rho, btor_lambda_get_static_rho (cur));
        assert (!btor_lambda_get_static_rho (lambda)
                == !btor_lambda_get_static_rho (cur));
      }
    }
    BTORLOG (2,
             "merged %u lambdas (%u static_rho entries)",
             merge_lambdas->count,
             static_rho->count);
    btor_delete_ptr_hash_table (merge_lambdas);

    if (static_rho->count > 0)
    {
      /* 'subst' is already an existing lambda with a 'static_rho', if
       * this is the case we have to check that subst->static_rho constains
       * the same elements as static_rho */
      if (btor_lambda_get_static_rho (subst))
      {
        //	      assert (btor_check_static_rho_equal_dbg (
        //			   btor_lambda_get_static_rho (subst),
        // static_rho));
        /* 'static_rho' contains elements so we have to release them
         * properly */
        delete_static_rho (btor, static_rho);
      }
      else
        btor_lambda_set_static_rho (subst, static_rho);
    }
    else
      btor_delete_ptr_hash_table (static_rho);

    btor_insert_substitution (btor, lambda, subst, 0);
    btor_release_exp (btor, subst);
    while (!BTOR_EMPTY_STACK (params))
      btor_release_exp (btor, BTOR_POP_STACK (params));
  }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  btor->stats.lambdas_merged += num_merged_lambdas;

  btor_delete_int_hash_table (mark);
  btor_delete_int_hash_table (mark_lambda);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (params);
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "merged %d lambdas in %.2f seconds",
            num_merged_lambdas,
            delta);
  btor->time.merge += delta;
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btormerge.h"
#include "btorbeta.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
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
//  btor_iter_hashptr_init (&it, t0);
//  while (btor_iter_hashptr_has_next (&it))
//    {
//      value = it.bucket->data.as_ptr;
//      args = btor_iter_hashptr_next (&it);
//      assert (args->arity == 1);
//      b = btor_hashptr_table_get (t1, args);
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

  btor_iter_hashptr_init (&it, static_rho);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_node_release (btor, it.bucket->data.as_ptr);
    btor_node_release (btor, btor_iter_hashptr_next (&it));
  }
  btor_hashptr_table_delete (static_rho);
}

static void
add_to_static_rho (Btor *btor, BtorPtrHashTable *to, BtorPtrHashTable *from)
{
  BtorNode *data, *key;
  BtorPtrHashTableIterator it;

  if (!from) return;

  btor_iter_hashptr_init (&it, from);
  while (btor_iter_hashptr_has_next (&it))
  {
    data = it.bucket->data.as_ptr;
    key  = btor_iter_hashptr_next (&it);
    if (btor_hashptr_table_get (to, key)) continue;
    btor_hashptr_table_add (to, btor_node_copy (btor, key))->data.as_ptr =
        btor_node_copy (btor, data);
  }
}

void
btor_merge_lambdas (Btor *btor)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0);

  uint32_t i, num_merged_lambdas = 0;
  double start, delta;
  BtorNode *cur, *lambda, *subst, *parent, *param, *body;
  BtorMemMgr *mm;
  BtorPtrHashTableIterator it;
  BtorNodeIterator nit;
  BtorNodePtrStack stack, visit, params;
  BtorPtrHashTable *merge_lambdas, *static_rho;
  BtorIntHashTable *mark, *mark_lambda;

  if (btor->lambdas->count == 0) return;

  start = btor_util_time_stamp ();
  mm    = btor->mm;

  mark        = btor_hashint_table_new (mm);
  mark_lambda = btor_hashint_table_new (mm);
  btor_init_substitutions (btor);
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, params);

  /* collect candidates for merging */
  btor_iter_hashptr_init (&it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&it))
  {
    lambda = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (lambda));

    /* found top lambda */
    parent = btor_node_real_addr (lambda->first_parent);
    if (lambda->parents > 1
        || lambda->parents == 0
        /* case lambda->parents == 1 */
        || (!parent->parameterized
            && (btor_node_is_apply (parent) || btor_node_is_fun_eq (parent))))
    {
      BTOR_PUSH_STACK (stack, lambda);
      continue;
    }
  }

  while (!BTOR_EMPTY_STACK (stack))
  {
    lambda = BTOR_POP_STACK (stack);
    assert (btor_node_is_regular (lambda));

    if (btor_hashint_table_contains (mark_lambda, lambda->id)) continue;

    btor_hashint_table_add (mark_lambda, lambda->id);
    /* search downwards and look for lambdas that can be merged */
    BTOR_RESET_STACK (visit);
    BTOR_PUSH_STACK (visit, btor_node_binder_get_body (lambda));
    merge_lambdas =
        btor_hashptr_table_new (mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    btor_hashptr_table_add (merge_lambdas, lambda);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = btor_node_real_addr (BTOR_POP_STACK (visit));

      if (btor_hashint_table_contains (mark, cur->id)
          || (!btor_node_is_lambda (cur) && !cur->parameterized)
          || !cur->lambda_below)
        continue;

      if (btor_node_is_lambda (cur))
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
        if (!btor_node_lambda_get_static_rho (cur)
                != !btor_node_lambda_get_static_rho (lambda)
            /* we can only merge lambdas that either represent arrays
             * or not */
            || cur->is_array != lambda->is_array)
        {
          /* try to merge lambdas starting from 'cur' */
          BTOR_PUSH_STACK (stack, cur);
          continue;
        }

        if (!btor_hashptr_table_get (merge_lambdas, cur))
          btor_hashptr_table_add (merge_lambdas, cur);
        BTOR_PUSH_STACK (visit, btor_node_binder_get_body (cur));
      }
      else
      {
        for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
      }
      btor_hashint_table_add (mark, cur->id);
    }

    /* no lambdas to merge found */
    if (merge_lambdas->count <= 1)
    {
      btor_hashptr_table_delete (merge_lambdas);
      continue;
    }

    /* assign parameters of top-most lambda with fresh parameters */
    btor_iter_lambda_init (&nit, lambda);
    while (btor_iter_lambda_has_next (&nit))
    {
      cur   = btor_iter_lambda_next (&nit);
      param = btor_exp_param (btor, btor_node_get_sort_id (cur->e[0]), 0);
      BTOR_PUSH_STACK (params, param);
      btor_beta_assign_param (btor, cur, param);
    }
    /* merge lambdas that are in 'merge_lambdas' table */
    body = btor_beta_reduce_merge (
        btor, btor_node_binder_get_body (lambda), merge_lambdas);
    btor_beta_unassign_params (btor, lambda);
    subst = btor_exp_fun (btor, params.start, BTOR_COUNT_STACK (params), body);
    if (lambda->is_array) subst->is_array = 1;
    btor_node_release (btor, body);

    /* generate static_rho from merged lambdas' static_rhos */
    assert (merge_lambdas->count > 0);
    num_merged_lambdas += merge_lambdas->count;
    static_rho = btor_hashptr_table_new (mm,
                                         (BtorHashPtr) btor_node_hash_by_id,
                                         (BtorCmpPtr) btor_node_compare_by_id);
    if (btor_node_lambda_get_static_rho (lambda))
    {
      btor_iter_hashptr_init (&it, merge_lambdas);
      while (btor_iter_hashptr_has_next (&it))
      {
        cur = btor_iter_hashptr_next (&it);
        add_to_static_rho (
            btor, static_rho, btor_node_lambda_get_static_rho (cur));
        assert (!btor_node_lambda_get_static_rho (lambda)
                == !btor_node_lambda_get_static_rho (cur));
      }
    }
    BTORLOG (2,
             "merged %u lambdas (%u static_rho entries)",
             merge_lambdas->count,
             static_rho->count);
    btor_hashptr_table_delete (merge_lambdas);

    if (static_rho->count > 0)
    {
      /* 'subst' is already an existing lambda with a 'static_rho', if
       * this is the case we have to check that subst->static_rho constains
       * the same elements as static_rho */
      if (btor_node_lambda_get_static_rho (subst))
      {
        //	      assert (btor_check_static_rho_equal_dbg (
        //			   btor_node_lambda_get_static_rho (subst),
        // static_rho));
        /* 'static_rho' contains elements so we have to release them
         * properly */
        delete_static_rho (btor, static_rho);
      }
      else
        btor_node_lambda_set_static_rho (subst, static_rho);
    }
    else
      btor_hashptr_table_delete (static_rho);

    btor_insert_substitution (btor, lambda, subst, false);
    btor_node_release (btor, subst);
    while (!BTOR_EMPTY_STACK (params))
      btor_node_release (btor, BTOR_POP_STACK (params));
  }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  btor->stats.lambdas_merged += num_merged_lambdas;

  btor_hashint_table_delete (mark);
  btor_hashint_table_delete (mark_lambda);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (params);
  delta = btor_util_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "merged %d lambdas in %.2f seconds",
            num_merged_lambdas,
            delta);
  btor->time.merge += delta;
}

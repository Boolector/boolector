/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
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
#include "utils/btoriter.h"
#include "utils/btorutil.h"

#ifndef NDEBUG
static bool
check_static_rho_equal_dbg (BtorPtrHashTable *t0, BtorPtrHashTable *t1)
{
  assert (t0);
  assert (t1);
  assert (t0->count == t1->count);

  BtorNode *args0, *args1, *value0, *value1;
  BtorHashTableIterator it0, it1;

  btor_init_node_hash_table_iterator (&it0, t0);
  btor_init_node_hash_table_iterator (&it1, t1);
  while (btor_has_next_node_hash_table_iterator (&it0))
  {
    value0 = it0.bucket->data.asPtr;
    value1 = it1.bucket->data.asPtr;
    args0  = btor_next_node_hash_table_iterator (&it0);
    args1  = btor_next_node_hash_table_iterator (&it1);
    assert (args0->arity == 1);
    assert (args0->arity == args1->arity);
    assert ((BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (args0->e[0]))
             && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (args1->e[0])))
            || (args0 == args1 && value0 == value1));
  }
  return true;
}
#endif

static void
delete_static_rho (Btor *btor, BtorPtrHashTable *static_rho)
{
  BtorHashTableIterator it;

  btor_init_node_hash_table_iterator (&it, static_rho);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    btor_release_exp (btor, it.bucket->data.asPtr);
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
  }
  btor_delete_ptr_hash_table (static_rho);
}

static void
add_to_static_rho (Btor *btor, BtorPtrHashTable *to, BtorPtrHashTable *from)
{
  BtorNode *data, *key;
  BtorHashTableIterator it;

  if (!from) return;

  btor_init_node_hash_table_iterator (&it, from);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    data = it.bucket->data.asPtr;
    key  = btor_next_node_hash_table_iterator (&it);
    if (btor_find_in_ptr_hash_table (to, key)) continue;
    btor_insert_in_ptr_hash_table (to, btor_copy_exp (btor, key))->data.asPtr =
        btor_copy_exp (btor, data);
  }
}

void
btor_merge_lambdas (Btor *btor)
{
  assert (btor);
  assert (btor->options.rewrite_level.val > 0);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (check_id_table_aux_mark_unset_dbg (btor));

  unsigned num_merged_lambdas = 0;
  int i;
  double start, delta;
  BtorNode *cur, *lambda, *subst, *parent, *param, *body;
  BtorMemMgr *mm;
  BtorHashTableIterator it;
  BtorNodeIterator nit;
  BtorNodePtrStack stack, unmark, visit, params;
  BtorPtrHashTable *merge_lambdas, *static_rho;

  start = btor_time_stamp ();
  mm    = btor->mm;

  btor_init_substitutions (btor);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (params);

  /* collect candidates for merging */
  btor_init_node_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    lambda = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    /* found top lambda */
    parent = BTOR_REAL_ADDR_NODE (lambda->first_parent);
    if (lambda->parents > 1
        || lambda->parents == 0
        /* case lambda->parents == 1 */
        || (!parent->parameterized
            && (BTOR_IS_APPLY_NODE (parent) || BTOR_IS_FEQ_NODE (parent))))
    {
      BTOR_PUSH_STACK (mm, stack, lambda);
      continue;
    }
  }

  while (!BTOR_EMPTY_STACK (stack))
  {
    lambda = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    if (lambda->mark) continue;

    lambda->mark = 1;
    BTOR_PUSH_STACK (mm, unmark, lambda);

    /* search downwards and look for lambdas that can be merged */
    BTOR_RESET_STACK (visit);
    BTOR_PUSH_STACK (mm, visit, btor_lambda_get_body (lambda));
    merge_lambdas = btor_new_ptr_hash_table (mm, 0, 0);
    btor_insert_in_ptr_hash_table (merge_lambdas, lambda);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (cur->aux_mark || (!BTOR_IS_LAMBDA_NODE (cur) && !cur->parameterized)
          || !cur->lambda_below)
        continue;

      if (BTOR_IS_LAMBDA_NODE (cur))
      {
        /* lambdas with more than one parents cannot be merged */
        if (cur->parents > 1)
        {
          /* try to merge lambdas starting from 'cur' */
          BTOR_PUSH_STACK (mm, stack, cur);
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
          BTOR_PUSH_STACK (mm, stack, cur);
          continue;
        }

        if (!btor_find_in_ptr_hash_table (merge_lambdas, cur))
          btor_insert_in_ptr_hash_table (merge_lambdas, cur);
        BTOR_PUSH_STACK (mm, visit, btor_lambda_get_body (cur));
      }
      else
      {
        for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
      }

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (mm, unmark, cur);
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
      param = btor_param_exp (btor, btor_get_exp_width (btor, cur->e[0]), 0);
      BTOR_PUSH_STACK (mm, params, param);
      btor_assign_param (btor, cur, param);
    }
    /* merge lambdas that are in 'merge_lambdas' table */
    body = btor_beta_reduce_merge (
        btor, btor_lambda_get_body (lambda), merge_lambdas);
    btor_unassign_params (btor, lambda);
    subst = btor_fun_exp (btor, BTOR_COUNT_STACK (params), params.start, body);
    if (lambda->is_array) subst->is_array = 1;
    btor_release_exp (btor, body);

    /* generate static_rho from merged lambdas' static_rhos */
    assert (merge_lambdas->count > 0);
    num_merged_lambdas += merge_lambdas->count;
    static_rho = btor_new_ptr_hash_table (mm, 0, 0);
    if (btor_lambda_get_static_rho (lambda))
    {
      btor_init_node_hash_table_iterator (&it, merge_lambdas);
      while (btor_has_next_node_hash_table_iterator (&it))
      {
        cur = btor_next_node_hash_table_iterator (&it);
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
        assert (check_static_rho_equal_dbg (btor_lambda_get_static_rho (subst),
                                            static_rho));
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

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark))
  {
    cur           = BTOR_POP_STACK (unmark);
    cur->mark     = 0;
    cur->aux_mark = 0;
  }

  btor_substitute_and_rebuild (btor, btor->substitutions, 0);
  btor_delete_substitutions (btor);
  btor->stats.lambdas_merged += num_merged_lambdas;

  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, unmark);
  BTOR_RELEASE_STACK (mm, params);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "merged %d lambdas in %.2f seconds",
            num_merged_lambdas,
            delta);
}

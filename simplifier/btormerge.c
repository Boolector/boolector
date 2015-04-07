/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormerge.h"
#include "btorbeta.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btoriter.h"
#include "btorutil.h"

void
btor_merge_lambdas (Btor *btor)
{
  assert (btor);
  assert (btor->options.rewrite_level.val > 0);
  assert (check_id_table_mark_unset_dbg (btor));
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (check_unique_table_merge_unset_dbg (btor));

  int i, delta_lambdas;
  double start, delta;
  BtorNode *cur, *lambda, *subst, *parent, *merge;
  BtorMemMgr *mm;
  BtorHashTableIterator it;
  BtorNodeIterator nit;
  BtorNodePtrStack stack, unmark, visit;

  start         = btor_time_stamp ();
  mm            = btor->mm;
  delta_lambdas = btor->lambdas->count;

  btor_init_substitutions (btor);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark);
  BTOR_INIT_STACK (visit);

  /* collect candidates for merging */
  init_node_hash_table_iterator (&it, btor->lambdas);
  while (has_next_node_hash_table_iterator (&it))
  {
    lambda = next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    if (lambda->parents != 1) continue;

    parent = BTOR_REAL_ADDR_NODE (lambda->first_parent);
    assert (parent);
    /* stop at non-parameterized applies */
    if (!parent->parameterized && BTOR_IS_APPLY_NODE (parent)) continue;

    lambda->merge = 1;
    BTOR_PUSH_STACK (mm, stack, lambda);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    lambda = BTOR_PEEK_STACK (stack, i);
    assert (BTOR_IS_REGULAR_NODE (lambda));
    assert (lambda->parents == 1);

    if (lambda->mark) continue;

    lambda->mark = 1;
    BTOR_PUSH_STACK (mm, unmark, lambda);

    /* skip curried lambdas */
    if (BTOR_IS_LAMBDA_NODE (lambda->first_parent)) continue;

    /* search upwards for top-most lambda */
    merge = 0;
    BTOR_RESET_STACK (visit);
    BTOR_PUSH_STACK (mm, visit, lambda);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (mm, unmark, cur);

      /* we can only merge non-paremeterized lambdas */
      // TODO: remove parameterized if we handle btorparamcache differently
      if (BTOR_IS_LAMBDA_NODE (cur) && !cur->merge && !cur->parameterized)
      {
        merge = cur;
        break;
      }

      init_full_parent_iterator (&nit, cur);
      while (has_next_parent_full_parent_iterator (&nit))
        BTOR_PUSH_STACK (mm, visit, next_parent_full_parent_iterator (&nit));
    }

    /* no lambda to merge found */
    if (!merge) continue;

    assert (!merge->parameterized);

    /* already processed */
    if (merge->mark) continue;

    merge->mark = 1;
    BTOR_PUSH_STACK (mm, unmark, merge);

    init_lambda_iterator (&nit, merge);
    while (has_next_lambda_iterator (&nit))
    {
      cur = next_lambda_iterator (&nit);
      btor_assign_param (btor, cur, cur->e[0]);
    }
    /* merge lambdas that are marked with 'merge' flag */
    subst = btor_beta_reduce_merge (btor, BTOR_LAMBDA_GET_BODY (merge));
    subst = BTOR_COND_INVERT_NODE (BTOR_LAMBDA_GET_BODY (merge), subst);
    btor_unassign_params (btor, merge);
    btor_insert_substitution (btor, BTOR_LAMBDA_GET_BODY (merge), subst, 0);
    btor_release_exp (btor, subst);
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark))
  {
    cur           = BTOR_POP_STACK (unmark);
    cur->mark     = 0;
    cur->aux_mark = 0;
    cur->merge    = 0;
  }

  btor_substitute_and_rebuild (btor, btor->substitutions, 0);
  btor_delete_substitutions (btor);
  delta_lambdas -= btor->lambdas->count;
  btor->stats.lambdas_merged += delta_lambdas;

  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, unmark);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (check_unique_table_merge_unset_dbg (btor));
  delta = btor_time_stamp () - start;
  BTOR_MSG (
      btor->msg, 1, "merged %d lambdas in %.2f seconds", delta_lambdas, delta);
}

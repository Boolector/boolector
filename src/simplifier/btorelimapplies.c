/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorelimapplies.h"
#include "btorbeta.h"
#include "btorcore.h"
#include "btordbg.h"
#include "utils/btorexpiter.h"
#include "utils/btorutil.h"

static void
eliminate_update_nodes (Btor *btor)
{
  uint32_t i;
  BtorNode *cur, *p, *cond, *eq, *app, *lambda;

  btor_init_substitutions (btor);

  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (!cur || !btor_is_update_node (cur)) continue;
    p      = btor_param_exp (btor, btor_exp_get_sort_id (cur->e[1]->e[0]), 0);
    app    = btor_apply_exps (btor, &p, 1, cur->e[0]);
    eq     = btor_eq_exp (btor, p, cur->e[1]->e[0]);
    cond   = btor_cond_exp (btor, eq, cur->e[2], app);
    lambda = btor_lambda_exp (btor, p, cond);

    btor_insert_substitution (btor, cur, lambda, 0);
    btor_release_exp (btor, p);
    btor_release_exp (btor, app);
    btor_release_exp (btor, eq);
    btor_release_exp (btor, cond);
    btor_release_exp (btor, lambda);
  }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
}

void
btor_eliminate_applies (Btor *btor)
{
  assert (btor);

  int num_applies, num_applies_total = 0, round;
  double start, delta;
  BtorNode *app, *fun, *subst;
  BtorNodeIterator it;
  BtorPtrHashTableIterator h_it;
  BtorPtrHashTable *cache;

  eliminate_update_nodes (btor);

  if (btor->lambdas->count == 0) return;

  start = btor_time_stamp ();
  round = 1;
  cache = btor_new_ptr_hash_table (btor->mm,
                                   (BtorHashPtr) btor_hash_exp_pair,
                                   (BtorCmpPtr) btor_compare_exp_pair);

  /* NOTE: in some cases substitute_and_rebuild creates applies that can be
   * beta-reduced. this can happen when parameterized applies become not
   * parameterized. hence, we beta-reduce applies until fix point.
   */
  do
  {
    num_applies = 0;
    btor_init_substitutions (btor);

    /* collect function applications */
    btor_init_ptr_hash_table_iterator (&h_it, btor->lambdas);
    while (btor_has_next_ptr_hash_table_iterator (&h_it))
    {
      fun = btor_next_ptr_hash_table_iterator (&h_it);

      btor_init_apply_parent_iterator (&it, fun);
      while (btor_has_next_apply_parent_iterator (&it))
      {
        app = btor_next_apply_parent_iterator (&it);

        if (app->parameterized) continue;

        num_applies++;
        subst = btor_beta_reduce_full (btor, app, cache);
        assert (!btor_get_ptr_hash_table (btor->substitutions, app));
        btor_insert_substitution (btor, app, subst, 0);
        btor_release_exp (btor, subst);
      }
    }

    num_applies_total += num_applies;
    BTOR_MSG (btor->msg,
              1,
              "eliminate %d applications in round %d",
              num_applies,
              round);

    btor_substitute_and_rebuild (btor, btor->substitutions);
    btor_delete_substitutions (btor);
    round++;
  } while (num_applies > 0);

#ifndef NDEBUG
  btor_init_ptr_hash_table_iterator (&h_it, btor->lambdas);
  while (btor_has_next_ptr_hash_table_iterator (&h_it))
  {
    fun = btor_next_ptr_hash_table_iterator (&h_it);

    btor_init_apply_parent_iterator (&it, fun);
    while (btor_has_next_apply_parent_iterator (&it))
    {
      app = btor_next_apply_parent_iterator (&it);
      assert (app->parameterized);
    }
  }
#endif

  btor_init_ptr_hash_table_iterator (&h_it, cache);
  while (btor_has_next_ptr_hash_table_iterator (&h_it))
  {
    btor_release_exp (btor, h_it.bucket->data.as_ptr);
    btor_delete_exp_pair (btor, btor_next_ptr_hash_table_iterator (&h_it));
  }
  btor_delete_ptr_hash_table (cache);

  delta = btor_time_stamp () - start;
  btor->time.elimapplies += delta;
  BTOR_MSG (btor->msg,
            1,
            "eliminated %d function applications in %.1f seconds",
            num_applies_total,
            delta);
  assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
  assert (btor_check_all_hash_tables_simp_free_dbg (btor));
  assert (btor_check_unique_table_children_proxy_free_dbg (btor));
}

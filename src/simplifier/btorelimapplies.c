/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorelimapplies.h"
#include "btorbeta.h"
#include "btorcore.h"
#include "btordbg.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static void
eliminate_update_nodes (Btor *btor)
{
  uint32_t i;
  BtorNode *cur, *subst;

  btor_init_substitutions (btor);
  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (!cur || !btor_node_is_update (cur)) continue;
    subst = btor_exp_lambda_write (btor, cur->e[0], cur->e[1]->e[0], cur->e[2]);
    btor_insert_substitution (btor, cur, subst, 0);
    btor_node_release (btor, subst);
  }
  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
}

void
btor_eliminate_applies (Btor *btor)
{
  assert (btor);

  uint32_t num_applies, num_applies_total = 0, round;
  double start, delta;
  BtorNode *app, *fun, *subst;
  BtorNodeIterator it;
  BtorPtrHashTableIterator h_it;
  BtorPtrHashTable *cache;

  eliminate_update_nodes (btor);

  if (btor->lambdas->count == 0) return;

  start = btor_util_time_stamp ();
  round = 1;
  cache = btor_hashptr_table_new (btor->mm,
                                  (BtorHashPtr) btor_node_pair_hash,
                                  (BtorCmpPtr) btor_node_pair_compare);

  /* NOTE: in some cases substitute_and_rebuild creates applies that can be
   * beta-reduced. this can happen when parameterized applies become not
   * parameterized. hence, we beta-reduce applies until fix point.
   */
  do
  {
    num_applies = 0;
    btor_init_substitutions (btor);

    /* collect function applications */
    btor_iter_hashptr_init (&h_it, btor->lambdas);
    while (btor_iter_hashptr_has_next (&h_it))
    {
      fun = btor_iter_hashptr_next (&h_it);

      btor_iter_apply_parent_init (&it, fun);
      while (btor_iter_apply_parent_has_next (&it))
      {
        app = btor_iter_apply_parent_next (&it);

        /* If we have quantifiers, we always want to eliminate lambdas. */
        if (btor->quantifiers->count == 0 && app->parameterized) continue;

        num_applies++;
        subst = btor_beta_reduce_full (btor, app, cache);
        assert (!btor_hashptr_table_get (btor->substitutions, app));
        btor_insert_substitution (btor, app, subst, false);
        btor_node_release (btor, subst);
      }
    }

    num_applies_total += num_applies;
    BTOR_MSG (btor->msg,
              1,
              "eliminate %u applications in round %u",
              num_applies,
              round);

    btor_substitute_and_rebuild (btor, btor->substitutions);
    btor_delete_substitutions (btor);
    round++;
  } while (num_applies > 0);

#ifndef NDEBUG
  btor_iter_hashptr_init (&h_it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&h_it))
  {
    fun = btor_iter_hashptr_next (&h_it);

    btor_iter_apply_parent_init (&it, fun);
    while (btor_iter_apply_parent_has_next (&it))
    {
      app = btor_iter_apply_parent_next (&it);
      assert (app->parameterized);
    }
  }
#endif

  btor_iter_hashptr_init (&h_it, cache);
  while (btor_iter_hashptr_has_next (&h_it))
  {
    btor_node_release (btor, h_it.bucket->data.as_ptr);
    btor_node_pair_delete (btor, btor_iter_hashptr_next (&h_it));
  }
  btor_hashptr_table_delete (cache);

  delta = btor_util_time_stamp () - start;
  btor->time.elimapplies += delta;
  BTOR_MSG (btor->msg,
            1,
            "eliminated %d function applications in %.1f seconds",
            num_applies_total,
            delta);
  assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
  assert (btor_dbg_check_all_hash_tables_simp_free (btor));
  assert (btor_dbg_check_unique_table_children_proxy_free (btor));
}

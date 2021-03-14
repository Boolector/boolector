/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "preprocess/btorelimapplies.h"

#include "btorbeta.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorlog.h"
#include "btorsubst.h"
#include "preprocess/btorpputils.h"
#include "preprocess/btorpreprocess.h"
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
    if (!cur || !btor_node_is_update (cur) || btor_node_is_simplified (cur))
      continue;
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

  size_t i;
  uint32_t num_applies, num_applies_total = 0, round;
  double start, delta;
  BtorNode *app, *fun, *subst;
  BtorNodeIterator it;
  BtorNodePtrStack lambdas;
  BtorPtrHashTableIterator h_it;
  BtorPtrHashTable *cache;
  BtorPtrHashTable *substs;
  BtorIntHashTable *app_cache;

  if (btor_opt_get (btor, BTOR_OPT_BETA_REDUCE) == BTOR_BETA_REDUCE_ALL)
  {
    eliminate_update_nodes (btor);
  }

  if (btor->lambdas->count == 0) return;

  start     = btor_util_time_stamp ();
  round     = 1;
  cache     = btor_hashptr_table_new (btor->mm,
                                  (BtorHashPtr) btor_node_pair_hash,
                                  (BtorCmpPtr) btor_node_pair_compare);
  app_cache = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, lambdas);

  /* NOTE: in some cases substitute_and_rebuild creates applies that can be
   * beta-reduced. this can happen when parameterized applies become not
   * parameterized. hence, we beta-reduce applies until fix point.
   */
  do
  {
    BTORLOG (1, "start apply elimination (round %u)", round);

    num_applies = 0;

    substs = btor_hashptr_table_new (btor->mm,
                                     (BtorHashPtr) btor_node_hash_by_id,
                                     (BtorCmpPtr) btor_node_compare_by_id);

    btor_pputils_collect_lambdas (btor, &lambdas);

    /* collect function applications */
    for (i = 0; i < BTOR_COUNT_STACK (lambdas); i++)
    {
      fun = BTOR_PEEK_STACK (lambdas, i);

      btor_iter_apply_parent_init (&it, fun);
      while (btor_iter_apply_parent_has_next (&it))
      {
        app = btor_iter_apply_parent_next (&it);

        if (btor_node_is_simplified (app)) continue;

        if (btor_hashint_table_contains (app_cache, btor_node_get_id (app)))
          continue;

        /* If we have quantifiers, we always want to eliminate lambdas. */
        if (btor->quantifiers->count == 0 && app->parameterized) continue;

        num_applies++;
        subst = btor_beta_reduce_full (btor, app, cache);
        assert (!btor_hashptr_table_get (substs, app));
        btor_hashptr_table_add (substs, app)->data.as_ptr = subst;
        btor_hashint_table_add (app_cache, btor_node_get_id (app));
      }
    }
    BTOR_RESET_STACK (lambdas);

    num_applies_total += num_applies;
    BTOR_MSG (btor->msg,
              1,
              "eliminate %u applications in round %u",
              num_applies,
              round);

    btor_substitute_and_rebuild (btor, substs);

    btor_iter_hashptr_init (&h_it, substs);
    while (btor_iter_hashptr_has_next (&h_it))
    {
      btor_node_release (btor, btor_iter_hashptr_next_data (&h_it)->as_ptr);
    }
    btor_hashptr_table_delete (substs);

    BTORLOG (1, "end apply elimination (round %u)", round);
    round++;
  } while (num_applies > 0);

  btor_hashint_table_delete (app_cache);

  btor_iter_hashptr_init (&h_it, cache);
  while (btor_iter_hashptr_has_next (&h_it))
  {
    btor_node_release (btor, h_it.bucket->data.as_ptr);
    btor_node_pair_delete (btor, btor_iter_hashptr_next (&h_it));
  }
  btor_hashptr_table_delete (cache);

#ifndef NDEBUG
  BTOR_RESET_STACK (lambdas);
  btor_pputils_collect_lambdas (btor, &lambdas);
  for (i = 0; i < BTOR_COUNT_STACK (lambdas); i++)
  {
    fun = BTOR_PEEK_STACK (lambdas, i);

    btor_iter_apply_parent_init (&it, fun);
    while (btor_iter_apply_parent_has_next (&it))
    {
      app = btor_iter_apply_parent_next (&it);
      assert (app->parameterized
              || btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST));
    }
  }
#endif
  BTOR_RELEASE_STACK (lambdas);

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

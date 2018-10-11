/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorack.h"
#include "btorcore.h"
#include "btorexp.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

void
btor_add_ackermann_constraints (Btor *btor)
{
  assert (btor);

  uint32_t i, j, num_constraints = 0;
  double start, delta;
  BtorNode *uf, *app_i, *app_j, *p, *c, *imp, *a_i, *a_j, *eq, *tmp;
  BtorNode *cur;
  BtorArgsIterator ait_i, ait_j;
  BtorNodeIterator nit;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack applies, visit;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  start = btor_util_time_stamp ();
  mm    = btor->mm;
  cache = btor_hashint_table_new (mm);
  BTOR_INIT_STACK (mm, visit);

  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    BTOR_PUSH_STACK (visit, btor_iter_hashptr_next (&it));

  /* mark reachable nodes */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)) continue;
    btor_hashint_table_add (cache, cur->id);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);

  btor_iter_hashptr_init (&it, btor->ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    uf = btor_iter_hashptr_next (&it);
    BTOR_INIT_STACK (btor->mm, applies);
    btor_iter_apply_parent_init (&nit, uf);
    while (btor_iter_apply_parent_has_next (&nit))
    {
      app_i = btor_iter_apply_parent_next (&nit);
      if (app_i->parameterized) continue;
      if (!btor_hashint_table_contains (cache, app_i->id)) continue;
      BTOR_PUSH_STACK (applies, app_i);
    }

    for (i = 0; i < BTOR_COUNT_STACK (applies); i++)
    {
      app_i = BTOR_PEEK_STACK (applies, i);
      for (j = i + 1; j < BTOR_COUNT_STACK (applies); j++)
      {
        app_j = BTOR_PEEK_STACK (applies, j);
        p     = 0;
        assert (btor_node_get_sort_id (app_i->e[1])
                == btor_node_get_sort_id (app_j->e[1]));
        btor_iter_args_init (&ait_i, app_i->e[1]);
        btor_iter_args_init (&ait_j, app_j->e[1]);
        while (btor_iter_args_has_next (&ait_i))
        {
          a_i = btor_iter_args_next (&ait_i);
          a_j = btor_iter_args_next (&ait_j);
          eq  = btor_exp_eq (btor, a_i, a_j);

          if (!p)
            p = eq;
          else
          {
            tmp = p;
            p   = btor_exp_bv_and (btor, tmp, eq);
            btor_node_release (btor, tmp);
            btor_node_release (btor, eq);
          }
        }
        c   = btor_exp_eq (btor, app_i, app_j);
        imp = btor_exp_implies (btor, p, c);
        btor->stats.ackermann_constraints++;
        num_constraints++;
        btor_assert_exp (btor, imp);
        btor_node_release (btor, p);
        btor_node_release (btor, c);
        btor_node_release (btor, imp);
      }
    }
    BTOR_RELEASE_STACK (applies);
  }
  btor_hashint_table_delete (cache);
  delta = btor_util_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "added %d ackermann constraints in %.3f seconds",
            num_constraints,
            delta);
  btor->time.ack += delta;
}

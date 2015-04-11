/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorack.h"
#include "btorcore.h"
#include "utils/btoriter.h"
#include "utils/btorutil.h"

void
btor_add_ackermann_constraints (Btor *btor)
{
  assert (btor);

  int i, j, num_constraints = 0;
  double start;
  BtorNode *uf, *app_i, *app_j, *p, *c, *imp, *a_i, *a_j, *eq, *tmp;
  BtorArgsIterator ait_i, ait_j;
  BtorNodeIterator nit;
  BtorHashTableIterator it;
  BtorNodePtrStack applies;

  start = btor_time_stamp ();
  init_node_hash_table_iterator (&it, btor->ufs);
  while (has_next_node_hash_table_iterator (&it))
  {
    uf = next_node_hash_table_iterator (&it);
    BTOR_INIT_STACK (applies);
    init_apply_parent_iterator (&nit, uf);
    while (has_next_parent_apply_parent_iterator (&nit))
    {
      app_i = next_parent_apply_parent_iterator (&nit);
      if (app_i->parameterized) continue;
      BTOR_PUSH_STACK (btor->mm, applies, app_i);
    }

    for (i = 0; i < BTOR_COUNT_STACK (applies); i++)
    {
      app_i = BTOR_PEEK_STACK (applies, i);
      for (j = i + 1; j < BTOR_COUNT_STACK (applies); j++)
      {
        app_j = BTOR_PEEK_STACK (applies, j);
        p     = 0;
        assert (app_i->e[1]->sort_id == app_j->e[1]->sort_id);
        init_args_iterator (&ait_i, app_i->e[1]);
        init_args_iterator (&ait_j, app_j->e[1]);
        while (has_next_args_iterator (&ait_i))
        {
          a_i = next_args_iterator (&ait_i);
          a_j = next_args_iterator (&ait_j);
          eq  = btor_eq_exp (btor, a_i, a_j);

          if (!p)
            p = eq;
          else
          {
            tmp = p;
            p   = btor_and_exp (btor, tmp, eq);
            btor_release_exp (btor, tmp);
            btor_release_exp (btor, eq);
          }
        }
        c   = btor_eq_exp (btor, app_i, app_j);
        imp = btor_implies_exp (btor, p, c);
        btor->stats.ackermann_constraints++;
        num_constraints++;
        btor_assert_exp (btor, imp);
        btor_release_exp (btor, p);
        btor_release_exp (btor, c);
        btor_release_exp (btor, imp);
      }
    }
    BTOR_RELEASE_STACK (btor->mm, applies);
  }
  BTOR_MSG (btor->msg,
            1,
            "added %d ackermann constraints in %.3f seconds",
            num_constraints,
            btor_time_stamp () - start);
}

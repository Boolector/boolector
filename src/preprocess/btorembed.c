/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2019 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "preprocess/btorembed.h"

#include "btorcore.h"
#include "btordbg.h"
#include "btorlog.h"
#include "btorsubst.h"
#include "utils/btorutil.h"

void
btor_process_embedded_constraints (Btor *btor)
{
  assert (btor);

  BtorPtrHashTableIterator it;
  BtorNodePtrStack ec;
  double start, delta;
  BtorNode *cur;
  uint32_t count;

  if (btor->embedded_constraints->count == 0u)
  {
    return;
  }

  BTORLOG (1, "start embedded constraint processing");

  start = btor_util_time_stamp ();
  count = 0;
  BTOR_INIT_STACK (btor->mm, ec);
  btor_iter_hashptr_init (&it, btor->embedded_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_node_copy (btor, btor_iter_hashptr_next (&it));
    assert (btor_node_real_addr (cur)->constraint);
    BTOR_PUSH_STACK (ec, cur);
    if (btor_node_real_addr (cur)->parents > 0)
    {
      btor->stats.ec_substitutions++;
    }
  }

  btor_substitute_and_rebuild (btor, btor->embedded_constraints);

  while (!BTOR_EMPTY_STACK (ec))
  {
    cur = BTOR_POP_STACK (ec);

    if (btor_hashptr_table_get (btor->embedded_constraints, cur))
    {
      count++;
      btor_hashptr_table_remove (btor->embedded_constraints, cur, 0, 0);
      btor_node_release (btor, cur);
    }
    btor_node_release (btor, cur);
  }
  BTOR_RELEASE_STACK (ec);

  delta = btor_util_time_stamp () - start;
  btor->time.embedded += delta;
  BTOR_MSG (btor->msg,
            1,
            "replaced %u embedded constraints in %1.f seconds",
            count,
            delta);
  assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
  assert (btor_dbg_check_all_hash_tables_simp_free (btor));
  assert (btor_dbg_check_unique_table_children_proxy_free (btor));
  BTORLOG (1, "end embedded constraint processing");
}

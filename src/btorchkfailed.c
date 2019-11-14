/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2019 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorchkfailed.h"

#include "btorclone.h"
#include "btorcore.h"
#include "btorlog.h"
#include "btorsubst.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

void
btor_check_failed_assumptions (Btor *btor)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_RESULT_UNSAT);

  Btor *clone;
  BtorNode *ass, *cass;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack stack;

  clone = btor_clone_exp_layer (btor, 0, true);
  btor_opt_set (clone, BTOR_OPT_LOGLEVEL, 0);
  btor_opt_set (clone, BTOR_OPT_VERBOSITY, 0);
  btor_opt_set (clone, BTOR_OPT_FUN_DUAL_PROP, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_UNCONSTRAINED, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_MODEL, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
  btor_set_term (clone, 0, 0);

  btor_opt_set (clone, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
  assert (clone->slv);
  clone->slv->api.delet (clone->slv);
  clone->slv = 0;

  /* clone->assertions have been already added at this point. */
  while (!BTOR_EMPTY_STACK (clone->assertions))
  {
    ass = BTOR_POP_STACK (clone->assertions);
    btor_node_release (clone, ass);
  }

  /* assert failed assumptions */
  BTOR_INIT_STACK (btor->mm, stack);
  btor_iter_hashptr_init (&it, btor->orig_assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    ass = btor_iter_hashptr_next (&it);
    if (btor_failed_exp (btor, ass))
    {
      BTORLOG (2, "failed assumption: %s", btor_util_node2string (ass));
      cass = btor_node_match (clone, ass);
      assert (cass);
      BTOR_PUSH_STACK (stack, cass);
    }
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cass = BTOR_POP_STACK (stack);
    btor_assert_exp (clone, cass);
    btor_node_release (clone, cass);
  }
  BTOR_RELEASE_STACK (stack);

  /* cleanup assumptions */
  btor_iter_hashptr_init (&it, clone->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (clone, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (clone->assumptions);
  clone->assumptions =
      btor_hashptr_table_new (clone->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  assert (btor_check_sat (clone, -1, -1) == BTOR_RESULT_UNSAT);
  btor_delete (clone);
}

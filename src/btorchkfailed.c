/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2020 Mathias Preiner.
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

static void
rebuild_formula (Btor *btor, uint32_t rewrite_level)
{
  assert (btor);

  uint32_t i, cnt;
  BtorNode *cur;
  BtorPtrHashTable *t;

  BTORLOG (1, "rebuild formula with rewrite level %u", rewrite_level);

  /* set new rewrite level */
  btor_opt_set (btor, BTOR_OPT_REWRITE_LEVEL, rewrite_level);

  t = btor_hashptr_table_new (btor->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = 1, cnt = BTOR_COUNT_STACK (btor->nodes_id_table); i <= cnt; i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i))) continue;

    if (btor_node_is_simplified (cur)) continue;

    if (cur->arity == 0)
    {
      assert (btor_node_is_bv_var (cur) || btor_node_is_bv_const (cur)
              || btor_node_is_param (cur) || btor_node_is_uf (cur));
      btor_hashptr_table_add (t, cur);
    }
  }

  btor_substitute_and_rebuild (btor, t);
  btor_hashptr_table_delete (t);

  BTORLOG (1, "rebuild formula done");
}

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
  btor_set_msg_prefix (clone, "chkf");
  btor_opt_set (clone, BTOR_OPT_FUN_DUAL_PROP, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_UNCONSTRAINED, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_MODEL, 0);
  btor_opt_set (clone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
  btor_opt_set (clone, BTOR_OPT_PRINT_DIMACS, 0);
  btor_opt_set (clone, BTOR_OPT_AUTO_CLEANUP, 1);
  btor_set_term (clone, 0, 0);

  btor_opt_set (clone, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
  assert (clone->slv);
  clone->slv->api.delet (clone->slv);
  clone->slv = 0;

  /* clone->assertions have already been added at this point. */
  while (!BTOR_EMPTY_STACK (clone->assertions))
  {
    ass = BTOR_POP_STACK (clone->assertions);
    btor_node_release (clone, ass);
  }

  /* Set to false in order to not trigger a reset of the assumptions when a
   * constraint is replaced (and thus a 'new' one added) when simplifying
   * expressions in btor_substitute_and_rebuild. */
  clone->valid_assignments = 0;

  /* rebuild formula to eliminate all simplified nodes. */
  rebuild_formula (clone, 3);

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

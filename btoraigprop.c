/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraigprop.h"
#include "aigprop.h"
#include "btorabort.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btormodel.h"
#include "btorprop.h"
#include "btorsls.h"  // for score computation
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"

#define BTOR_AIGPROP_MAXSTEPS_CFACT 100
#define BTOR_AIGPROP_MAXSTEPS(i) \
  (BTOR_AIGPROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

/*------------------------------------------------------------------------*/

static void *
clone_aigprop_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (btor);
  assert (exp_map);

  BtorAIGPropSolver *slv, *res;

  if (!(slv = BTOR_AIGPROP_SOLVER (btor))) return 0;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorAIGPropSolver));

  return res;
}

static void
delete_aigprop_solver (Btor *btor)
{
  assert (btor);

  BtorAIGPropSolver *slv;

  if (!(slv = BTOR_AIGPROP_SOLVER (btor))) return;
  if (slv->aprop) aigprop_delete_aigprop (slv->aprop);
  BTOR_DELETE (btor->mm, slv);
}

static int
get_assignment_aig (BtorPtrHashTable *model, BtorAIG *aig)
{
  assert (model);

  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;
  /* initialize don't care bits with false */
  if (!btor_get_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig)))
    return BTOR_IS_INVERTED_AIG (aig) ? 1 : -1;
  return aigprop_get_assignment_aig (model, aig);
}

BtorBitVector *
get_assignment_bv (BtorMemMgr *mm, BtorNode *exp, BtorPtrHashTable *model)
{
  assert (mm);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (model);

  int i, j, len, bit;
  BtorBitVector *res;
  BtorAIGVec *av;

  if (!exp->av) return btor_new_bv (mm, btor_get_exp_width (exp->btor, exp));

  av  = exp->av;
  len = av->len;
  res = btor_new_bv (mm, len);

  for (i = 0, j = len - 1; i < len; i++, j--)
  {
    bit = get_assignment_aig (model, av->aigs[j]);
    assert (bit == -1 || bit == 1);
    btor_set_bit_bv (res, i, bit == 1 ? 1 : 0);
  }
  return res;
}

static void
generate_model_aigprop_solver (Btor *btor, int model_for_all_nodes, int reset)
{
  assert (btor);

  int i;
  BtorNode *cur, *real_cur;
  BtorBitVector *bv;
  BtorAIGPropSolver *slv;
  BtorHashTableIterator it;
  BtorNodePtrStack stack;
  BtorIntHashTable *cache;
  AIGProp *aprop;

  if (!(slv = BTOR_AIGPROP_SOLVER (btor))) return;

  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);

  aprop = BTOR_AIGPROP_SOLVER (btor)->aprop;
  /* generate AIG model */
  aigprop_generate_model (aprop, reset);
  /* map back to expression layer */
  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (btor->mm);
  assert (btor->unsynthesized_constraints->count == 0);
  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, btor_next_node_hash_table_iterator (&it));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    if (btor_contains_int_hash_table (cache, real_cur->id)) continue;
    btor_add_int_hash_table (cache, real_cur->id);
    bv = get_assignment_bv (btor->mm, real_cur, aprop->model);
    btor_add_to_bv_model (btor, btor->bv_model, real_cur, bv);
    btor_free_bv (btor->mm, bv);
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (btor->mm, stack);
  btor_delete_int_hash_table (cache);
  /* generate model for unreachable nodes */
  if (model_for_all_nodes)
    btor_generate_model (
        btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

/* Note: limits are currently unused */
static int
sat_aigprop_solver (Btor *btor, int limit0, int limit1)
{
  assert (btor);

  int sat_result;
  BtorAIGPropSolver *slv;
  BtorHashTableIterator it;
  BtorNode *root;
  BtorAIG *aig;

  (void) limit0;
  (void) limit1;

  slv = BTOR_AIGPROP_SOLVER (btor);
  assert (slv);

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  sat_result = btor_simplify (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->ufs->count != 0
          || (!btor->options.beta_reduce_all.val && btor->lambdas->count != 0),
      "aigprop engine supports QF_BV only");
  btor_update_assumptions (btor);

  if (btor->inconsistent) goto UNSAT;

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_UNKNOWN;
    goto DONE;
  }

  btor_process_unsynthesized_constraints (btor);

  if (btor->found_constraint_false)
  {
  UNSAT:
    sat_result = BTOR_UNSAT;
    goto DONE;
  }
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
  assert (btor_check_all_hash_tables_simp_free_dbg (btor));

#ifndef NDEBUG
  btor_init_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    assert (!BTOR_REAL_ADDR_NODE (btor_next_node_hash_table_iterator (&it))
                 ->simplified);
#endif

  slv->aprop = aigprop_new_aigprop (btor_get_aig_mgr_btor (btor),
                                    btor->options.seed.val);
#ifndef NBTORLOG
  slv->aprop->loglevel = btor->options.loglevel.val;
#endif

  /* collect roots AIGs */
  slv->aprop->roots =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_aig_by_id,
                               (BtorCmpPtr) btor_compare_aig_by_id);
  assert (btor->unsynthesized_constraints->count == 0);
  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_REAL_ADDR_NODE (root)->av->len == 1);
    if (!btor_get_ptr_hash_table (slv->aprop->roots, root))
    {
      aig = BTOR_REAL_ADDR_NODE (root)->av->aigs[0];
      if (BTOR_IS_INVERTED_NODE (root)) aig = BTOR_INVERT_AIG (aig);
      if (aig == BTOR_AIG_FALSE) goto UNSAT;
      if (aig == BTOR_AIG_TRUE) continue;
      (void) btor_add_ptr_hash_table (slv->aprop->roots, aig);
    }
  }

  if ((sat_result = aigprop_sat (slv->aprop)) == BTOR_UNSAT) goto UNSAT;
  generate_model_aigprop_solver (btor, 0, 0);
  assert (sat_result == BTOR_SAT);
DONE:
  btor->valid_assignments = 1;
  slv->stats.moves        = slv->aprop->stats.moves;
  slv->stats.restarts     = slv->aprop->stats.restarts;
  slv->time.aprop_sat     = slv->aprop->time.sat;
  btor->last_sat_result   = sat_result;
  return sat_result;
}

static void
print_stats_aigprop_solver (Btor *btor)
{
  assert (btor);
  BtorAIGPropSolver *slv;

  if (!(slv = BTOR_AIGPROP_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "moves: %d", slv->stats.moves);
  BTOR_MSG (btor->msg, 1, "restarts: %d", slv->stats.restarts);
}

static void
print_time_stats_aigprop_solver (Btor *btor)
{
  assert (btor);
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds in AIG propagator");
}

BtorSolver *
btor_new_aigprop_solver (Btor *btor)
{
  assert (btor);

  BtorAIGPropSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind                 = BTOR_AIGPROP_SOLVER_KIND;
  slv->api.clone            = clone_aigprop_solver;
  slv->api.delet            = delete_aigprop_solver;
  slv->api.sat              = sat_aigprop_solver;
  slv->api.generate_model   = generate_model_aigprop_solver;
  slv->api.print_stats      = print_stats_aigprop_solver;
  slv->api.print_time_stats = print_time_stats_aigprop_solver;

  BTOR_MSG (btor->msg, 1, "enabled aigprop engine");

  return (BtorSolver *) slv;
}

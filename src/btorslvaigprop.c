/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvaigprop.h"
#include "aigprop.h"
#include "btorabort.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btormodel.h"
#include "btoropt.h"
#include "btorslvprop.h"
#include "btorslvsls.h"  // for score computation
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/

#define BTOR_AIGPROP_MAXSTEPS_CFACT 100
#define BTOR_AIGPROP_MAXSTEPS(i) \
  (BTOR_AIGPROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

/*------------------------------------------------------------------------*/

static BtorAIGPropSolver *
clone_aigprop_solver (Btor *clone, BtorAIGPropSolver *slv, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (slv);
  assert (slv->kind == BTOR_AIGPROP_SOLVER_KIND);
  assert (exp_map);

  (void) exp_map;

  BtorAIGPropSolver *res;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorAIGPropSolver));
  res->btor = clone;
  res->aprop =
      aigprop_clone_aigprop (btor_get_aig_mgr_btor (clone), slv->aprop);
  return res;
}

static void
delete_aigprop_solver (BtorAIGPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_AIGPROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

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
generate_model_from_aig_model (Btor *btor)
{
  assert (btor);

  int i;
  BtorNode *cur, *real_cur;
  BtorBitVector *bv;
  BtorAIGPropSolver *slv;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack stack;
  BtorIntHashTable *cache;
  AIGProp *aprop;

  if (!(slv = BTOR_AIGPROP_SOLVER (btor))) return;

  aprop = slv->aprop;
  assert (aprop);
  assert (aprop->model);

  btor_init_bv_model (btor, &btor->bv_model);
  btor_init_fun_model (btor, &btor->fun_model);

  /* map inputs back to expression layer
   * Note: we can only map inputs back, since other nodes might have partial
   *       assignments only (e.g. for a slice we may have AIGs for the sliced
   *       bits of its input only) */
  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (btor->mm);
  assert (btor->unsynthesized_constraints->count == 0);
  btor_init_ptr_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    BTOR_PUSH_STACK (btor->mm, stack, btor_next_ptr_hash_table_iterator (&it));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    if (btor_contains_int_hash_table (cache, real_cur->id)) continue;
    btor_add_int_hash_table (cache, real_cur->id);
    if (btor_is_bv_const_node (real_cur))
      btor_add_to_bv_model (
          btor, btor->bv_model, real_cur, btor_const_get_bits (real_cur));
    if (btor_is_bv_var_node (real_cur))
    {
      bv = get_assignment_bv (btor->mm, real_cur, aprop->model);
      btor_add_to_bv_model (btor, btor->bv_model, real_cur, bv);
      btor_free_bv (btor->mm, bv);
    }
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (btor->mm, stack, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (btor->mm, stack);
  btor_delete_int_hash_table (cache);
}

static void
generate_model_aigprop_solver (BtorAIGPropSolver *slv,
                               int model_for_all_nodes,
                               int reset)
{
  assert (slv);

  Btor *btor = slv->btor;

  if (reset)
  {
    btor_init_bv_model (btor, &btor->bv_model);
    btor_init_fun_model (btor, &btor->fun_model);
    btor_generate_model (
        btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
    return;
  }

  /* generate model for non-input nodes */
  btor_generate_model (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

/* Note: limits are currently unused */
static int
sat_aigprop_solver (BtorAIGPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_AIGPROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  int sat_result;
  BtorPtrHashTableIterator it;
  BtorNode *root;
  BtorAIG *aig;
  Btor *btor;

  btor = slv->btor;

  if (btor->inconsistent) goto UNSAT;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  sat_result = btor_simplify (btor);
  BTOR_ABORT (btor->ufs->count != 0
                  || (!btor_get_opt (btor, BTOR_OPT_BETA_REDUCE_ALL)
                      && btor->lambdas->count != 0),
              "aigprop engine supports QF_BV only");

  if (btor->inconsistent) goto UNSAT;

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  btor_process_unsynthesized_constraints (btor);

  if (btor->found_constraint_false)
  {
  UNSAT:
    sat_result = BTOR_RESULT_UNSAT;
    goto DONE;
  }
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
  assert (btor_check_all_hash_tables_simp_free_dbg (btor));

#ifndef NDEBUG
  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    assert (!BTOR_REAL_ADDR_NODE (
        ((BtorNode *) btor_next_ptr_hash_table_iterator (&it))->simplified));
#endif

  assert (slv->aprop);
  assert (!slv->aprop->roots);
  assert (!slv->aprop->score);
  assert (!slv->aprop->model);
#ifndef NBTORLOG
  slv->aprop->loglevel = btor_get_opt (btor, BTOR_OPT_LOGLEVEL);
#endif
  slv->aprop->seed         = btor_get_opt (btor, BTOR_OPT_SEED);
  slv->aprop->use_restarts = btor_get_opt (btor, BTOR_OPT_AIGPROP_USE_RESTARTS);
  slv->aprop->use_bandit   = btor_get_opt (btor, BTOR_OPT_AIGPROP_USE_BANDIT);

  /* collect roots AIGs */
  slv->aprop->roots =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_aig_by_id,
                               (BtorCmpPtr) btor_compare_aig_by_id);
  assert (btor->unsynthesized_constraints->count == 0);
  btor_init_ptr_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    root = btor_next_ptr_hash_table_iterator (&it);

    if (!BTOR_REAL_ADDR_NODE (root)->av) btor_synthesize_exp (btor, root, 0);
    assert (BTOR_REAL_ADDR_NODE (root)->av->len == 1);
    aig = BTOR_REAL_ADDR_NODE (root)->av->aigs[0];
    if (BTOR_IS_INVERTED_NODE (root)) aig = BTOR_INVERT_AIG (aig);
    if (aig == BTOR_AIG_FALSE) goto UNSAT;
    if (aig == BTOR_AIG_TRUE) continue;
    if (!btor_get_ptr_hash_table (slv->aprop->roots, aig))
      (void) btor_add_ptr_hash_table (slv->aprop->roots, aig);
  }

  if ((sat_result = aigprop_sat (slv->aprop)) == BTOR_RESULT_UNSAT) goto UNSAT;
  generate_model_from_aig_model (btor);
  assert (sat_result == BTOR_RESULT_SAT);
  slv->stats.moves    = slv->aprop->stats.moves;
  slv->stats.restarts = slv->aprop->stats.restarts;
  slv->time.aprop_sat = slv->aprop->time.sat;
DONE:
  if (slv->aprop->roots)
  {
    btor_delete_ptr_hash_table (slv->aprop->roots);
    slv->aprop->roots = 0;
  }
  if (slv->aprop->score)
  {
    btor_delete_ptr_hash_table (slv->aprop->score);
    slv->aprop->score = 0;
  }
  if (slv->aprop->model)
  {
    btor_delete_ptr_hash_table (slv->aprop->model);
    slv->aprop->model = 0;
  }
  btor->valid_assignments = 1;
  btor->last_sat_result   = sat_result;
  return sat_result;
}

static void
print_stats_aigprop_solver (BtorAIGPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_AIGPROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;

  btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "restarts: %d", slv->stats.restarts);
  BTOR_MSG (btor->msg, 1, "moves: %d", slv->stats.moves);
  BTOR_MSG (btor->msg,
            1,
            "moves per second: %.2f",
            (double) slv->stats.moves / slv->time.aprop_sat);
}

static void
print_time_stats_aigprop_solver (BtorAIGPropSolver *slv)
{
  assert (slv);

  Btor *btor;

  btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "%.2f seconds in AIG propagator", slv->time.aprop_sat);
  BTOR_MSG (btor->msg, 1, "");
}

BtorSolver *
btor_new_aigprop_solver (Btor *btor)
{
  assert (btor);

  BtorAIGPropSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->btor = btor;
  slv->kind = BTOR_AIGPROP_SOLVER_KIND;

  slv->api.clone = (BtorSolverClone) clone_aigprop_solver;
  slv->api.delet = (BtorSolverDelete) delete_aigprop_solver;
  slv->api.sat   = (BtorSolverSat) sat_aigprop_solver;
  slv->api.generate_model =
      (BtorSolverGenerateModel) generate_model_aigprop_solver;
  slv->api.print_stats = (BtorSolverPrintStats) print_stats_aigprop_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_aigprop_solver;

  slv->aprop =
      aigprop_new_aigprop (btor_get_aig_mgr_btor (btor),
                           btor_get_opt (btor, BTOR_OPT_SEED),
                           btor_get_opt (btor, BTOR_OPT_AIGPROP_USE_RESTARTS),
                           btor_get_opt (btor, BTOR_OPT_AIGPROP_USE_BANDIT));

  BTOR_MSG (btor->msg, 1, "enabled aigprop engine");

  return (BtorSolver *) slv;
}

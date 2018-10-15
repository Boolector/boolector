/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
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
#include "btorprintmodel.h"
#include "btorslvprop.h"
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
  res->btor  = clone;
  res->aprop = aigprop_clone_aigprop (btor_get_aig_mgr (clone), slv->aprop);
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

static int32_t
get_assignment_aig (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (aprop->model);

  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;
  /* initialize don't care bits with false */
  if (!btor_hashint_map_contains (aprop->model, BTOR_REAL_ADDR_AIG (aig)->id))
    return BTOR_IS_INVERTED_AIG (aig) ? 1 : -1;
  return aigprop_get_assignment_aig (aprop, aig);
}

BtorBitVector *
get_assignment_bv (BtorMemMgr *mm, BtorNode *exp, AIGProp *aprop)
{
  assert (mm);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (aprop);

  int32_t bit;
  uint32_t i, j, width;
  BtorBitVector *res;
  BtorAIGVec *av;

  if (!exp->av)
    return btor_bv_new (mm, btor_node_bv_get_width (exp->btor, exp));

  av    = exp->av;
  width = av->width;
  res   = btor_bv_new (mm, width);

  for (i = 0, j = width - 1; i < width; i++, j--)
  {
    bit = get_assignment_aig (aprop, av->aigs[j]);
    assert (bit == -1 || bit == 1);
    btor_bv_set_bit (res, i, bit == 1 ? 1 : 0);
  }
  return res;
}

static void
generate_model_from_aig_model (Btor *btor)
{
  assert (btor);

  uint32_t i;
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

  btor_model_init_bv (btor, &btor->bv_model);
  btor_model_init_fun (btor, &btor->fun_model);

  /* map inputs back to expression layer
   * Note: we can only map inputs back, since other nodes might have partial
   *       assignments only (e.g. for a slice we may have AIGs for the sliced
   *       bits of its input only) */
  BTOR_INIT_STACK (btor->mm, stack);
  cache = btor_hashint_table_new (btor->mm);
  assert (btor->unsynthesized_constraints->count == 0);
  btor_iter_hashptr_init (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    BTOR_PUSH_STACK (stack, btor_iter_hashptr_next (&it));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = btor_node_real_addr (cur);
    if (btor_hashint_table_contains (cache, real_cur->id)) continue;
    btor_hashint_table_add (cache, real_cur->id);
    if (btor_node_is_bv_const (real_cur))
      btor_model_add_to_bv (btor,
                            btor->bv_model,
                            real_cur,
                            btor_node_bv_const_get_bits (real_cur));
    if (btor_node_is_bv_var (real_cur))
    {
      bv = get_assignment_bv (btor->mm, real_cur, aprop);
      btor_model_add_to_bv (btor, btor->bv_model, real_cur, bv);
      btor_bv_free (btor->mm, bv);
    }
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (stack, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (stack);
  btor_hashint_table_delete (cache);
}

static void
generate_model_aigprop_solver (BtorAIGPropSolver *slv,
                               bool model_for_all_nodes,
                               bool reset)
{
  assert (slv);

  Btor *btor = slv->btor;

  if (reset)
  {
    btor_model_init_bv (btor, &btor->bv_model);
    btor_model_init_fun (btor, &btor->fun_model);
    btor_model_generate (
        btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
    return;
  }

  /* generate model for non-input nodes */
  btor_model_generate (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

/* Note: limits are currently unused */
static int32_t
sat_aigprop_solver (BtorAIGPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_AIGPROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  int32_t sat_result;
  BtorIntHashTable *roots;
  BtorPtrHashTableIterator it;
  BtorNode *root;
  BtorAIG *aig;
  Btor *btor;

  btor = slv->btor;
  assert (!btor->inconsistent);
  roots = 0;

  if (btor_terminate (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  BTOR_ABORT (btor->ufs->count != 0
                  || (!btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL)
                      && btor->lambdas->count != 0),
              "aigprop engine supports QF_BV only");

  btor_process_unsynthesized_constraints (btor);

  if (btor->found_constraint_false)
  {
  UNSAT:
    sat_result = BTOR_RESULT_UNSAT;
    goto DONE;
  }
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
  assert (btor_dbg_check_all_hash_tables_simp_free (btor));

#ifndef NDEBUG
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    assert (!btor_node_real_addr (((BtorNode *) btor_iter_hashptr_next (&it)))
                 ->simplified);
#endif

  assert (slv->aprop);
  assert (!slv->aprop->roots);
  assert (!slv->aprop->score);
  assert (!slv->aprop->model);
  slv->aprop->loglevel     = btor_opt_get (btor, BTOR_OPT_LOGLEVEL);
  slv->aprop->seed         = btor_opt_get (btor, BTOR_OPT_SEED);
  slv->aprop->use_restarts = btor_opt_get (btor, BTOR_OPT_AIGPROP_USE_RESTARTS);
  slv->aprop->use_bandit   = btor_opt_get (btor, BTOR_OPT_AIGPROP_USE_BANDIT);

  /* collect roots AIGs */
  roots = btor_hashint_table_new (btor->mm);
  assert (btor->unsynthesized_constraints->count == 0);
  btor_iter_hashptr_init (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    root = btor_iter_hashptr_next (&it);

    if (!btor_node_real_addr (root)->av) btor_synthesize_exp (btor, root, 0);
    assert (btor_node_real_addr (root)->av->width == 1);
    aig = btor_node_real_addr (root)->av->aigs[0];
    if (btor_node_is_inverted (root)) aig = BTOR_INVERT_AIG (aig);
    if (aig == BTOR_AIG_FALSE) goto UNSAT;
    if (aig == BTOR_AIG_TRUE) continue;
    if (!btor_hashint_table_contains (roots, btor_aig_get_id (aig)))
      (void) btor_hashint_table_add (roots, btor_aig_get_id (aig));
  }

  if ((sat_result = aigprop_sat (slv->aprop, roots)) == BTOR_RESULT_UNSAT)
    goto UNSAT;
  generate_model_from_aig_model (btor);
  assert (sat_result == BTOR_RESULT_SAT);
  slv->stats.moves                  = slv->aprop->stats.moves;
  slv->stats.restarts               = slv->aprop->stats.restarts;
  slv->time.aprop_sat               = slv->aprop->time.sat;
  slv->time.aprop_update_cone       = slv->aprop->time.update_cone;
  slv->time.aprop_update_cone_reset = slv->aprop->time.update_cone_reset;
  slv->time.aprop_update_cone_model_gen =
      slv->aprop->time.update_cone_model_gen;
  slv->time.aprop_update_cone_compute_score =
      slv->aprop->time.update_cone_compute_score;
DONE:
  if (slv->aprop->model)
  {
    btor_hashint_map_delete (slv->aprop->model);
    slv->aprop->model = 0;
  }
  if (roots) btor_hashint_table_delete (roots);
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
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (total)",
            slv->time.aprop_update_cone);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (reset)",
            slv->time.aprop_update_cone_reset);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (model gen)",
            slv->time.aprop_update_cone_model_gen);
  if (btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT))
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds for updating cone (compute score)",
              slv->time.aprop_update_cone_compute_score);
  BTOR_MSG (btor->msg, 1, "");
}

static void
print_model (BtorAIGPropSolver *slv, const char *format, FILE *file)
{
  btor_print_model_aufbv (slv->btor, format, file);
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
  slv->api.print_model = (BtorSolverPrintModel) print_model;

  slv->aprop =
      aigprop_new_aigprop (btor_get_aig_mgr (btor),
                           btor_opt_get (btor, BTOR_OPT_LOGLEVEL),
                           btor_opt_get (btor, BTOR_OPT_SEED),
                           btor_opt_get (btor, BTOR_OPT_AIGPROP_USE_RESTARTS),
                           btor_opt_get (btor, BTOR_OPT_AIGPROP_USE_BANDIT));

  BTOR_MSG (btor->msg, 1, "enabled aigprop engine");

  return (BtorSolver *) slv;
}

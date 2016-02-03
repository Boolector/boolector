/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvcore.h"
#include "btorbeta.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btordcr.h"
#include "btorexit.h"
#include "btorlog.h"
#include "btormodel.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#define DP_QSORT_JUST 0
#define DP_QSORT_ASC 1
#define DP_QSORT_DESC 2
#define DP_QSORT_ASC_DESC_FIRST 3
#define DP_QSORT_ASC_DESC_ALW 4
#define DP_QSORT DP_QSORT_JUST

// TODO (ma): better abort handling BTOR_ABORT_INTERNAL?
#define BTOR_ABORT_CORE(cond, msg)                   \
  do                                                 \
  {                                                  \
    if (cond)                                        \
    {                                                \
      printf ("[btorcore] %s: %s\n", __func__, msg); \
      fflush (stdout);                               \
      exit (BTOR_ERR_EXIT);                          \
    }                                                \
  } while (0)

static BtorCoreSolver *
clone_core_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp_map);

  int h;
  BtorCoreSolver *slv;
  BtorCoreSolver *res;

  if (!(slv = BTOR_CORE_SOLVER (btor))) return 0;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorCoreSolver));

  res->btor   = clone;
  res->lemmas = btor_clone_ptr_hash_table (
      clone->mm, slv->lemmas, btor_clone_key_as_node, 0, exp_map, 0);

  btor_clone_node_ptr_stack (
      clone->mm, &slv->cur_lemmas, &res->cur_lemmas, exp_map);

  if (slv->score)
  {
    h = btor->options.just_heuristic.val;
    if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
    {
      res->score = btor_clone_ptr_hash_table (clone->mm,
                                              slv->score,
                                              btor_clone_key_as_node,
                                              btor_clone_data_as_htable_ptr,
                                              exp_map,
                                              exp_map);
    }
    else
    {
      assert (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
      res->score = btor_clone_ptr_hash_table (clone->mm,
                                              slv->score,
                                              btor_clone_key_as_node,
                                              btor_clone_data_as_int,
                                              exp_map,
                                              0);
    }
  }

  BTOR_INIT_STACK (res->stats.lemmas_size);
  if (BTOR_SIZE_STACK (slv->stats.lemmas_size) > 0)
  {
    BTOR_CNEWN (clone->mm,
                res->stats.lemmas_size.start,
                BTOR_SIZE_STACK (slv->stats.lemmas_size));

    res->stats.lemmas_size.end =
        res->stats.lemmas_size.start + BTOR_SIZE_STACK (slv->stats.lemmas_size);
    res->stats.lemmas_size.top = res->stats.lemmas_size.start
                                 + BTOR_COUNT_STACK (slv->stats.lemmas_size);
    memcpy (res->stats.lemmas_size.start,
            slv->stats.lemmas_size.start,
            BTOR_SIZE_STACK (slv->stats.lemmas_size) * sizeof (int));
  }

  return res;
}

static void
delete_core_solver (BtorCoreSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BtorPtrHashTable *t;
  BtorHashTableIterator it, iit;
  BtorNode *exp;
  Btor *btor;

  btor = slv->btor;

  btor_init_node_hash_table_iterator (&it, slv->lemmas);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (slv->lemmas);

  if (slv->score)
  {
    btor_init_node_hash_table_iterator (&it, slv->score);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      if (btor->options.just_heuristic.val == BTOR_JUST_HEUR_BRANCH_MIN_APP)
      {
        t   = (BtorPtrHashTable *) it.bucket->data.as_ptr;
        exp = btor_next_node_hash_table_iterator (&it);
        btor_release_exp (btor, exp);

        btor_init_node_hash_table_iterator (&iit, t);
        while (btor_has_next_node_hash_table_iterator (&iit))
          btor_release_exp (btor, btor_next_node_hash_table_iterator (&iit));
        btor_delete_ptr_hash_table (t);
      }
      else
      {
        assert (btor->options.just_heuristic.val
                == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
        btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
      }
    }
    btor_delete_ptr_hash_table (slv->score);
  }

  BTOR_RELEASE_STACK (btor->mm, slv->cur_lemmas);
  BTOR_RELEASE_STACK (btor->mm, slv->stats.lemmas_size);
  BTOR_DELETE (btor->mm, slv);
  btor->slv = 0;
}

/*------------------------------------------------------------------------*/

static void
configure_sat_mgr (Btor *btor)
{
  BtorSATMgr *smgr;

  smgr = btor_get_sat_mgr_btor (btor);
  if (btor_is_initialized_sat (smgr)) return;

  switch (btor->options.sat_engine.val)
  {
#ifdef BTOR_USE_LINGELING
    case BTOR_SAT_ENGINE_LINGELING:
      btor_enable_lingeling_sat (smgr,
                                 btor->options.sat_engine.valstr,
                                 btor->options.sat_engine_lgl_fork.val == 1);
      break;
#endif
#ifdef BTOR_USE_PICOSAT
    case BTOR_SAT_ENGINE_PICOSAT: btor_enable_picosat_sat (smgr); break;
#endif
#ifdef BTOR_USE_MINISAT
    case BTOR_SAT_ENGINE_MINISAT: btor_enable_minisat_sat (smgr); break;
#endif
    default: BTOR_ABORT_CORE (1, "no SAT solver configured");
  }

  btor_init_sat (smgr);

  /* reset SAT solver to non-incremental if all functions have been
   * eliminated */
  if (!btor->options.incremental.val && smgr->inc_required
      && btor->lambdas->count == 0 && btor->ufs->count == 0)
  {
    smgr->inc_required = 0;
    BTOR_MSG (btor->msg,
              1,
              "no functions found, resetting SAT solver to non-incremental");
  }
}

static BtorSolverResult
timed_sat_sat (Btor *btor, int limit)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  double start, delta;
  BtorSolverResult res;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;

  amgr = btor_get_aig_mgr_btor (btor);
  BTOR_MSG (btor->msg,
            1,
            "%u AIG vars, %u AIG ands, %u CNF vars, %u CNF clauses",
            amgr->cur_num_aig_vars,
            amgr->cur_num_aigs,
            amgr->num_cnf_vars,
            amgr->num_cnf_clauses);
  smgr  = btor_get_sat_mgr_btor (btor);
  start = btor_time_stamp ();
  res   = btor_sat_sat (smgr, limit);
  delta = btor_time_stamp () - start;
  BTOR_CORE_SOLVER (btor)->time.sat += delta;

  BTOR_MSG (
      btor->msg, 2, "SAT solver returns %d after %.1f seconds", res, delta);

  return res;
}

static bool
has_bv_assignment (Btor *btor, BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  return (btor->bv_model && btor_get_ptr_hash_table (btor->bv_model, exp) != 0)
         || BTOR_IS_SYNTH_NODE (exp) || BTOR_IS_BV_CONST_NODE (exp);
}

static BtorBitVector *
get_bv_assignment (Btor *btor, BtorNode *exp)
{
  assert (btor->bv_model);
  assert (!BTOR_REAL_ADDR_NODE (exp)->parameterized);

  BtorNode *real_exp;
  BtorBitVector *bv, *result;
  BtorPtrHashBucket *b;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  b        = btor_get_ptr_hash_table (btor->bv_model, real_exp);
  if (b)
    bv = btor_copy_bv (btor->mm, b->data.as_ptr);
  else /* cache assignment to avoid querying the sat solver multiple times */
  {
    /* synthesized nodes are always encoded and have an assignment */
    if (BTOR_IS_SYNTH_NODE (real_exp))
      bv = btor_get_assignment_bv (btor->mm, real_exp, false);
    else if (BTOR_IS_BV_CONST_NODE (real_exp))
      bv = btor_copy_bv (btor->mm, btor_const_get_bits (real_exp));
    /* initialize var, apply, and feq nodes if they are not yet synthesized
     * and encoded (not in the BV skeleton yet, and thus unconstrained). */
    else if (BTOR_IS_BV_VAR_NODE (real_exp) || BTOR_IS_APPLY_NODE (real_exp)
             || BTOR_IS_FEQ_NODE (real_exp))
    {
      if (!BTOR_IS_SYNTH_NODE (real_exp))
        BTORLOG (1, "zero-initialize: %s", node2string (real_exp));
      bv = btor_get_assignment_bv (btor->mm, real_exp, true);
    }
    else
      bv = btor_eval_exp (btor, real_exp);
    btor_add_to_bv_model (btor, btor->bv_model, real_exp, bv);
  }

  if (BTOR_IS_INVERTED_NODE (exp))
  {
    result = btor_not_bv (btor->mm, bv);
    btor_free_bv (btor->mm, bv);
  }
  else
    result = bv;

  return result;
}

/*------------------------------------------------------------------------*/

static Btor *
new_exp_layer_clone_for_dual_prop (Btor *btor,
                                   BtorNodeMap **exp_map,
                                   BtorNode **root)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp_map);
  assert (root);

  double start;
  Btor *clone;
  BtorNode *cur, *and;
  BtorHashTableIterator it;

  /* empty formula */
  if (btor->unsynthesized_constraints->count == 0) return 0;

  start = btor_time_stamp ();
  clone = btor_clone_exp_layer (btor, exp_map);
  assert (!clone->synthesized_constraints->count);
  assert (clone->unsynthesized_constraints->count);

  clone->options.model_gen.val   = 0;
  clone->options.incremental.val = 1;
#ifdef BTOR_CHECK_MODEL
  /* cleanup dangling references when model validation is enabled */
  clone->options.auto_cleanup_internal.val = 1;
#endif
#ifndef NBTORLOG
  clone->options.loglevel.val = 0;
#endif
  clone->options.verbosity.val = 0;
  clone->options.dual_prop.val = 0;

  assert (!btor_is_initialized_sat (btor_get_sat_mgr_btor (clone)));
  btor_set_opt_str (clone, BTOR_OPT_SAT_ENGINE, "plain=1");
  configure_sat_mgr (clone);

  btor_init_node_hash_table_iterator (&it, clone->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_REAL_ADDR_NODE (cur)->constraint = 0;
    if (!*root)
    {
      *root = btor_copy_exp (clone, cur);
    }
    else
    {
      and = btor_and_exp (clone, *root, cur);
      btor_release_exp (clone, *root);
      *root = and;
    }
  }

  btor_init_node_hash_table_iterator (&it, clone->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, clone->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (clone, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (clone->unsynthesized_constraints);
  btor_delete_ptr_hash_table (clone->assumptions);
  clone->unsynthesized_constraints =
      btor_new_ptr_hash_table (clone->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  clone->assumptions =
      btor_new_ptr_hash_table (clone->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_CORE_SOLVER (btor)->time.search_init_apps_cloning +=
      btor_time_stamp () - start;
  return clone;
}

static void
assume_inputs (Btor *btor,
               Btor *clone,
               BtorNodePtrStack *inputs,
               BtorNodeMap *exp_map,
               BtorNodeMap *key_map,
               BtorNodeMap *assumptions)
{
  assert (btor);
  assert (clone);
  assert (inputs);
  assert (exp_map);
  assert (key_map);
  assert (key_map->table->count == 0);
  assert (assumptions);

  int i;
  BtorNode *cur_btor, *cur_clone, *bv_const, *bv_eq;
  BtorBitVector *bv;

  for (i = 0; i < BTOR_COUNT_STACK (*inputs); i++)
  {
    cur_btor  = BTOR_PEEK_STACK (*inputs, i);
    cur_clone = btor_mapped_node (exp_map, cur_btor);
    assert (cur_clone);
    assert (BTOR_IS_REGULAR_NODE (cur_clone));
    assert (!btor_mapped_node (key_map, cur_clone));
    btor_map_node (key_map, cur_clone, cur_btor);

    assert (BTOR_IS_REGULAR_NODE (cur_btor));
    bv       = get_bv_assignment (btor, cur_btor);
    bv_const = btor_const_exp (clone, bv);
    btor_free_bv (btor->mm, bv);
    bv_eq = btor_eq_exp (clone, cur_clone, bv_const);
    BTORLOG (1,
             "assume input: %s (%s)",
             node2string (cur_btor),
             node2string (bv_const));
    btor_assume_exp (clone, bv_eq);
    btor_map_node (assumptions, bv_eq, cur_clone);
    btor_release_exp (clone, bv_const);
    btor_release_exp (clone, bv_eq);
  }
}

static BtorNode *
create_function_inequality (Btor *btor, BtorNode *feq)
{
  assert (BTOR_IS_REGULAR_NODE (feq));
  assert (BTOR_IS_FEQ_NODE (feq));

  BtorMemMgr *mm;
  BtorNode *var, *app0, *app1, *eq, *arg;
  BtorSortUniqueTable *sorts;
  BtorSortId funsort, sort;
  BtorNodePtrStack args;
  BtorTupleSortIterator it;

  BTOR_INIT_STACK (args);

  mm      = btor->mm;
  sorts   = &btor->sorts_unique_table;
  funsort = btor_get_domain_fun_sort (sorts, feq->e[0]->sort_id);

  btor_init_tuple_sort_iterator (&it, sorts, funsort);
  while (btor_has_next_tuple_sort_iterator (&it))
  {
    sort = btor_next_tuple_sort_iterator (&it);
    assert (btor_is_bitvec_sort (sorts, sort));
    var = btor_var_exp (btor, btor_get_width_bitvec_sort (sorts, sort), 0);
    BTOR_PUSH_STACK (mm, args, var);
  }

  arg  = btor_args_exp (btor, BTOR_COUNT_STACK (args), args.start);
  app0 = btor_apply_exp_node (btor, feq->e[0], arg);
  app1 = btor_apply_exp_node (btor, feq->e[1], arg);
  eq   = btor_eq_exp (btor, app0, app1);

  btor_release_exp (btor, arg);
  btor_release_exp (btor, app0);
  btor_release_exp (btor, app1);
  while (!BTOR_EMPTY_STACK (args))
    btor_release_exp (btor, BTOR_POP_STACK (args));
  BTOR_RELEASE_STACK (mm, args);

  return BTOR_INVERT_NODE (eq);
}

/* for every function equality f = g, add
 * f != g -> f(a) != g(a) */
static void
add_function_inequality_constraints (Btor *btor)
{
  uint32_t i;
  BtorNode *cur, *neq, *con;
  BtorNodePtrStack feqs, visit;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;

  mm = btor->mm;
  BTOR_INIT_STACK (visit);
  /* we have to add inequality constraints for every function equality
   * in the formula (var_rhs and fun_rhs are still part of the formula). */
  btor_init_node_hash_table_iterator (&it, btor->var_rhs);
  btor_queue_node_hash_table_iterator (&it, btor->fun_rhs);
  btor_queue_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  assert (btor->embedded_constraints->count == 0);
  assert (btor->varsubst_constraints->count == 0);
  /* we don't have to traverse synthesized_constraints as we already created
   * inequality constraints for them in a previous sat call */
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    cur = btor_pointer_chase_simplified_exp (btor, cur);
    BTOR_PUSH_STACK (mm, visit, cur);
  }

  /* collect all reachable function equalities */
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (feqs);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)) continue;

    btor_add_int_hash_table (cache, cur->id);
    if (BTOR_IS_FEQ_NODE (cur))
    {
      b = btor_get_ptr_hash_table (btor->feqs, cur);
      /* already visited and created inequality constraint in a previous
       * sat call */
      if (b->data.as_int) continue;
      BTOR_PUSH_STACK (mm, feqs, cur);
      BTOR_ABORT_CORE (
          (!cur->e[0]->is_array || !cur->e[1]->is_array)
              && (!BTOR_IS_UF_NODE (cur->e[0]) || !BTOR_IS_UF_NODE (cur->e[1])),
          "equality over lambda not supported yet");
    }
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  /* add inequality constraint for every reachable function equality */
  while (!BTOR_EMPTY_STACK (feqs))
  {
    cur = BTOR_POP_STACK (feqs);
    assert (BTOR_IS_FEQ_NODE (cur));
    assert (!cur->parameterized);
    b = btor_get_ptr_hash_table (btor->feqs, cur);
    assert (b);
    assert (b->data.as_int == 0);
    b->data.as_int = 1;
    neq            = create_function_inequality (btor, cur);
    con            = btor_implies_exp (btor, BTOR_INVERT_NODE (cur), neq);
    btor_assert_exp (btor, con);
    btor_release_exp (btor, con);
    btor_release_exp (btor, neq);
    BTORLOG (2, "add inequality constraint for %s", node2string (cur));
  }
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, feqs);
  btor_delete_int_hash_table (cache);
}

static int
sat_aux_btor_dual_prop (Btor *btor)
{
  assert (btor);

  BtorSolverResult result;

  if (btor->inconsistent) goto DONE;

  BTOR_MSG (btor->msg, 1, "calling SAT");
  configure_sat_mgr (btor);

  if (btor->valid_assignments == 1) btor_reset_incremental_usage (btor);

  if (btor->feqs->count > 0) add_function_inequality_constraints (btor);

  assert (btor->synthesized_constraints->count == 0);
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
  assert (btor_check_all_hash_tables_simp_free_dbg (btor));
  assert (btor_check_assumptions_simp_free_dbg (btor));

  btor_add_again_assumptions (btor);

  result = timed_sat_sat (btor, -1);

  assert (result == BTOR_RESULT_UNSAT
          || (btor_terminate_btor (btor) && result == BTOR_RESULT_UNKNOWN));

DONE:
  result                  = BTOR_RESULT_UNSAT;
  btor->valid_assignments = 1;

  btor->last_sat_result = result;
  return result;
}

static void
collect_applies (Btor *btor,
                 Btor *clone,
                 BtorNodeMap *key_map,
                 BtorNodeMap *assumptions,
                 BtorNodePtrStack *top_applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (key_map);
  assert (assumptions);

  double start;
  int i;
  BtorMemMgr *mm;
  BtorCoreSolver *slv;
  BtorNode *cur_btor, *cur_clone, *bv_eq;
  BtorNodePtrStack unmark_stack, failed_eqs;
  BtorNodeMapIterator it;

  start = btor_time_stamp ();

  mm  = btor->mm;
  slv = BTOR_CORE_SOLVER (btor);

  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (failed_eqs);

  btor_init_node_map_iterator (&it, assumptions);
  while (btor_has_next_node_map_iterator (&it))
  {
    bv_eq     = btor_next_node_map_iterator (&it);
    cur_clone = btor_mapped_node (assumptions, bv_eq);
    assert (cur_clone);
    /* Note: node mapping is normalized, revert */
    if (BTOR_IS_INVERTED_NODE (cur_clone))
    {
      bv_eq     = BTOR_INVERT_NODE (bv_eq);
      cur_clone = BTOR_INVERT_NODE (cur_clone);
    }
    cur_btor = btor_mapped_node (key_map, cur_clone);
    assert (cur_btor);
    assert (BTOR_IS_REGULAR_NODE (cur_btor));
    assert (BTOR_IS_BV_VAR_NODE (cur_btor) || BTOR_IS_APPLY_NODE (cur_btor)
            || BTOR_IS_FEQ_NODE (cur_btor));

    if (BTOR_IS_BV_VAR_NODE (cur_btor))
      slv->stats.dp_assumed_vars += 1;
    else if (BTOR_IS_FEQ_NODE (cur_btor))
      slv->stats.dp_assumed_eqs += 1;
    else
    {
      assert (BTOR_IS_APPLY_NODE (cur_btor));
      slv->stats.dp_assumed_applies += 1;
    }

    if (btor_failed_exp (clone, bv_eq))
    {
      BTORLOG (1, "failed: %s", node2string (cur_btor));
      if (BTOR_IS_BV_VAR_NODE (cur_btor))
        slv->stats.dp_failed_vars += 1;
      else if (BTOR_IS_FEQ_NODE (cur_btor))
      {
        slv->stats.dp_failed_eqs += 1;
        BTOR_PUSH_STACK (mm, failed_eqs, cur_btor);
      }
      else
      {
        assert (BTOR_IS_APPLY_NODE (cur_btor));
        if (cur_btor->aux_mark) continue;
        slv->stats.dp_failed_applies += 1;
        cur_btor->aux_mark = 1;
        BTOR_PUSH_STACK (mm, unmark_stack, cur_btor);
        BTOR_PUSH_STACK (mm, *top_applies, cur_btor);
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (mm, unmark_stack);

  /* collect applies below failed function equalities */
  while (!BTOR_EMPTY_STACK (failed_eqs))
  {
    cur_btor = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (failed_eqs));

    if (!cur_btor->apply_below || cur_btor->aux_mark) continue;

    cur_btor->aux_mark = 1;
    BTOR_PUSH_STACK (mm, unmark_stack, cur_btor);

    /* we only need the "top applies" below a failed function equality */
    if (!cur_btor->parameterized && BTOR_IS_APPLY_NODE (cur_btor))
    {
      BTORLOG (1, "apply below eq: %s", node2string (cur_btor));
      BTOR_PUSH_STACK (mm, *top_applies, cur_btor);
      continue;
    }

    for (i = 0; i < cur_btor->arity; i++)
      BTOR_PUSH_STACK (mm, failed_eqs, cur_btor->e[i]);
  }
  BTOR_RELEASE_STACK (mm, failed_eqs);

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (mm, unmark_stack);

  slv->time.search_init_apps_collect_fa += btor_time_stamp () - start;
}

static void
set_up_dual_and_collect (Btor *btor,
                         Btor *clone,
                         BtorNode *clone_root,
                         BtorNodeMap *exp_map,
                         BtorNodePtrStack *inputs,
                         BtorNodePtrStack *top_applies,
                         int (*dp_cmp_inputs) (const void *, const void *))
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (clone_root);
  assert (exp_map);
  assert (inputs);
  assert (top_applies);
  assert (dp_cmp_inputs);

  double delta;
  BtorCoreSolver *slv;
  BtorNodeMap *assumptions, *key_map;

  delta = btor_time_stamp ();
  slv   = BTOR_CORE_SOLVER (btor);

  assumptions = btor_new_node_map (btor);
  key_map     = btor_new_node_map (btor);

  /* assume root */
  btor_assume_exp (clone, BTOR_INVERT_NODE (clone_root));

  /* assume assignments of bv vars and applies, partial assignments are
   * assumed as partial assignment (as slice on resp. var/apply) */
  qsort (inputs->start,
         BTOR_COUNT_STACK (*inputs),
         sizeof (BtorNode *),
         dp_cmp_inputs);
  assume_inputs (btor, clone, inputs, exp_map, key_map, assumptions);
  slv->time.search_init_apps_collect_var_apps += btor_time_stamp () - delta;

  /* let solver determine failed assumptions */
  delta = btor_time_stamp ();
  sat_aux_btor_dual_prop (clone);
  assert (clone->last_sat_result == BTOR_RESULT_UNSAT);
  slv->time.search_init_apps_sat += btor_time_stamp () - delta;

  /* extract partial model via failed assumptions */
  collect_applies (btor, clone, key_map, assumptions, top_applies);

  btor_delete_node_map (assumptions);
  btor_delete_node_map (key_map);
}

static void
search_initial_applies_dual_prop (Btor *btor,
                                  Btor *clone,
                                  BtorNode *clone_root,
                                  BtorNodeMap *exp_map,
                                  BtorNodePtrStack *top_applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (clone_root);
  assert (exp_map);
  assert (top_applies);
  assert (btor_check_id_table_aux_mark_unset_dbg (btor));

  double start;
  int i;
  BtorNode *cur;
  BtorNodePtrStack stack, unmark_stack, inputs;
  BtorHashTableIterator it;
  BtorSATMgr *smgr;
  BtorCoreSolver *slv;

  start = btor_time_stamp ();

  BTORLOG (1, "");
  BTORLOG (1, "*** search initial applies");

  slv                           = BTOR_CORE_SOLVER (btor);
  slv->stats.dp_failed_vars     = 0;
  slv->stats.dp_assumed_vars    = 0;
  slv->stats.dp_failed_applies  = 0;
  slv->stats.dp_assumed_applies = 0;

  smgr = btor_get_sat_mgr_btor (btor);
  if (!smgr->inc_required) return;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (inputs);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_FEQ_NODE (cur)
          || BTOR_IS_APPLY_NODE (cur))
      {
        assert (BTOR_IS_SYNTH_NODE (cur));
        BTOR_PUSH_STACK (btor->mm, inputs, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  (void) btor_cmp_exp_by_id_qsort_asc;

#if DP_QSORT == DP_QSORT_JUST
  btor_compute_scores_dual_prop (btor);
  set_up_dual_and_collect (btor,
                           clone,
                           clone_root,
                           exp_map,
                           &inputs,
                           top_applies,
                           btor_compare_scores_qsort);
#elif DP_QSORT == DP_QSORT_ASC
  set_up_dual_and_collect (btor,
                           clone,
                           clone_root,
                           exp_map,
                           &inputs,
                           top_applies,
                           btor_cmp_exp_by_id_qsort_asc);
#elif DP_QSORT == DP_QSORT_DESC
  set_up_dual_and_collect (btor,
                           clone,
                           clone_root,
                           exp_map,
                           &inputs,
                           top_applies,
                           btor_cmp_exp_by_id_qsort_desc);
#else

#if DP_QSORT_ASC_DESC_FIRST
  if (!slv->dp_cmp_inputs)
#endif
  {
    /* try different strategies and determine best */
    BtorNodePtrStack tmp_asc, tmp_desc;
    BTOR_INIT_STACK (tmp_asc);
    BTOR_INIT_STACK (tmp_desc);

    set_up_dual_and_collect (btor,
                             clone,
                             clone_root,
                             exp_map,
                             &inputs,
                             &tmp_desc,
                             btor_cmp_exp_by_id_qsort_desc);
    set_up_dual_and_collect (btor,
                             clone,
                             clone_root,
                             exp_map,
                             &inputs,
                             &tmp_asc,
                             btor_cmp_exp_by_id_qsort_asc);

    if (BTOR_COUNT_STACK (tmp_asc) < BTOR_COUNT_STACK (tmp_desc))
    {
      slv->dp_cmp_inputs = btor_cmp_exp_by_id_qsort_asc;
      for (i = 0; i < BTOR_COUNT_STACK (tmp_asc); i++)
        BTOR_PUSH_STACK (btor->mm, *top_applies, BTOR_PEEK_STACK (tmp_asc, i));
    }
    else
    {
      slv->dp_cmp_inputs = btor_cmp_exp_by_id_qsort_desc;
      for (i = 0; i < BTOR_COUNT_STACK (tmp_desc); i++)
        BTOR_PUSH_STACK (btor->mm, *top_applies, BTOR_PEEK_STACK (tmp_desc, i));
    }

    BTOR_RELEASE_STACK (btor->mm, tmp_asc);
    BTOR_RELEASE_STACK (btor->mm, tmp_desc);
  }
#if DP_QSORT_ASC_DESC_FIRST
  else
    set_up_dual_and_collect (btor,
                             clone,
                             clone_root,
                             exp_map,
                             &inputs,
                             top_applies,
                             slv->dp_cmp_inputs);
#endif
#endif

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, inputs);

  slv->time.search_init_apps += btor_time_stamp () - start;
}

static void
add_lemma_to_dual_prop_clone (Btor *btor,
                              Btor *clone,
                              BtorNode **root,
                              BtorNode *lemma,
                              BtorNodeMap *exp_map)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (clone);
  assert (lemma);

  BtorNode *clemma, *and;

  /* clone and rebuild lemma with rewrite level 0 (as we want the exact
   * expression) */
  clemma = btor_recursively_rebuild_exp_clone (btor, clone, lemma, exp_map, 0);
  assert (clemma);
  and = btor_and_exp (clone, *root, clemma);
  btor_release_exp (clone, clemma);
  btor_release_exp (clone, *root);
  *root = and;
}

/*------------------------------------------------------------------------*/

static void
search_initial_applies_bv_skeleton (Btor *btor, BtorNodePtrStack *applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (applies);
  assert (BTOR_EMPTY_STACK (*applies));
  assert (btor_check_id_table_aux_mark_unset_dbg (btor));

  double start;
  int i;
  BtorNode *cur;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;

  start = btor_time_stamp ();

  BTORLOG (1, "");
  BTORLOG (1, "*** search initial applies");

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_APPLY_NODE (cur) && !cur->parameterized)
      {
        //	      assert (BTOR_IS_SYNTH_NODE (cur));
        BTORLOG (1, "initial apply: %s", node2string (cur));
        BTOR_PUSH_STACK (btor->mm, *applies, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);

  BTOR_CORE_SOLVER (btor)->time.search_init_apps += btor_time_stamp () - start;
}

static void
search_initial_applies_just (Btor *btor, BtorNodePtrStack *top_applies)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (top_applies);
  assert (btor->unsynthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (btor_check_id_table_aux_mark_unset_dbg (btor));

  int i, h;
  int a, a0, a1;
  double start;
  BtorNode *cur, *e0, *e1;
  BtorHashTableIterator it;
  BtorNodePtrStack stack, unmark_stack;
  BtorAIGMgr *amgr;

  start = btor_time_stamp ();

  BTORLOG (1, "");
  BTORLOG (1, "*** search initial applies");

  amgr = btor_get_aig_mgr_btor (btor);
  h    = btor->options.just_heuristic.val;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  btor_compute_scores (btor);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_APPLY_NODE (cur) && !cur->parameterized)
      {
        BTORLOG (1, "initial apply: %s", node2string (cur));
        BTOR_PUSH_STACK (btor->mm, *top_applies, cur);
        continue;
      }

      if (!cur->parameterized && !BTOR_IS_FUN_NODE (cur)
          && btor_get_exp_width (btor, cur) == 1)
      {
        switch (cur->kind)
        {
          case BTOR_FEQ_NODE:
            a = BTOR_IS_SYNTH_NODE (cur)
                    ? btor_get_assignment_aig (amgr, cur->av->aigs[0])
                    : 0;  // 'x';

            if (a == 1 || a == 0) goto PUSH_CHILDREN;
            /* if equality is false (-1), we do not need to check
             * applies below for consistency as it is sufficient to
             * check the witnesses of inequality */
            break;

          case BTOR_AND_NODE:

            a = BTOR_IS_SYNTH_NODE (cur)
                    ? btor_get_assignment_aig (amgr, cur->av->aigs[0])
                    : 0;  // 'x'

            e0 = BTOR_REAL_ADDR_NODE (cur->e[0]);
            e1 = BTOR_REAL_ADDR_NODE (cur->e[1]);

            a0 = BTOR_IS_SYNTH_NODE (e0)
                     ? btor_get_assignment_aig (amgr, e0->av->aigs[0])
                     : 0;  // 'x'
            if (a0 && BTOR_IS_INVERTED_NODE (cur->e[0])) a0 *= -1;

            a1 = BTOR_IS_SYNTH_NODE (e1)
                     ? btor_get_assignment_aig (amgr, e1->av->aigs[0])
                     : 0;  // 'x'
            if (a1 && BTOR_IS_INVERTED_NODE (cur->e[1])) a1 *= -1;

            if (a != -1)  // and = 1 or x
            {
              BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
              BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
            }
            else  // and = 0
            {
              if (a0 == -1 && a1 == -1)  // both inputs 0
              {
                /* branch selection w.r.t selected heuristic */
                if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP
                    || h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
                {
                  if (btor_compare_scores (btor, cur->e[0], cur->e[1]))
                    BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
                  else
                    BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
                }
                else
                {
                  assert (h == BTOR_JUST_HEUR_LEFT);
                  BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
                }
              }
              else if (a0 == -1)  // only one input 0
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
              else if (a1 == -1)  // only one input 0
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
              else if (a0 == 0 && a1 == 1)  // first input x, second 0
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
              else if (a0 == 1 && a1 == 0)  // first input 0, second x
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
              else  // both inputs x
              {
                assert (a0 == 0);
                assert (a1 == 0);
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
                BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
              }
            }
            break;

#if 0
		  case BTOR_BCOND_NODE:
		    BTOR_PUSH_STACK (btor->mm, stack, cur->e[0]);
		    c = bv_assignment_str_exp (btor, cur->e[0]);
		    if (c[0] == '1')  // then
		      BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
		    else if (c[0] == '0')
		      BTOR_PUSH_STACK (btor->mm, stack, cur->e[2]);
		    else                   // else
		      {
			BTOR_PUSH_STACK (btor->mm, stack, cur->e[1]);
			BTOR_PUSH_STACK (btor->mm, stack, cur->e[2]);
		      }
		    btor_release_bv_assignment_str (btor, c);
		    break;
#endif

          default: goto PUSH_CHILDREN;
        }
      }
      else
      {
      PUSH_CHILDREN:
        for (i = 0; i < cur->arity; i++)
          BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
  BTOR_RELEASE_STACK (btor->mm, stack);

  BTOR_CORE_SOLVER (btor)->time.search_init_apps += btor_time_stamp () - start;
}

static bool
equal_bv_assignments (BtorNode *exp0, BtorNode *exp1)
{
  bool equal;
  Btor *btor;
  BtorBitVector *bv0, *bv1;

  btor  = BTOR_REAL_ADDR_NODE (exp0)->btor;
  bv0   = get_bv_assignment (btor, exp0);
  bv1   = get_bv_assignment (btor, exp1);
  equal = btor_compare_bv (bv0, bv1) == 0;
  btor_free_bv (btor->mm, bv0);
  btor_free_bv (btor->mm, bv1);
  return equal;
}

static int
compare_args_assignments (BtorNode *e0, BtorNode *e1)
{
  assert (BTOR_IS_REGULAR_NODE (e0));
  assert (BTOR_IS_REGULAR_NODE (e1));
  assert (BTOR_IS_ARGS_NODE (e0));
  assert (BTOR_IS_ARGS_NODE (e1));

  bool equal;
  BtorBitVector *bv0, *bv1;
  BtorNode *arg0, *arg1;
  Btor *btor;
  BtorArgsIterator it0, it1;
  btor = e0->btor;

  if (e0->sort_id != e1->sort_id) return 1;

  btor_init_args_iterator (&it0, e0);
  btor_init_args_iterator (&it1, e1);

  while (btor_has_next_args_iterator (&it0))
  {
    assert (btor_has_next_args_iterator (&it1));
    arg0 = btor_next_args_iterator (&it0);
    arg1 = btor_next_args_iterator (&it1);

    bv0 = get_bv_assignment (btor, arg0);
    bv1 = get_bv_assignment (btor, arg1);

    equal = btor_compare_bv (bv0, bv1) == 0;
    btor_free_bv (btor->mm, bv0);
    btor_free_bv (btor->mm, bv1);

    if (!equal) return 1;
  }

  return 0;
}

static unsigned int
hash_args_assignment (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARGS_NODE (exp));

  unsigned int hash;
  Btor *btor;
  BtorNode *arg;
  BtorArgsIterator it;
  BtorBitVector *bv;

  btor = exp->btor;
  hash = 0;
  btor_init_args_iterator (&it, exp);
  while (btor_has_next_args_iterator (&it))
  {
    arg = btor_next_args_iterator (&it);
    bv  = get_bv_assignment (btor, arg);
    hash += btor_hash_bv (bv);
    btor_free_bv (btor->mm, bv);
  }
  return hash;
}

static void
collect_premisses (Btor *btor,
                   BtorNode *from,
                   BtorNode *to,
                   BtorNode *args,
                   BtorPtrHashTable *cond_sel_if,
                   BtorPtrHashTable *cond_sel_else)
{
  assert (btor);
  assert (from);
  assert (to);
  assert (cond_sel_if);
  assert (cond_sel_else);
  assert (BTOR_IS_REGULAR_NODE (from));
  assert (BTOR_IS_REGULAR_NODE (args));
  assert (BTOR_IS_ARGS_NODE (args));
  assert (BTOR_IS_REGULAR_NODE (to));

  BTORLOG (1,
           "%s: %s, %s, %s",
           __FUNCTION__,
           node2string (from),
           node2string (to),
           node2string (args));

  BtorMemMgr *mm;
  BtorNode *fun, *result;
  BtorPtrHashTable *t;
  BtorBitVector *bv_assignment;

  mm = btor->mm;

  /* follow propagation path and collect all conditions that have been
   * evaluated during propagation */
  if (BTOR_IS_APPLY_NODE (from))
  {
    assert (BTOR_IS_REGULAR_NODE (to));
    assert (BTOR_IS_FUN_NODE (to));

    fun = from->e[0];

    for (;;)
    {
      assert (BTOR_IS_REGULAR_NODE (fun));
      assert (BTOR_IS_FUN_NODE (fun));

      if (fun == to) break;

      if (BTOR_IS_FUN_COND_NODE (fun))
      {
        bv_assignment = get_bv_assignment (btor, fun->e[0]);

        /* propagate over function ite */
        if (btor_is_true_bv (bv_assignment))
        {
          result = fun->e[1];
          t      = cond_sel_if;
        }
        else
        {
          result = fun->e[2];
          t      = cond_sel_else;
        }
        btor_free_bv (mm, bv_assignment);
        if (!btor_get_ptr_hash_table (t, fun->e[0]))
          btor_add_ptr_hash_table (t, btor_copy_exp (btor, fun->e[0]));
        fun = result;
        continue;
      }

      assert (BTOR_IS_LAMBDA_NODE (fun));

      btor_assign_args (btor, fun, args);
      result = btor_beta_reduce_partial_collect (
          btor, fun, cond_sel_if, cond_sel_else);
      btor_unassign_params (btor, fun);
      result = BTOR_REAL_ADDR_NODE (result);

      assert (BTOR_IS_APPLY_NODE (result));
      assert (result->e[1] == args);

      fun = result->e[0];
      btor_release_exp (btor, result);
    }
  }
  else
  {
    assert (BTOR_IS_LAMBDA_NODE (from));
    fun = from;

    btor_assign_args (btor, fun, args);
    result = btor_beta_reduce_partial_collect (
        btor, fun, cond_sel_if, cond_sel_else);
    btor_unassign_params (btor, fun);
    assert (BTOR_REAL_ADDR_NODE (result) == to);
    btor_release_exp (btor, result);
  }
}

static void
add_symbolic_lemma (Btor *btor,
                    BtorPtrHashTable *bconds_sel1,
                    BtorPtrHashTable *bconds_sel2,
                    BtorNode *a,
                    BtorNode *b,
                    BtorNode *args0,
                    BtorNode *args1)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (bconds_sel1);
  assert (bconds_sel2);
  assert (a);
  assert (b);
  assert (BTOR_IS_REGULAR_NODE (a));
  assert (BTOR_IS_APPLY_NODE (a));
  assert (BTOR_IS_REGULAR_NODE (args0));
  assert (BTOR_IS_ARGS_NODE (args0));
  assert (!args1 || BTOR_IS_REGULAR_NODE (b));
  assert (!args1 || BTOR_IS_APPLY_NODE (b));
  assert (!args1 || BTOR_IS_REGULAR_NODE (args1));
  assert (!args1 || BTOR_IS_ARGS_NODE (args1));
  assert (!a->parameterized);
  assert (!BTOR_REAL_ADDR_NODE (b)->parameterized);

  int lemma_size = 0;
  BtorCoreSolver *slv;
  BtorNode *cond, *eq, *and, *arg0, *arg1;
  BtorNode *premise = 0, *conclusion = 0, *lemma;
  BtorArgsIterator it0, it1;
  BtorHashTableIterator it;

  slv = BTOR_CORE_SOLVER (btor);

  BTORLOG (2, "lemma:");
  /* function congruence axiom conflict:
   *   apply arguments: a_0,...,a_n, b_0,...,b_n
   *   encode premisses: \forall i <= n . /\ a_i = b_i */
  if (args1)
  {
    assert (args0->sort_id == args1->sort_id);

    btor_init_args_iterator (&it0, args0);
    btor_init_args_iterator (&it1, args1);

    while (btor_has_next_args_iterator (&it0))
    {
      assert (btor_has_next_args_iterator (&it1));
      arg0 = btor_next_args_iterator (&it0);
      arg1 = btor_next_args_iterator (&it1);
      BTORLOG (2, "  p %s = %s", node2string (arg0), node2string (arg1));
      eq = btor_eq_exp (btor, arg0, arg1);
      if (premise)
      {
        and = btor_and_exp (btor, premise, eq);
        btor_release_exp (btor, premise);
        btor_release_exp (btor, eq);
        premise = and;
      }
      else
        premise = eq;

      lemma_size += 1;
    }
  }
  /* else beta reduction conflict */

  /* encode conclusion a = b */
  conclusion = btor_eq_exp (btor, a, b);

  lemma_size += 1; /* a == b */
  lemma_size += bconds_sel1->count;
  lemma_size += bconds_sel2->count;

  /* premisses bv conditions:
   *   true conditions: c_0, ..., c_k
   *   encode premisses: \forall i <= k. /\ c_i */
  btor_init_node_hash_table_iterator (&it, bconds_sel1);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cond = btor_next_node_hash_table_iterator (&it);
    BTORLOG (1, "  p %s", node2string (cond));
    assert (btor_get_exp_width (btor, cond) == 1);
    assert (!BTOR_REAL_ADDR_NODE (cond)->parameterized);
    if (premise)
    {
      and = btor_and_exp (btor, premise, cond);
      btor_release_exp (btor, premise);
      premise = and;
    }
    else
      premise = btor_copy_exp (btor, cond);
    btor_release_exp (btor, cond);
  }

  /* premisses bv conditions:
   *   false conditions: c_0, ..., c_l
   *   encode premisses: \forall i <= l. /\ \not c_i */
  btor_init_node_hash_table_iterator (&it, bconds_sel2);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cond = btor_next_node_hash_table_iterator (&it);
    BTORLOG (2, "  p %s", node2string (BTOR_INVERT_NODE (cond)));
    assert (btor_get_exp_width (btor, cond) == 1);
    assert (!BTOR_REAL_ADDR_NODE (cond)->parameterized);
    if (premise)
    {
      and = btor_and_exp (btor, premise, BTOR_INVERT_NODE (cond));
      btor_release_exp (btor, premise);
      premise = and;
    }
    else
      premise = btor_copy_exp (btor, BTOR_INVERT_NODE (cond));
    btor_release_exp (btor, cond);
  }
  BTORLOG (2, "  c %s = %s", node2string (a), node2string (b));

  assert (conclusion);
  if (premise)
  {
    lemma = btor_implies_exp (btor, premise, conclusion);
    btor_release_exp (btor, premise);
  }
  else
    lemma = btor_copy_exp (btor, conclusion);

  /* delaying lemmas may in some cases produce the same lemmas with different *
   * conflicts */
  if (!btor_get_ptr_hash_table (slv->lemmas, lemma))
  {
    BTORLOG (2, "  lemma: %s", node2string (lemma));
    btor_add_ptr_hash_table (slv->lemmas, btor_copy_exp (btor, lemma));
    BTOR_PUSH_STACK (btor->mm, slv->cur_lemmas, lemma);
    slv->stats.lod_refinements++;
    slv->stats.lemmas_size_sum += lemma_size;
    if (lemma_size >= BTOR_SIZE_STACK (slv->stats.lemmas_size))
      BTOR_FIT_STACK (btor->mm, slv->stats.lemmas_size, lemma_size);
    slv->stats.lemmas_size.start[lemma_size] += 1;
  }
  btor_release_exp (btor, lemma);
  btor_release_exp (btor, conclusion);
}

static void
add_lemma (Btor *btor, BtorNode *fun, BtorNode *app0, BtorNode *app1)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (fun);
  assert (app0);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (!fun->parameterized);
  assert (BTOR_IS_REGULAR_NODE (app0));
  assert (BTOR_IS_APPLY_NODE (app0));
  assert (!app1 || BTOR_IS_REGULAR_NODE (app1));
  assert (!app1 || BTOR_IS_APPLY_NODE (app1));

  double start;
  BtorPtrHashTable *cond_sel_if, *cond_sel_else;
  BtorNode *args, *value, *exp;
  BtorMemMgr *mm;

  mm    = btor->mm;
  start = btor_time_stamp ();

  /* collect intermediate conditions of bit vector conditionals */
  cond_sel_if   = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  cond_sel_else = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  /* function congruence axiom conflict */
  if (app1)
  {
    for (exp = app0; exp; exp = exp == app0 ? app1 : 0)
    {
      assert (exp);
      assert (BTOR_IS_APPLY_NODE (exp));
      args = exp->e[1];
      /* path from exp to conflicting fun */
      collect_premisses (btor, exp, fun, args, cond_sel_if, cond_sel_else);
    }
    add_symbolic_lemma (
        btor, cond_sel_if, cond_sel_else, app0, app1, app0->e[1], app1->e[1]);
  }
  /* beta reduction conflict */
  else
  {
    args = app0->e[1];
    btor_assign_args (btor, fun, args);
    value = btor_beta_reduce_partial (btor, fun, 0);
    btor_unassign_params (btor, fun);
    assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (value)));

    /* path from app0 to conflicting fun */
    collect_premisses (btor, app0, fun, args, cond_sel_if, cond_sel_else);

    /* path from conflicting fun to value */
    collect_premisses (btor,
                       fun,
                       BTOR_REAL_ADDR_NODE (value),
                       args,
                       cond_sel_if,
                       cond_sel_else);

    add_symbolic_lemma (
        btor, cond_sel_if, cond_sel_else, app0, value, app0->e[1], 0);
    btor_release_exp (btor, value);
  }

  btor_delete_ptr_hash_table (cond_sel_if);
  btor_delete_ptr_hash_table (cond_sel_else);
  BTOR_CORE_SOLVER (btor)->time.lemma_gen += btor_time_stamp () - start;
}

static void
push_applies_for_propagation (Btor *btor,
                              BtorNode *exp,
                              BtorNodePtrStack *prop_stack,
                              BtorIntHashTable *apply_search_cache)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp);
  assert (prop_stack);

  int i;
  double start;
  BtorCoreSolver *slv;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;

  start = btor_time_stamp ();
  slv   = BTOR_CORE_SOLVER (btor);
  mm    = btor->mm;

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, exp);
  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));
    assert (!cur->parameterized);
    assert (!BTOR_IS_FUN_NODE (cur));

    if (!cur->apply_below
        || btor_contains_int_hash_table (apply_search_cache, cur->id)
        || BTOR_IS_FEQ_NODE (cur))
      continue;

    btor_add_int_hash_table (apply_search_cache, cur->id);

    if (BTOR_IS_APPLY_NODE (cur))
    {
      BTOR_PUSH_STACK (mm, *prop_stack, cur);
      BTOR_PUSH_STACK (mm, *prop_stack, cur->e[0]);
      continue;
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  } while (!BTOR_EMPTY_STACK (visit));
  BTOR_RELEASE_STACK (mm, visit);
  slv->time.find_prop_app += btor_time_stamp () - start;
}

static void
propagate (Btor *btor,
           BtorNodePtrStack *prop_stack,
           BtorPtrHashTable *cleanup_table,
           BtorIntHashTable *apply_search_cache)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (prop_stack);
  assert (cleanup_table);
  assert (apply_search_cache);

  bool prop_down, conflict;
  BtorBitVector *bv;
  BtorMemMgr *mm;
  BtorCoreSolver *slv;
  BtorNode *fun, *app, *args, *fun_value, *cur;
  BtorNode *hashed_app;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorPtrHashTable *conds;

  mm  = btor->mm;
  slv = BTOR_CORE_SOLVER (btor);

  BTORLOG (1, "");
  BTORLOG (1, "*** %s", __FUNCTION__);
  while (!BTOR_EMPTY_STACK (*prop_stack))
  {
    fun = BTOR_POP_STACK (*prop_stack);
    assert (BTOR_IS_REGULAR_NODE (fun));
    assert (BTOR_IS_FUN_NODE (fun));
    assert (!fun->simplified);
    assert (!BTOR_EMPTY_STACK (*prop_stack));
    app = BTOR_POP_STACK (*prop_stack);
    assert (BTOR_IS_REGULAR_NODE (app));
    assert (BTOR_IS_APPLY_NODE (app));
    assert (app->refs - app->ext_refs > 0);

    conflict = false;

    if (app->propagated) continue;

    app->propagated = 1;
    if (!btor_get_ptr_hash_table (cleanup_table, app))
      btor_add_ptr_hash_table (cleanup_table, app);
    slv->stats.propagations++;

    BTORLOG (1, "propagate");
    BTORLOG (1, "  app: %s", node2string (app));
    BTORLOG (1, "  fun: %s", node2string (fun));

    args = app->e[1];
    assert (BTOR_IS_REGULAR_NODE (args));
    assert (BTOR_IS_ARGS_NODE (args));

    push_applies_for_propagation (btor, args, prop_stack, apply_search_cache);

    if (!fun->rho)
    {
      fun->rho =
          btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) hash_args_assignment,
                                   (BtorCmpPtr) compare_args_assignments);
      if (!btor_get_ptr_hash_table (cleanup_table, fun))
        btor_add_ptr_hash_table (cleanup_table, fun);
    }
    else
    {
      b = btor_get_ptr_hash_table (fun->rho, args);
      if (b)
      {
        hashed_app = (BtorNode *) b->data.as_ptr;
        assert (BTOR_IS_REGULAR_NODE (hashed_app));
        assert (BTOR_IS_APPLY_NODE (hashed_app));

        /* function congruence conflict */
        if (!equal_bv_assignments (hashed_app, app))
        {
          BTORLOG (1, "\e[1;31m");
          BTORLOG (1, "FC conflict at: %s", node2string (fun));
          BTORLOG (1, "add_lemma:");
          BTORLOG (1, "  fun: %s", node2string (fun));
          BTORLOG (1, "  app1: %s", node2string (hashed_app));
          BTORLOG (1, "  app2: %s", node2string (app));
          BTORLOG (1, "\e[0;39m");
          slv->stats.function_congruence_conflicts++;
          add_lemma (btor, fun, hashed_app, app);
          conflict = true;
          /* stop at first conflict */
          if (!btor->options.eager_lemmas.val) break;
        }
        continue;
      }
    }
    assert (fun->rho);
    assert (!btor_get_ptr_hash_table (fun->rho, args));
    btor_add_ptr_hash_table (fun->rho, args)->data.as_ptr = app;
    BTORLOG (1, "  save app: %s (%s)", node2string (args), node2string (app));

    /* skip array vars/uf */
    if (BTOR_IS_UF_NODE (fun)) continue;

    if (BTOR_IS_FUN_COND_NODE (fun))
    {
      push_applies_for_propagation (
          btor, fun->e[0], prop_stack, apply_search_cache);
      bv = get_bv_assignment (btor, fun->e[0]);

      /* propagate over function ite */
      BTORLOG (1, "  propagate down: %s", node2string (app));
      app->propagated = 0;
      BTOR_PUSH_STACK (mm, *prop_stack, app);
      if (btor_is_true_bv (bv))
        BTOR_PUSH_STACK (mm, *prop_stack, fun->e[1]);
      else
        BTOR_PUSH_STACK (mm, *prop_stack, fun->e[2]);
      btor_free_bv (mm, bv);
      continue;
    }

    assert (BTOR_IS_LAMBDA_NODE (fun));
    conds = btor_new_ptr_hash_table (mm,
                                     (BtorHashPtr) btor_hash_exp_by_id,
                                     (BtorCmpPtr) btor_compare_exp_by_id);
    btor_assign_args (btor, fun, args);
    fun_value = btor_beta_reduce_partial (btor, fun, conds);
    assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (fun_value)));
    btor_unassign_params (btor, fun);

    prop_down = false;
    // TODO: how can we still propagate negated applies down?
    if (!BTOR_IS_INVERTED_NODE (fun_value) && BTOR_IS_APPLY_NODE (fun_value))
      prop_down = fun_value->e[1] == args;

    if (prop_down)
    {
      assert (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (fun_value)));
      BTOR_PUSH_STACK (mm, *prop_stack, app);
      BTOR_PUSH_STACK (mm, *prop_stack, BTOR_REAL_ADDR_NODE (fun_value)->e[0]);
      slv->stats.propagations_down++;
      app->propagated = 0;
      BTORLOG (1, "  propagate down: %s", node2string (app));
    }
    else if (!equal_bv_assignments (app, fun_value))
    {
      BTORLOG (1, "\e[1;31m");
      BTORLOG (1, "BR conflict at: %s", node2string (fun));
      BTORLOG (1, "add_lemma:");
      BTORLOG (1, "  fun: %s", node2string (fun));
      BTORLOG (1, "  app: %s", node2string (app));
      BTORLOG (1, "\e[0;39m");
      slv->stats.beta_reduction_conflicts++;
      add_lemma (btor, fun, app, 0);
      conflict = true;
    }

    /* we have a conflict and the values are inconsistent, we do not have
     * to push applies onto 'prop_stack' that produce this inconsistent
     * value */
    if (conflict)
    {
      btor_init_node_hash_table_iterator (&it, conds);
      while (btor_has_next_node_hash_table_iterator (&it))
        btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
    }
    /* push applies onto 'prop_stack' that are necesary to derive 'fun_value'
     */
    else
    {
      /* in case of down propagation 'fun_value' is a function application
       * and we can propagate 'app' instead. hence, we to not have to
       * push 'fun_value' onto 'prop_stack'. */
      if (!prop_down)
        push_applies_for_propagation (
            btor, fun_value, prop_stack, apply_search_cache);

      /* push applies in evaluated conditions */
      btor_init_node_hash_table_iterator (&it, conds);
      while (btor_has_next_node_hash_table_iterator (&it))
      {
        cur = btor_next_node_hash_table_iterator (&it);
        push_applies_for_propagation (
            btor, cur, prop_stack, apply_search_cache);
        btor_release_exp (btor, cur);
      }
    }
    btor_delete_ptr_hash_table (conds);
    btor_release_exp (btor, fun_value);

    /* stop at first conflict */
    if (!btor->options.eager_lemmas.val && conflict) break;
  }
}

/* generate hash table for function 'fun' consisting of all rho and static_rho
 * hash tables. */
static BtorPtrHashTable *
generate_table (Btor *btor, BtorNode *fun)
{
  int i;
  BtorMemMgr *mm;
  BtorNode *cur, *value, *args;
  BtorPtrHashTable *table, *rho, *static_rho;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableIterator it;
  BtorBitVector *evalbv;

  mm    = btor->mm;
  table = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) hash_args_assignment,
                                   (BtorCmpPtr) compare_args_assignments);
  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, fun);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)
        || (!BTOR_IS_FUN_NODE (cur) && !cur->parameterized))
      continue;

    btor_add_int_hash_table (cache, cur->id);

    if (BTOR_IS_FUN_NODE (cur))
    {
      assert (cur->is_array);
      rho        = cur->rho;
      static_rho = 0;

      if (BTOR_IS_LAMBDA_NODE (cur))
      {
        static_rho = btor_lambda_get_static_rho (cur);
        assert (static_rho);
      }
      else if (BTOR_IS_FUN_COND_NODE (cur))
      {
        evalbv = get_bv_assignment (btor, cur->e[0]);
        if (btor_is_true_bv (evalbv))
          BTOR_PUSH_STACK (mm, visit, cur->e[1]);
        else
          BTOR_PUSH_STACK (mm, visit, cur->e[2]);
        btor_free_bv (mm, evalbv);
      }

      if (rho)
      {
        btor_init_node_hash_table_iterator (&it, rho);
        if (static_rho) btor_queue_node_hash_table_iterator (&it, static_rho);
      }
      else if (static_rho)
        btor_init_node_hash_table_iterator (&it, static_rho);

      if (rho || static_rho)
      {
        while (btor_has_next_node_hash_table_iterator (&it))
        {
          value = it.bucket->data.as_ptr;
          assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (value)));
          args = btor_next_node_hash_table_iterator (&it);
          assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (args)));

          if (!btor_get_ptr_hash_table (table, args))
            btor_add_ptr_hash_table (table, args)->data.as_ptr = value;
        }
      }

      if (BTOR_IS_FUN_COND_NODE (cur)) continue;
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (cache);

  return table;
}

static void
add_extensionality_lemmas (Btor *btor)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  bool skip;
  BtorBitVector *evalbv;
  unsigned num_lemmas = 0;
  BtorNode *cur, *cur_args, *app0, *app1, *eq, *con, *value;
  BtorHashTableIterator it;
  BtorPtrHashTable *table0, *table1, *conflicts;
  BtorHashTableIterator hit;
  BtorNodePtrStack feqs;
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  BtorCoreSolver *slv;

  BTORLOG (1, "");
  BTORLOG (1, "*** %s", __FUNCTION__);

  slv = BTOR_CORE_SOLVER (btor);
  mm  = btor->mm;
  BTOR_INIT_STACK (feqs);

  /* collect all reachable function equalities */
  btor_init_node_hash_table_iterator (&it, btor->feqs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_FEQ_NODE (cur));
    BTOR_PUSH_STACK (btor->mm, feqs, cur);
  }

  while (!BTOR_EMPTY_STACK (feqs))
  {
    cur = BTOR_POP_STACK (feqs);
    assert (BTOR_IS_FEQ_NODE (cur));
    assert (cur->e[0]->is_array);
    assert (cur->e[1]->is_array);

    evalbv = get_bv_assignment (btor, cur);
    assert (evalbv);
    skip = btor_is_false_bv (evalbv);
    btor_free_bv (btor->mm, evalbv);

    if (skip) continue;

    table0 = generate_table (btor, cur->e[0]);
    table1 = generate_table (btor, cur->e[1]);

    conflicts = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) hash_args_assignment,
                                         (BtorCmpPtr) compare_args_assignments);

    btor_init_node_hash_table_iterator (&hit, table0);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      value    = hit.bucket->data.as_ptr;
      cur_args = btor_next_node_hash_table_iterator (&hit);
      b        = btor_get_ptr_hash_table (table1, cur_args);

      if (btor_get_ptr_hash_table (conflicts, cur_args)) continue;

      if (!b || !equal_bv_assignments (value, b->data.as_ptr))
        btor_add_ptr_hash_table (conflicts, cur_args);
    }

    btor_init_node_hash_table_iterator (&hit, table1);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      value    = hit.bucket->data.as_ptr;
      cur_args = btor_next_node_hash_table_iterator (&hit);
      b        = btor_get_ptr_hash_table (table0, cur_args);

      if (btor_get_ptr_hash_table (conflicts, cur_args)) continue;

      if (!b || !equal_bv_assignments (value, b->data.as_ptr))
        btor_add_ptr_hash_table (conflicts, cur_args);
    }

    BTORLOG (1, "  %s", node2string (cur));
    btor_init_node_hash_table_iterator (&hit, conflicts);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      cur_args = btor_next_node_hash_table_iterator (&hit);
      app0     = btor_apply_exp (btor, cur->e[0], cur_args);
      app1     = btor_apply_exp (btor, cur->e[1], cur_args);
      eq       = btor_eq_exp (btor, app0, app1);
      con      = btor_implies_exp (btor, cur, eq);

      /* add instantiation of extensionality lemma */
      if (!btor_get_ptr_hash_table (slv->lemmas, con))
      {
        btor_add_ptr_hash_table (slv->lemmas, btor_copy_exp (btor, con));
        BTOR_PUSH_STACK (btor->mm, slv->cur_lemmas, con);
        slv->stats.extensionality_lemmas++;
        slv->stats.lod_refinements++;
        num_lemmas++;
        BTORLOG (1, "    %s, %s", node2string (app0), node2string (app1));
      }
      btor_release_exp (btor, app0);
      btor_release_exp (btor, app1);
      btor_release_exp (btor, eq);
      btor_release_exp (btor, con);
    }
    btor_delete_ptr_hash_table (conflicts);
    btor_delete_ptr_hash_table (table0);
    btor_delete_ptr_hash_table (table1);
  }
  BTOR_RELEASE_STACK (btor->mm, feqs);

  BTORLOG (1, "  added %u extensionality lemmas", num_lemmas);
}

static void
check_and_resolve_conflicts (Btor *btor,
                             Btor *clone,
                             BtorNode *clone_root,
                             BtorNodeMap *exp_map)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);

  bool found_conflicts;
  BtorMemMgr *mm;
  BtorCoreSolver *slv;
  BtorNode *app, *cur;
  BtorNodePtrStack prop_stack;
  BtorNodePtrStack top_applies;
  BtorPtrHashTable *cleanup_table;
  BtorIntHashTable *apply_search_cache;
  BtorHashTableIterator it;

  slv                = BTOR_CORE_SOLVER (btor);
  apply_search_cache = 0;
  found_conflicts    = false;
  mm                 = btor->mm;
  slv                = BTOR_CORE_SOLVER (btor);

  /* initialize new bit vector model, which will be constructed while
   * consistency checking. this also deletes the model from the previous run */
  btor_init_bv_model (btor, &btor->bv_model);

  assert (!found_conflicts);
  cleanup_table = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (prop_stack);
  BTOR_INIT_STACK (top_applies);

  /* cache applies that were visited while searching for applies to propagate.
   * applies added to this cache will be skipped in the apply search the next
   * time they are visited.
   * Note: the id of the resp. apply will be added to 'apply_search_cache',
   *       hence, we don't have to ensure that these applies still exist in
   *       memory.
   */
  if (!apply_search_cache) apply_search_cache = btor_new_int_hash_table (mm);

  /* NOTE: terms in var_rhs are always part of the formula (due to the implicit
   * top level equality). if terms containing applies do not occur in the
   * formula anymore due to variable substitution, we still need to ensure that
   * the assignment computed for the substituted variable is correct. hence, we
   * need to check the applies for consistency and push them onto the
   * propagation stack.
   * this also applies for don't care reasoning.
   */
  btor_init_node_hash_table_iterator (&it, btor->var_rhs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_simplify_exp (btor, btor_next_node_hash_table_iterator (&it));
    /* no parents -> is not reachable from the roots */
    if (BTOR_REAL_ADDR_NODE (cur)->parents > 0) continue;
    push_applies_for_propagation (btor, cur, &prop_stack, apply_search_cache);
  }

  if (clone)
    search_initial_applies_dual_prop (
        btor, clone, clone_root, exp_map, &top_applies);
  else if (btor->options.just.val)
    search_initial_applies_just (btor, &top_applies);
  else
    search_initial_applies_bv_skeleton (btor, &top_applies);

  while (!BTOR_EMPTY_STACK (top_applies))
  {
    app = BTOR_POP_STACK (top_applies);
    assert (BTOR_IS_REGULAR_NODE (app));
    assert (BTOR_IS_APPLY_NODE (app));
    assert (!app->parameterized);
    assert (!app->propagated);
    BTOR_PUSH_STACK (mm, prop_stack, app);
    BTOR_PUSH_STACK (mm, prop_stack, app->e[0]);
  }

  propagate (btor, &prop_stack, cleanup_table, apply_search_cache);
  found_conflicts = BTOR_COUNT_STACK (slv->cur_lemmas) > 0;

  if (!found_conflicts && btor->feqs->count > 0)
  {
    assert (BTOR_EMPTY_STACK (prop_stack));
    add_extensionality_lemmas (btor);
    found_conflicts = BTOR_COUNT_STACK (slv->cur_lemmas) > 0;
  }

  /* applies may have assignments that were not checked for consistency, which
   * is the case when they are not required for deriving SAT (don't care
   * reasoning). hence, we remove those applies from the 'bv_model' as they do
   * not have a valid assignment. an assignment will be generated during
   * model construction */
  if (!found_conflicts)
  {
    btor_init_node_hash_table_iterator (&it, btor->bv_model);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      if (BTOR_IS_APPLY_NODE (cur) && !cur->propagated)
        btor_remove_from_bv_model (btor, btor->bv_model, cur);
    }
  }

  btor_init_node_hash_table_iterator (&it, cleanup_table);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (BTOR_IS_APPLY_NODE (cur))
    {
      /* generate model for apply */
      if (!found_conflicts)
        btor_free_bv (btor->mm, get_bv_assignment (btor, cur));
      cur->propagated = 0;
    }
    else
    {
      assert (BTOR_IS_FUN_NODE (cur));
      assert (cur->rho);

      if (found_conflicts)
      {
        btor_delete_ptr_hash_table (cur->rho);
        cur->rho = 0;
      }
      else
      {
        /* remember functions for incremental usage (and prevent
         * premature release in case that function is released via API
         * call) */
        BTOR_PUSH_STACK (
            mm, btor->functions_with_model, btor_copy_exp (btor, cur));
      }
    }
  }
  btor_delete_ptr_hash_table (cleanup_table);
  BTOR_RELEASE_STACK (mm, prop_stack);
  BTOR_RELEASE_STACK (mm, top_applies);

  btor_delete_int_hash_table (apply_search_cache);
  apply_search_cache = 0;
}

static BtorSolverResult
sat_core_solver (BtorCoreSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  double start;
  int i;
  BtorSolverResult result;
  Btor *btor, *clone;
  BtorNode *clone_root, *lemma;
  BtorNodeMap *exp_map;

  start = btor_time_stamp ();
  btor  = slv->btor;

  clone      = 0;
  clone_root = 0;
  exp_map    = 0;

  BTOR_MSG (btor->msg, 1, "calling SAT");

  result = btor_simplify (btor);

  if (result == BTOR_RESULT_UNSAT)
  {
    assert (btor->inconsistent);
    goto DONE;
  }

  if (btor_terminate_btor (btor))
  {
  UNKNOWN:
    result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  configure_sat_mgr (btor);

  if (btor->valid_assignments == 1) btor_reset_incremental_usage (btor);

  if (btor->feqs->count > 0) add_function_inequality_constraints (btor);

  /* initialize dual prop clone */
  if (btor->options.dual_prop.val)
    clone = new_exp_layer_clone_for_dual_prop (btor, &exp_map, &clone_root);

  while (true)
  {
    if (btor_terminate_btor (btor)
        || (slv->lod_limit > -1
            && slv->stats.lod_refinements >= slv->lod_limit))
    {
      goto UNKNOWN;
    }

    btor_process_unsynthesized_constraints (btor);
    if (btor->found_constraint_false)
    {
    UNSAT:
      result = BTOR_RESULT_UNSAT;
      goto DONE;
    }
    assert (btor->unsynthesized_constraints->count == 0);
    assert (btor_check_all_hash_tables_proxy_free_dbg (btor));
    assert (btor_check_all_hash_tables_simp_free_dbg (btor));

    /* make SAT call on bv skeleton */
    btor_add_again_assumptions (btor);
    result = timed_sat_sat (btor, slv->sat_limit);

    if (result == BTOR_RESULT_UNSAT)
      goto DONE;
    else if (result == BTOR_RESULT_UNKNOWN)
    {
      assert (slv->sat_limit > -1);
      goto DONE;
    }

    assert (result == BTOR_RESULT_SAT);

    check_and_resolve_conflicts (btor, clone, clone_root, exp_map);
    if (BTOR_EMPTY_STACK (slv->cur_lemmas)) break;
    slv->stats.refinement_iterations++;

    BTORLOG (1, "add %d lemma(s)", BTOR_COUNT_STACK (slv->cur_lemmas));
    /* add generated lemmas to formula */
    for (i = 0; i < BTOR_COUNT_STACK (slv->cur_lemmas); i++)
    {
      lemma = BTOR_PEEK_STACK (slv->cur_lemmas, i);
      assert (!BTOR_REAL_ADDR_NODE (lemma)->simplified);
      // TODO (ma): use btor_assert_exp?
      if (slv->assume_lemmas)
        btor_assume_exp (btor, lemma);
      else
        btor_insert_unsynthesized_constraint (btor, lemma);
      if (clone)
        add_lemma_to_dual_prop_clone (btor, clone, &clone_root, lemma, exp_map);
    }
    BTOR_RESET_STACK (slv->cur_lemmas);

    if (btor->options.verbosity.val)
    {
      fprintf (stdout,
               "\r[btorcore] %d iterations, %d lemmas, %d ext. lemmas, "
               "vars %d, applies %d\r",
               slv->stats.refinement_iterations,
               slv->stats.lod_refinements,
               slv->stats.extensionality_lemmas,
               btor->ops[BTOR_BV_VAR_NODE].cur,
               btor->ops[BTOR_APPLY_NODE].cur);
      fflush (stdout);
    }

    /* may be set via insert_unsythesized_constraint
     * in case generated lemma is false */
    if (btor->inconsistent) goto UNSAT;
  }

DONE:
  if (btor->options.verbosity.val && slv->stats.lod_refinements > 0)
    fprintf (stdout, "\n");

  btor->valid_assignments = 1;
  btor->last_sat_result   = result;

  if (clone)
  {
    assert (exp_map);
    btor_delete_node_map (exp_map);
    btor_release_exp (clone, clone_root);
    btor_delete_btor (clone);
  }
  BTOR_MSG (btor->msg,
            1,
            "SAT call %d returned %d in %.3f seconds",
            btor->btor_sat_btor_called + 1,
            result,
            btor_time_stamp () - start);
  return result;
}

/*------------------------------------------------------------------------*/

static void
generate_model_core_solver (BtorCoreSolver *slv,
                            bool model_for_all_nodes,
                            bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  (void) reset;
  if (!slv->btor->bv_model)
    btor_init_bv_model (slv->btor, &slv->btor->bv_model);
  btor_init_fun_model (slv->btor, &slv->btor->fun_model);

  btor_generate_model (slv->btor,
                       slv->btor->bv_model,
                       slv->btor->fun_model,
                       model_for_all_nodes);
}

static void
print_stats_core_solver (BtorCoreSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  int i;
  Btor *btor;

  btor = slv->btor;

  if (!(slv = BTOR_CORE_SOLVER (btor))) return;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "lemmas on demand statistics:");
  BTOR_MSG (btor->msg,
            1,
            " refinement iterations: %d",
            slv->stats.refinement_iterations);
  BTOR_MSG (btor->msg, 1, " LOD refinements: %d", slv->stats.lod_refinements);
  if (slv->stats.lod_refinements)
  {
    BTOR_MSG (btor->msg,
              1,
              " function congruence conflicts: %d",
              slv->stats.function_congruence_conflicts);
    BTOR_MSG (btor->msg,
              1,
              " beta reduction conflicts: %d",
              slv->stats.beta_reduction_conflicts);
    BTOR_MSG (btor->msg,
              1,
              " extensionality lemmas: %d",
              slv->stats.extensionality_lemmas);
    BTOR_MSG (btor->msg,
              1,
              " average lemma size: %.1f",
              BTOR_AVERAGE_UTIL (slv->stats.lemmas_size_sum,
                                 slv->stats.lod_refinements));
    for (i = 1; i < BTOR_SIZE_STACK (slv->stats.lemmas_size); i++)
    {
      if (!slv->stats.lemmas_size.start[i]) continue;
      BTOR_MSG (btor->msg,
                1,
                "   lemmas of size %d: %d",
                i,
                slv->stats.lemmas_size.start[i]);
    }
  }

  BTOR_MSG (
      btor->msg, 1, "expression evaluations: %lld", slv->stats.eval_exp_calls);
  BTOR_MSG (btor->msg, 1, "propagations: %lld", slv->stats.propagations);
  BTOR_MSG (
      btor->msg, 1, "propagations down: %lld", slv->stats.propagations_down);
  BTOR_MSG (btor->msg,
            1,
            "partial beta reduction restarts: %lld",
            slv->stats.partial_beta_reduction_restarts);

  if (btor->options.dual_prop.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "dual prop. vars (failed/assumed): %d/%d",
              slv->stats.dp_failed_vars,
              slv->stats.dp_assumed_vars);
    BTOR_MSG (btor->msg,
              1,
              "dual prop. applies (failed/assumed): %d/%d",
              slv->stats.dp_failed_applies,
              slv->stats.dp_assumed_applies);
  }
}

static void
print_time_stats_core_solver (BtorCoreSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;

  btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "%.2f seconds expression evaluation", slv->time.eval);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds initial applies search",
            slv->time.search_init_apps);

  if (btor->options.just.val || btor->options.dual_prop.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds compute scores for initial applies search",
              slv->time.search_init_apps_compute_scores);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds merge applies in compute scores for init apps search",
        slv->time.search_init_apps_compute_scores_merge_applies);
  }

  if (btor->options.dual_prop.val)
  {
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds cloning for initial applies search",
              slv->time.search_init_apps_cloning);
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds SAT solving for initial applies search",
              slv->time.search_init_apps_sat);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds collecting bv vars and apps for initial applies search",
        slv->time.search_init_apps_collect_var_apps);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds collecting initial applies via failed assumptions (FA)",
        slv->time.search_init_apps_collect_fa);
    BTOR_MSG (
        btor->msg,
        1,
        "%.2f seconds cone traversal when collecting initial applies via FA",
        slv->time.search_init_apps_collect_fa_cone);
  }

  BTOR_MSG (btor->msg, 1, "%.2f seconds lemma generation", slv->time.lemma_gen);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds not encoded apply search",
            slv->time.find_nenc_app);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds propagation apply search",
            slv->time.find_prop_app);

  if (btor->options.dual_prop.val)
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds propagation apply in conds search",
              slv->time.find_cond_prop_app);

  BTOR_MSG (btor->msg, 1, "%.2f seconds in pure SAT solving", slv->time.sat);
  BTOR_MSG (btor->msg, 1, "");
}

BtorSolver *
btor_new_core_solver (Btor *btor)
{
  assert (btor);

  BtorCoreSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind      = BTOR_CORE_SOLVER_KIND;
  slv->btor      = btor;
  slv->api.clone = (BtorSolverClone) clone_core_solver;
  slv->api.delet = (BtorSolverDelete) delete_core_solver;
  slv->api.sat   = (BtorSolverSat) sat_core_solver;
  slv->api.generate_model =
      (BtorSolverGenerateModel) generate_model_core_solver;
  slv->api.print_stats = (BtorSolverPrintStats) print_stats_core_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_core_solver;

  slv->lod_limit = -1;
  slv->sat_limit = -1;

  slv->lemmas = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (slv->cur_lemmas);

  BTOR_INIT_STACK (slv->stats.lemmas_size);

  BTOR_MSG (btor->msg, 1, "enabled core engine");

  return (BtorSolver *) slv;
}

// TODO (ma): this is just a fix for now, this should be moved elsewhere
BtorBitVector *
btor_eval_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (btor->slv);
  assert (btor->slv->kind == BTOR_CORE_SOLVER_KIND);
  assert (exp);
  assert (btor->bv_model);

  int i;
  double start;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next;
  BtorPtrHashTable *cache;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorBitVector *result = 0, *inv_result, **e;
  BtorCoreSolver *slv;

  start = btor_time_stamp ();
  mm    = btor->mm;
  slv   = BTOR_CORE_SOLVER (btor);
  slv->stats.eval_exp_calls++;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  cache = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_PUSH_STACK (mm, work_stack, exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->eval_mark);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur      = BTOR_POP_STACK (work_stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!real_cur->simplified);

    if (real_cur->eval_mark == 0)
    {
      if (BTOR_IS_BV_VAR_NODE (real_cur) || BTOR_IS_APPLY_NODE (real_cur)
          || BTOR_IS_FEQ_NODE (real_cur) || has_bv_assignment (btor, real_cur))
      {
        result = get_bv_assignment (btor, real_cur);
        goto EVAL_EXP_PUSH_RESULT;
      }
      else if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_copy_bv (btor->mm, btor_const_get_bits (real_cur));
        goto EVAL_EXP_PUSH_RESULT;
      }
      /* substitute param with its assignment */
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        next = btor_param_get_assigned_exp (real_cur);
        assert (next);
        if (BTOR_IS_INVERTED_NODE (cur)) next = BTOR_INVERT_NODE (next);
        BTOR_PUSH_STACK (mm, work_stack, next);
        continue;
      }

      BTOR_PUSH_STACK (mm, work_stack, cur);
      real_cur->eval_mark = 1;

      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, work_stack, real_cur->e[i]);
    }
    else if (real_cur->eval_mark == 1)
    {
      assert (!BTOR_IS_PARAM_NODE (real_cur));
      assert (!BTOR_IS_ARGS_NODE (real_cur));
      assert (!BTOR_IS_FUN_NODE (real_cur));
      assert (real_cur->arity >= 1);
      assert (real_cur->arity <= 3);
      assert (real_cur->arity <= BTOR_COUNT_STACK (arg_stack));

      real_cur->eval_mark = 2;
      arg_stack.top -= real_cur->arity;
      e = (BtorBitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  e[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          btor_free_bv (mm, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_BEQ_NODE:
          result = btor_eq_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_BCOND_NODE:
          if (btor_is_true_bv (e[2]))
            result = btor_copy_bv (mm, e[1]);
          else
            result = btor_copy_bv (mm, e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          btor_free_bv (mm, e[2]);
          break;
        default:
          BTORLOG (1, "  *** %s", node2string (real_cur));
          /* should be unreachable */
          assert (0);
      }

      assert (!btor_get_ptr_hash_table (cache, real_cur));
      btor_add_ptr_hash_table (cache, real_cur)->data.as_ptr =
          btor_copy_bv (mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (mm, result);
        btor_free_bv (mm, result);
        result = inv_result;
      }

      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (real_cur->eval_mark == 2);
      b = btor_get_ptr_hash_table (cache, real_cur);
      assert (b);
      result = btor_copy_bv (mm, (BtorBitVector *) b->data.as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur            = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));
    cur->eval_mark = 0;
  }

  while (!BTOR_EMPTY_STACK (arg_stack))
  {
    inv_result = BTOR_POP_STACK (arg_stack);
    btor_free_bv (mm, inv_result);
  }

  btor_init_node_hash_table_iterator (&it, cache);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    btor_free_bv (mm, (BtorBitVector *) it.bucket->data.as_ptr);
    real_cur            = btor_next_node_hash_table_iterator (&it);
    real_cur->eval_mark = 0;
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_ptr_hash_table (cache);

  //  BTORLOG ("%s: %s '%s'", __FUNCTION__, node2string (exp), result);
  slv->time.eval += btor_time_stamp () - start;

  return result;
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvef.h"
#include "btorbitvec.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btorslvcore.h"
#include "utils/btoriter.h"

/*------------------------------------------------------------------------*/

static void
setup_exists_solver (BtorEFSolver *slv)
{
  Btor *exists_solver, *forall_solver;
  BtorNode *cur, *var;
  BtorNodeMapIterator it;
  BtorNodeMap *exists_vars;

  exists_solver                          = btor_new_btor ();
  exists_solver->options.model_gen.val   = 1;
  exists_solver->options.incremental.val = 1;
  exists_vars                            = btor_new_node_map (exists_solver);
  btor_set_msg_prefix_btor (exists_solver, "exists");

  forall_solver = slv->forall_solver;
  btor_init_node_map_iterator (&it, slv->f_exists_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    cur = btor_next_node_map_iterator (&it);
    var = btor_var_exp (exists_solver,
                        btor_get_exp_width (forall_solver, cur),
                        btor_get_symbol_exp (forall_solver, cur));
    btor_map_node (exists_vars, var, cur);
  }
  exists_solver->slv = btor_new_core_solver (exists_solver);
  slv->exists_solver = exists_solver;
  slv->e_exists_vars = exists_vars;
}

static void
setup_forall_solver (BtorEFSolver *slv)
{
  Btor *forall_solver;
  BtorNode *cur, *param, *subst, *var, *root = 0, *and;
  BtorHashTableIterator it;
  BtorPtrHashTable *t;
  BtorNodeMap *map, *exists_vars, *forall_vars, *m;

  forall_solver = btor_clone_formula (slv->btor);
  btor_set_msg_prefix_btor (forall_solver, "forall");
  exists_vars = btor_new_node_map (forall_solver);
  forall_vars = btor_new_node_map (forall_solver);

  /* configure options */
  forall_solver->options.model_gen.val   = 1;
  forall_solver->options.incremental.val = 1;
  /* disable variable substitution (not sound in the context of quantifiers) */
  // TODO (ma): check if it can still be used (may be sound since we are in
  // QF_BV)
  forall_solver->options.var_subst.val = 0;

  btor_init_node_hash_table_iterator (&it, forall_solver->bv_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    btor_map_node (exists_vars,
                   btor_copy_exp (forall_solver, cur),
                   btor_copy_exp (forall_solver, cur));
    //      printf ("exists var: %s (%d)\n", node2string (cur), cur->refs);
  }

  /* instantiate exists/forall params with fresh variables */
  btor_init_substitutions (forall_solver);
  btor_init_node_hash_table_iterator (&it, forall_solver->quantifiers);
  map = btor_new_node_map (forall_solver);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_QUANTIFIER_NODE (cur));
    param = cur->e[0];
    var   = btor_var_exp (
        forall_solver, btor_get_exp_width (forall_solver, param), 0);
    btor_map_node (map, param, var);
    if (btor_param_is_exists_var (param))
      m = exists_vars;
    else
    {
      assert (btor_param_is_forall_var (param));
      m = forall_vars;
    }
    btor_map_node (m, var, btor_copy_exp (forall_solver, param));
  }

  /* eliminate quantified terms by substituting bound variables with fresh
   * variables */
  btor_init_node_hash_table_iterator (&it, forall_solver->quantifiers);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_QUANTIFIER_NODE (cur));
    subst =
        btor_substitute_terms (forall_solver, btor_binder_get_body (cur), map);
    btor_map_node (map, cur, subst);
    assert (!btor_get_ptr_hash_table (forall_solver->substitutions, cur));
    btor_insert_substitution (forall_solver, cur, subst, 0);
    btor_release_exp (forall_solver, subst);
  }
  btor_delete_node_map (map);

  btor_substitute_and_rebuild (forall_solver, forall_solver->substitutions);
  btor_delete_substitutions (forall_solver);

  assert (forall_solver->exists_vars->count == 0);
  assert (forall_solver->forall_vars->count == 0);
  assert (forall_solver->quantifiers->count == 0);
  assert (forall_solver->synthesized_constraints->count == 0);
  assert (forall_solver->varsubst_constraints->count == 0);

  /* make conjunction of constraints and add negated formula */
  btor_init_node_hash_table_iterator (&it,
                                      forall_solver->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it,
                                       forall_solver->embedded_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    t   = it.stack[it.pos];
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_get_ptr_hash_table (t, cur));
    btor_remove_ptr_hash_table (t, cur, 0, 0);
    BTOR_REAL_ADDR_NODE (cur)->constraint = 0;
    if (root)
    {
      and = btor_and_exp (forall_solver, root, cur);
      btor_release_exp (forall_solver, root);
      root = and;
    }
    else
      root = btor_copy_exp (forall_solver, cur);
    btor_release_exp (forall_solver, cur);
  }
  assert (root);
  assert (forall_solver->unsynthesized_constraints->count == 0);
  assert (forall_solver->embedded_constraints->count == 0);

  slv->f_formula = BTOR_INVERT_NODE (root);

  assert (!forall_solver->slv);
  forall_solver->slv = btor_new_core_solver (forall_solver);
  slv->forall_solver = forall_solver;
  slv->f_exists_vars = exists_vars;
  slv->f_forall_vars = forall_vars;
}

static BtorNode *
construct_generalization (BtorEFSolver *slv)
{
  Btor *forall_solver, *exists_solver;
  BtorNodeMap *map;
  BtorNodeMapIterator it;
  BtorNode *var, *var_fs, *c, *res;
  BtorNodePtrStack consts;
  const BtorBitVector *bv;
  BtorMemMgr *mm;

  mm            = slv->btor->mm;
  forall_solver = slv->forall_solver;
  exists_solver = slv->exists_solver;

  map = btor_new_node_map (forall_solver);

  BTOR_INIT_STACK (consts);
  /* map f_forall_vars to resp. assignment */
  //  printf ("found counter example\n");
  btor_init_node_map_iterator (&it, slv->f_forall_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var = btor_next_node_map_iterator (&it);
    bv  = btor_get_bv_model (forall_solver,
                            btor_simplify_exp (forall_solver, var));
    //      printf ("  %s := ", node2string (var));
    //      btor_print_bv (bv);
    c = btor_const_exp (exists_solver, (BtorBitVector *) bv);
    btor_map_node (map, var, c);
    BTOR_PUSH_STACK (mm, consts, c);
  }
  /* map f_exists_vars to e_exists_vars */
  btor_init_node_map_iterator (&it, slv->e_exists_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var    = btor_next_node_map_iterator (&it);
    btor_map_node (map, var_fs, var);
  }

  assert (forall_solver->unsynthesized_constraints->count == 0);
  assert (forall_solver->synthesized_constraints->count == 0);
  assert (forall_solver->embedded_constraints->count == 0);
  assert (forall_solver->varsubst_constraints->count == 0);
  res = btor_recursively_rebuild_exp_clone (
      forall_solver,
      exists_solver,
      slv->f_formula,
      map,
      exists_solver->options.rewrite_level.val);

  while (!BTOR_EMPTY_STACK (consts))
    btor_release_exp (exists_solver, BTOR_POP_STACK (consts));
  BTOR_RELEASE_STACK (mm, consts);

  btor_delete_node_map (map);
  return res;
}

static bool
is_ef_formula (BtorEFSolver *slv)
{
  BtorNode *cur, *param;
  BtorHashTableIterator it;
  BtorNodeIterator nit;
  bool exists_allowed;

  btor_init_node_hash_table_iterator (&it, slv->btor->quantifiers);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_QUANTIFIER_NODE (cur));

    if (cur->parameterized) continue;

    btor_init_param_iterator (&nit, cur);
    exists_allowed = true;
    while (btor_has_next_param_iterator (&nit))
    {
      param = btor_next_param_iterator (&nit);
      if (btor_param_is_exists_var (param))
      {
        if (!exists_allowed) return false;
      }
      else
      {
        assert (btor_param_is_forall_var (param));
        exists_allowed = false;
      }
    }
  }
  return true;
}

/*------------------------------------------------------------------------*/

static BtorEFSolver *
clone_ef_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  return 0;
}

static void
delete_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;
  BtorNodeMapIterator it;

  btor = slv->btor;

  if (slv->e_exists_vars)
  {
    btor_init_node_map_iterator (&it, slv->e_exists_vars);
    while (btor_has_next_node_map_iterator (&it))
    {
      btor_release_exp (slv->exists_solver, btor_next_node_map_iterator (&it));
    }
    btor_delete_node_map (slv->e_exists_vars);
  }

  if (slv->f_exists_vars)
  {
    assert (slv->f_forall_vars);
    btor_init_node_map_iterator (&it, slv->f_exists_vars);
    btor_queue_node_map_iterator (&it, slv->f_forall_vars);
    while (btor_has_next_node_map_iterator (&it))
    {
      btor_release_exp (slv->forall_solver, it.it.bucket->data.as_ptr);
      btor_release_exp (slv->forall_solver, btor_next_node_map_iterator (&it));
    }
    btor_delete_node_map (slv->f_exists_vars);
    btor_delete_node_map (slv->f_forall_vars);
  }

  btor_release_exp (slv->forall_solver, slv->f_formula);
  btor_delete_btor (slv->exists_solver);
  btor_delete_btor (slv->forall_solver);
  BTOR_DELETE (btor->mm, slv);
  btor->slv = 0;
}

static BtorSolverResult
sat_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  double start;
  Btor *exists_solver, *forall_solver;
  BtorSolverResult res;
  BtorNodeMapIterator it;
  BtorNode *var, *c, *var_fs, *g;
  BtorNodeMap *map, *e_exists_vars;
  const BtorBitVector *bv;

  if (!is_ef_formula (slv))
  {
    // TODO (ma): proper abort
    printf ("not an exists/forall formula\n");
    abort ();
  }
  else if (slv->btor->ufs->count > 0)
  {
    // TODO (ma): proper abort
    printf (
        "uninterpreted functions in exists/forall formula not yet supported\n");
    abort ();
  }

  // TODO (ma): incremental support
  setup_forall_solver (slv);
  setup_exists_solver (slv);

  exists_solver = slv->exists_solver;
  forall_solver = slv->forall_solver;
  e_exists_vars = slv->e_exists_vars;

  res = BTOR_RESULT_UNKNOWN;
  while (true)
  {
    /* first round is always sat since exists_vars are not constrained */
    if (res == BTOR_RESULT_UNKNOWN)
      res = BTOR_RESULT_SAT;
    else
    {
      start = btor_time_stamp ();
      res   = exists_solver->slv->api.sat (exists_solver->slv);
      slv->time.exists_solver += btor_time_stamp () - start;
    }

    if (res == BTOR_RESULT_UNSAT) /* formula is UNSAT */
      break;

    assert (res == BTOR_RESULT_SAT);
    exists_solver->slv->api.generate_model (exists_solver->slv, false, false);

    //      printf ("found candidate model\n");
    /* substitute exists variables with model and assume new formula to
     * forall solver */
    map = btor_new_node_map (forall_solver);
    btor_init_node_map_iterator (&it, e_exists_vars);
    while (btor_has_next_node_map_iterator (&it))
    {
      var    = btor_next_node_map_iterator (&it);
      var_fs = btor_mapped_node (e_exists_vars, var);
      bv     = btor_get_bv_model (exists_solver,
                              btor_simplify_exp (exists_solver, var));
      //	  printf ("  %s := ", node2string (var));
      //	  btor_print_bv (bv);
      //	  var_fs = btor_get_node_by_id (forall_solver, var->id);
      assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (var_fs)));
      c = btor_const_exp (forall_solver, (BtorBitVector *) bv);
      btor_map_node (map, var_fs, c);
    }

    g = btor_substitute_terms (forall_solver, slv->f_formula, map);
    btor_assume_exp (forall_solver, g);
    btor_release_exp (forall_solver, g);

    btor_init_node_map_iterator (&it, map);
    while (btor_has_next_node_map_iterator (&it))
    {
      btor_release_exp (forall_solver, it.it.bucket->data.as_ptr);
      (void) btor_next_node_map_iterator (&it);
    }
    btor_delete_node_map (map);

    //      printf ("check candidate model\n");
    start = btor_time_stamp ();
    res   = forall_solver->slv->api.sat (forall_solver->slv);
    slv->time.forall_solver += btor_time_stamp () - start;
    if (res == BTOR_RESULT_UNSAT) /* formula is SAT */
    {
      res = BTOR_RESULT_SAT;
      break;
    }

    forall_solver->slv->api.generate_model (forall_solver->slv, false, false);
    g = construct_generalization (slv);
    //      printf ("refine (%u): %s\n", slv->stats.refinements + 1, node2string
    //      (BTOR_INVERT_NODE (g))); btor_dump_btor_node (exists_solver, stdout,
    //      BTOR_INVERT_NODE (g));
    btor_assert_exp (exists_solver, BTOR_INVERT_NODE (g));
    btor_release_exp (exists_solver, g);
    slv->stats.refinements++;
  }

  slv->btor->last_sat_result = res;
  return res;
}

static void
generate_model_ef_solver (BtorEFSolver *slv,
                          bool model_for_all_nodes,
                          bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BtorNode *cur, *param, *var_fs, *param_fs;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;

  btor_init_bv_model (slv->btor, &slv->btor->bv_model);
  btor_init_fun_model (slv->btor, &slv->btor->fun_model);
  btor_init_node_map_iterator (&it, slv->e_exists_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur    = btor_next_node_map_iterator (&it);
    var_fs = btor_mapped_node (slv->e_exists_vars, cur);
    param  = btor_mapped_node (slv->f_exists_vars, var_fs);

    bv = btor_get_bv_model (slv->exists_solver,
                            btor_simplify_exp (slv->exists_solver, cur));
    assert (btor_get_node_by_id (slv->btor, param->id));
    btor_add_to_bv_model (slv->btor,
                          slv->btor->bv_model,
                          btor_get_node_by_id (slv->btor, param->id),
                          (BtorBitVector *) bv);
  }
}

static void
print_stats_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BTOR_MSG (slv->btor->msg, 1, "");
  BTOR_MSG (slv->btor->msg,
            1,
            "exists solver refinements: %u",
            slv->stats.refinements);
  //  printf ("****************\n");
  //  btor_print_stats_btor (slv->exists_solver);
  //  btor_print_stats_btor (slv->forall_solver);
}

static void
print_time_stats_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BTOR_MSG (
      slv->btor->msg, 1, "%.2f seconds exists solver", slv->time.exists_solver);
  BTOR_MSG (
      slv->btor->msg, 1, "%.2f seconds forall solver", slv->time.forall_solver);
}

BtorSolver *
btor_new_ef_solver (Btor *btor)
{
  assert (btor);
  // TODO (ma): incremental calls not supported yet
  assert (btor->options.incremental.val == 0);

  BtorEFSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind               = BTOR_EF_SOLVER_KIND;
  slv->btor               = btor;
  slv->api.clone          = (BtorSolverClone) clone_ef_solver;
  slv->api.delet          = (BtorSolverDelete) delete_ef_solver;
  slv->api.sat            = (BtorSolverSat) sat_ef_solver;
  slv->api.generate_model = (BtorSolverGenerateModel) generate_model_ef_solver;
  slv->api.print_stats    = (BtorSolverPrintStats) print_stats_ef_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_ef_solver;

  BTOR_MSG (btor->msg, 1, "enabled ef engine");

  return (BtorSolver *) slv;
}

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
#include "btorabort.h"
#include "btorbeta.h"
#include "btorbitvec.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btorslvfun.h"
#include "btorsynthfun.h"
#include "normalizer/btornormquant.h"
#include "normalizer/btorskolemize.h"
#include "simplifier/btorder.h"
#include "simplifier/btorminiscope.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

// TODO (ma): debug
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"

//#define PRINT_DBG

struct BtorEFGroundSolvers
{
  Btor *exists;
  Btor *forall;
  BtorNodeMap *exists_evars;
  BtorNodeMap *forall_evars;
  BtorNodeMap *forall_uvars;
  BtorNode *forall_formula;
  BtorPtrHashTable *forall_synth_funs;   /* synthesized functions cache */
  BtorPtrHashTable *forall_synth_inputs; /* synthesized functions input cache */
  BtorNodeMap *exists_cur_model;

  struct
  {
    double e_solver;
    double f_solver;
    double synth;
    double qinst;
  } time;
};

typedef struct BtorEFGroundSolvers BtorEFGroundSolvers;

/*------------------------------------------------------------------------*/

static void
delete_exists_model (BtorNodeMap *model)
{
  BtorNodeMapIterator it;
  BtorNode *cur;

  btor_init_node_map_iterator (&it, model);
  while (btor_has_next_node_map_iterator (&it))
  {
    cur = btor_next_data_node_map_iterator (&it)->as_ptr;
    assert (cur);
    btor_release_exp (BTOR_REAL_ADDR_NODE (cur)->btor, cur);
  }
  btor_delete_node_map (model);
}

static void
update_node_map (BtorIntHashTable *node_map, BtorIntHashTable *update)
{
  assert (node_map->data);
  assert (update->data);

  int32_t key;
  size_t i;

  for (i = 0; i < node_map->size; i++)
  {
    if (!node_map->keys[i]) continue;
    key = node_map->data[i].as_int;
    /* if key didn't get updated we don't have to update 'node_map' */
    if (!btor_contains_int_hash_map (update, key)) continue;
    node_map->data[i].as_int = btor_get_int_hash_map (update, key)->as_int;
  }
}

static BtorEFGroundSolvers *
setup_efg_solvers (BtorEFSolver *slv,
                   BtorNode *root,
                   BtorIntHashTable *node_map,
                   const char *prefix_forall,
                   const char *prefix_exists)
{
  bool opt_dual_solver;
  char *symbol;
  BtorEFGroundSolvers *res;
  BtorNode *cur, *param, *var, *tmp;
  BtorHashTableIterator it;
  BtorNodeMapIterator nit;
  BtorNodeMap *map, *evars, *uvars;
  BtorFunSolver *fslv;
  BtorNodeMap *exp_map;
  Btor *btor;
  BtorSortId sortid;
  BtorIntHashTable *tmp_map = 0;

  btor            = slv->btor;
  opt_dual_solver = btor_get_opt (btor, BTOR_OPT_EF_DUAL_SOLVER) == 1;
  BTOR_CNEW (btor->mm, res);

  /* new forall solver */
  res->forall = btor_new_btor ();
  btor_delete_opts (res->forall);
  btor_clone_opts (btor, res->forall);
  btor_set_msg_prefix_btor (res->forall, prefix_forall);

  evars   = btor_new_node_map (res->forall);
  uvars   = btor_new_node_map (res->forall);
  exp_map = btor_new_node_map (btor);
  if (opt_dual_solver) tmp_map = btor_new_int_hash_map (btor->mm);

  /* configure options */
  btor_set_opt (res->forall, BTOR_OPT_MODEL_GEN, 1);
  btor_set_opt (res->forall, BTOR_OPT_INCREMENTAL, 1);
  // FIXME (ma): if -bra is enabled then test_synth5.smt2 fails without
  // disabling this since f_formula will be simplified
  btor_set_opt (res->forall, BTOR_OPT_BETA_REDUCE_ALL, 0);

  // TODO: use build_refinement?
  tmp = btor_recursively_rebuild_exp_clone (
      btor,
      res->forall,
      root,
      exp_map,
      btor_get_opt (res->forall, BTOR_OPT_REWRITE_LEVEL));
  /* all bv vars are quantified with exists */
  assert (res->forall->bv_vars->count == 0);

  /* update 'tmp_map' for mapping nodes */
  if (opt_dual_solver)
  {
    btor_init_node_map_iterator (&nit, exp_map);
    while (btor_has_next_node_map_iterator (&nit))
    {
      tmp = nit.it.bucket->data.as_ptr;
      cur = btor_next_node_map_iterator (&nit);
      btor_add_int_hash_map (tmp_map, cur->id)->as_int =
          BTOR_REAL_ADDR_NODE (tmp)->id;
    }
  }
  btor_delete_node_map (exp_map);

  if (opt_dual_solver)
  {
    update_node_map (node_map, tmp_map);
    btor_delete_int_hash_map (tmp_map);
    tmp_map = btor_new_int_hash_map (btor->mm);
  }

  //  res->forall_formula = btor_copy_exp (res->forall, tmp);
  root = tmp;

  // FIXME: fix CER
  if (0 && btor_get_opt (res->forall, BTOR_OPT_EF_CER))
  {
    tmp = btor_cer_node (res->forall, root, node_map);
    btor_release_exp (res->forall, root);
    root = tmp;

    if (opt_dual_solver)
    {
      update_node_map (node_map, tmp_map);
      btor_delete_int_hash_map (tmp_map);
      tmp_map = btor_new_int_hash_map (btor->mm);
    }
  }

  tmp = btor_skolemize_node (res->forall, root, tmp_map);
  btor_release_exp (res->forall, root);
  root = tmp;

  if (opt_dual_solver)
  {
    update_node_map (node_map, tmp_map);
    btor_delete_int_hash_map (tmp_map);
    tmp_map = btor_new_int_hash_map (btor->mm);
  }

  // FIXME: fix DER
  if (0 && btor_get_opt (res->forall, BTOR_OPT_EF_DER))
  {
    tmp = btor_der_node (res->forall, root, tmp_map);
    btor_release_exp (res->forall, root);
    root = tmp;

    if (opt_dual_solver)
    {
      update_node_map (node_map, tmp_map);
      btor_delete_int_hash_map (tmp_map);
      tmp_map = btor_new_int_hash_map (btor->mm);
    }
  }

  /* existential vars in outermost scope */
  btor_init_node_hash_table_iterator (&it, res->forall->bv_vars);
  btor_queue_hash_table_iterator (&it, res->forall->ufs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    btor_map_node (evars,
                   btor_copy_exp (res->forall, cur),
                   btor_copy_exp (res->forall, cur));
  }

  /* instantiate universal vars with fresh variables */
  map = btor_new_node_map (res->forall);
  btor_init_node_hash_table_iterator (&it, res->forall->quantifiers);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_is_forall_node (cur));
    param = cur->e[0];
    symbol =
        btor_strdup (res->forall->mm, btor_get_symbol_exp (res->forall, param));
    btor_set_symbol_exp (res->forall, param, 0);
    var = btor_var_exp (
        res->forall, btor_get_exp_width (res->forall, param), symbol);
    btor_freestr (res->forall->mm, symbol);
    btor_map_node (map, param, var);
    assert (btor_param_is_forall_var (param));
    btor_map_node (uvars, var, btor_copy_exp (res->forall, param));
  }

  /* eliminate universal vars by substituting them with fresh variables */
  tmp = btor_substitute_terms_node_map (res->forall, root, map, tmp_map);
  btor_release_exp (res->forall, root);
  btor_delete_node_map (map);
  root = tmp;

  if (opt_dual_solver)
  {
    update_node_map (node_map, tmp_map);
    btor_delete_int_hash_map (tmp_map);
  }

  res->forall_formula = root;
  assert (!btor_is_proxy_node (root));
  assert (!BTOR_REAL_ADDR_NODE (root)->quantifier_below);
  res->forall_evars        = evars;
  res->forall_uvars        = uvars;
  res->forall_synth_funs   = btor_new_ptr_hash_table (res->forall->mm, 0, 0);
  res->forall_synth_inputs = btor_new_ptr_hash_table (res->forall->mm, 0, 0);

  /* create ground solver for forall */
  assert (!res->forall->slv);
  fslv                = (BtorFunSolver *) btor_new_fun_solver (res->forall);
  fslv->assume_lemmas = true;
  res->forall->slv    = (BtorSolver *) fslv;

  /* new exists solver */
  res->exists = btor_new_btor ();
  btor_delete_opts (res->exists);
  btor_clone_opts (res->forall, res->exists);
  btor_set_msg_prefix_btor (res->exists, prefix_exists);
  btor_set_opt (res->exists, BTOR_OPT_AUTO_CLEANUP_INTERNAL, 1);

  evars = btor_new_node_map (res->exists);

  /* map evars of exists solver to evars of forall solver */
  btor_init_node_map_iterator (&nit, res->forall_evars);
  while (btor_has_next_node_map_iterator (&nit))
  {
    cur = btor_next_node_map_iterator (&nit);
    assert (btor_is_uf_node (cur) || btor_is_bv_var_node (cur));
    if (btor_is_bv_var_node (cur))
    {
      var = btor_var_exp (res->exists,
                          btor_get_exp_width (res->forall, cur),
                          btor_get_symbol_exp (res->forall, cur));
    }
    else
    {
      sortid = btor_recursively_rebuild_sort_clone (
          res->forall, res->exists, cur->sort_id);
      var = btor_uf_exp (
          res->exists, sortid, btor_get_symbol_exp (res->forall, cur));
      btor_release_sort (&res->exists->sorts_unique_table, sortid);
    }
    btor_map_node (evars, var, cur);
  }

#if 0
  /* map ufs of exists solver to ufs of forall solver */
  btor_init_node_hash_table_iterator (&it, res->forall->ufs);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      sortid = btor_recursively_rebuild_sort_clone (
		   res->forall, res->exists, cur->sort_id);
      var = btor_uf_exp (res->exists, sortid,
			 btor_get_symbol_exp (res->forall, cur));
      btor_release_sort (&res->exists->sorts_unique_table, sortid);
      btor_map_node (evars, var, cur);
    }
#endif

  /* create ground solver for exists */
  res->exists->slv  = btor_new_fun_solver (res->exists);
  res->exists_evars = evars;

  return res;
}

static void
delete_efg_solvers (BtorEFSolver *slv, BtorEFGroundSolvers *gslv)
{
  BtorNodeMapIterator it;
  BtorHashTableIterator hit;
  BtorNode *cur;

  assert (gslv->exists_evars);
  btor_init_node_map_iterator (&it, gslv->exists_evars);
  while (btor_has_next_node_map_iterator (&it))
    btor_release_exp (gslv->exists, btor_next_node_map_iterator (&it));
  btor_delete_node_map (gslv->exists_evars);

  btor_delete_btor (gslv->exists);

  assert (gslv->forall_evars);
  btor_init_node_map_iterator (&it, gslv->forall_evars);
  btor_queue_node_map_iterator (&it, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&it))
  {
    btor_release_exp (gslv->forall, it.it.bucket->data.as_ptr);
    btor_release_exp (gslv->forall, btor_next_node_map_iterator (&it));
  }
  btor_delete_node_map (gslv->forall_evars);
  btor_delete_node_map (gslv->forall_uvars);

  btor_init_node_hash_table_iterator (&hit, gslv->forall_synth_funs);
  while (btor_has_next_node_hash_table_iterator (&hit))
  {
    cur = btor_next_data_node_hash_table_iterator (&hit)->as_ptr;
    if (cur) btor_release_exp (gslv->forall, cur);
  }
  btor_delete_ptr_hash_table (gslv->forall_synth_funs);

  btor_init_node_hash_table_iterator (&hit, gslv->forall_synth_inputs);
  while (btor_has_next_node_hash_table_iterator (&hit))
    btor_delete_ptr_hash_table (
        btor_next_data_node_hash_table_iterator (&hit)->as_ptr);
  btor_delete_ptr_hash_table (gslv->forall_synth_inputs);

  if (gslv->exists_cur_model) delete_exists_model (gslv->exists_cur_model);

  //  btor_release_exp (gslv->forall, gslv->forall_formula);
  //  btor_release_exp (gslv->forall, gslv->forall_sk_formula);
  btor_release_exp (gslv->forall, gslv->forall_formula);

  btor_delete_btor (gslv->forall);

  BTOR_DELETE (slv->btor->mm, gslv);
}

static BtorNode *
build_refinement (Btor *f_solver,
                  Btor *e_solver,
                  BtorNode *root,
                  BtorNodeMap *map)
{
  assert (f_solver);
  assert (e_solver);
  assert (root);
  assert (map);

  char *symbol;
  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, **e;
  BtorNodePtrStack visit, args, cleanup;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorSortId sort;
  //  BtorBitVector *bv, *bv0, *bv1;

  mm = f_solver->mm;
  // TODO: merge mark, cache
  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (cleanup);
  BTOR_PUSH_STACK (mm, visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!btor_is_proxy_node (real_cur));

    if ((result = btor_mapped_node (map, real_cur)))
    {
      result = btor_copy_exp (e_solver, result);
      goto PUSH_RESULT;
    }

    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
      (void) btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      args.top -= real_cur->arity;
      e = args.top;

      if (btor_is_bv_const_node (real_cur))
      {
        result = btor_const_exp (e_solver, btor_const_get_bits (real_cur));
      }
      else if (btor_is_bv_var_node (real_cur) || btor_is_param_node (real_cur)
               || btor_is_uf_node (real_cur))
      {
        symbol = btor_get_symbol_exp (f_solver, real_cur);
        if (symbol && (result = btor_get_node_by_symbol (e_solver, symbol)))
        {
          //		  assert (result->sort_id == real_cur->sort_id);
          assert (result->kind == real_cur->kind);
          result = btor_copy_exp (e_solver, result);
        }
        else if (btor_is_bv_var_node (real_cur))
          result = btor_var_exp (
              e_solver, btor_get_exp_width (f_solver, real_cur), symbol);
        else if (btor_is_param_node (real_cur))
          result = btor_param_exp (
              e_solver, btor_get_exp_width (f_solver, real_cur), symbol);
        else
        {
          assert (btor_is_uf_node (real_cur));
          sort = btor_recursively_rebuild_sort_clone (
              f_solver, e_solver, cur->sort_id);
          result = btor_uf_exp (e_solver, sort, symbol);
          btor_release_sort (&e_solver->sorts_unique_table, sort);
        }
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (e_solver,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
#if 0
	  else if (0 && btor_is_and_node (real_cur)
		   && btor_get_exp_width (f_solver, real_cur) == 1
		   && (bv = btor_get_bv_model (f_solver, real_cur))
		   && btor_is_false_bv (bv))
	    {
	      bv0 = btor_get_bv_model (f_solver, real_cur->e[0]);
	      bv1 = btor_get_bv_model (f_solver, real_cur->e[1]);

	      if (btor_is_false_bv (bv0))
		result = btor_copy_exp (e_solver, e[0]);
	      else
		{
		  assert (btor_is_false_bv (bv1));
		  result = btor_copy_exp (e_solver, e[1]);
		}
	    }
#endif
      else
        result = btor_create_exp (e_solver, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (e_solver, e[i]);

      d->as_ptr = btor_copy_exp (e_solver, result);
      BTOR_PUSH_STACK (mm, cleanup, result);
    PUSH_RESULT:
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (e_solver, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_release_exp (e_solver, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (mm, cleanup);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);
  btor_delete_int_hash_map (mark);
  return result;
}

static void
refine_exists_solver (BtorEFGroundSolvers *gslv)
{
  Btor *f_solver, *e_solver;
  BtorNodeMap *map;
  BtorNodeMapIterator it;
  BtorNode *var_es, *var_fs, *c, *res;
  BtorNodePtrStack consts;
  const BtorBitVector *bv;
  BtorMemMgr *mm;

  //  printf ("  refine\n");
  mm       = gslv->exists->mm;
  f_solver = gslv->forall;
  e_solver = gslv->exists;

  map = btor_new_node_map (f_solver);

  /* generate counter example for universal vars */
  assert (f_solver->last_sat_result == BTOR_RESULT_SAT);
  f_solver->slv->api.generate_model (f_solver->slv, false, false);

  /* map f_exists_vars to e_exists_vars */
  btor_init_node_map_iterator (&it, gslv->exists_evars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var_es = btor_next_node_map_iterator (&it);
    btor_map_node (map, var_fs, var_es);
  }

  /* map f_forall_vars to resp. assignment */
  BTOR_INIT_STACK (consts);
  btor_init_node_map_iterator (&it, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = btor_next_node_map_iterator (&it);
    bv     = btor_get_bv_model (f_solver, btor_simplify_exp (f_solver, var_fs));
    c      = btor_const_exp (e_solver, (BtorBitVector *) bv);
    btor_map_node (map, var_fs, c);
    BTOR_PUSH_STACK (mm, consts, c);
    //      printf ("    %s = ", node2string (var_fs));
    //      btor_print_bv (bv);
  }

  assert (f_solver->unsynthesized_constraints->count == 0);
  assert (f_solver->synthesized_constraints->count == 0);
  assert (f_solver->embedded_constraints->count == 0);
  assert (f_solver->varsubst_constraints->count == 0);
  res = build_refinement (f_solver, e_solver, gslv->forall_formula, map);

  while (!BTOR_EMPTY_STACK (consts))
    btor_release_exp (e_solver, BTOR_POP_STACK (consts));
  BTOR_RELEASE_STACK (mm, consts);

  btor_delete_node_map (map);

  assert (res != e_solver->true_exp);
  BTOR_ABORT (
      res == e_solver->true_exp, "invalid refinement '%s'", node2string (res));
  btor_assert_exp (e_solver, res);
  btor_release_exp (e_solver, res);
}

#if 0
static void
refine_exists_solver (BtorEFGroundSolvers * gslv)
{
  uint32_t i, inst_mode;
  Btor *f_solver, *e_solver;
  BtorNodeMap *map;
  BtorNodeMapIterator it;
  BtorNode *var_es, *var_fs, *c, *res, *synth_fun, *inst_exp;
  BtorNodePtrStack consts, inputs;
  const BtorBitVector *bv;
  BtorPtrHashTable *var_es_assignments, *model;
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  BtorBitVectorTuple *sig = 0;

  mm = gslv->exists->mm;
  f_solver = gslv->forall;
  e_solver = gslv->exists;
  inst_mode = btor_get_opt (f_solver, BTOR_OPT_EF_QINST_MODE);

  map = btor_new_node_map (f_solver);
  var_es_assignments = btor_new_ptr_hash_table (mm,
					 (BtorHashPtr) btor_hash_bv,
					 (BtorCmpPtr) btor_compare_bv);

  /* generate counter example for universal vars */
  assert (f_solver->last_sat_result == BTOR_RESULT_SAT);
  f_solver->slv->api.generate_model (f_solver->slv, false, false);

  BTOR_INIT_STACK (inputs);
  if (e_solver->bv_model
      && (inst_mode == BTOR_EF_QINST_SYNTH || inst_mode == BTOR_EF_QINST_SYM))
    {
      for (i = 1; i < BTOR_COUNT_STACK (e_solver->nodes_id_table); i++)
	{
	  var_es = BTOR_PEEK_STACK (e_solver->nodes_id_table, i);

	  if (!var_es
	      || !BTOR_IS_SYNTH_NODE (var_es)
	      || BTOR_IS_PROXY_NODE (var_es)
	      || BTOR_IS_FUN_NODE (var_es)
	      || BTOR_IS_ARGS_NODE (var_es)
	      || BTOR_IS_BV_CONST_NODE (var_es))
	    continue;

	  bv = btor_get_bv_model (e_solver, var_es);
	  if (btor_get_ptr_hash_table (var_es_assignments, bv))
	    continue;
	  btor_add_ptr_hash_table (var_es_assignments, bv)->data.as_ptr =
	    var_es;
	  BTOR_PUSH_STACK (mm, inputs, var_es);
#if 0
	  if (!BTOR_IS_BV_VAR_NODE (var_es))
//	      || BTOR_IS_BV_CONST_NODE (var_es)
//	      || BTOR_IS_FUN_NODE (var_es)
//	      || BTOR_IS_ARGS_NODE (var_es)
//	      || BTOR_IS_PROXY_NODE (var_es))
	    continue;
#endif
	}

      if (inst_mode == BTOR_EF_QINST_SYNTH && BTOR_COUNT_STACK (inputs) > 0)
	{
//	  printf ("inputs: %u\n", BTOR_COUNT_STACK (inputs));
	  sig = btor_new_bv_tuple (mm, BTOR_COUNT_STACK (inputs));
	  for (i = 0; i < BTOR_COUNT_STACK (inputs); i++)
	    {
	      var_es = BTOR_PEEK_STACK (inputs, i);
//	      printf ("in: %s := ", node2string (var_es));
	      bv = btor_get_bv_model (e_solver, var_es);
//	      btor_print_bv (bv);
	      btor_add_to_bv_tuple (mm, sig, bv, i);
	    }
	}
      else
	sig = 0;
    }

  /* map f_exists_vars to e_exists_vars */
  btor_init_node_map_iterator (&it, gslv->exists_evars);
  while (btor_has_next_node_map_iterator (&it))
    {
      var_fs = it.it.bucket->data.as_ptr;
      var_es = btor_next_node_map_iterator (&it);
      btor_map_node (map, var_fs, var_es);
    }

#ifdef PRINT_DBG
  printf ("found counter example\n");
#endif

  /* map f_forall_vars to resp. assignment */
  BTOR_INIT_STACK (consts);
  btor_init_node_map_iterator (&it, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&it))
    {
      var_fs = btor_next_node_map_iterator (&it);
      bv = btor_get_bv_model (f_solver, btor_simplify_exp (f_solver, var_fs));
#ifdef PRINT_DBG
      printf ("%s := ", node2string (var_fs));
      btor_print_bv (bv);
#endif

      if (inst_mode == BTOR_EF_QINST_SYNTH && sig)
	{
	  model = btor_new_ptr_hash_table (mm,
		      (BtorHashPtr) btor_hash_bv_tuple,
		      (BtorCmpPtr) btor_compare_bv_tuple);
	  assert (sig);
	  btor_add_ptr_hash_table (model, sig)->data.as_ptr =
	    (BtorBitVector *) bv;
	  synth_fun = btor_synthesize_fun (e_solver, 0, model, 0, 0, 0, 0, 3);
	  btor_delete_ptr_hash_table (model);
	  if (synth_fun)
	    {
	      inst_exp = btor_apply_and_reduce (e_solver,
			     BTOR_COUNT_STACK (inputs), inputs.start,
			     synth_fun);
	      btor_dump_smt2_node (e_solver, stdout, inst_exp, -1);
	      btor_map_node (map, var_fs, inst_exp);
	      continue;
	    }
	}

      if (inst_mode == BTOR_EF_QINST_SYM
	  && (b = btor_get_ptr_hash_table (var_es_assignments, (void *) bv)))
	{
//	  printf ("choose sym: %s\n", node2string (b->data.as_ptr));
	  btor_map_node (map, var_fs, b->data.as_ptr);
	}
      else
	{
#ifdef PRINT_DBG
	  printf ("%s := ",
		  node2string (btor_mapped_node (gslv->forall_uvars, var_fs)));
	  btor_print_bv (bv);
#endif
	  c = btor_const_exp (e_solver, (BtorBitVector *) bv);
	  btor_map_node (map, var_fs, c);
	  BTOR_PUSH_STACK (mm, consts, c);
	}
    }

  assert (f_solver->unsynthesized_constraints->count == 0);
  assert (f_solver->synthesized_constraints->count == 0);
  assert (f_solver->embedded_constraints->count == 0);
  assert (f_solver->varsubst_constraints->count == 0);
  res = build_refinement (f_solver, e_solver, gslv->forall_formula, map);

  while (!BTOR_EMPTY_STACK (consts))
    btor_release_exp (e_solver, BTOR_POP_STACK (consts));
  BTOR_RELEASE_STACK (mm, consts);

  BTOR_RELEASE_STACK (mm, inputs);
  btor_delete_ptr_hash_table (var_es_assignments);
  btor_delete_node_map (map);
  if (sig)
    btor_free_bv_tuple (mm, sig);
  assert (res != e_solver->true_exp);
  BTOR_ABORT (res == e_solver->true_exp,
	      "invalid refinement '%s'", node2string (res));
//  btor_set_opt (e_solver, BTOR_OPT_PRETTY_PRINT, 1);
//  btor_dump_smt2_node (e_solver, stdout, res, -1);
  btor_assert_exp (e_solver, res);
  btor_release_exp (e_solver, res);
}
#endif

/* collect all function applications on skolem functions below 'exp'. */
static void
build_dependencies (BtorMemMgr *mm,
                    BtorNode *uf,
                    BtorNode *exp,
                    BtorPtrHashTable *deps)
{
  uint32_t i;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;

  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, exp);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)) continue;

    btor_add_int_hash_table (cache, cur->id);
    /* only function applications on UFs are considered as inputs */
    if (btor_is_apply_node (cur) && btor_is_uf_node (cur->e[0]))
    {
      b = btor_get_ptr_hash_table (deps, cur->e[0]);
      if (!b)
      {
        b              = btor_add_ptr_hash_table (deps, cur->e[0]);
        t              = btor_new_ptr_hash_table (mm, 0, 0);
        b->data.as_ptr = t;
      }
      else
        t = b->data.as_ptr;
      //	  printf ("dep: %s -> %s\n", node2string (cur->e[0]),
      // node2string (uf));
      btor_add_ptr_hash_table (t, uf);
      continue;
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
}

/* check whether 'to_synth' is dependent on 'cur_in' */
static bool
is_dependent (BtorMemMgr *mm,
              BtorNode *to_synth,
              BtorNode *cur_in,
              BtorPtrHashTable *deps)
{
  bool result = false;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *t;
  BtorIntHashTable *cache;
  BtorNodePtrStack to_check;
  BtorNode *cur;

  BTOR_INIT_STACK (to_check);
  cache = btor_new_int_hash_table (mm);
  cur   = to_synth;
  goto START_CYCLE_CHECK;
  while (!BTOR_EMPTY_STACK (to_check))
  {
    cur = BTOR_POP_STACK (to_check);

    if (cur == cur_in)
    {
      result = true;
      break;
    }

  START_CYCLE_CHECK:
    b = btor_get_ptr_hash_table (deps, cur);
    if (!b) continue;
    assert (b->data.as_ptr);
    t = b->data.as_ptr;
    btor_init_node_hash_table_iterator (&it, t);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      if (!btor_contains_int_hash_table (cache, cur->id))
      {
        BTOR_PUSH_STACK (mm, to_check, cur);
        btor_add_int_hash_table (cache, cur->id);
      }
    }
  }
  BTOR_RELEASE_STACK (mm, to_check);
  btor_delete_int_hash_table (cache);
  return result;
}

static void
filter_inputs (BtorMemMgr *mm, BtorNode *fs_uf, BtorPtrHashTable *inputs)
{
  uint32_t i, pos;
  BtorNode *cur;
  BtorNodeIterator it, iit;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableIterator hit;

  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  btor_init_parent_iterator (&it, fs_uf);
  while (btor_has_next_parent_iterator (&it))
  {
    cur = btor_next_parent_iterator (&it);

    btor_init_parent_iterator (&iit, cur);
    while (btor_has_next_parent_iterator (&iit))
    {
      pos = BTOR_GET_TAG_NODE (iit.cur);
      cur = btor_next_parent_iterator (&iit);

      for (i = 0; i < cur->arity; i++)
        if (i != pos) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }
  }

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)) continue;

    btor_add_int_hash_table (cache, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  btor_init_node_hash_table_iterator (&hit, inputs);
  while (btor_has_next_node_hash_table_iterator (&hit))
  {
    cur = btor_next_node_hash_table_iterator (&hit);
    if (!btor_contains_int_hash_table (cache, cur->id))
      btor_remove_ptr_hash_table (inputs, cur, 0, 0);
  }
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
}

static bool
check_input_prefix (Btor *btor, BtorNode *uf, BtorNode *cur_uf)
{
  assert (BTOR_IS_REGULAR_NODE (uf));
  assert (BTOR_IS_REGULAR_NODE (cur_uf));
  assert (btor_is_uf_node (cur_uf));
  assert (btor_is_uf_node (cur_uf));

  uint32_t arity0, arity1;
  BtorArgsIterator it0, it1;
  BtorNodeIterator it;
  BtorNode *app0 = 0, *app1 = 0, *arg0, *arg1, *cur;

  btor_init_parent_iterator (&it, uf);
  while (btor_has_next_parent_iterator (&it))
  {
    cur = btor_next_parent_iterator (&it);
    if (!cur->parameterized)
    {
      if (app0) return false;
      app0 = cur;
    }
  }

  btor_init_parent_iterator (&it, cur_uf);
  while (btor_has_next_parent_iterator (&it))
  {
    cur = btor_next_parent_iterator (&it);
    if (!cur->parameterized)
    {
      if (app1) return false;
      app1 = cur;
    }
  }

  if (!app0 || !app1) return false;

  arity0 = btor_get_fun_arity (btor, uf);
  arity1 = btor_get_fun_arity (btor, cur_uf);

  /* 'cur_uf' is dependent on more universals than 'uf', hence it cannot be an
   * input for 'uf'. */
  if (arity1 > arity0) return false;

  app0 = uf->first_parent;
  app1 = cur_uf->first_parent;
  assert (BTOR_IS_REGULAR_NODE (app0));
  assert (BTOR_IS_REGULAR_NODE (app1));
  assert (btor_is_apply_node (app0));
  assert (btor_is_apply_node (app1));

  if (app0->e[1] == app1->e[1])
    return true;
  else if (arity0 == arity1)
    return false;

  assert (arity0 > arity1);
  btor_init_args_iterator (&it0, app0->e[1]);
  btor_init_args_iterator (&it1, app1->e[1]);
  while (btor_has_next_args_iterator (&it1))
  {
    assert (btor_has_next_args_iterator (&it0));
    arg0 = btor_next_args_iterator (&it0);
    arg1 = btor_next_args_iterator (&it1);
    if (arg0 != arg1) return false;
  }
  return true;
}

static BtorPtrHashTable *
prepare_inputs (BtorEFGroundSolvers *gslv, BtorNode *fs_uf, BtorNodeMap *model)
{
  assert (BTOR_IS_REGULAR_NODE (fs_uf));
  assert (btor_is_uf_node (fs_uf));

  BtorNode *cur, *cur_fs, *cur_synth_fun;
  BtorHashTableIterator it;
  const BtorPtrHashTable *m;
  BtorPtrHashTable *deps, *inputs;
  Btor *e_solver, *f_solver;
  BtorMemMgr *mm;

  mm       = gslv->forall->mm;
  deps     = btor_new_ptr_hash_table (mm, 0, 0);
  inputs   = btor_new_ptr_hash_table (mm, 0, 0);
  e_solver = gslv->exists;
  f_solver = gslv->forall;

  btor_init_node_hash_table_iterator (&it, gslv->forall_evars->table);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur           = btor_next_node_hash_table_iterator (&it);
    cur_synth_fun = btor_mapped_node (model, cur);
    if (!cur_synth_fun) continue;
    build_dependencies (mm, cur, cur_synth_fun, deps);
  }

  btor_init_node_hash_table_iterator (&it, gslv->exists_evars->table);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur_fs = it.bucket->data.as_ptr;
    cur    = btor_next_node_hash_table_iterator (&it);

    if (cur_fs->id == fs_uf->id) continue;

    if (btor_is_uf_node (cur_fs)
        && !check_input_prefix (f_solver, fs_uf, cur_fs))
      continue;

    if (is_dependent (mm, fs_uf, cur_fs, deps)) continue;

    if (btor_is_fun_sort (&e_solver->sorts_unique_table,
                          BTOR_REAL_ADDR_NODE (cur)->sort_id))
    {
      m = btor_get_fun_model (e_solver, btor_simplify_exp (e_solver, cur));
      if (m) btor_add_ptr_hash_table (inputs, cur_fs)->data.as_ptr = (void *) m;
    }
    else
      btor_add_ptr_hash_table (inputs, cur_fs)->data.as_ptr =
          (void *) btor_get_bv_model (e_solver,
                                      btor_simplify_exp (e_solver, cur));
  }

  btor_init_hash_table_iterator (&it, deps);
  while (btor_has_next_hash_table_iterator (&it))
    btor_delete_ptr_hash_table (
        btor_next_data_hash_table_iterator (&it)->as_ptr);
  btor_delete_ptr_hash_table (deps);

  filter_inputs (mm, fs_uf, inputs);
  return inputs;
}

static bool
check_inputs (BtorPtrHashTable *inputs, BtorPtrHashTable *prev_inputs)
{
  BtorNode *cur;
  BtorHashTableIterator it;

  if (inputs->count != prev_inputs->count) return false;

  btor_init_node_hash_table_iterator (&it, inputs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    if (!btor_get_ptr_hash_table (prev_inputs, cur)) return false;
  }
  return true;
}

BtorNode *
generate_lambda_model_from_fun_model (Btor *btor,
                                      BtorNode *exp,
                                      const BtorPtrHashTable *model,
                                      BtorNode *best_match)
{
  assert (btor);
  assert (exp);
  assert (model);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_fun_node (exp));

  uint32_t i;
  BtorNode *uf, *res, *c, *p, *cond, *e_if, *e_else, *tmp, *eq, *ite, *args;
  BtorHashTableIterator it;
  BtorNodePtrStack params, consts;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorTupleSortIterator iit;
  BtorSortId sort;
  BtorSortUniqueTable *sorts;
  BtorPtrHashTable *static_rho;

  static_rho = btor_new_ptr_hash_table (btor->mm, 0, 0);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (consts);

  sorts = &btor->sorts_unique_table;
  /* create params from domain sort */
  btor_init_tuple_sort_iterator (
      &iit, sorts, btor_get_domain_fun_sort (sorts, exp->sort_id));
  while (btor_has_next_tuple_sort_iterator (&iit))
  {
    sort = btor_next_tuple_sort_iterator (&iit);
    p    = btor_param_exp (btor, btor_get_width_bitvec_sort (sorts, sort), 0);
    BTOR_PUSH_STACK (btor->mm, params, p);
  }
  if (best_match)
    uf = btor_copy_exp (btor, best_match);
  else
    uf = btor_uf_exp (btor, exp->sort_id, 0);
  args = btor_args_exp (btor, params.start, BTOR_COUNT_STACK (params));
  assert (args->sort_id = btor_get_domain_fun_sort (sorts, uf->sort_id));
  e_else = btor_apply_exp (btor, uf, args);
  assert (BTOR_REAL_ADDR_NODE (e_else)->sort_id
          == btor_get_codomain_fun_sort (sorts, uf->sort_id));
  btor_release_exp (btor, args);
  btor_release_exp (btor, uf);

  /* generate ITEs */
  ite = 0;
  res = 0;
  btor_init_hash_table_iterator (&it, (BtorPtrHashTable *) model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    value      = (BtorBitVector *) it.bucket->data.as_ptr;
    args_tuple = btor_next_hash_table_iterator (&it);

    /* create condition */
    assert (btor_get_fun_arity (btor, uf) == args_tuple->arity);
    assert (BTOR_EMPTY_STACK (consts));
    assert (BTOR_COUNT_STACK (params) == args_tuple->arity);
    for (i = 0; i < args_tuple->arity; i++)
    {
      c = btor_const_exp (btor, args_tuple->bv[i]);
      assert (BTOR_REAL_ADDR_NODE (c)->sort_id
              == BTOR_PEEK_STACK (params, i)->sort_id);
      BTOR_PUSH_STACK (btor->mm, consts, c);
    }

    assert (!BTOR_EMPTY_STACK (params));
    assert (BTOR_COUNT_STACK (params) == BTOR_COUNT_STACK (consts));
    cond = btor_eq_exp (
        btor, BTOR_PEEK_STACK (params, 0), BTOR_PEEK_STACK (consts, 0));
    for (i = 1; i < BTOR_COUNT_STACK (params); i++)
    {
      eq = btor_eq_exp (
          btor, BTOR_PEEK_STACK (params, i), BTOR_PEEK_STACK (consts, i));
      tmp = btor_and_exp (btor, cond, eq);
      btor_release_exp (btor, cond);
      btor_release_exp (btor, eq);
      cond = tmp;
    }

    /* args for static_rho */
    args = btor_args_exp (btor, consts.start, BTOR_COUNT_STACK (consts));

    while (!BTOR_EMPTY_STACK (consts))
      btor_release_exp (btor, BTOR_POP_STACK (consts));

    /* create ITE */
    e_if = btor_const_exp (btor, value);
    ite  = btor_cond_exp (btor, cond, e_if, e_else);

    /* add to static rho */
    btor_add_ptr_hash_table (static_rho, args)->data.as_ptr =
        btor_copy_exp (btor, e_if);

    btor_release_exp (btor, cond);
    btor_release_exp (btor, e_if);
    btor_release_exp (btor, e_else);
    e_else = ite;
  }

  assert (ite);
  if (ite) /* get rid of compiler warning */
  {
    res = btor_fun_exp (btor, params.start, BTOR_COUNT_STACK (params), ite);
    btor_release_exp (btor, ite);
  }

  while (!BTOR_EMPTY_STACK (params))
    btor_release_exp (btor, BTOR_POP_STACK (params));
  BTOR_RELEASE_STACK (btor->mm, params);
  BTOR_RELEASE_STACK (btor->mm, consts);

  /* res already exists */
  if (((BtorLambdaNode *) res)->static_rho)
  {
    btor_init_node_hash_table_iterator (&it, static_rho);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      btor_release_exp (btor, it.bucket->data.as_ptr);
      btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
    }
    btor_delete_ptr_hash_table (static_rho);
  }
  else
    ((BtorLambdaNode *) res)->static_rho = static_rho;
  assert (res->sort_id == exp->sort_id);
  return res;
}

/*------------------------------------------------------------------------*/

static BtorEFSolver *
clone_ef_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  (void) clone;
  (void) btor;
  (void) exp_map;
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
  btor = slv->btor;
  BTOR_DELETE (btor->mm, slv);
  btor->slv = 0;
}

static BtorNodeMap *
synthesize_model (BtorEFSolver *slv, BtorEFGroundSolvers *gslv)
{
  bool opt_synth_fun;
  uint32_t max_level;
  BtorNodeMap *model, *e_vars;
  Btor *e_solver, *f_solver;
  BtorNode *e_uf, *e_uf_fs, *synth_fun, *best_match;
  BtorNode *prev_synth_fun;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;
  const BtorPtrHashTable *uf_model;
  BtorPtrHashTable *inputs, *synth_funs, *synth_inputs;
  BtorPtrHashBucket *b, *bb;
  //  double sum = 0;

  e_solver      = gslv->exists;
  f_solver      = gslv->forall;
  synth_funs    = gslv->forall_synth_funs;
  synth_inputs  = gslv->forall_synth_inputs;
  e_vars        = gslv->exists_evars;
  model         = btor_new_node_map (f_solver);
  opt_synth_fun = btor_get_opt (f_solver, BTOR_OPT_EF_SYNTH) == 1;

  /* generate model for exists vars/ufs */
  assert (e_solver->last_sat_result == BTOR_RESULT_SAT);
  e_solver->slv->api.generate_model (e_solver->slv, false, false);

  /* map existential variables to their resp. assignment */
  btor_init_node_map_iterator (&it, e_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    e_uf_fs = it.it.bucket->data.as_ptr;
    e_uf    = btor_next_node_map_iterator (&it);

    if (btor_is_bitvec_sort (&e_solver->sorts_unique_table,
                             BTOR_REAL_ADDR_NODE (e_uf)->sort_id))
    {
      bv = btor_get_bv_model (e_solver, btor_simplify_exp (e_solver, e_uf));
#ifdef PRINT_DBG
      printf ("exists %s := ", node2string (e_uf));
      btor_print_bv (bv);
#endif
      assert (!btor_is_proxy_node (e_uf_fs));
      synth_fun = btor_const_exp (f_solver, (BtorBitVector *) bv);
    }
    /* map skolem functions to resp. synthesized functions */
    else
    {
      assert (btor_is_fun_sort (&e_solver->sorts_unique_table,
                                BTOR_REAL_ADDR_NODE (e_uf)->sort_id));
      assert (btor_is_fun_sort (&f_solver->sorts_unique_table,
                                BTOR_REAL_ADDR_NODE (e_uf_fs)->sort_id));

      uf_model = btor_get_fun_model (e_solver, e_uf);

      if (!uf_model) continue;
#ifdef PRINT_DBG
      printf ("exists %s\n", node2string (e_uf));
      BtorHashTableIterator mit;
      BtorBitVectorTuple *tup;
      uint32_t i;
      btor_init_hash_table_iterator (&mit, uf_model);
      while (btor_has_next_hash_table_iterator (&mit))
      {
        bv  = mit.bucket->data.as_ptr;
        tup = btor_next_hash_table_iterator (&mit);

        for (i = 0; i < tup->arity; i++)
        {
          printf ("a ");
          btor_print_bv (tup->bv[i]);
        }
        printf ("r ");
        btor_print_bv (bv);
      }
#endif
      //	  double start = btor_time_stamp ();
      best_match = 0;
      b          = btor_get_ptr_hash_table (synth_funs, e_uf_fs);
      if (opt_synth_fun)
      {
        bb     = btor_get_ptr_hash_table (synth_inputs, e_uf_fs);
        inputs = prepare_inputs (gslv, e_uf_fs, model);

        if (b && bb && check_inputs (inputs, bb->data.as_ptr))
          prev_synth_fun = b->data.as_ptr;
        else
          prev_synth_fun = 0;

        /* last synthesize step failed and no candidate was found */
        if (b && !b->data.as_ptr)
          max_level = 2;
        else
          max_level = 0;
        synth_fun = btor_synthesize_fun (f_solver,
                                         e_uf_fs,
                                         uf_model,
                                         prev_synth_fun,
                                         inputs,
                                         &best_match,
                                         100000,
                                         max_level);
        assert (!synth_fun || e_uf_fs->sort_id == synth_fun->sort_id);
        if (bb)
          btor_delete_ptr_hash_table (bb->data.as_ptr);
        else
          bb = btor_add_ptr_hash_table (synth_inputs, e_uf_fs);
        bb->data.as_ptr = inputs;
      }
      else
        synth_fun = 0;

      if (!b) b = btor_add_ptr_hash_table (synth_funs, e_uf_fs);

      if (!synth_fun)
      {
        //	      printf ("NO CANDIDATE FOUND for %s in %.2fs\n",
        // node2string (e_uf_fs), 		      btor_time_stamp () -
        // start);
        slv->stats.synth_aborts++;
        // FIXME: using best_match only oftern produces true_exp refinements
        if (false && best_match)
        {
          //		  printf ("USE BEST MATCH\n");
          synth_fun = btor_copy_exp (f_solver, best_match);
        }
        else
        {
          //	    if (best_match)
          //	      btor_dump_smt2_node (f_solver, stdout, best_match, -1);
          synth_fun = generate_lambda_model_from_fun_model (
              f_solver, e_uf_fs, uf_model, best_match);
        }
        if (best_match) btor_release_exp (f_solver, best_match);

        if (b->data.as_ptr != 0)
        {
          btor_release_exp (f_solver, b->data.as_ptr);
          b->data.as_ptr = 0;
        }
      }
      else
      {
        //	      printf ("CANDIDATE FOUND for %s in %.2fs\n", node2string
        //(e_uf_fs), 		      btor_time_stamp () - start);
        if (b->data.as_ptr != synth_fun)
        {
          //		printf ("NEW\n");
          slv->stats.synth_funs++;
        }
        else
        {
          //		printf ("NOT CHANGED\n");
          slv->stats.synth_funs_reused++;
        }

        /* save synthesized function for next iteration (if changed) */
        if (b->data.as_ptr != synth_fun)
        {
          if (b->data.as_ptr) btor_release_exp (f_solver, b->data.as_ptr);
          b->data.as_ptr = btor_copy_exp (f_solver, synth_fun);
        }
      }
      //      if (btor_time_stamp () - start >= 1)
      //	{
      //      btor_dump_smt2_node (f_solver, stdout, synth_fun, -1);
      //	}
      //	  sum += btor_time_stamp() - start;
    }
    assert (BTOR_IS_REGULAR_NODE (e_uf_fs));
    assert (e_uf_fs->sort_id == BTOR_REAL_ADDR_NODE (synth_fun)->sort_id);
    btor_map_node (model, e_uf_fs, synth_fun);
    //      printf ("CANDIDATE FOUND for %s\n", node2string (e_uf_fs));
    //      btor_dump_smt2_node (f_solver, stdout, synth_fun, -1);
  }

  //  printf ("SUM: %.2f\n", sum);
  return model;
}

static void
update_formula (BtorEFGroundSolvers *gslv)
{
  Btor *forall;
  BtorNode *f, *g;

  forall = gslv->forall;
  f      = gslv->forall_formula;
  /* update formula if changed via simplifications */
  if (btor_is_proxy_node (f))
  {
    g = btor_copy_exp (forall, btor_simplify_exp (forall, f));
    btor_release_exp (forall, f);
    gslv->forall_formula = g;
  }
}

#if 0
static BtorSolverResult
find_model2 (BtorEFSolver * slv, BtorEFGroundSolvers * gslv)
{
  double start;
  BtorSolverResult res;
  BtorNode *g;
  BtorNodeMap *map;
  printf ("\nfind_model\n");

  /* query forall solver */
  start = btor_time_stamp ();
  res = btor_sat_btor (gslv->forall, -1, -1);
  update_formula (gslv);
  slv->time.f_solver += btor_time_stamp () - start;

  if (res == BTOR_RESULT_UNSAT) /* formula is SAT */
    {
      res = BTOR_RESULT_SAT;
      return res;
    }

#if 0
  if (map)
    {
      delete_exists_model (map);
      map = 0;
    }
#endif

  start = btor_time_stamp ();
  refine_exists_solver (gslv);
  slv->time.qinst += btor_time_stamp () - start;
  slv->stats.refinements++;

//  printf ("**************************** NEW ITERATION "
//	  "****************************\n");

  /* query exists solver */
  start = btor_time_stamp ();
  res = btor_sat_btor (gslv->exists, -1, -1);
  slv->time.e_solver += btor_time_stamp () - start;

  if (res == BTOR_RESULT_UNSAT)  /* formula is UNSAT */
    return res;

  printf ("synthesize model\n");
  start = btor_time_stamp ();
  map = synthesize_model (slv, gslv);
  slv->time.synth += btor_time_stamp () - start;
  assert (!btor_is_proxy_node (gslv->forall_formula));
  g = btor_substitute_terms (gslv->forall, gslv->forall_formula, map);
  btor_assume_exp (gslv->forall, BTOR_INVERT_NODE (g));
  btor_release_exp (gslv->forall, g);
  if (gslv->exists_cur_model)
    delete_exists_model (gslv->exists_cur_model);
  gslv->exists_cur_model = map;

  return BTOR_RESULT_UNKNOWN;
}
#endif

static BtorSolverResult
find_model (BtorEFSolver *slv, BtorEFGroundSolvers *gslv)
{
  double start;
  BtorSolverResult res;
  BtorNode *g;
  BtorNodeMap *map;

  /* exists solver does not have any constraints, so it does not make much
   * sense to initialize every variable by zero and ask if the model
   * is correct. */
  if (gslv->exists->unsynthesized_constraints->count
          + gslv->exists->synthesized_constraints->count
      > 0)
  {
    /* query exists solver */
    start = btor_time_stamp ();
    res   = btor_sat_btor (gslv->exists, -1, -1);
    gslv->time.e_solver += btor_time_stamp () - start;

    if (res == BTOR_RESULT_UNSAT) /* formula is UNSAT */
      return res;

    start = btor_time_stamp ();
    map   = synthesize_model (slv, gslv);
    gslv->time.synth += btor_time_stamp () - start;
    assert (!btor_is_proxy_node (gslv->forall_formula));
    g = btor_substitute_terms (gslv->forall, gslv->forall_formula, map);
    btor_assume_exp (gslv->forall, BTOR_INVERT_NODE (g));
    btor_release_exp (gslv->forall, g);
    if (gslv->exists_cur_model) delete_exists_model (gslv->exists_cur_model);
    gslv->exists_cur_model = map;
  }
  else
    btor_assume_exp (gslv->forall, BTOR_INVERT_NODE (gslv->forall_formula));

  /* query forall solver */
  start = btor_time_stamp ();
  res   = btor_sat_btor (gslv->forall, -1, -1);
  update_formula (gslv);
  gslv->time.f_solver += btor_time_stamp () - start;

  if (res == BTOR_RESULT_UNSAT) /* formula is SAT */
  {
    res = BTOR_RESULT_SAT;
    return res;
  }

  start = btor_time_stamp ();
  refine_exists_solver (gslv);
  gslv->time.qinst += btor_time_stamp () - start;
  slv->stats.refinements++;

  return BTOR_RESULT_UNKNOWN;
}

static void
map_vars (BtorEFGroundSolvers *gslv,
          BtorEFGroundSolvers *dual_gslv,
          BtorIntHashTable *node_map,
          BtorIntHashTable *node_map_dual,
          BtorNodeMap *vars_map,
          BtorNodeMap *dual_vars_map)
{
  int32_t key, mapped, mapped_dual;
  size_t i;
  BtorNode *cur, *cur_dual;

  for (i = 0; i < node_map->size; i++)
  {
    key = node_map->keys[i];
    if (!key) continue;
    assert (btor_contains_int_hash_map (node_map_dual, key));
    mapped      = node_map->data[i].as_int;
    mapped_dual = btor_get_int_hash_map (node_map_dual, key)->as_int;

    cur      = btor_get_node_by_id (gslv->forall, mapped);
    cur_dual = btor_get_node_by_id (dual_gslv->forall, mapped_dual);
    if (!cur) continue;      /* variable was eliminated in original formula */
    if (!cur_dual) continue; /* variable was eliminated in dual formula */
    assert (cur);
    assert (cur_dual);

    if (btor_is_bv_var_node (cur)
        && (btor_mapped_node (gslv->forall_evars, cur)
            || btor_mapped_node (gslv->forall_uvars, cur)))
    {
      btor_map_node (vars_map,
                     cur,
                     btor_is_apply_node (cur_dual) ? cur_dual->e[0] : cur_dual);
    }
    else if (btor_is_apply_node (cur)
             && btor_mapped_node (gslv->forall_evars, cur->e[0]))
    {
      assert (btor_is_bv_var_node (cur_dual));
      btor_map_node (vars_map, cur->e[0], cur_dual);
    }

    if (btor_is_bv_var_node (cur_dual)
        && (btor_mapped_node (dual_gslv->forall_evars, cur_dual)
            || btor_mapped_node (dual_gslv->forall_uvars, cur_dual)))
    {
      btor_map_node (
          dual_vars_map, cur_dual, btor_is_apply_node (cur) ? cur->e[0] : cur);
    }
    else if (btor_is_apply_node (cur_dual)
             && btor_mapped_node (dual_gslv->forall_evars, cur_dual->e[0]))
    {
      assert (btor_is_bv_var_node (cur));
      btor_map_node (dual_vars_map, cur_dual->e[0], cur);
    }
  }
}

/* instantiate universal variables in gslv->forall_formula with model of
 * dual_gslv->exists_cur_model */
static void
add_instantiation (BtorEFGroundSolvers *gslv,
                   BtorEFGroundSolvers *dual_gslv,
                   BtorNodeMap *vars_map)
{
  BtorNodeMap *map, *exp_map;
  BtorNodeMapIterator it;
  BtorNodePtrStack substs, args;
  BtorNode *var_fs, *var_es, *res;
  BtorNode *cur, *m, *subst, *arg, *fun;
  BtorMemMgr *mm;
  BtorArgsIterator ait;

  mm  = gslv->forall->mm;
  map = btor_new_node_map (gslv->forall);
  BTOR_INIT_STACK (args);

  /* map f_forall_vars to resp. assignment */
  BTOR_INIT_STACK (substs);
  btor_init_node_map_iterator (&it, dual_gslv->exists_cur_model);
  while (btor_has_next_node_map_iterator (&it))
  {
    m      = it.it.bucket->data.as_ptr;
    cur    = btor_next_node_map_iterator (&it);
    var_fs = btor_mapped_node (vars_map, cur);
    /* some variables may have been eliminated in the dual formula */
    if (!var_fs) continue;
    assert (var_fs);
    exp_map = btor_new_node_map (gslv->forall);
    if (btor_is_bv_var_node (cur))
    {
      assert (btor_is_bv_const_node (m));
      subst = build_refinement (dual_gslv->forall, gslv->forall, m, exp_map);
    }
    else  // instantiate UFs with resp. arguments
    {
      assert (btor_is_uf_node (cur));
      assert (btor_is_lambda_node (m));
      //	  printf ("  %s (%d) %s\n", node2string (cur), cur->parents,
      // node2string (cur->first_parent));
      /* map universal vars from gslv->forall to existential vars of
       * gslv->forall and then to glsv->exists */
      btor_init_args_iterator (&ait, cur->first_parent->e[1]);
      while (btor_has_next_args_iterator (&ait))
      {
        arg = btor_next_args_iterator (&ait);
        assert (btor_is_bv_var_node (arg));
        //	      printf ("  arg: %s\n", node2string (arg));
        arg = btor_mapped_node (vars_map, arg);
        //	      printf ("  arg_mapped: %s\n", node2string (arg));
        assert (arg);
        assert (arg->btor == gslv->forall);
        BTOR_PUSH_STACK (mm, args, arg);
      }
      fun   = build_refinement (dual_gslv->forall, gslv->forall, m, vars_map);
      subst = btor_apply_exps (
          gslv->forall, args.start, BTOR_COUNT_STACK (args), fun);
      btor_release_exp (gslv->forall, fun);
      BTOR_RESET_STACK (args);
    }
    assert (BTOR_REAL_ADDR_NODE (subst)->btor == gslv->forall);
    btor_delete_node_map (exp_map);
    btor_map_node (map, var_fs, subst);
    BTOR_PUSH_STACK (mm, substs, subst);
  }

  subst = btor_substitute_terms (gslv->forall, gslv->forall_formula, map);
  //  btor_dump_smt2_node (gslv->forall, stdout, subst, -1);

  btor_delete_node_map (map);
  map = btor_new_node_map (gslv->forall);

  /* map f_exists_vars to e_exists_vars */
  btor_init_node_map_iterator (&it, gslv->exists_evars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var_es = btor_next_node_map_iterator (&it);
    btor_map_node (map, var_fs, var_es);
  }

  res = build_refinement (gslv->forall, gslv->exists, subst, map);
  btor_release_exp (gslv->forall, subst);

  while (!BTOR_EMPTY_STACK (substs))
    btor_release_exp (gslv->forall, BTOR_POP_STACK (substs));
  BTOR_RELEASE_STACK (mm, substs);

  BTOR_RELEASE_STACK (mm, args);
  btor_delete_node_map (map);

  // FIXME: for some reason true_exp is generated once for the dual case?
  //  assert (res != gslv->exists->true_exp);
  //  BTOR_ABORT (res == gslv->exists->true_exp,
  //	      "invalid refinement '%s'", node2string (res));
  btor_assert_exp (gslv->exists, res);
  btor_release_exp (gslv->exists, res);
}

static BtorSolverResult
sat_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  //  double start;
  bool opt_dual_solver;
  int32_t key;
  size_t i;
  BtorSolverResult res;
  BtorNode *g, *dual_g, *cur;
  BtorEFGroundSolvers *gslv, *dual_gslv;
  BtorNodeMap *vars_map = 0, *dual_vars_map = 0;
  BtorIntHashTable *node_map = 0, *node_map_dual = 0, *tmp_map = 0;
  /* 'vars_map' maps existential/universal (gslv) to universal/existential
   * vars (dual_gslv) */

  // TODO (ma): incremental support

  /* simplify formula and normalize quantifiers */
  btor_simplify (slv->btor);

  opt_dual_solver = btor_get_opt (slv->btor, BTOR_OPT_EF_DUAL_SOLVER) == 1;

  g = btor_normalize_quantifiers (slv->btor);

  if (opt_dual_solver)
  {
    vars_map      = btor_new_node_map (slv->btor);
    dual_vars_map = btor_new_node_map (slv->btor);
    tmp_map       = btor_new_int_hash_map (slv->btor->mm);
    node_map      = btor_new_int_hash_map (slv->btor->mm);
    node_map_dual = btor_new_int_hash_map (slv->btor->mm);
    dual_g        = btor_normalize_quantifiers_node (
        slv->btor, BTOR_INVERT_NODE (g), tmp_map);
    for (i = 0; i < tmp_map->size; i++)
    {
      key = tmp_map->keys[i];
      if (!key) continue;
      cur = btor_get_node_by_id (slv->btor, key);
      if (!btor_is_param_node (cur)
          || (!btor_param_is_forall_var (cur)
              && !btor_param_is_exists_var (cur)))
        continue;
      btor_add_int_hash_map (node_map, key)->as_int = key;
      btor_add_int_hash_map (node_map_dual, key)->as_int =
          tmp_map->data[i].as_int;
    }
    btor_delete_int_hash_map (tmp_map);
  }

  gslv = setup_efg_solvers (slv, g, node_map, "forall", "exists");
  btor_release_exp (slv->btor, g);
  //  btor_assume_exp (gslv->forall, BTOR_INVERT_NODE (gslv->forall_formula));

  if (opt_dual_solver)
  {
    dual_gslv = setup_efg_solvers (
        slv, dual_g, node_map_dual, "dual_forall", "dual_exists");
    btor_release_exp (slv->btor, dual_g);

    assert (!opt_dual_solver || node_map->count == node_map_dual->count);
    map_vars (
        gslv, dual_gslv, node_map, node_map_dual, vars_map, dual_vars_map);
    btor_delete_int_hash_map (node_map);
    btor_delete_int_hash_map (node_map_dual);
    //      btor_assume_exp (dual_gslv->forall,
    //		       BTOR_INVERT_NODE (dual_gslv->forall_formula));
  }

  while (true)
  {
    res = find_model (slv, gslv);
    if (res != BTOR_RESULT_UNKNOWN) break;

    if (opt_dual_solver)
    {
      add_instantiation (dual_gslv, gslv, vars_map);

      res = find_model (slv, dual_gslv);
      if (res == BTOR_RESULT_SAT || res == BTOR_RESULT_UNKNOWN)
      {
        add_instantiation (gslv, dual_gslv, dual_vars_map);
        /* the formula is only UNSAT if there are no UFs in the original
         * one */
        if (res == BTOR_RESULT_SAT && slv->btor->ufs->count == 0)
          printf ("FOUND DUAL MODEL\n");
      }
      else if (res == BTOR_RESULT_UNSAT)
      {
        printf ("VALID\n");
      }
      slv->time.dual_e_solver = dual_gslv->time.e_solver;
      slv->time.dual_f_solver = dual_gslv->time.f_solver;
      slv->time.dual_synth    = dual_gslv->time.synth;
      slv->time.dual_qinst    = dual_gslv->time.qinst;
    }
    slv->time.e_solver = gslv->time.e_solver;
    slv->time.f_solver = gslv->time.f_solver;
    slv->time.synth    = gslv->time.synth;
    slv->time.qinst    = gslv->time.qinst;
  }

  slv->time.e_solver = gslv->time.e_solver;
  slv->time.f_solver = gslv->time.f_solver;
  slv->time.synth    = gslv->time.synth;
  slv->time.qinst    = gslv->time.qinst;

  if (opt_dual_solver)
  {
    slv->time.dual_e_solver = dual_gslv->time.e_solver;
    slv->time.dual_f_solver = dual_gslv->time.f_solver;
    slv->time.dual_synth    = dual_gslv->time.synth;
    slv->time.dual_qinst    = dual_gslv->time.qinst;
    btor_delete_node_map (vars_map);
    btor_delete_node_map (dual_vars_map);
    delete_efg_solvers (slv, dual_gslv);
  }
  delete_efg_solvers (slv, gslv);
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

  // TODO (ma): for now not supported
  (void) model_for_all_nodes;
  (void) reset;

  //  BtorNode *cur, *param, *var_fs;
  //  BtorNodeMapIterator it;
  //  const BtorBitVector *bv;

  btor_init_bv_model (slv->btor, &slv->btor->bv_model);
  btor_init_fun_model (slv->btor, &slv->btor->fun_model);
#if 0
  btor_init_node_map_iterator (&it, slv->e_exists_vars);
  while (btor_has_next_node_map_iterator (&it))
    {
      cur = btor_next_node_map_iterator (&it);
      var_fs = btor_mapped_node (slv->e_exists_vars, cur);
      param = btor_mapped_node (slv->f_exists_vars, var_fs);

      bv = btor_get_bv_model (slv->e_solver,
	       btor_simplify_exp (slv->e_solver, cur));
      assert (btor_get_node_by_id (slv->btor, param->id));
      btor_add_to_bv_model (
	  slv->btor, slv->btor->bv_model,
	  btor_get_node_by_id (slv->btor, param->id),
	  (BtorBitVector *) bv);
    }

  return;
  // TODO (ma): UF models
  btor_init_node_map_iterator (&it, slv->f_synth_fun_models);
  while (btor_has_next_node_map_iterator (&it))
    {
      printf ("model for %s\n", node2string (it.it.cur));
      cur = btor_next_data_node_map_iterator (&it)->as_ptr;
      btor_dump_btor_node (slv->f_solver, stdout, cur);
      btor_dump_smt2_node (slv->f_solver, stdout, cur, -1);
    }
#endif
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
  BTOR_MSG (slv->btor->msg,
            1,
            "synthesize function aborts: %u",
            slv->stats.synth_aborts);
  BTOR_MSG (
      slv->btor->msg, 1, "synthesized functions: %u", slv->stats.synth_funs);
  BTOR_MSG (slv->btor->msg,
            1,
            "synthesized functions reused: %u",
            slv->stats.synth_funs_reused);
  //  printf ("****************\n");
  //  btor_print_stats_btor (slv->e_solver);
  //  btor_print_stats_btor (slv->f_solver);
}

static void
print_time_stats_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BTOR_MSG (
      slv->btor->msg, 1, "%.2f seconds exists solver", slv->time.e_solver);
  BTOR_MSG (
      slv->btor->msg, 1, "%.2f seconds forall solver", slv->time.f_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds synthesizing functions",
            slv->time.synth);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds quantifier instantiation",
            slv->time.qinst);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds dual exists solver",
            slv->time.dual_e_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds dual forall solver",
            slv->time.dual_f_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds dual synthesizing functions",
            slv->time.dual_synth);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds dual quantifier instantiation",
            slv->time.dual_qinst);
}

BtorSolver *
btor_new_ef_solver (Btor *btor)
{
  assert (btor);
  // TODO (ma): incremental calls not supported yet
  assert (!btor_get_opt (btor, BTOR_OPT_INCREMENTAL));

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

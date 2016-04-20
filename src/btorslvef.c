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
#include "utils/btorutil.h"

// TODO (ma): debug
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"

//#define PRINT_DBG

/*------------------------------------------------------------------------*/

static void
setup_exists_solver (BtorEFSolver *slv)
{
  Btor *e_solver, *f_solver;
  BtorNode *cur, *var;
  BtorNodeMapIterator it;
  BtorHashTableIterator hit;
  BtorNodeMap *exists_vars, *exists_ufs;

  f_solver    = slv->f_solver;
  e_solver    = btor_clone_formula (f_solver);
  exists_vars = btor_new_node_map (e_solver);
  exists_ufs  = btor_new_node_map (e_solver);
  btor_set_msg_prefix_btor (e_solver, "exists");
  btor_set_opt (e_solver, BTOR_OPT_AUTO_CLEANUP_INTERNAL, 1);

  btor_init_node_map_iterator (&it, slv->f_exists_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    cur = btor_next_node_map_iterator (&it);
    var = btor_match_node_by_id (e_solver, cur->id);
    btor_map_node (exists_vars, var, cur);
  }

  btor_init_node_hash_table_iterator (&hit, slv->f_solver->ufs);
  while (btor_has_next_hash_table_iterator (&hit))
  {
    cur = btor_next_hash_table_iterator (&hit);
    var = btor_match_node_by_id (e_solver, cur->id);
    btor_map_node (exists_ufs, var, cur);
  }

  btor_init_node_map_iterator (&it, slv->f_forall_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    cur = btor_next_node_map_iterator (&it);
    var = btor_match_node_by_id (e_solver, cur->id);
    btor_release_exp (e_solver, var);
  }

  btor_release_exp (e_solver,
                    btor_match_node_by_id (
                        e_solver, BTOR_REAL_ADDR_NODE (slv->f_formula)->id));

  e_solver->slv      = btor_new_fun_solver (e_solver);
  slv->e_solver      = e_solver;
  slv->e_exists_vars = exists_vars;
  slv->e_exists_ufs  = exists_ufs;
}

static void
setup_forall_solver (BtorEFSolver *slv)
{
  char *symbol;
  Btor *f_solver, *btor;
  BtorNode *cur, *param, *var, *root, *tmp;
  BtorHashTableIterator it;
  BtorNodeMap *map, *exists_vars, *forall_vars;
  BtorFunSolver *fslv;
  BtorNodeMap *exp_map;

  btor = slv->btor;

  (void) btor_simplify (btor);
  btor->options[BTOR_OPT_PRETTY_PRINT].val = 0;

  f_solver = btor_new_btor ();
  btor_delete_opts (f_solver);
  btor_clone_opts (btor, f_solver);
  btor_set_msg_prefix_btor (f_solver, "forall");

  exists_vars = btor_new_node_map (f_solver);
  forall_vars = btor_new_node_map (f_solver);
  exp_map     = btor_new_node_map (btor);

  /* configure options */
  btor_set_opt (f_solver, BTOR_OPT_MODEL_GEN, 1);
  btor_set_opt (f_solver, BTOR_OPT_INCREMENTAL, 1);
  // FIXME (ma): if -bra is enabled then test_synth5.smt2 fails without
  // disabling this since f_formula will be simplified
  btor_set_opt (f_solver, BTOR_OPT_BETA_REDUCE_ALL, 0);

  root = btor_normalize_quantifiers (btor);
  printf ("nnf_root: %s\n", node2string (root));
  tmp = btor_recursively_rebuild_exp_clone (
      btor,
      f_solver,
      root,
      exp_map,
      btor_get_opt (f_solver, BTOR_OPT_REWRITE_LEVEL));
  printf ("root: %s\n", node2string (tmp));
  btor_delete_node_map (exp_map);
  btor_release_exp (btor, root);
  root = tmp;

  if (btor_get_opt (f_solver, BTOR_OPT_EF_CER))
  {
    tmp = btor_cer_node (f_solver, root);
    btor_release_exp (f_solver, root);
    root = tmp;
  }

  tmp = btor_skolemize_node (f_solver, root);
  printf ("sk_root: %s\n", node2string (tmp));
  btor_release_exp (f_solver, root);
  root = tmp;

  if (btor_get_opt (f_solver, BTOR_OPT_EF_DER))
  {
    tmp = btor_der_node (f_solver, root);
    btor_release_exp (f_solver, root);
    root = tmp;
  }

  assert (f_solver->exists_vars->count == 0);

  btor_init_node_hash_table_iterator (&it, f_solver->bv_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    btor_map_node (exists_vars,
                   btor_copy_exp (f_solver, cur),
                   btor_copy_exp (f_solver, cur));
  }

  /* instantiate forall params with fresh variables */
  btor_init_node_hash_table_iterator (&it, f_solver->quantifiers);
  map = btor_new_node_map (f_solver);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_FORALL_NODE (cur));
    param  = cur->e[0];
    symbol = btor_strdup (f_solver->mm, btor_get_symbol_exp (f_solver, param));
    btor_set_symbol_exp (f_solver, param, 0);
    var = btor_var_exp (f_solver, btor_get_exp_width (f_solver, param), symbol);
    btor_freestr (f_solver->mm, symbol);
    btor_map_node (map, param, var);
    assert (btor_param_is_forall_var (param));
    btor_map_node (forall_vars, var, btor_copy_exp (f_solver, param));
  }

  /* eliminate quantified terms by substituting bound variables with fresh
   * variables */
  tmp = btor_substitute_terms (f_solver, root, map);
  btor_release_exp (f_solver, root);
  btor_delete_node_map (map);
  root = tmp;

  assert (f_solver->forall_vars->count == 0);
  assert (f_solver->quantifiers->count == 0);

  slv->f_formula = BTOR_INVERT_NODE (root);
  assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (slv->f_formula)));
  assert (!f_solver->slv);
  fslv                = (BtorFunSolver *) btor_new_fun_solver (f_solver);
  fslv->assume_lemmas = true;
  f_solver->slv       = (BtorSolver *) fslv;
  slv->f_solver       = f_solver;
  slv->f_exists_vars  = exists_vars;
  slv->f_forall_vars  = forall_vars;
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
  BtorIntHashTableData *d;
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

      if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_const_exp (e_solver, btor_const_get_bits (real_cur));
      }
      else if (BTOR_IS_BV_VAR_NODE (real_cur) || BTOR_IS_PARAM_NODE (real_cur)
               || BTOR_IS_UF_NODE (real_cur))
      {
        symbol = btor_get_symbol_exp (f_solver, real_cur);
        if (symbol && (result = btor_get_node_by_symbol (e_solver, symbol)))
        {
          assert (result->sort_id == real_cur->sort_id);
          assert (result->kind == real_cur->kind);
          result = btor_copy_exp (e_solver, result);
        }
        else if (BTOR_IS_BV_VAR_NODE (real_cur))
          result = btor_var_exp (
              e_solver, btor_get_exp_width (f_solver, real_cur), symbol);
        else if (BTOR_IS_PARAM_NODE (real_cur))
          result = btor_param_exp (
              e_solver, btor_get_exp_width (f_solver, real_cur), symbol);
        else
        {
          assert (BTOR_IS_UF_NODE (real_cur));
          sort = btor_recursively_rebuild_sort_clone (
              f_solver, e_solver, cur->sort_id);
          result = btor_uf_exp (e_solver, sort, symbol);
          btor_release_sort (&e_solver->sorts_unique_table, sort);
        }
      }
      else if (BTOR_IS_SLICE_NODE (real_cur))
      {
        result = btor_slice_exp (e_solver,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
#if 0
	  else if (0 && BTOR_IS_AND_NODE (real_cur)
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
      assert (real_cur->sort_id == BTOR_REAL_ADDR_NODE (result)->sort_id);
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
refine_exists_solver (BtorEFSolver *slv)
{
  bool found_candidate;
  uint32_t i;
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

  mm       = slv->btor->mm;
  f_solver = slv->f_solver;
  e_solver = slv->e_solver;

  map                = btor_new_node_map (f_solver);
  var_es_assignments = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv, (BtorCmpPtr) btor_compare_bv);
  BTOR_INIT_STACK (inputs);

  /* map f_exists_vars to e_exists_vars */
  btor_init_node_map_iterator (&it, slv->e_exists_vars);
  btor_queue_node_map_iterator (&it, slv->e_exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var_es = btor_next_node_map_iterator (&it);
    btor_map_node (map, var_fs, var_es);
  }

  if (btor_get_opt (slv->btor, BTOR_OPT_EF_SYMQINST) && e_solver->bv_model)
  {
    for (i = 1; i < BTOR_COUNT_STACK (e_solver->nodes_id_table); i++)
    {
      var_es = BTOR_PEEK_STACK (e_solver->nodes_id_table, i);

      if (!var_es || !BTOR_IS_BV_VAR_NODE (var_es)) continue;

      if (!var_es || BTOR_IS_BV_CONST_NODE (var_es) || BTOR_IS_FUN_NODE (var_es)
          || BTOR_IS_ARGS_NODE (var_es) || !BTOR_IS_SYNTH_NODE (var_es)
          || BTOR_IS_PROXY_NODE (var_es))
        continue;

      BTOR_PUSH_STACK (mm, inputs, var_es);
    }

    if (BTOR_COUNT_STACK (inputs) > 0)
    {
      sig = btor_new_bv_tuple (mm, BTOR_COUNT_STACK (inputs));
      for (i = 0; i < BTOR_COUNT_STACK (inputs); i++)
      {
        var_es = BTOR_PEEK_STACK (inputs, i);
        bv     = btor_get_bv_model (e_solver, var_es);
        btor_add_to_bv_tuple (mm, sig, bv, i);
      }
    }
    else
      sig = 0;
  }

  BTOR_INIT_STACK (consts);
  /* map f_forall_vars to resp. assignment */
#ifdef PRINT_DBG
  printf ("found counter example\n");
#endif
  btor_init_node_map_iterator (&it, slv->f_forall_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = btor_next_node_map_iterator (&it);
    bv     = btor_get_bv_model (f_solver, btor_simplify_exp (f_solver, var_fs));
#ifdef PRINT_DBG
    printf ("%s := ", node2string (var_fs));
    btor_print_bv (bv);
#endif

    found_candidate = false;
    if (sig)
    {
      model = btor_new_ptr_hash_table (mm,
                                       (BtorHashPtr) btor_hash_bv_tuple,
                                       (BtorCmpPtr) btor_compare_bv_tuple);
      assert (sig);
      btor_add_ptr_hash_table (model, sig)->data.as_ptr = (BtorBitVector *) bv;
      synth_fun = btor_synthesize_fun (e_solver, 0, model, 0, 0, 0, 100000, 0);
      btor_delete_ptr_hash_table (model);
      if (synth_fun)
      {
        inst_exp = btor_apply_and_reduce (
            e_solver, BTOR_COUNT_STACK (inputs), inputs.start, synth_fun);
        btor_dump_smt2_node (e_solver, stdout, inst_exp, -1);
        btor_map_node (map, var_fs, inst_exp);
        found_candidate = true;
      }
    }

    if (found_candidate) continue;
#if 1
    if ((b = btor_get_ptr_hash_table (var_es_assignments, (void *) bv)))
    {
      btor_map_node (map, var_fs, b->data.as_ptr);
    }
    else
    {
#ifdef PRINT_DBG
      printf ("%s := ",
              node2string (btor_mapped_node (slv->f_forall_vars, var_fs)));
      btor_print_bv (bv);
#endif
      c = btor_const_exp (e_solver, (BtorBitVector *) bv);
      btor_map_node (map, var_fs, c);
      BTOR_PUSH_STACK (mm, consts, c);
    }
#endif
  }

  assert (f_solver->unsynthesized_constraints->count == 0);
  assert (f_solver->synthesized_constraints->count == 0);
  assert (f_solver->embedded_constraints->count == 0);
  assert (f_solver->varsubst_constraints->count == 0);
  res = build_refinement (
      f_solver, e_solver, BTOR_INVERT_NODE (slv->f_formula), map);

  while (!BTOR_EMPTY_STACK (consts))
    btor_release_exp (e_solver, BTOR_POP_STACK (consts));
  BTOR_RELEASE_STACK (mm, consts);

  BTOR_RELEASE_STACK (mm, inputs);
  btor_delete_ptr_hash_table (var_es_assignments);
  btor_delete_node_map (map);
  if (sig) btor_free_bv_tuple (mm, sig);
  assert (res != e_solver->true_exp);
  BTOR_ABORT (
      res == e_solver->true_exp, "invalid refinement '%s'", node2string (res));
  //  btor_set_opt (e_solver, BTOR_OPT_PRETTY_PRINT, 1);
  //  btor_dump_smt2_node (e_solver, stdout, res, -1);
  btor_assert_exp (e_solver, res);
  btor_release_exp (e_solver, res);
}

#if 0
static BtorNode *
invert_formula (Btor * btor)
{
  assert (btor->synthesized_constraints->count == 0);
  assert (btor->varsubst_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);

  BtorNode *cur, *root, *and;
  BtorPtrHashTable *t;
  BtorHashTableIterator it;

  root = 0;
  /* make conjunction of constraints and add negated formula */
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      t = (BtorPtrHashTable *) it.stack[it.pos];
      cur = btor_next_node_hash_table_iterator (&it);
      assert (btor_get_ptr_hash_table (t, cur));
      btor_remove_ptr_hash_table (t, cur, 0, 0);
      BTOR_REAL_ADDR_NODE (cur)->constraint = 0;
      if (root)
	{
	  and = btor_and_exp (btor, root, cur);
	  btor_release_exp (btor, root);
	  root = and;
	}
      else
	root = btor_copy_exp (btor, cur);
      btor_release_exp (btor, cur);
    }
  assert (btor->unsynthesized_constraints->count == 0);
  if (root)
    return BTOR_INVERT_NODE (root);
  return 0;
}

static void
get_failed_vars (BtorEFSolver * slv,
		 BtorPtrHashTable * failed_vars,
		 BtorPtrHashTable * failed_ufs)
{
  Btor *clone, *e_solver;
  BtorNodeIterator n_it;
  BtorNodeMapIterator it;
  BtorHashTableIterator hit;
  BtorNode *var, *c, *a, *var_clone, *root, *uf;
  BtorPtrHashTable *assumptions;
  const BtorBitVector *bv;
#ifndef NDEBUG
  BtorSolverResult result;
#endif

  e_solver = slv->e_solver;
  clone = btor_clone_formula (e_solver);
  btor_set_opt (clone, BTOR_OPT_AUTO_CLEANUP, 1);
  btor_set_opt (clone, BTOR_OPT_AUTO_CLEANUP_INTERNAL, 1);
  root = invert_formula (clone);
  assert (clone->varsubst_constraints->count == 0);
  assert (clone->embedded_constraints->count == 0);
  assert (clone->synthesized_constraints->count == 0);

  if (!root)
    {
      btor_delete_btor (clone);
      return;
    }

  assumptions = btor_new_ptr_hash_table (slv->btor->mm, 0, 0);
  btor_set_msg_prefix_btor (clone, "dp");
  clone->slv = btor_new_fun_solver (clone);
  btor_assert_exp (clone, root);

  btor_init_node_map_iterator (&it, slv->e_exists_vars);
  while (btor_has_next_node_map_iterator (&it))
    {
      var = btor_next_node_map_iterator (&it);
      var_clone = btor_get_node_by_id (clone, var->id);
      assert (BTOR_IS_REGULAR_NODE (var_clone));
      assert (BTOR_IS_BV_VAR_NODE (var_clone));
      bv = btor_get_bv_model (e_solver,
			      btor_simplify_exp (e_solver, var));
      assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (var_clone)));
      c = btor_const_exp (clone, (BtorBitVector *) bv);
      a = btor_eq_exp (clone, var_clone, c);
      btor_add_ptr_hash_table (assumptions, a)->data.as_ptr = var;
      btor_assume_exp (clone, a);
    }

  btor_init_node_map_iterator (&it, slv->e_exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
    {
      uf = btor_next_node_map_iterator (&it);
      btor_init_parent_iterator (&n_it, uf);
      while (btor_has_next_parent_iterator (&n_it))
	{
	  var = btor_next_parent_iterator (&n_it);
	  var_clone = btor_get_node_by_id (clone, var->id);
	  assert (BTOR_IS_APPLY_NODE (var));
	  bv = btor_get_bv_model (e_solver,
				  btor_simplify_exp (e_solver, var));
	  assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (var_clone)));
	  c = btor_const_exp (clone, (BtorBitVector *) bv);
	  a = btor_eq_exp (clone, var_clone, c);
	  btor_add_ptr_hash_table (assumptions, a)->data.as_ptr = uf;
	  btor_assume_exp (clone, a);
	}
    }

#ifndef NDEBUG
  result =
#endif
  clone->slv->api.sat (clone->slv);
  assert (result == BTOR_RESULT_UNSAT);

  btor_init_hash_table_iterator (&hit, assumptions);
  while (btor_has_next_hash_table_iterator (&hit))
    {
      var = hit.bucket->data.as_ptr;
      a = btor_next_hash_table_iterator (&hit);

      if (btor_failed_exp (clone, a))
	{
	  if (BTOR_IS_UF_NODE (var))
	    {
	      if (!btor_get_ptr_hash_table (failed_ufs, var))
		btor_add_ptr_hash_table (failed_ufs, var);
	    }
	  else
	    btor_add_ptr_hash_table (failed_vars, var);
	  printf ("failed: %s\n", node2string (var));
	}
    }
  btor_delete_ptr_hash_table (assumptions);
  btor_delete_btor (clone);
}
#endif

#if 0
      if (btor_get_opt (slv->btor, BTOR_OPT_EF_DUAL_PROP))
	{
	  failed_vars = btor_new_ptr_hash_table (slv->btor->mm, 0, 0);
	  failed_ufs = btor_new_ptr_hash_table (slv->btor->mm, 0, 0);
	  get_failed_vars (slv, failed_vars, failed_ufs);
	  e_model_vars = failed_vars;
	  e_model_ufs = failed_ufs;
	}
      else
	{
	  e_model_vars = e_exists_vars->table;

#if 0
	  failed_ufs = btor_new_ptr_hash_table (slv->btor->mm, 0, 0);
	  e_model_ufs = failed_ufs; //slv->e_exists_ufs->table;
	  analyze_candidate_model (e_solver, e_model_ufs);
#endif
	  e_model_ufs = slv->e_exists_ufs->table;
	}
#endif

#if 0
static void
analyze_counter_example2 (Btor * btor, BtorNode * root)
{
  assert (btor->last_sat_result == BTOR_RESULT_SAT);

  uint32_t i;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorNode *cur, *real_cur;
  BtorMemMgr *mm;
  const BtorBitVector *bv, *bv0, *bv1;

  mm = btor->mm;
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_POP_STACK (visit);
      real_cur = BTOR_REAL_ADDR_NODE (cur);

      if (btor_contains_int_hash_table (cache, real_cur->id)
	  || BTOR_IS_FUN_NODE (real_cur)
	  || BTOR_IS_ARGS_NODE (real_cur))
	continue;

      bv = btor_get_bv_model (btor, real_cur);
      if (BTOR_IS_APPLY_NODE (real_cur))
	printf ("xx visit: %s (%s) := ", node2string (real_cur), node2string (real_cur->e[0]));
      else
	printf ("xx visit: %s := ", node2string (real_cur));
      btor_print_bv (bv);

      btor_add_int_hash_table (cache, real_cur->id);

      if (BTOR_IS_AND_NODE (real_cur)
	  && btor_get_exp_width (btor, real_cur) == 1
	  && btor_is_false_bv (bv))
	{
	  bv0 = btor_get_bv_model (btor, real_cur->e[0]);
	  bv1 = btor_get_bv_model (btor, real_cur->e[1]);

	  if (btor_is_false_bv (bv0))
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
	  else if (btor_is_false_bv (bv1))
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
	}
      else
	for (i = 0; i < real_cur->arity; i++)
	  BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }

  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
}

static void
analyze_counter_example (Btor * btor, BtorNodeMap * vars, BtorNode * root)
{
  assert (btor->last_sat_result == BTOR_RESULT_SAT);

  Btor *clone;
  BtorNode *root_clone, *var, *var_clone, *c, *eq;
  BtorPtrHashTable model;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;
  BtorNodePtrStack assumptions;
  BtorMemMgr *mm;
  BtorSolverResult res;

  analyze_counter_example2 (btor, root);
  clone = btor_clone_formula (btor);
  root_clone = btor_get_node_by_id (clone, BTOR_REAL_ADDR_NODE (root)->id);
  btor_assume_exp (clone, root_clone);
  mm = clone->mm;

  BTOR_INIT_STACK (assumptions);
  btor_init_node_map_iterator (&it, vars);
  while (btor_has_next_node_map_iterator (&it))
    {
      var = btor_next_node_map_iterator (&it);
      var_clone = btor_get_node_by_id (clone, var->id);
      bv = btor_get_bv_model (btor, btor_simplify_exp (btor, var));
      printf ("%s := ", node2string (var));
      btor_print_bv (bv);
      c = btor_const_exp (clone, bv);
      eq = btor_eq_exp (clone, var_clone, c); 
      btor_release_exp (clone, c);
      btor_assume_exp (clone, eq);
      BTOR_PUSH_STACK (mm, assumptions, eq); 
    }

  res = btor_sat_btor (clone, -1, -1);

  if (res == BTOR_RESULT_SAT)
    analyze_counter_example2 (clone, root_clone);
  assert (res == BTOR_RESULT_UNSAT);

  btor_delete_btor (clone);
}
#endif

#if 0
static void
analyze_counter_example (Btor * btor, BtorNode * root)
{
  assert (btor->last_sat_result == BTOR_RESULT_SAT);

  uint32_t i;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorNode *cur, *real_cur;
  BtorMemMgr *mm;
  const BtorBitVector *bv, *bv0, *bv1;

  mm = btor->mm;
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_POP_STACK (visit);
      real_cur = BTOR_REAL_ADDR_NODE (cur);

      if (btor_contains_int_hash_table (cache, real_cur->id)
	  || BTOR_IS_FUN_NODE (real_cur)
	  || BTOR_IS_ARGS_NODE (real_cur))
	continue;

      bv = btor_get_bv_model (btor, real_cur);
      if (BTOR_IS_APPLY_NODE (real_cur))
	printf ("xx visit: %s (%s) := ", node2string (real_cur), node2string (real_cur->e[0]));
      else
	printf ("xx visit: %s := ", node2string (real_cur));
      btor_print_bv (bv);

      btor_add_int_hash_table (cache, real_cur->id);

      if (BTOR_IS_AND_NODE (real_cur)
	  && btor_get_exp_width (btor, real_cur) == 1
	  && btor_is_false_bv (bv))
	{
	  bv0 = btor_get_bv_model (btor, real_cur->e[0]);
	  bv1 = btor_get_bv_model (btor, real_cur->e[1]);

	  if (btor_is_false_bv (bv0))
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
	  else if (btor_is_false_bv (bv1))
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
	}
      else
	for (i = 0; i < real_cur->arity; i++)
	  BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }

  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
}

static void
analyze_candidate_model (Btor * btor, BtorPtrHashTable * ufs)
{
  assert (btor->last_sat_result == BTOR_RESULT_SAT);

  uint32_t i;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorNode *root, *cur, *real_cur;
  BtorMemMgr *mm;
  BtorHashTableIterator it;
  const BtorBitVector *bv, *bv0, *bv1;

  mm = btor->mm;
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      root = btor_next_node_hash_table_iterator (&it);
      BTOR_PUSH_STACK (mm, visit, root);
      printf ("root: %s\n", node2string (root));
    }
  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_POP_STACK (visit);
      real_cur = BTOR_REAL_ADDR_NODE (cur);

      if (BTOR_IS_UF_NODE (real_cur)
	  && !btor_get_ptr_hash_table (ufs, real_cur))
	{
	  printf ("FAILED UF: %s\n", node2string (real_cur));
	  btor_add_ptr_hash_table (ufs, real_cur);
	}

      if (btor_contains_int_hash_table (cache, real_cur->id)
	  || BTOR_IS_FUN_NODE (real_cur)
	  || BTOR_IS_ARGS_NODE (real_cur))
	continue;

      bv = btor_get_bv_model (btor, real_cur);
      if (BTOR_IS_APPLY_NODE (real_cur))
	printf ("visit: %s (%s) := ", node2string (real_cur), node2string (real_cur->e[0]));
      else
	printf ("visit: %s := ", node2string (real_cur));
      btor_print_bv (bv);

      btor_add_int_hash_table (cache, real_cur->id);
      if (BTOR_IS_AND_NODE (real_cur)
	  && btor_get_exp_width (btor, real_cur) == 1
	  && btor_is_false_bv (bv))
	{
	  bv0 = btor_get_bv_model (btor, real_cur->e[0]);
	  bv1 = btor_get_bv_model (btor, real_cur->e[1]);

	  if (btor_is_false_bv (bv0))
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
	  else if (btor_is_false_bv (bv1))
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
	}
      else
	for (i = 0; i < real_cur->arity; i++)
	  BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }

  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
}
#endif

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
    if (BTOR_IS_APPLY_NODE (cur))
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
filter_inputs (BtorEFSolver *slv, BtorNode *fs_uf, BtorPtrHashTable *inputs)
{
  uint32_t i, pos;
  BtorNode *cur;
  BtorNodeIterator it, iit;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;
  BtorHashTableIterator hit;

  //  printf ("*** %s\n", node2string (fs_uf));
  mm    = slv->btor->mm;
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

    //      printf ("mark: %s\n", node2string (cur));
    btor_add_int_hash_table (cache, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  btor_init_node_hash_table_iterator (&hit, inputs);
  while (btor_has_next_node_hash_table_iterator (&hit))
  {
    cur = btor_next_node_hash_table_iterator (&hit);
    if (!btor_contains_int_hash_table (cache, cur->id))
    {
      //	printf ("remove: %s\n", node2string (cur));
      btor_remove_ptr_hash_table (inputs, cur, 0, 0);
    }
  }
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
}

static void
prepare_inputs (BtorEFSolver *slv,
                BtorNode *fs_uf,
                BtorNodeMap *map,
                BtorPtrHashTable *inputs)
{
  BtorNode *cur, *cur_fs, *cur_mapped;
  BtorHashTableIterator it;
  const BtorPtrHashTable *m;
  BtorPtrHashTable *deps;
  Btor *e_solver;
  BtorMemMgr *mm;

  mm       = slv->btor->mm;
  deps     = btor_new_ptr_hash_table (mm, 0, 0);
  e_solver = slv->e_solver;

  btor_init_node_hash_table_iterator (&it, slv->e_exists_vars->table);
  btor_queue_node_hash_table_iterator (&it, slv->e_exists_ufs->table);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur    = btor_next_node_hash_table_iterator (&it);
    cur_fs = btor_mapped_node (
        BTOR_IS_BV_VAR_NODE (cur) ? slv->e_exists_vars : slv->e_exists_ufs,
        cur);
    cur_mapped = btor_mapped_node (map, cur_fs);
    if (!cur_mapped) continue;
    build_dependencies (mm, cur_fs, cur_mapped, deps);
  }

  btor_init_node_hash_table_iterator (&it, slv->e_exists_vars->table);
  btor_queue_node_hash_table_iterator (&it, slv->e_exists_ufs->table);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur    = btor_next_node_hash_table_iterator (&it);
    cur_fs = btor_mapped_node (
        BTOR_IS_BV_VAR_NODE (cur) ? slv->e_exists_vars : slv->e_exists_ufs,
        cur);

    if (cur_fs->id == fs_uf->id) continue;

#if 0
      cur_mapped = btor_mapped_node (map, cur_fs);
      if (cur_mapped)
	build_dependencies (e_solver, cur_fs, cur_mapped, deps);
#endif

    if (is_dependent (mm, fs_uf, cur_fs, deps))
    {
      //	  printf ("##### %s is dependent on %s\n", node2string (fs_uf),
      // node2string (cur_fs));
      continue;
    }

    //      printf ("input: %s\n", node2string (cur));
    if (BTOR_IS_BV_VAR_NODE (cur))
    {
      btor_add_ptr_hash_table (inputs, cur_fs)->data.as_ptr =
          (void *) btor_get_bv_model (e_solver, cur);
    }
    else
    {
      assert (BTOR_IS_UF_NODE (cur));
      assert (BTOR_IS_UF_NODE (cur_fs));
      m = btor_get_fun_model (e_solver, cur);
      if (m) btor_add_ptr_hash_table (inputs, cur_fs)->data.as_ptr = (void *) m;
    }
  }
  btor_init_hash_table_iterator (&it, deps);
  while (btor_has_next_hash_table_iterator (&it))
    btor_delete_ptr_hash_table (
        btor_next_data_hash_table_iterator (&it)->as_ptr);
  btor_delete_ptr_hash_table (deps);

  filter_inputs (slv, fs_uf, inputs);
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
  assert (BTOR_IS_FUN_NODE (exp));

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
  BtorNodeMapIterator it;

  btor = slv->btor;

  if (slv->e_exists_vars)
  {
    btor_init_node_map_iterator (&it, slv->e_exists_vars);
    while (btor_has_next_node_map_iterator (&it))
    {
      btor_release_exp (slv->e_solver, btor_next_node_map_iterator (&it));
    }
    btor_delete_node_map (slv->e_exists_vars);
  }

  if (slv->e_exists_ufs)
  {
    btor_init_node_map_iterator (&it, slv->e_exists_ufs);
    while (btor_has_next_node_map_iterator (&it))
    {
      btor_release_exp (slv->e_solver, btor_next_node_map_iterator (&it));
    }
    btor_delete_node_map (slv->e_exists_ufs);
  }

  if (slv->f_synth_fun_models)
  {
    btor_init_node_map_iterator (&it, slv->f_synth_fun_models);
    while (btor_has_next_node_map_iterator (&it))
      btor_release_exp (slv->f_solver,
                        btor_next_data_node_map_iterator (&it)->as_ptr);
    btor_delete_node_map (slv->f_synth_fun_models);
  }

  if (slv->f_exists_vars)
  {
    assert (slv->f_forall_vars);
    btor_init_node_map_iterator (&it, slv->f_exists_vars);
    btor_queue_node_map_iterator (&it, slv->f_forall_vars);
    while (btor_has_next_node_map_iterator (&it))
    {
      btor_release_exp (slv->f_solver, it.it.bucket->data.as_ptr);
      btor_release_exp (slv->f_solver, btor_next_node_map_iterator (&it));
    }
    btor_delete_node_map (slv->f_exists_vars);
    btor_delete_node_map (slv->f_forall_vars);
  }

  btor_release_exp (slv->f_solver, slv->f_formula);
  btor_delete_btor (slv->e_solver);
  btor_delete_btor (slv->f_solver);
  BTOR_DELETE (btor->mm, slv);
  btor->slv = 0;
}

static BtorNodeMap *
synthesize_model (BtorEFSolver *slv,
                  BtorPtrHashTable *synth_funs,
                  BtorPtrHashTable *synth_inputs)
{
  bool opt_synth_fun;
  uint32_t max_level;
  BtorNodeMap *model, *e_vars, *e_ufs;
  Btor *e_solver, *f_solver;
  BtorNode *e_var, *e_var_fs, *e_uf, *e_uf_fs, *synth_fun, *best_match;
  BtorNode *prev_synth_fun;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;
  const BtorPtrHashTable *uf_model;
  BtorPtrHashTable *inputs;
  BtorPtrHashBucket *b, *bb;
  double sum = 0;

  e_solver      = slv->e_solver;
  f_solver      = slv->f_solver;
  e_vars        = slv->e_exists_vars;
  e_ufs         = slv->e_exists_ufs;
  model         = btor_new_node_map (f_solver);
  opt_synth_fun = btor_get_opt (slv->btor, BTOR_OPT_EF_SYNTH) == 1;

  /* map existential variables to their resp. assignment */
  btor_init_node_map_iterator (&it, e_vars);
  while (btor_has_next_node_map_iterator (&it))
  {
    e_var    = btor_next_node_map_iterator (&it);
    e_var_fs = btor_mapped_node (e_vars, e_var);
    bv = btor_get_bv_model (e_solver, btor_simplify_exp (e_solver, e_var));
#ifdef PRINT_DBG
    printf ("exists %s := ", node2string (e_var));
    btor_print_bv (bv);
#endif
    assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (e_var_fs)));
    btor_map_node (model, e_var_fs, btor_const_exp (f_solver, bv));
  }

  /* map skolem functions to resp. synthesized functions */
  btor_init_node_map_iterator (&it, e_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    e_uf     = btor_next_node_map_iterator (&it);
    e_uf_fs  = btor_mapped_node (e_ufs, e_uf);
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
    double start = btor_time_stamp ();
    best_match   = 0;
    b            = btor_get_ptr_hash_table (synth_funs, e_uf_fs);
    if (opt_synth_fun)
    {
      bb     = btor_get_ptr_hash_table (synth_inputs, e_uf_fs);
      inputs = btor_new_ptr_hash_table (f_solver->mm, 0, 0);
      prepare_inputs (slv, e_uf_fs, model, inputs);

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
      if (bb)
        btor_delete_ptr_hash_table (bb->data.as_ptr);
      else
        bb = btor_add_ptr_hash_table (synth_inputs, e_uf_fs);
      bb->data.as_ptr = inputs;
      //	  btor_delete_ptr_hash_table (inputs);
    }
    else
      synth_fun = 0;

    if (!b) b = btor_add_ptr_hash_table (synth_funs, e_uf_fs);

    if (!synth_fun)
    {
      printf ("NO CANDIDATE FOUND for %s in %.2fs\n",
              node2string (e_uf_fs),
              btor_time_stamp () - start);
      slv->stats.synth_aborts++;
      // FIXME: using best_match only oftern produces true_exp refinements
      if (false && best_match)
      {
        printf ("USE BEST MATCH\n");
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
      printf ("CANDIDATE FOUND for %s in %.2fs\n",
              node2string (e_uf_fs),
              btor_time_stamp () - start);
      if (b->data.as_ptr != synth_fun)
      {
        printf ("NEW\n");
        slv->stats.synth_funs++;
      }
      else
      {
        printf ("NOT CHANGED\n");
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
    assert (e_uf_fs->sort_id == synth_fun->sort_id);
    //      btor_dump_smt2_node (f_solver, stdout, synth_fun, -1);
    btor_map_node (model, e_uf_fs, synth_fun);
    sum += btor_time_stamp () - start;
  }
  printf ("SUM: %.2f\n", sum);
  return model;
}

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

static BtorSolverResult
sat_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  double start;
  Btor *e_solver, *f_solver;
  BtorSolverResult res;
  BtorNode *g, *cur_uf, *cur_synth_fun;
  BtorNodeMap *map;
  BtorHashTableIterator it;
  BtorPtrHashTable *synth_funs, *synth_inputs;
  BtorNodeMap *synth_fun_model;

  // TODO (ma): incremental support
  setup_forall_solver (slv);
  setup_exists_solver (slv);

  e_solver     = slv->e_solver;
  f_solver     = slv->f_solver;
  synth_funs   = btor_new_ptr_hash_table (f_solver->mm, 0, 0);
  synth_inputs = btor_new_ptr_hash_table (f_solver->mm, 0, 0);

  btor_set_opt (f_solver, BTOR_OPT_PRETTY_PRINT, 1);
  g = btor_copy_exp (f_solver, slv->f_formula);
  goto CHECK_FORALL;

  while (true)
  {
    start = btor_time_stamp ();
    res   = btor_sat_btor (e_solver, -1, -1);
    slv->time.e_solver += btor_time_stamp () - start;

    if (res == BTOR_RESULT_UNSAT) /* formula is UNSAT */
      break;

    assert (res == BTOR_RESULT_SAT);
    e_solver->slv->api.generate_model (e_solver->slv, false, false);

    start = btor_time_stamp ();
    printf (
        "**************************** NEW ITERATION "
        "*****************************\n");
    map = synthesize_model (slv, synth_funs, synth_inputs);
    slv->time.synth += btor_time_stamp () - start;
    g = btor_substitute_terms (f_solver, slv->f_formula, map);
    delete_exists_model (map);

  CHECK_FORALL:
    btor_assume_exp (f_solver, g);
    btor_release_exp (f_solver, g);

    start = btor_time_stamp ();
    res   = btor_sat_btor (f_solver, -1, -1);
    slv->time.f_solver += btor_time_stamp () - start;
    if (res == BTOR_RESULT_UNSAT) /* formula is SAT */
    {
      // TODO: map contains the actual model need to pass it to
      // f_synth_fun_models?
      res = BTOR_RESULT_SAT;
      break;
    }

    f_solver->slv->api.generate_model (f_solver->slv, false, false);
    start = btor_time_stamp ();
    refine_exists_solver (slv);
    slv->time.qinst += btor_time_stamp () - start;
    slv->stats.refinements++;
  }
#if 0
  if (res == BTOR_RESULT_SAT && synth_fun_model)
    {
      /* increment reference counts for UF models */
      btor_init_node_map_iterator (&it, synth_fun_model);
      while (btor_has_next_node_map_iterator (&it))
	(void) btor_copy_exp (f_solver,
		   btor_next_data_node_map_iterator (&it)->as_ptr);
      slv->f_synth_fun_models = synth_fun_model;
    }
  btor_init_node_hash_table_iterator (&hit, synth_fun_cache);
  while (btor_has_next_node_hash_table_iterator (&hit))
    btor_release_exp (f_solver, btor_next_node_hash_table_iterator (&hit));
  btor_delete_ptr_hash_table (synth_fun_cache);
#endif
  btor_init_node_hash_table_iterator (&it, synth_funs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur_synth_fun = btor_next_data_node_hash_table_iterator (&it)->as_ptr;
    if (cur_synth_fun) btor_release_exp (f_solver, cur_synth_fun);
  }
  btor_init_node_hash_table_iterator (&it, synth_inputs);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_delete_ptr_hash_table (
        btor_next_data_node_hash_table_iterator (&it)->as_ptr);
  btor_delete_ptr_hash_table (synth_funs);
  btor_delete_ptr_hash_table (synth_inputs);
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

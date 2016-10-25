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

#include <pthread.h>
#include <signal.h>
#include <unistd.h>

struct BtorEFGroundSolvers
{
  Btor *forall; /* solver for checking the model */
  BtorNode *forall_formula;
  BtorNodeMap *forall_evars;     /* existential vars (map to skolem
                                    constants of exists solver) */
  BtorNodeMap *forall_uvars;     /* universal vars map to fresh bv vars */
  BtorNodeMap *forall_evar_deps; /* existential vars map to argument nodes
                                    of universal vars */
  BtorNodePtrStack forall_consts;
  BtorPtrHashTable *forall_synth_model; /* currently synthesized model for
                                         existential vars */
  BtorPtrHashTable *forall_ces;         /* counter examples */
  BtorBitVectorTuple *forall_last_ce;
  BtorNodeMap *forall_skolem; /* skolem functions for evars */

  Btor *exists;              /* solver for computing the model */
  BtorNodeMap *exists_evars; /* skolem constants (map to existential
                                vars of forall solver) */
  BtorNodeMap *exists_ufs;   /* UFs (non-skolem constants), map to UFs
                                of forall solver */
  BtorSolverResult result;

  BtorEFStats *statistics;
};

typedef struct BtorEFGroundSolvers BtorEFGroundSolvers;

BTOR_DECLARE_STACK (BtorBitVectorTuplePtr, BtorBitVectorTuple *);

/*------------------------------------------------------------------------*/

struct SynthResult
{
  bool partial;
  uint32_t limit;
  BtorNode *value;
};

typedef struct SynthResult SynthResult;

static SynthResult *
new_synth_result (BtorMemMgr *mm)
{
  SynthResult *res;
  BTOR_CNEW (mm, res);
  return res;
}

static void
delete_synth_result (BtorMemMgr *mm, SynthResult *res)
{
  BtorNode *cur;

  if (res->value)
  {
    cur = BTOR_REAL_ADDR_NODE (res->value);
    btor_release_exp (cur->btor, cur);
  }
  BTOR_DELETE (mm, res);
}

/*------------------------------------------------------------------------*/

struct FlatModel
{
  BtorMemMgr *mm;
  BtorPtrHashTable *model;
  BtorIntHashTable *uvar_index_map;
  BtorIntHashTable *evar_index_map;
};

typedef struct FlatModel FlatModel;

static BtorBitVector *
flat_model_get_value (FlatModel *flat_model,
                      BtorNode *var,
                      BtorBitVectorTuple *ce)
{
  uint32_t i;
  BtorBitVectorTuple *t;
  BtorPtrHashBucket *b;
  BtorBitVector *res;

  if (btor_param_is_exists_var (var))
  {
    i = btor_get_int_hash_map (flat_model->evar_index_map, var->id)->as_int;
    if (ce)
    {
      b = btor_get_ptr_hash_table (flat_model->model, ce);
      assert (b);
      t   = b->data.as_ptr;
      res = t->bv[i];
    }
    else
    {
      b = flat_model->model->first;
      assert (b);
      t   = b->data.as_ptr;
      res = t->bv[i];
      /* value of 'var' is the same for every ce (outermost var) */
#ifndef NDEBUG
      BtorHashTableIterator it;
      BtorBitVectorTuple *tup;
      btor_init_hash_table_iterator (&it, flat_model->model);
      while (btor_has_next_hash_table_iterator (&it))
      {
        tup = it.bucket->data.as_ptr;
        (void) btor_next_hash_table_iterator (&it);
        assert (btor_compare_bv (res, tup->bv[i]) == 0);
      }
#endif
    }
  }
  else
  {
    assert (ce);
    assert (btor_param_is_forall_var (var));
    i   = btor_get_int_hash_map (flat_model->uvar_index_map, var->id)->as_int;
    res = ce->bv[i];
  }
  return res;
}

static FlatModel *
flat_model_generate (BtorEFGroundSolvers *gslv)
{
  bool free_bv;
  uint32_t i, j, pos, nevars;
  Btor *e_solver, *f_solver;
  BtorNode *cur, *e_evar, *f_evar, *args;
  BtorHashTableIterator it;
  BtorNodeMapIterator nit;
  BtorBitVectorTuple *ce, *mtup, *evar_values;
  const BtorPtrHashTable *m;
  BtorBitVector *bv;
  BtorArgsIterator ait;
  BtorPtrHashBucket *b;
  BtorMemMgr *mm;
  FlatModel *flat_model;

  e_solver = gslv->exists;
  f_solver = gslv->forall;
  mm       = e_solver->mm;
  BTOR_CNEW (mm, flat_model);
  flat_model->mm    = mm;
  flat_model->model = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv_tuple, (BtorCmpPtr) btor_compare_bv_tuple);
  flat_model->uvar_index_map = btor_new_int_hash_map (mm);
  flat_model->evar_index_map = btor_new_int_hash_map (mm);

  nevars = gslv->exists_evars->table->count;

  i = 0;
  btor_init_node_map_iterator (&nit, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&nit))
  {
    cur = btor_next_node_map_iterator (&nit);
    btor_add_int_hash_map (flat_model->uvar_index_map, cur->id)->as_int = i++;
  }

  i = 0;
  btor_init_node_map_iterator (&nit, gslv->forall_evars);
  while (btor_has_next_node_map_iterator (&nit))
  {
    cur = btor_next_node_map_iterator (&nit);
    btor_add_int_hash_map (flat_model->evar_index_map, cur->id)->as_int = i++;
  }

  /* generate model for exists vars/ufs */
  assert (e_solver->last_sat_result == BTOR_RESULT_SAT);
  e_solver->slv->api.generate_model (e_solver->slv, false, false);

  btor_init_hash_table_iterator (&it, gslv->forall_ces);
  while (btor_has_next_hash_table_iterator (&it))
  {
    ce = btor_next_hash_table_iterator (&it);

    pos         = 0;
    evar_values = btor_new_bv_tuple (mm, nevars);
    btor_init_node_map_iterator (&nit, gslv->forall_evars);
    while (btor_has_next_node_map_iterator (&nit))
    {
      e_evar = nit.it.bucket->data.as_ptr;
      f_evar = btor_next_node_map_iterator (&nit);

      free_bv = false;
      if ((args = btor_mapped_node (gslv->forall_evar_deps, f_evar)))
      {
        bv = 0;
        m  = btor_get_fun_model (e_solver, e_evar);
        if (m)
        {
          mtup = btor_new_bv_tuple (mm, btor_get_args_arity (f_solver, args));
          j    = 0;
          btor_init_args_iterator (&ait, args);
          while (btor_has_next_args_iterator (&ait))
          {
            cur = btor_next_args_iterator (&ait);
            i   = btor_get_int_hash_map (flat_model->uvar_index_map, cur->id)
                    ->as_int;
            btor_add_to_bv_tuple (mm, mtup, ce->bv[i], j++);
          }
          b = btor_get_ptr_hash_table ((BtorPtrHashTable *) m, mtup);
          btor_free_bv_tuple (mm, mtup);
          if (b) bv = b->data.as_ptr;
        }
        if (!bv)
        {
          free_bv = true;
          bv      = btor_new_bv (mm, btor_get_exp_width (f_solver, f_evar));
        }
      }
      else
      {
        assert (btor_param_is_exists_var (f_evar));
        bv = (BtorBitVector *) btor_get_bv_model (
            e_solver, btor_simplify_exp (e_solver, e_evar));
      }
      btor_add_to_bv_tuple (mm, evar_values, bv, pos++);
      if (free_bv) btor_free_bv (mm, bv);
    }
    btor_add_ptr_hash_table (flat_model->model, ce)->data.as_ptr = evar_values;
  }
  return flat_model;
}

/*------------------------------------------------------------------------*/

static bool g_measure_thread_time = false;

static double
time_stamp (void)
{
  if (g_measure_thread_time) return btor_process_time_thread ();
  return btor_time_stamp ();
}

/*------------------------------------------------------------------------*/

static void
underapprox (Btor *btor, BtorPtrHashTable *vars, BtorPtrHashTable *assumptions)
{
  uint32_t w, upper;
  BtorNode *var, *eq, *s, *z;
  BtorHashTableIterator it;

  btor_init_node_hash_table_iterator (&it, vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    upper = it.bucket->data.as_int;
    var   = btor_next_node_hash_table_iterator (&it);
    w     = btor_get_exp_width (btor, var) - 1;
    if (w >= upper + 1)
    {
      s  = btor_slice_exp (btor, var, w, upper + 1);
      z  = btor_zero_exp (btor, w - upper);
      eq = btor_eq_exp (btor, s, z);
      btor_release_exp (btor, z);
      btor_release_exp (btor, s);
      if (!btor_get_ptr_hash_table (assumptions, eq))
      {
        btor_assume_exp (btor, eq);
        btor_add_ptr_hash_table (assumptions, eq)->data.as_ptr = var;
      }
      else
        btor_release_exp (btor, eq);
    }
  }
}

static bool
underapprox_check (Btor *btor,
                   BtorPtrHashTable *vars,
                   BtorPtrHashTable *assumptions,
                   BtorNode *root)
{
  bool res = true;
  BtorNode *cur, *var;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;

  btor_init_node_hash_table_iterator (&it, assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    var = it.bucket->data.as_ptr;
    cur = btor_next_node_hash_table_iterator (&it);
    if (btor_failed_exp (btor, cur))
    {
      b = btor_get_ptr_hash_table (vars, var);
      assert (b);
      /* increase bit-width of var */
      b->data.as_int = b->data.as_int * 2;
      printf ("FAILED: %s\n", node2string (cur));
      res = false;
    }
  }

  if (!res && root)
  {
    btor_assume_exp (btor, BTOR_INVERT_NODE (root));
    res = btor_sat_btor (btor, -1, -1) == BTOR_RESULT_UNSAT;
  }

  return res;
}

static void
underapprox_release (Btor *btor, BtorPtrHashTable *assumptions)
{
  BtorHashTableIterator it;

  btor_init_node_hash_table_iterator (&it, assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (assumptions);
}

/*------------------------------------------------------------------------*/

static void
print_cur_model (BtorEFGroundSolvers *gslv)
{
  BtorNode *cur;
  BtorHashTableIterator it;
  SynthResult *synth_res;

  if (!gslv->forall_synth_model) return;

  btor_init_node_hash_table_iterator (&it, gslv->forall_synth_model);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    synth_res = it.bucket->data.as_ptr;
    cur       = btor_next_node_hash_table_iterator (&it);
    assert (btor_is_uf_node (cur) || btor_param_is_exists_var (cur));
    printf ("\nmodel for %s\n", btor_get_symbol_exp (gslv->forall, cur));
    btor_dump_smt2_node (gslv->forall, stdout, synth_res->value, -1);
  }
}

static void
delete_model (BtorEFGroundSolvers *gslv)
{
  BtorNode *cur;
  BtorHashTableIterator it;
  SynthResult *synth_res;

  if (!gslv->forall_synth_model) return;

  btor_init_node_hash_table_iterator (&it, gslv->forall_synth_model);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    synth_res = it.bucket->data.as_ptr;
    cur       = btor_next_node_hash_table_iterator (&it);
    assert (btor_is_uf_node (cur) || btor_param_is_exists_var (cur));
    delete_synth_result (gslv->forall->mm, synth_res);
  }
  btor_delete_ptr_hash_table (gslv->forall_synth_model);
  gslv->forall_synth_model = 0;
}

/* compute dependencies between existential variables and universal variables.
 * 'deps' maps existential variables to a list of universal variables by means
 * of an argument node.
 */
BtorNodeMap *
compute_edeps (Btor *btor, BtorNode *root)
{
  uint32_t i;
  BtorNode *cur, *real_cur, *q, *args;
  BtorNodePtrStack visit, quants, uvars;
  BtorMemMgr *mm;
  BtorIntHashTable *map;
  BtorHashTableData *d;
  BtorNodeMap *deps;

  mm = btor->mm;

  BTOR_INIT_STACK (uvars);
  BTOR_INIT_STACK (quants);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  map  = btor_new_int_hash_map (mm);
  deps = btor_new_node_map (btor);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (map, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (map, real_cur->id);

      if (btor_is_forall_node (real_cur)) BTOR_PUSH_STACK (mm, quants, cur);

      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (btor_is_exists_node (real_cur) && !BTOR_EMPTY_STACK (quants))
      {
        /* create dependency of 'real_cur' with all universal vars of
         * 'quants' */
        for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
        {
          q = BTOR_PEEK_STACK (quants, i);
          BTOR_PUSH_STACK (mm, uvars, BTOR_REAL_ADDR_NODE (q)->e[0]);
        }

        args = btor_args_exp (btor, uvars.start, BTOR_COUNT_STACK (uvars));
        btor_map_node (deps, real_cur->e[0], args);
        btor_release_exp (btor, args);
        BTOR_RESET_STACK (uvars);
      }
      else if (btor_is_forall_node (real_cur))
      {
        q = BTOR_POP_STACK (quants);
        assert (q == cur);
      }
    }
  }
  btor_delete_int_hash_map (map);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, quants);
  BTOR_RELEASE_STACK (mm, uvars);
  return deps;
}

static BtorNode *
mk_dual_formula (Btor *btor,
                 Btor *dual_btor,
                 BtorNode *root,
                 BtorNodeMap *var_map,
                 BtorNodeMap *dual_var_map)
{
  assert (var_map);
  assert (dual_var_map);

  char *sym;
  size_t j;
  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, **e, *body;
  BtorNodePtrStack stack, args;
  BtorIntHashTable *map, *inv;
  BtorHashTableData *d;
  BtorSortId sortid;

  mm  = btor->mm;
  map = btor_new_int_hash_map (mm);
  inv = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (args);
  BTOR_PUSH_STACK (mm, stack, root);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_map (map, real_cur->id)) continue;

    btor_add_int_hash_map (map, real_cur->id);

    if (btor_is_quantifier_node (real_cur))
    {
      body = BTOR_REAL_ADDR_NODE (btor_binder_get_body (real_cur));
      btor_add_int_hash_table (inv, body->id);
    }
    else
    {
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
  }

  btor_delete_int_hash_map (map);
  map = btor_new_int_hash_map (mm);

  BTOR_RESET_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, root);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    d        = btor_get_int_hash_map (map, real_cur->id);

    if (!d)
    {
      btor_add_int_hash_table (map, real_cur->id);

      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      /* bit vector variables should be existentially quantified */
      assert (!btor_is_bv_var_node (real_cur));
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_is_param_node (real_cur))
        {
          sym    = btor_get_symbol_exp (btor, real_cur);
          result = btor_param_exp (
              dual_btor, btor_get_exp_width (btor, real_cur), sym);

          if (btor_param_is_forall_var (real_cur)
              || btor_param_is_exists_var (real_cur))
          {
            btor_map_node (var_map, real_cur, result);
            btor_map_node (dual_var_map, result, real_cur);
          }
        }
        else if (btor_is_bv_const_node (real_cur))
          result = btor_const_exp (dual_btor, btor_const_get_bits (real_cur));
        else
        {
          assert (btor_is_uf_node (real_cur));
          sortid = btor_recursively_rebuild_sort_clone (
              btor, dual_btor, real_cur->sort_id);
          result = btor_uf_exp (dual_btor, sortid, 0);
          btor_release_sort (&dual_btor->sorts_unique_table, sortid);
        }
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (dual_btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      /* invert quantifier nodes */
      else if (btor_is_quantifier_node (real_cur))
      {
        result = btor_create_exp (dual_btor,
                                  real_cur->kind == BTOR_EXISTS_NODE
                                      ? BTOR_FORALL_NODE
                                      : BTOR_EXISTS_NODE,
                                  e,
                                  real_cur->arity);
      }
      else
        result =
            btor_create_exp (dual_btor, real_cur->kind, e, real_cur->arity);

      d->as_ptr = btor_copy_exp (dual_btor, result);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (dual_btor, e[i]);
    PUSH_RESULT:
      /* quantifiers are never negated (but flipped) */
      if (!btor_is_quantifier_node (real_cur))
        result = BTOR_COND_INVERT_NODE (cur, result);
      /* invert body */
      if (btor_contains_int_hash_table (inv, real_cur->id))
        result = BTOR_INVERT_NODE (result);
      BTOR_PUSH_STACK (mm, args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (dual_btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, args);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_release_exp (dual_btor, map->data[j].as_ptr);
  }
  btor_delete_int_hash_map (map);
  btor_delete_int_hash_table (inv);

  if (!btor_is_quantifier_node (root)) result = BTOR_INVERT_NODE (result);

  return result;
}

static void
collect_consts (Btor *btor, BtorNode *root, BtorNodePtrStack *consts)
{
  uint32_t i;
  int32_t id;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorNode *cur, *real_cur;
  BtorMemMgr *mm;

  mm    = btor->mm;
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    id = btor_is_bv_const_node (real_cur) ? BTOR_GET_ID_NODE (cur)
                                          : real_cur->id;

    if (btor_contains_int_hash_table (cache, id)) continue;

    if (btor_is_bv_const_node (real_cur)) BTOR_PUSH_STACK (mm, *consts, cur);

    btor_add_int_hash_table (cache, id);
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (cache);
}

static BtorEFGroundSolvers *
setup_efg_solvers (BtorEFSolver *slv,
                   BtorNode *root,
                   bool setup_dual,
                   const char *prefix_forall,
                   const char *prefix_exists,
                   BtorNodeMap *var_map,
                   BtorNodeMap *dual_var_map)
{
  uint32_t width;
  char *sym;
  BtorEFGroundSolvers *res;
  BtorNode *cur, *var, *tmp;
  BtorHashTableIterator it;
  BtorFunSolver *fslv;
  BtorNodeMap *exp_map;
  Btor *btor;
  BtorSortUniqueTable *sorts;
  BtorSortId dsortid, cdsortid, funsortid;
  BtorMemMgr *mm;
  BtorPtrHashTable *forall_ufs;

  btor       = slv->btor;
  mm         = btor->mm;
  forall_ufs = btor_new_ptr_hash_table (mm, 0, 0);
  BTOR_CNEW (mm, res);

  /* new forall solver */
  res->result = BTOR_RESULT_UNKNOWN;
  res->forall = btor_new_btor ();
  btor_delete_opts (res->forall);
  btor_clone_opts (btor, res->forall);
  btor_set_msg_prefix_btor (res->forall, prefix_forall);

  /* configure options */
  btor_set_opt (res->forall, BTOR_OPT_MODEL_GEN, 1);
  btor_set_opt (res->forall, BTOR_OPT_INCREMENTAL, 1);

  if (setup_dual)
  {
    assert (var_map);
    assert (dual_var_map);

    root = mk_dual_formula (BTOR_REAL_ADDR_NODE (root)->btor,
                            res->forall,
                            root,
                            var_map,
                            dual_var_map);
  }
  else
  {
    exp_map = btor_new_node_map (btor);
    tmp     = btor_recursively_rebuild_exp_clone (
        btor,
        res->forall,
        root,
        exp_map,
        btor_get_opt (res->forall, BTOR_OPT_REWRITE_LEVEL));
    /* all bv vars are quantified with exists */
    assert (res->forall->bv_vars->count == 0);
    btor_delete_node_map (exp_map);
    root = tmp;
  }
  assert (!btor_is_proxy_node (root));

  //  btor_dump_smt2_node (res->forall, stdout, root, -1);
  res->forall_formula   = root;
  res->forall_evar_deps = compute_edeps (res->forall, root);
  res->forall_evars     = btor_new_node_map (res->forall);
  res->forall_uvars     = btor_new_node_map (res->forall);
  res->forall_skolem    = btor_new_node_map (res->forall);
  res->forall_ces =
      btor_new_ptr_hash_table (res->forall->mm,
                               (BtorHashPtr) btor_hash_bv_tuple,
                               (BtorCmpPtr) btor_compare_bv_tuple);
  collect_consts (res->forall, res->forall_formula, &res->forall_consts);
  sorts = &res->forall->sorts_unique_table;

  /* store UFs in a separate table for later */
  btor_init_node_hash_table_iterator (&it, res->forall->ufs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    btor_add_ptr_hash_table (forall_ufs, cur);
  }

  /* map fresh bit vector vars to universal vars */
  btor_init_node_hash_table_iterator (&it, res->forall->forall_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_param_is_forall_var (cur));
    var = btor_var_exp (res->forall, btor_get_exp_width (res->forall, cur), 0);
    btor_map_node (res->forall_uvars, cur, var);
    btor_release_exp (res->forall, var);
  }

  /* map fresh skolem constants to existential vars */
  btor_init_node_hash_table_iterator (&it, res->forall->exists_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_param_is_exists_var (cur));

    tmp = btor_mapped_node (res->forall_evar_deps, cur);
    if (tmp)
    {
      funsortid = btor_fun_sort (sorts, tmp->sort_id, cur->sort_id);
      var       = btor_uf_exp (res->forall, funsortid, 0);
      btor_release_sort (sorts, funsortid);
    }
    else
      var =
          btor_var_exp (res->forall, btor_get_exp_width (res->forall, cur), 0);

    btor_map_node (res->forall_skolem, cur, var);
    btor_release_exp (res->forall, var);
  }

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

  /* create ground solver for exists */
  res->exists->slv  = btor_new_fun_solver (res->exists);
  res->exists_evars = btor_new_node_map (res->exists);
  res->exists_ufs   = btor_new_node_map (res->exists);
  sorts             = &res->exists->sorts_unique_table;

  /* map evars of exists solver to evars of forall solver */
  btor_init_node_hash_table_iterator (&it, res->forall->exists_vars);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_param_is_exists_var (cur));
    width = btor_get_exp_width (res->forall, cur);
    sym   = btor_get_symbol_exp (res->forall, cur);
    //      printf ("evar: %s\n", node2string (cur));

    if ((tmp = btor_mapped_node (res->forall_evar_deps, cur)))
    {
      /* 'tmp' is an argument node that holds all universal dependencies of
       * existential variable 'cur'*/
      assert (btor_is_args_node (tmp));

      cdsortid = btor_bitvec_sort (sorts, width);
      dsortid  = btor_recursively_rebuild_sort_clone (
          res->forall, res->exists, tmp->sort_id);
      funsortid = btor_fun_sort (sorts, dsortid, cdsortid);
      var       = btor_uf_exp (res->exists, funsortid, sym);
      btor_release_sort (sorts, cdsortid);
      btor_release_sort (sorts, dsortid);
      btor_release_sort (sorts, funsortid);
    }
    else
      var = btor_var_exp (res->exists, width, sym);
    btor_map_node (res->exists_evars, var, cur);
    btor_map_node (res->forall_evars, cur, var);
    btor_release_exp (res->exists, var);
  }

  /* map ufs of exists solver to ufs of forall solver */
  btor_init_node_hash_table_iterator (&it, forall_ufs);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur       = btor_next_node_hash_table_iterator (&it);
    funsortid = btor_recursively_rebuild_sort_clone (
        res->forall, res->exists, cur->sort_id);
    var = btor_uf_exp (
        res->exists, funsortid, btor_get_symbol_exp (res->forall, cur));
    btor_release_sort (sorts, funsortid);
    btor_map_node (res->exists_ufs, var, cur);
    btor_release_exp (res->exists, var);
  }
  btor_delete_ptr_hash_table (forall_ufs);

  return res;
}

static void
delete_efg_solvers (BtorEFSolver *slv, BtorEFGroundSolvers *gslv)
{
  BtorHashTableIterator it;
  BtorBitVectorTuple *ce;

  /* delete exists solver */
  btor_delete_node_map (gslv->exists_evars);
  btor_delete_node_map (gslv->exists_ufs);

  /* delete forall solver */
  delete_model (gslv);
  btor_delete_node_map (gslv->forall_evars);
  btor_delete_node_map (gslv->forall_uvars);
  btor_delete_node_map (gslv->forall_evar_deps);
  btor_delete_node_map (gslv->forall_skolem);

  btor_init_hash_table_iterator (&it, gslv->forall_ces);
  while (btor_has_next_hash_table_iterator (&it))
  {
    ce = btor_next_hash_table_iterator (&it);
    btor_free_bv_tuple (gslv->forall->mm, ce);
  }
  btor_delete_ptr_hash_table (gslv->forall_ces);
  BTOR_RELEASE_STACK (gslv->forall->mm, gslv->forall_consts);

  btor_release_exp (gslv->forall, gslv->forall_formula);
  btor_delete_btor (gslv->forall);
  btor_delete_btor (gslv->exists);
  BTOR_DELETE (slv->btor->mm, gslv);
}

static BtorNode *
build_refinement (Btor *btor, BtorNode *root, BtorNodeMap *map)
{
  assert (btor);
  assert (root);
  assert (map);

  size_t j;
  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, **e;
  BtorNodePtrStack visit, args;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm   = btor->mm;
  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_PUSH_STACK (mm, visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!btor_is_proxy_node (real_cur));

    if ((result = btor_mapped_node (map, real_cur)))
    {
      result = btor_copy_exp (btor, result);
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
      assert (!btor_is_param_node (real_cur)
              || !btor_param_is_exists_var (real_cur)
              || !btor_param_is_forall_var (real_cur));
      assert (!btor_is_bv_var_node (real_cur));
      assert (!btor_is_uf_node (real_cur));

      args.top -= real_cur->arity;
      e = args.top;

      if (btor_is_bv_const_node (real_cur))
      {
        result = btor_const_exp (btor, btor_const_get_bits (real_cur));
      }
      else if (btor_is_param_node (real_cur))
      {
        assert (!btor_param_is_exists_var (real_cur));
        assert (!btor_param_is_forall_var (real_cur));
        result = btor_param_exp (
            btor, btor_get_exp_width (real_cur->btor, real_cur), 0);
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      /* universal/existential vars get substituted */
      else if (btor_is_quantifier_node (real_cur))
      {
        assert (!btor_is_param_node (e[0]));
        result = btor_copy_exp (btor, e[1]);
      }
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      d->as_ptr = btor_copy_exp (btor, result);

    PUSH_RESULT:
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->keys[j]) continue;
    assert (mark->data[j].as_ptr);
    btor_release_exp (btor, mark->data[j].as_ptr);
  }
  btor_delete_int_hash_map (mark);

  return result;
}

static BtorNode *
instantiate_args (Btor *btor, BtorNode *args, BtorNodeMap *map)
{
  assert (map);
  assert (btor_is_args_node (args));

  BtorNodePtrStack stack;
  BtorArgsIterator it;
  BtorNode *res, *arg, *mapped;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  btor_init_args_iterator (&it, args);
  while (btor_has_next_args_iterator (&it))
  {
    arg = btor_next_args_iterator (&it);
    assert (btor_param_is_forall_var (arg));
    mapped = btor_mapped_node (map, arg);
    assert (mapped);
    BTOR_PUSH_STACK (mm, stack, mapped);
  }
  res = btor_args_exp (btor, stack.start, BTOR_COUNT_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
  return res;
}

static bool
refine_exists_solver (BtorEFGroundSolvers *gslv)
{
  assert (gslv->forall_uvars->table->count > 0);

  uint32_t i;
  Btor *f_solver, *e_solver;
  BtorNodeMap *map;
  BtorNodeMapIterator it;
  BtorNode *var_es, *var_fs, *c, *res, *uvar, *a;
  const BtorBitVector *bv;
  BtorBitVectorTuple *ce;
  BtorPtrHashBucket *b;

  //  printf ("  refine\n");
  f_solver = gslv->forall;
  e_solver = gslv->exists;

  map = btor_new_node_map (f_solver);

  /* generate counter example for universal vars */
  assert (f_solver->last_sat_result == BTOR_RESULT_SAT);
  f_solver->slv->api.generate_model (f_solver->slv, false, false);

  /* instantiate universal vars with counter example */
  //  printf ("CE (refine)\n");
  i  = 0;
  ce = btor_new_bv_tuple (f_solver->mm, gslv->forall_uvars->table->count);
  btor_init_node_map_iterator (&it, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    uvar   = btor_next_node_map_iterator (&it);
    bv     = btor_get_bv_model (f_solver, btor_simplify_exp (f_solver, var_fs));
    //      printf ("%s, %s = ", node2string (var_fs), btor_get_symbol_exp
    //      (f_solver, uvar)); btor_print_bv (bv);
    c = btor_const_exp (e_solver, (BtorBitVector *) bv);
    btor_map_node (map, uvar, c);
    btor_release_exp (e_solver, c);
    btor_add_to_bv_tuple (f_solver->mm, ce, bv, i++);
  }

  /* map existential variables to skolem constants */
  btor_init_node_map_iterator (&it, gslv->forall_evars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_es = it.it.bucket->data.as_ptr;
    var_fs = btor_next_node_map_iterator (&it);

    a = btor_mapped_node (gslv->forall_evar_deps, var_fs);
    if (a)
    {
      assert (btor_is_uf_node (var_es));
      a      = instantiate_args (e_solver, a, map);
      var_es = btor_apply_exp (e_solver, var_es, a);
      btor_map_node (map, var_fs, var_es);
      btor_release_exp (e_solver, a);
      btor_release_exp (e_solver, var_es);
    }
    else
      btor_map_node (map, var_fs, var_es);
  }

  /* map UFs */
  btor_init_node_map_iterator (&it, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var_es = btor_next_node_map_iterator (&it);
    btor_map_node (map, var_fs, var_es);
  }

  res = build_refinement (e_solver, gslv->forall_formula, map);

  btor_delete_node_map (map);

  // TODO (ma): need to check why this still occurs
  //            probably because of findpm=1
  if ((b = btor_get_ptr_hash_table (gslv->forall_ces, ce)))
  {
    gslv->forall_last_ce = b->data.as_ptr;
    btor_free_bv_tuple (f_solver->mm, ce);
    return false;
  }

  if (res == e_solver->true_exp)
  {
    btor_free_bv_tuple (f_solver->mm, ce);
    return false;
  }

  assert (res != e_solver->true_exp);
  BTOR_ABORT (
      res == e_solver->true_exp, "invalid refinement '%s'", node2string (res));
  gslv->statistics->stats.refinements++;
  assert (!btor_get_ptr_hash_table (gslv->forall_ces, ce));
  btor_add_ptr_hash_table (gslv->forall_ces, ce);
  gslv->forall_last_ce = ce;

  btor_assert_exp (e_solver, res);
  btor_release_exp (e_solver, res);
  return true;
}

BtorNode *
mk_concrete_lambda_model (Btor *btor, const BtorPtrHashTable *model)

{
  assert (btor);
  assert (model);

  uint32_t i;
  bool opt_synth_complete;
  BtorNode *uf;
  BtorNode *res, *c, *p, *cond, *e_if, *e_else, *tmp, *eq, *ite, *args;
  BtorHashTableIterator it;
  BtorNodePtrStack params, consts;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorSortId dsortid, cdsortid, funsortid;
  BtorSortUniqueTable *sorts;
  BtorSortIdStack tup_sorts;
  BtorPtrHashTable *static_rho;
  BtorMemMgr *mm;

  mm         = btor->mm;
  static_rho = btor_new_ptr_hash_table (mm, 0, 0);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (consts);
  BTOR_INIT_STACK (tup_sorts);
  opt_synth_complete = btor_get_opt (btor, BTOR_OPT_EF_SYNTH_ITE_COMPLETE) == 1;

  sorts      = &btor->sorts_unique_table;
  args_tuple = model->first->key;
  value      = model->first->data.as_ptr;

  /* create params from domain sort */
  for (i = 0; i < args_tuple->arity; i++)
  {
    p = btor_param_exp (btor, args_tuple->bv[i]->width, 0);
    BTOR_PUSH_STACK (mm, params, p);
    BTOR_PUSH_STACK (mm, tup_sorts, p->sort_id);
  }

  dsortid =
      btor_tuple_sort (sorts, tup_sorts.start, BTOR_COUNT_STACK (tup_sorts));
  cdsortid  = btor_bitvec_sort (sorts, value->width);
  funsortid = btor_fun_sort (sorts, dsortid, cdsortid);
  btor_release_sort (sorts, dsortid);
  btor_release_sort (sorts, cdsortid);
  BTOR_RELEASE_STACK (mm, tup_sorts);

  if (opt_synth_complete)
    e_else = btor_zero_exp (btor, value->width);
  else
  {
    uf   = btor_uf_exp (btor, funsortid, 0);
    args = btor_args_exp (btor, params.start, BTOR_COUNT_STACK (params));
    assert (args->sort_id = btor_get_domain_fun_sort (sorts, uf->sort_id));
    e_else = btor_apply_exp (btor, uf, args);
    assert (BTOR_REAL_ADDR_NODE (e_else)->sort_id
            == btor_get_codomain_fun_sort (sorts, uf->sort_id));
    btor_release_exp (btor, args);
    btor_release_exp (btor, uf);
  }

  /* generate ITEs */
  ite = 0;
  res = 0;
  btor_init_hash_table_iterator (&it, (BtorPtrHashTable *) model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    value      = (BtorBitVector *) it.bucket->data.as_ptr;
    args_tuple = btor_next_hash_table_iterator (&it);

    /* create condition */
    //      assert (btor_get_fun_arity (btor, uf) == args_tuple->arity);
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
  assert (res->sort_id == funsortid);
  btor_release_sort (sorts, funsortid);

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
  return res;
}

BtorNode *
mk_concrete_ite_model (BtorEFGroundSolvers *gslv,
                       BtorNode *evar,
                       FlatModel *model)

{
  assert (model);

  uint32_t i;
  bool opt_synth_complete;
  BtorNode *uf;
  BtorNode *res, *c, *cond, *e_if, *e_else, *tmp, *eq, *args, *uvar;
  BtorHashTableIterator it;
  BtorNodePtrStack params;
  BtorBitVector *value, *bv;
  BtorBitVectorTuple *ce;
  BtorSortId ufsortid;
  BtorSortUniqueTable *sorts;
  BtorMemMgr *mm;
  Btor *btor;
  BtorArgsIterator ait;

  btor = gslv->forall;
  mm   = btor->mm;
  BTOR_INIT_STACK (params);
  opt_synth_complete = btor_get_opt (btor, BTOR_OPT_EF_SYNTH_ITE_COMPLETE) == 1;

  sorts = &btor->sorts_unique_table;
  args  = btor_mapped_node (gslv->forall_evar_deps, evar);
  assert (args);

  /* create params from domain sort */
  btor_init_args_iterator (&ait, args);
  while (btor_has_next_args_iterator (&ait))
    BTOR_PUSH_STACK (mm, params, btor_next_args_iterator (&ait));

  if (opt_synth_complete)
    e_else = btor_zero_exp (btor, btor_get_exp_width (btor, evar));
  else
  {
    ufsortid = btor_fun_sort (sorts, args->sort_id, evar->sort_id);
    uf       = btor_uf_exp (btor, ufsortid, 0);
    btor_release_sort (sorts, ufsortid);
    e_else = btor_apply_exp (btor, uf, args);
    assert (BTOR_REAL_ADDR_NODE (e_else)->sort_id
            == btor_get_codomain_fun_sort (sorts, uf->sort_id));
    btor_release_exp (btor, uf);
  }

  /* generate ITEs */
  res = 0;
  btor_init_hash_table_iterator (&it, gslv->forall_ces);
  while (btor_has_next_hash_table_iterator (&it))
  {
    ce    = btor_next_hash_table_iterator (&it);
    value = flat_model_get_value (model, evar, ce);

    cond = 0;
    for (i = 0; i < BTOR_COUNT_STACK (params); i++)
    {
      uvar = BTOR_PEEK_STACK (params, i);
      bv   = flat_model_get_value (model, uvar, ce);
      c    = btor_const_exp (btor, bv);

      eq = btor_eq_exp (btor, uvar, c);
      btor_release_exp (btor, c);

      if (cond)
      {
        tmp = btor_and_exp (btor, cond, eq);
        btor_release_exp (btor, cond);
        btor_release_exp (btor, eq);
        cond = tmp;
      }
      else
        cond = eq;
    }
    assert (cond);

    /* create ITE */
    e_if = btor_const_exp (btor, value);
    res  = btor_cond_exp (btor, cond, e_if, e_else);

    btor_release_exp (btor, cond);
    btor_release_exp (btor, e_if);
    btor_release_exp (btor, e_else);
    e_else = res;
  }
  assert (res);

  BTOR_RELEASE_STACK (btor->mm, params);
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

/*------------------------------------------------------------------------*/

// TODO: optimization, do not use another solver instance, with inputs fixed
//       everything can be computed via eval_exp
static void
filter_flat_model (BtorEFGroundSolvers *gslv, FlatModel *flat_model)
{
  uint32_t i;
  BtorIntHashTable *cache;
  Btor *f_solver, *e_solver;
  Btor *r_solver;
  BtorNodeMap *map, *varmap, *rev_varmap, *rev_evars;
  BtorNodeMapIterator it;
  BtorNode *var_es, *var_fs, *c, *ref, *uvar, *a, *var, *eq, *cur;
  BtorNode *r_evar;
  const BtorBitVector *bv;
  BtorBitVectorTuple *ce;
  BtorNodePtrStack visit, bool_exps, true_exps, false_exps, models, outer_evars;
  BtorPtrHashTable *r_evars_ufs;
  BtorMemMgr *mm;
  BtorSolverResult r;
  BtorSortId sort_id;
  BtorHashTableIterator ce_it;
  BtorHashTableData d;

  r_solver = btor_new_btor ();
  f_solver = gslv->forall;
  e_solver = gslv->exists;
  btor_delete_opts (r_solver);
  btor_clone_opts (e_solver, r_solver);
  assert (btor_get_opt (r_solver, BTOR_OPT_EF_FINDPM_MODE)
          == BTOR_EF_FINDPM_REF);

  mm = e_solver->mm;

  map         = btor_new_node_map (r_solver);
  varmap      = btor_new_node_map (r_solver);
  rev_varmap  = btor_new_node_map (r_solver);
  rev_evars   = btor_new_node_map (r_solver);
  r_evars_ufs = btor_new_ptr_hash_table (mm, 0, 0);
  cache       = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (bool_exps);
  BTOR_INIT_STACK (true_exps);
  BTOR_INIT_STACK (false_exps);
  BTOR_INIT_STACK (outer_evars);
  BTOR_INIT_STACK (models);

  //  printf ("CE (skeleton) %u\n", gslv->forall_ces->count);
  /* position of last refinement */
  //  i = BTOR_TOP_STACK (gslv->forall_ce_trail);
  i = 0;
  //  ce = gslv->forall_ces->last->key;
  ce = gslv->forall_last_ce;
  /* instantiate universal vars with fresh vars */
  btor_init_node_map_iterator (&it, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    uvar   = btor_next_node_map_iterator (&it);

    var = btor_var_exp (r_solver, btor_get_exp_width (f_solver, uvar), 0);
    btor_map_node (varmap, uvar, var);
    btor_map_node (rev_varmap, var, uvar);

    bv = ce->bv[i++];
    assert (bv);
    c = btor_const_exp (r_solver, (BtorBitVector *) bv);
    btor_map_node (map, var, c);

    btor_release_exp (r_solver, c);
    btor_release_exp (r_solver, var);
  }

  /* map existential variables to skolem constants */
  btor_init_node_map_iterator (&it, gslv->forall_evars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_es = it.it.bucket->data.as_ptr;
    var_fs = btor_next_node_map_iterator (&it);

    sort_id = btor_recursively_rebuild_sort_clone (
        e_solver, r_solver, var_es->sort_id);

    a      = btor_mapped_node (gslv->forall_evar_deps, var_fs);
    r_evar = btor_var_exp (r_solver, btor_get_exp_width (f_solver, var_fs), 0);
    btor_map_node (varmap, var_fs, r_evar);
    if (!a) BTOR_PUSH_STACK (mm, outer_evars, r_evar);

    btor_add_ptr_hash_table (r_evars_ufs, r_evar);
    btor_map_node (rev_evars, r_evar, var_fs);
    btor_release_sort (&r_solver->sorts_unique_table, sort_id);
  }

  /* map UFs */
  // TODO: no UF support for now
  assert (gslv->exists_ufs->table->count == 0);
#if 0
  btor_init_node_map_iterator (&it, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
    {
      var_fs = it.it.bucket->data.as_ptr;
      var_es = btor_next_node_map_iterator (&it);
      sort_id = btor_recursively_rebuild_sort_clone (e_solver, r_solver,
						     var_es->sort_id);
      var_es = btor_uf_exp (r_solver, sort_id, 0);
      btor_release_sort (&r_solver->sorts_unique_table, sort_id);
      btor_map_node (varmap, var_fs, var_es);
      btor_map_node (rev_evars, var_es, var_fs);
      btor_add_ptr_hash_table (r_evars_ufs, var_es);
    }
#endif

  ref = build_refinement (r_solver, gslv->forall_formula, varmap);

  /* collect and nodes in boolean skeleton */
  BTOR_PUSH_STACK (mm, visit, ref);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)) continue;

    btor_add_int_hash_table (cache, cur->id);
    if (btor_is_and_node (cur) && btor_get_exp_width (r_solver, cur) == 1)
    {
      BTOR_PUSH_STACK (mm, bool_exps, btor_copy_exp (r_solver, cur));
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }
  }

  /* fix assignments of outermost existential variables */
  btor_init_node_map_iterator (&it, gslv->forall_evars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = btor_next_node_map_iterator (&it);
    bv     = flat_model_get_value (flat_model, var_fs, ce);
    // btor_get_bv_model (e_solver, btor_simplify_exp (e_solver, var_es));
    r_evar = btor_mapped_node (varmap, var_fs);
    assert (r_evar);
    c  = btor_const_exp (r_solver, (BtorBitVector *) bv);
    eq = btor_eq_exp (r_solver, r_evar, c);
    btor_release_exp (r_solver, c);
    if (btor_mapped_node (gslv->forall_evar_deps, var_fs))
      btor_assume_exp (r_solver, eq);
    else
      btor_assert_exp (r_solver, eq);
    btor_release_exp (r_solver, eq);
  }

  /* initial SAT call */
  btor_assert_exp (r_solver, ref);
  btor_release_exp (r_solver, ref);

  /* assume current counter example (from last refinement) */
  btor_init_node_map_iterator (&it, map);
  while (btor_has_next_node_map_iterator (&it))
  {
    c   = it.it.bucket->data.as_ptr;
    var = btor_next_node_map_iterator (&it);
    eq  = btor_eq_exp (r_solver, var, c);
    btor_assume_exp (r_solver, eq);
    btor_release_exp (r_solver, eq);
  }

  r = btor_sat_btor (r_solver, -1, -1);

  if (r == BTOR_RESULT_SAT)
  {
    r_solver->slv->api.generate_model (r_solver->slv, false, false);

    /* collect true/false exps in boolean skeleton */
    for (i = 0; i < BTOR_COUNT_STACK (bool_exps); i++)
    {
      cur = BTOR_PEEK_STACK (bool_exps, i);
      bv  = btor_get_bv_model (r_solver, btor_simplify_exp (r_solver, cur));

      if (btor_is_true_bv (bv))
        BTOR_PUSH_STACK (mm, true_exps, cur);
      else
      {
        assert (btor_is_false_bv (bv));
        BTOR_PUSH_STACK (mm, false_exps, cur);
      }
    }

    btor_init_hash_table_iterator (&ce_it, gslv->forall_ces);
    while (btor_has_next_hash_table_iterator (&ce_it))
    {
      i  = 0;
      ce = btor_next_hash_table_iterator (&ce_it);

      /* assume counterexample */
      btor_init_node_map_iterator (&it, gslv->forall_uvars);
      while (btor_has_next_node_map_iterator (&it))
      {
        var = btor_mapped_node (varmap, btor_next_node_map_iterator (&it));
        bv  = ce->bv[i++];
        c   = btor_const_exp (r_solver, (BtorBitVector *) bv);
        eq  = btor_eq_exp (r_solver, var, c);
        btor_assume_exp (r_solver, eq);
        btor_release_exp (r_solver, c);
        btor_release_exp (r_solver, eq);
      }

      /* fix values of existential variables under current counterexample */
      btor_init_node_map_iterator (&it, gslv->forall_evars);
      while (btor_has_next_node_map_iterator (&it))
      {
        var_fs = btor_next_node_map_iterator (&it);
        /* outermost variables already asserted */
        if (!btor_mapped_node (gslv->forall_evar_deps, var_fs)) continue;
        bv     = flat_model_get_value (flat_model, var_fs, ce);
        r_evar = btor_mapped_node (varmap, var_fs);
        assert (r_evar);
        c  = btor_const_exp (r_solver, (BtorBitVector *) bv);
        eq = btor_eq_exp (r_solver, r_evar, c);
        btor_release_exp (r_solver, c);
        btor_assume_exp (r_solver, eq);
        btor_release_exp (r_solver, eq);
      }

      // TODO: check if assertion would be faster
      for (i = 0; i < BTOR_COUNT_STACK (true_exps); i++)
        btor_assume_exp (r_solver, BTOR_PEEK_STACK (true_exps, i));
      for (i = 0; i < BTOR_COUNT_STACK (false_exps); i++)
        btor_assume_exp (r_solver,
                         BTOR_INVERT_NODE (BTOR_PEEK_STACK (false_exps, i)));

      r = btor_sat_btor (r_solver, -1, -1);

      /* skip counter-example, does not satisfy current boolean
       * skeleton */
      if (r == BTOR_RESULT_UNSAT)
      {
        btor_remove_ptr_hash_table (flat_model->model, ce, 0, &d);
        btor_free_bv_tuple (flat_model->mm, d.as_ptr);
        printf ("remove\n");
      }
    }
  }
  assert (flat_model->model->count >= 1);

  /* cleanup */
  while (!BTOR_EMPTY_STACK (models))
    btor_release_exp (r_solver, BTOR_POP_STACK (models));

  BTOR_RELEASE_STACK (mm, models);
  BTOR_RELEASE_STACK (mm, true_exps);
  BTOR_RELEASE_STACK (mm, false_exps);
  BTOR_RELEASE_STACK (mm, outer_evars);
  BTOR_RELEASE_STACK (mm, visit);

  while (!BTOR_EMPTY_STACK (bool_exps))
    btor_release_exp (r_solver, BTOR_POP_STACK (bool_exps));
  BTOR_RELEASE_STACK (mm, bool_exps);

  btor_delete_node_map (map);
  btor_delete_node_map (varmap);
  btor_delete_node_map (rev_varmap);
  btor_delete_node_map (rev_evars);
  btor_delete_ptr_hash_table (r_evars_ufs);
  btor_delete_int_hash_table (cache);

  btor_delete_btor (r_solver);
}

static void
build_input_output_values (BtorEFGroundSolvers *gslv,
                           BtorNode *evar,
                           FlatModel *flat_model,
                           BtorBitVectorTuplePtrStack *value_in,
                           BtorBitVectorPtrStack *value_out)
{
  uint32_t i, pos;
  BtorHashTableIterator it;
  BtorBitVector *out;
  BtorBitVectorTuple *in, *uvar_tup, *evar_tup;
  BtorMemMgr *mm;
  Btor *btor;

  btor = gslv->forall;
  mm   = btor->mm;

  btor_init_hash_table_iterator (&it, flat_model->model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    evar_tup = it.bucket->data.as_ptr;
    uvar_tup = btor_next_hash_table_iterator (&it);

    in = btor_new_bv_tuple (mm, uvar_tup->arity + evar_tup->arity);

    pos = 0;
    for (i = 0; i < uvar_tup->arity; i++)
      btor_add_to_bv_tuple (mm, in, uvar_tup->bv[i], pos++);
    for (i = 0; i < evar_tup->arity; i++)
      btor_add_to_bv_tuple (mm, in, evar_tup->bv[i], pos++);

    out = flat_model_get_value (flat_model, evar, uvar_tup);
    BTOR_PUSH_STACK (mm, *value_in, in);
    BTOR_PUSH_STACK (mm, *value_out, btor_copy_bv (mm, out));
  }
  assert (BTOR_COUNT_STACK (*value_in) == BTOR_COUNT_STACK (*value_out));
}

static BtorBitVector *
eval_exp (Btor *btor,
          BtorNode *exp,
          FlatModel *flat_model,
          BtorBitVectorTuple *ce)
{
  assert (btor);

  size_t j;
  int32_t i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorBitVectorPtrStack arg_stack;
  BtorMemMgr *mm;
  BtorBitVector **bv, *result, *inv_result, *a;

  mm    = btor->mm;
  cache = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, exp);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (cache, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (cache, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);

      if (btor_is_apply_node (real_cur)) continue;

      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (!btor_is_fun_node (real_cur));
      assert (!btor_is_apply_node (real_cur));
      assert (!btor_is_bv_var_node (real_cur));

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          result = btor_copy_bv (mm, btor_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
          a      = flat_model_get_value (flat_model, real_cur, ce);
          result = btor_copy_bv (mm, a);
          break;

        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  bv[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          break;

        case BTOR_AND_NODE: result = btor_and_bv (mm, bv[0], bv[1]); break;

        case BTOR_BV_EQ_NODE: result = btor_eq_bv (mm, bv[0], bv[1]); break;

        case BTOR_ADD_NODE: result = btor_add_bv (mm, bv[0], bv[1]); break;

        case BTOR_MUL_NODE: result = btor_mul_bv (mm, bv[0], bv[1]); break;

        case BTOR_ULT_NODE: result = btor_ult_bv (mm, bv[0], bv[1]); break;

        case BTOR_SLL_NODE: result = btor_sll_bv (mm, bv[0], bv[1]); break;

        case BTOR_SRL_NODE: result = btor_srl_bv (mm, bv[0], bv[1]); break;

        case BTOR_UDIV_NODE: result = btor_udiv_bv (mm, bv[0], bv[1]); break;

        case BTOR_UREM_NODE: result = btor_urem_bv (mm, bv[0], bv[1]); break;

        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (mm, bv[0], bv[1]);
          break;

        case BTOR_EXISTS_NODE:
        case BTOR_FORALL_NODE: result = btor_copy_bv (mm, bv[1]); break;

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_is_true_bv (bv[0]))
            result = btor_copy_bv (mm, bv[1]);
          else
            result = btor_copy_bv (mm, bv[2]);
      }

      if (!btor_is_apply_node (real_cur))
      {
        for (i = 0; i < real_cur->arity; i++) btor_free_bv (mm, bv[i]);
      }

      d->as_ptr = btor_copy_bv (mm, result);

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
      result = btor_copy_bv (mm, d->as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }

  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    btor_free_bv (mm, a);
  }
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_int_hash_map (cache);

  return result;
}

static void
update_flat_model (BtorEFGroundSolvers *gslv,
                   FlatModel *flat_model,
                   BtorNode *evar,
                   BtorNode *result)
{
  uint32_t evar_pos;
  BtorHashTableIterator it;
  BtorBitVectorTuple *ce, *evalues;
  BtorBitVector *bv;
  BtorPtrHashBucket *b;
  Btor *btor;
  BtorMemMgr *mm;

  btor = gslv->forall;
  mm   = btor->mm;
  evar_pos =
      btor_get_int_hash_map (flat_model->evar_index_map, evar->id)->as_int;

  btor_init_hash_table_iterator (&it, flat_model->model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    b       = it.bucket;
    evalues = b->data.as_ptr;
    ce      = btor_next_hash_table_iterator (&it);
    btor_free_bv (mm, evalues->bv[evar_pos]);
    bv                    = eval_exp (btor, result, flat_model, ce);
    evalues->bv[evar_pos] = bv;
  }
}

static void
select_inputs (BtorEFGroundSolvers *gslv,
               BtorNode *var,
               BtorNodePtrStack *inputs)
{
  BtorNodeMapIterator nit;
  BtorArgsIterator it;
  BtorNode *args, *cur;
  BtorMemMgr *mm;

  mm = gslv->forall->mm;
  if (btor_param_is_exists_var (var))
  {
    args = btor_mapped_node (gslv->forall_evar_deps, var);
    btor_init_args_iterator (&it, args);
    while (btor_has_next_args_iterator (&it))
    {
      cur = btor_next_args_iterator (&it);
      BTOR_PUSH_STACK (mm, *inputs, cur);
    }
  }
  else
  {
    assert (btor_param_is_forall_var (var));
    btor_init_node_map_iterator (&nit, gslv->forall_evars);
    while (btor_has_next_node_map_iterator (&nit))
    {
      cur = btor_next_node_map_iterator (&nit);
      BTOR_PUSH_STACK (mm, *inputs, cur);
    }
  }
}

static BtorNode *
synthesize (BtorEFGroundSolvers *gslv,
            BtorNode *evar,
            FlatModel *flat_model,
            uint32_t limit,
            BtorNode *prev_synth_fun)
{
  uint32_t i, pos, opt_synth_mode;
  BtorNode *cur, *par, *result = 0;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *reachable, *cache, *value_in_map;
  BtorNodeIterator it;
  BtorNodePtrStack constraints, inputs;
  BtorBitVectorTuplePtrStack value_in;
  BtorBitVectorPtrStack value_out;
  BtorNodeMapIterator nit;

  mm             = gslv->forall->mm;
  reachable      = btor_new_int_hash_table (mm);
  cache          = btor_new_int_hash_table (mm);
  value_in_map   = btor_new_int_hash_map (mm);
  opt_synth_mode = btor_get_opt (gslv->forall, BTOR_OPT_EF_SYNTH);

  BTOR_INIT_STACK (value_in);
  BTOR_INIT_STACK (value_out);
  BTOR_INIT_STACK (constraints);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (inputs);

  /* value_in_map maps variables to the position in the assignment vector
   * value_in[k] */
  pos = 0;
  btor_init_node_map_iterator (&nit, gslv->forall_uvars);
  while (btor_has_next_node_map_iterator (&nit))
  {
    cur = btor_next_node_map_iterator (&nit);
    btor_add_int_hash_map (value_in_map, cur->id)->as_int = pos++;
  }
  btor_init_node_map_iterator (&nit, gslv->forall_evars);
  while (btor_has_next_node_map_iterator (&nit))
  {
    cur = btor_next_node_map_iterator (&nit);
    btor_add_int_hash_map (value_in_map, cur->id)->as_int = pos++;
  }

  select_inputs (gslv, evar, &inputs);

  /* 'evar' is a special placeholder for constraint evaluation */
  btor_add_int_hash_map (value_in_map, evar->id)->as_int = -1;

  build_input_output_values (gslv, evar, flat_model, &value_in, &value_out);

  if (opt_synth_mode == BTOR_EF_SYNTH_EL
      || opt_synth_mode == BTOR_EF_SYNTH_EL_ELMC)
  {
    result =
        btor_synthesize_fun_constraints (gslv->forall,
                                         inputs.start,
                                         BTOR_COUNT_STACK (inputs),
                                         value_in.start,
                                         value_out.start,
                                         BTOR_COUNT_STACK (value_in),
                                         value_in_map,
                                         prev_synth_fun,
                                         constraints.start,
                                         BTOR_COUNT_STACK (constraints),
                                         gslv->forall_consts.start,
                                         BTOR_COUNT_STACK (gslv->forall_consts),
                                         limit,
                                         0);
  }

  if (!result
      && (opt_synth_mode == BTOR_EF_SYNTH_ELMC
          || opt_synth_mode == BTOR_EF_SYNTH_EL_ELMC))
  {
    /* mark reachable exps */
    BTOR_PUSH_STACK (mm, visit, gslv->forall_formula);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (btor_contains_int_hash_table (reachable, cur->id)) continue;

      btor_add_int_hash_table (reachable, cur->id);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }

    assert (btor_contains_int_hash_table (reachable, evar->id));

    /* collect constraints in cone of 'evar' */
    BTOR_PUSH_STACK (mm, visit, evar);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (!btor_contains_int_hash_table (reachable, cur->id)
          || btor_contains_int_hash_table (cache, cur->id))
        continue;

      /* cut-off at boolean layer */
      if (btor_get_exp_width (gslv->forall, cur) == 1)
      {
        BTOR_PUSH_STACK (mm, constraints, cur);
        continue;
      }

      btor_add_int_hash_table (cache, cur->id);
      btor_init_parent_iterator (&it, cur);
      while (btor_has_next_parent_iterator (&it))
      {
        par = btor_next_parent_iterator (&it);
        BTOR_PUSH_STACK (mm, visit, par);
      }
    }
  }
  else if (opt_synth_mode == BTOR_EF_SYNTH_ELMR)
  {
    assert (opt_synth_mode == BTOR_EF_SYNTH_ELMR);
    BTOR_PUSH_STACK (mm, constraints, gslv->forall_formula);
  }

  if (!result)
  {
    result =
        btor_synthesize_fun_constraints (gslv->forall,
                                         inputs.start,
                                         BTOR_COUNT_STACK (inputs),
                                         value_in.start,
                                         value_out.start,
                                         BTOR_COUNT_STACK (value_in),
                                         value_in_map,
                                         prev_synth_fun,
                                         constraints.start,
                                         BTOR_COUNT_STACK (constraints),
                                         gslv->forall_consts.start,
                                         BTOR_COUNT_STACK (gslv->forall_consts),
                                         limit,
                                         0);
  }

  if (result && btor_get_opt (gslv->forall, BTOR_OPT_EF_FIXSYNTH))
    update_flat_model (gslv, flat_model, evar, result);

  while (!BTOR_EMPTY_STACK (value_in))
    btor_free_bv_tuple (mm, BTOR_POP_STACK (value_in));
  while (!BTOR_EMPTY_STACK (value_out))
    btor_free_bv (mm, BTOR_POP_STACK (value_out));

  BTOR_RELEASE_STACK (mm, inputs);

  btor_delete_int_hash_map (value_in_map);
  btor_delete_int_hash_table (reachable);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, value_in);
  BTOR_RELEASE_STACK (mm, value_out);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, constraints);
  return result;
}

static BtorPtrHashTable *
synthesize_model (BtorEFGroundSolvers *gslv, FlatModel *flat_model)
{
  uint32_t limit;
  uint32_t opt_synth_limit, opt_synth_mode;
  BtorPtrHashTable *synth_model, *prev_synth_model;
  Btor *f_solver;
  BtorNode *evar, *prev_synth_fun, *candidate;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;
  SynthResult *synth_res, *prev_synth_res;
  BtorPtrHashBucket *b;
  BtorMemMgr *mm;

  f_solver         = gslv->forall;
  mm               = f_solver->mm;
  prev_synth_model = gslv->forall_synth_model;
  synth_model      = btor_new_ptr_hash_table (mm, 0, 0);
  opt_synth_mode   = btor_get_opt (f_solver, BTOR_OPT_EF_SYNTH);
  opt_synth_limit  = btor_get_opt (f_solver, BTOR_OPT_EF_SYNTH_LIMIT);

  /* reset stats for currently synthesized model */
  gslv->statistics->stats.synthesize_model_const = 0;
  gslv->statistics->stats.synthesize_model_term  = 0;
  gslv->statistics->stats.synthesize_model_none  = 0;

  /* map existential variables to their resp. assignment */
  btor_init_node_map_iterator (&it, gslv->forall_evars);
  // TODO: no UFs supported for now
  //  btor_queue_node_map_iterator (&it, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    evar = btor_next_node_map_iterator (&it);
    assert (btor_is_uf_node (evar) || btor_param_is_exists_var (evar));

    if (btor_terminate_btor (gslv->forall)) break;

    synth_res = new_synth_result (mm);
    /* map skolem functions to resp. synthesized functions */
    if (btor_mapped_node (gslv->forall_evar_deps, evar)
        || btor_is_uf_node (evar))
    {
      prev_synth_res = 0;
      prev_synth_fun = 0;
      candidate      = 0;
      if (opt_synth_mode)
      {
        limit = opt_synth_limit;

        /* check previously synthesized function */
        if (prev_synth_model
            && (b = btor_get_ptr_hash_table (prev_synth_model, evar)))
        {
          prev_synth_res = b->data.as_ptr;
          assert (prev_synth_res);

          limit = prev_synth_res->limit;
          if (!prev_synth_res->partial) prev_synth_fun = prev_synth_res->value;
          /* we did not find expressions that cover all input/output
           * pairs previously, increase previous limit */
          else
            limit = limit * 1.5;
        }

        // TODO: set limit of UFs to 10000 fixed
        if (limit > opt_synth_limit * 10) limit = opt_synth_limit;

        candidate = synthesize (gslv, evar, flat_model, limit, prev_synth_fun);
#if 0
	      if (candidate)
		{
		  printf ("found candidate for %s\n", node2string (evar));
		  btor_dump_smt2_node (gslv->forall, stdout, candidate, -1);
		}
	      else
		printf ("no candidate found for %s\n", node2string (evar));
#endif

        synth_res->limit = limit;
      }

      assert (!btor_is_uf_node (evar));
      if (candidate)
      {
        synth_res->partial = false;
        if (btor_is_bv_const_node (candidate))
          gslv->statistics->stats.synthesize_const++;
        else
          gslv->statistics->stats.synthesize_model_term++;
        synth_res->value = candidate;
      }
      else
      {
        synth_res->value   = mk_concrete_ite_model (gslv, evar, flat_model);
        synth_res->partial = true;
        gslv->statistics->stats.synthesize_model_none++;
      }
    }
    else
    {
      bv               = flat_model_get_value (flat_model, evar, 0);
      synth_res->value = btor_const_exp (f_solver, (BtorBitVector *) bv);
    }
    assert (synth_res->value);
    btor_add_ptr_hash_table (synth_model, evar)->data.as_ptr = synth_res;
  }

  /* update overall synthesize statistics */
  gslv->statistics->stats.synthesize_const +=
      gslv->statistics->stats.synthesize_model_const;
  gslv->statistics->stats.synthesize_term +=
      gslv->statistics->stats.synthesize_model_term;
  gslv->statistics->stats.synthesize_none +=
      gslv->statistics->stats.synthesize_model_none;

  return synth_model;
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

/* instantiate each universal variable with the resp. fresh bit vector variable
 * and replace existential variables with the synthesized model (may expand the
 * quantifier tree if more synthesized functions available).
 * 'model' maps existential variables to synthesized function models. */
static BtorNode *
instantiate_formula (BtorEFGroundSolvers *gslv, BtorPtrHashTable *model)
{
  assert (gslv);
  assert (!btor_is_proxy_node (gslv->forall_formula));

  int32_t i;
  size_t j;
  Btor *btor;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args;
  BtorNode *cur, *real_cur, *result, **e, *a;
  BtorNode *fun;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorNodeMap *uvar_map, *skolem;
  BtorPtrHashBucket *b;
  BtorNodeMap *deps;
  SynthResult *synth_res;

  btor     = gslv->forall;
  mm       = btor->mm;
  mark     = btor_new_int_hash_map (mm);
  uvar_map = gslv->forall_uvars;
  deps     = gslv->forall_evar_deps;
  skolem   = gslv->forall_skolem;

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_PUSH_STACK (mm, visit, gslv->forall_formula);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
      if (btor_is_param_node (real_cur) && btor_param_is_exists_var (real_cur)
          && model && (b = btor_get_ptr_hash_table (model, real_cur)))
      {
        synth_res = b->data.as_ptr;
        assert (synth_res->value);
        BTOR_PUSH_STACK (
            mm, visit, BTOR_COND_INVERT_NODE (cur, synth_res->value));
        continue;
      }
      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (d->as_ptr == 0)
    {
      assert (real_cur->arity <= BTOR_COUNT_STACK (args));
      args.top -= real_cur->arity;
      e = args.top;

      if (btor_is_uf_node (real_cur))
      {
        if (model && (b = btor_get_ptr_hash_table (model, real_cur)))
        {
          synth_res = b->data.as_ptr;
          result    = btor_copy_exp (btor, synth_res->value);
        }
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (real_cur->arity == 0)
      {
        /* instantiate universal vars with fresh bv vars in 'uvar_map' */
        if (btor_is_param_node (real_cur))
        {
          if (btor_param_is_forall_var (real_cur))
          {
            result = btor_mapped_node (uvar_map, real_cur);
            assert (result);
            result = btor_copy_exp (btor, result);
          }
          else
          {
            assert (btor_param_is_exists_var (real_cur));
            /* exististential vars will be substituted while
             * traversing down */
            assert (!model || !btor_get_ptr_hash_table (model, real_cur));
            /* no model -> substitute with skolem constant */
            fun = btor_mapped_node (skolem, real_cur);
            assert (fun);
            if ((a = btor_mapped_node (deps, real_cur)))
            {
              a      = instantiate_args (btor, a, uvar_map);
              result = btor_apply_exp (btor, fun, a);
              btor_release_exp (btor, a);
            }
            else
              result = btor_copy_exp (btor, fun);
          }
        }
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      /* universal variable got substituted by var in 'uvar_map' */
      else if (btor_is_forall_node (real_cur) || btor_is_exists_node (real_cur))
        result = btor_copy_exp (btor, e[1]);
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      d->as_ptr = btor_copy_exp (btor, result);

    PUSH_RESULT:
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->keys[j]) continue;
    assert (mark->data[j].as_ptr);
    btor_release_exp (btor, mark->data[j].as_ptr);
  }
  btor_delete_int_hash_map (mark);

  assert (!BTOR_REAL_ADDR_NODE (result)->quantifier_below);
  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);
  return result;
}

static void
flat_model_free (FlatModel *flat_model)
{
  BtorHashTableIterator it;
  BtorBitVectorTuple *t;
  BtorMemMgr *mm;

  mm = flat_model->mm;

  btor_init_hash_table_iterator (&it, flat_model->model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    t = it.bucket->data.as_ptr;
    /* not need to free ce in gslv->forall_ces */
    (void) btor_next_hash_table_iterator (&it);
    btor_free_bv_tuple (mm, t);
  }
  btor_delete_ptr_hash_table (flat_model->model);
  btor_delete_int_hash_map (flat_model->uvar_index_map);
  btor_delete_int_hash_map (flat_model->evar_index_map);
  BTOR_DELETE (mm, flat_model);
}

static BtorSolverResult
find_model (BtorEFGroundSolvers *gslv, bool skip_exists)
{
  bool opt_underapprox, failed_refinement = false;
  uint32_t opt_pmfind_mode;
  double start;
  BtorSolverResult res          = BTOR_RESULT_UNKNOWN, r;
  BtorNode *g                   = 0;
  BtorPtrHashTable *synth_model = 0;
  BtorPtrHashTable *assumptions = 0, *vars = 0;
  BtorNodeMapIterator it;
  FlatModel *flat_model = 0;

  opt_underapprox = btor_get_opt (gslv->forall, BTOR_OPT_EF_UNDERAPPROX) == 1;
  opt_pmfind_mode = btor_get_opt (gslv->forall, BTOR_OPT_EF_FINDPM_MODE);

  /* initialize all universal variables with a bit-width of 1 */
  if (opt_underapprox)
  {
    vars = btor_new_ptr_hash_table (gslv->forall->mm, 0, 0);
    btor_init_node_map_iterator (&it, gslv->forall_uvars);
    while (btor_has_next_node_map_iterator (&it))
      btor_add_ptr_hash_table (vars,
                               btor_next_data_node_map_iterator (&it)->as_ptr)
          ->data.as_int = 1;
  }

  /* exists solver does not have any constraints, so it does not make much
   * sense to initialize every variable by zero and ask if the model
   * is correct. */
  if (!skip_exists)
  {
    /* query exists solver */
    start = time_stamp ();
    r     = btor_sat_btor (gslv->exists, -1, -1);
    gslv->statistics->time.e_solver += time_stamp () - start;

    if (r == BTOR_RESULT_UNSAT) /* formula is UNSAT */
    {
      res = BTOR_RESULT_UNSAT;
      goto DONE;
    }
    /* solver terminated due to termination callback */
    else if (r == BTOR_RESULT_UNKNOWN)
    {
      assert (gslv->exists->cbs.term.done);
      goto DONE;
    }

  RESTART:
    start      = time_stamp ();
    flat_model = flat_model_generate (gslv);
    if (!failed_refinement && opt_pmfind_mode == BTOR_EF_FINDPM_REF
        && (gslv->forall_evar_deps->table->count > 0
            || gslv->forall->ufs->count > 0))
      filter_flat_model (gslv, flat_model);
    gslv->statistics->time.findpm += time_stamp () - start;

    /* synthesize model based on 'partial_model' */
    start       = time_stamp ();
    synth_model = synthesize_model (gslv, flat_model);
    flat_model_free (flat_model);

    /* save currently synthesized model */
    delete_model (gslv);
    gslv->forall_synth_model = synth_model;
    gslv->statistics->time.synth += time_stamp () - start;
  }

  start = time_stamp ();
  g     = instantiate_formula (gslv, synth_model);
  gslv->statistics->time.checkinst += time_stamp () - start;

  /* if there are no universal variables in the formula, we have a simple
   * ground formula */
  if (gslv->forall_uvars->table->count == 0)
  {
    assert (skip_exists);
    btor_assert_exp (gslv->forall, g);
    start = time_stamp ();
    res   = btor_sat_btor (gslv->forall, -1, -1);
    gslv->statistics->time.f_solver += time_stamp () - start;
    goto DONE;
  }

UNDERAPPROX:
  btor_assume_exp (gslv->forall, BTOR_INVERT_NODE (g));

  if (opt_underapprox)
  {
    if (assumptions) underapprox_release (gslv->forall, assumptions);
    assumptions = btor_new_ptr_hash_table (gslv->forall->mm, 0, 0);
    underapprox (gslv->forall, vars, assumptions);
  }

  /* query forall solver */
  start = time_stamp ();
  r     = btor_sat_btor (gslv->forall, -1, -1);
  update_formula (gslv);
  assert (!btor_is_proxy_node (gslv->forall_formula));
  gslv->statistics->time.f_solver += time_stamp () - start;

  if (r == BTOR_RESULT_UNSAT) /* formula is SAT */
  {
    /* underapproximation failed, increase bit-widths and try again */
    if (opt_underapprox
        && !underapprox_check (gslv->forall, vars, assumptions, g))
      goto UNDERAPPROX;

    res = BTOR_RESULT_SAT;
    goto DONE;
  }
  /* solver terminated due to termination callback */
  else if (r == BTOR_RESULT_UNKNOWN)
  {
    assert (gslv->forall->cbs.term.done);
    goto DONE;
  }

  /* if refinement fails, we got a counter-example that we already got in
   * a previous call. in this case we produce a model using all refinements */
  start             = time_stamp ();
  failed_refinement = !refine_exists_solver (gslv);
  gslv->statistics->time.qinst += time_stamp () - start;
  if (failed_refinement)
  {
    printf ("failed refinment\n");
    btor_release_exp (gslv->forall, g);
    gslv->statistics->stats.failed_refinements++;
    goto RESTART;
  }

DONE:
  if (g) btor_release_exp (gslv->forall, g);
  if (opt_underapprox)
  {
    assert (vars);
    assert (assumptions);
    underapprox_release (gslv->forall, assumptions);
    btor_delete_ptr_hash_table (vars);
  }
  return res;
}

#if 0
/* Create new refinement for 'gslv->exists' by instantiating 
 * the universal variables of 'gslv->exists' with 'dual_gslv->forall_synth_model'.
 */
static void
add_instantiation (BtorEFGroundSolvers * gslv, BtorEFGroundSolvers * dual_gslv,
		   BtorNodeMap * var_map)
{
  BtorNode *ref;
  Btor *btor;
  BtorNodeMap *subst_map, *deps, *clone_map, *evar_map;
  BtorHashTableIterator it;
  BtorNodeMapIterator nit;
  BtorNode *evar, *uvar, *subst, *a, *fun, *cur, *mapped;
  BtorNode *e_evar, *f_evar;
  SynthResult *synth_res;
  BtorArgsIterator ait;

  if (!dual_gslv->forall_synth_model)
    return;

  btor = gslv->exists;
  subst_map = btor_new_node_map (btor);
  deps = dual_gslv->forall_evar_deps;

  btor_init_node_hash_table_iterator (&it, dual_gslv->forall_synth_model);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      synth_res = it.bucket->data.as_ptr; 
      evar = btor_next_node_hash_table_iterator (&it);

      if (!btor_is_param_node (evar) || !btor_param_is_exists_var (evar))
	continue;

      uvar = btor_mapped_node (var_map, evar);
      assert (btor_param_is_forall_var (uvar));

      if (synth_res->type == BTOR_SYNTH_TYPE_SK_VAR)
	{
	  subst = btor_const_exp (btor, btor_const_get_bits (synth_res->value));
	}
      else
	{
	  assert (synth_res->type == BTOR_SYNTH_TYPE_SK_UF);
	  fun = synth_res->value;
	  clone_map = btor_new_node_map (btor);
	  fun = btor_recursively_rebuild_exp_clone (dual_gslv->forall, btor, fun, clone_map, 3);
	  btor_delete_node_map (clone_map);

	  a = btor_mapped_node (deps, evar); 
	  assert (a);
	  evar_map = btor_new_node_map (btor);
	  btor_init_args_iterator (&ait, a);
	  while (btor_has_next_args_iterator (&ait))
	    {
	      /* get universal variable of 'dual_gslv->forall' */
	      cur = btor_next_args_iterator (&ait);
	      /* get existential variable of 'gslv->forall' */
	      mapped = btor_mapped_node (var_map, cur);
	      /* get existential variable of 'gslv->exists' */
	      mapped = btor_mapped_node (gslv->forall_evars, mapped);
	      btor_map_node (evar_map, cur, mapped);
	    }
	  // a contains universal variables of dual_gslv->forall
	  // 1) remap universal vars of dual_gslv->forall to existential vars of
	  //    gslv->forall
	  a = instantiate_args (btor, a, evar_map);
	  subst = btor_apply_exp (btor, fun, a);
	  btor_delete_node_map (evar_map);
	}

      btor_map_node (subst_map, uvar, subst);
      btor_release_exp (btor, subst);
    }

  /* map existential variables to skolem constants */
  btor_init_node_map_iterator (&nit, gslv->forall_evars);
  while (btor_has_next_node_map_iterator (&nit))
    {
      e_evar = nit.it.bucket->data.as_ptr;
      f_evar = btor_next_node_map_iterator (&nit);

      a = btor_mapped_node (gslv->forall_evar_deps, f_evar);
      if (a)
	{
	  assert (btor_is_uf_node (e_evar));
	  a = instantiate_args (btor, a, subst_map);
	  e_evar = btor_apply_exp (btor, e_evar, a); 
	  btor_map_node (subst_map, f_evar, e_evar);
	  btor_release_exp (btor, a);
	  btor_release_exp (btor, e_evar);
	}
      else
	btor_map_node (subst_map, f_evar, e_evar);
    }

  /* map UFs */
  btor_init_node_map_iterator (&nit, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&nit))
    {
      f_evar = nit.it.bucket->data.as_ptr;
      e_evar = btor_next_node_map_iterator (&nit);
      btor_map_node (subst_map, f_evar, e_evar);
    }

  ref = build_refinement (btor, gslv->forall_formula, subst_map);
  btor_delete_node_map (subst_map);

  btor_assert_exp (btor, ref);
  btor_release_exp (btor, ref);
}
#endif

bool thread_found_result            = false;
pthread_mutex_t thread_result_mutex = PTHREAD_MUTEX_INITIALIZER;

void *
thread_work (void *state)
{
  BtorSolverResult res = BTOR_RESULT_UNKNOWN;
  BtorEFGroundSolvers *gslv;
  bool skip_exists = true;

  gslv = state;
  while (res == BTOR_RESULT_UNKNOWN && !thread_found_result)
  {
    res         = find_model (gslv, skip_exists);
    skip_exists = false;
    gslv->statistics->stats.refinements++;
  }
  pthread_mutex_lock (&thread_result_mutex);
  if (!thread_found_result)
  {
    BTOR_MSG (gslv->exists->msg,
              1,
              "found solution in %.2f seconds",
              btor_process_time_thread ());
    thread_found_result = true;
  }
  assert (thread_found_result || res == BTOR_RESULT_UNKNOWN);
  pthread_mutex_unlock (&thread_result_mutex);
  gslv->result = res;
  return NULL;
}

int
thread_terminate (void *state)
{
  (void) state;
  return thread_found_result == true;
}

static BtorSolverResult
run_parallel (BtorEFGroundSolvers *gslv, BtorEFGroundSolvers *dual_gslv)
{
  BtorSolverResult res;
  pthread_t thread_orig, thread_dual;

  g_measure_thread_time = true;
  btor_set_term_btor (gslv->forall, thread_terminate, 0);
  btor_set_term_btor (gslv->exists, thread_terminate, 0);
  btor_set_term_btor (dual_gslv->forall, thread_terminate, 0);
  btor_set_term_btor (dual_gslv->exists, thread_terminate, 0);
  pthread_create (&thread_orig, 0, thread_work, gslv);
  pthread_create (&thread_dual, 0, thread_work, dual_gslv);
  pthread_join (thread_orig, 0);
  pthread_join (thread_dual, 0);

  if (gslv->result != BTOR_RESULT_UNKNOWN)
  {
    res = gslv->result;
    if (res == BTOR_RESULT_SAT) print_cur_model (gslv);
  }
  else
  {
    assert (dual_gslv->result != BTOR_RESULT_UNKNOWN);
    if (dual_gslv->result == BTOR_RESULT_SAT)
    {
      printf ("DUAL SOLVER: SAT -> UNSAT\n");
      res = BTOR_RESULT_UNSAT;
      print_cur_model (dual_gslv);
    }
    else
    {
      assert (dual_gslv->result == BTOR_RESULT_UNSAT);
      res = BTOR_RESULT_SAT;
      printf ("DUAL SOLVER: VALID -> SAT\n");
    }
  }
  return res;
}

static BtorSolverResult
sat_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  //  double start;
  bool opt_dual_solver, skip_exists = true;
  BtorSolverResult res;
  BtorNode *g;
  BtorEFGroundSolvers *gslv, *dual_gslv = 0;
  BtorNodeMap *var_map = 0, *dual_var_map = 0;
  /* 'var_map' maps existential/universal (gslv) to universal/existential
   * vars (dual_gslv) */

  // TODO (ma): incremental support

  // FIXME (ma): not sound with slice elimination. see red-vsl.proof3106.smt2
  btor_set_opt (slv->btor, BTOR_OPT_ELIMINATE_SLICES, 0);

  /* simplify formula and normalize quantifiers */
  res = btor_simplify (slv->btor);
  if (res != BTOR_RESULT_UNKNOWN) return res;

  opt_dual_solver = btor_get_opt (slv->btor, BTOR_OPT_EF_DUAL_SOLVER) == 1;

  g    = btor_normalize_quantifiers (slv->btor);
  gslv = setup_efg_solvers (slv, g, false, "forall", "exists", 0, 0);
  btor_release_exp (slv->btor, g);
  gslv->statistics = &slv->statistics;

  /* disable dual solver if UFs are present in the formula */
  // TODO: eliminate UFs with ackermann
  if (gslv->exists_ufs->table->count > 0) opt_dual_solver = false;

  if (opt_dual_solver)
  {
    var_map               = btor_new_node_map (slv->btor);
    dual_var_map          = btor_new_node_map (slv->btor);
    dual_gslv             = setup_efg_solvers (slv,
                                   gslv->forall_formula,
                                   true,
                                   "dual_forall",
                                   "dual_exists",
                                   var_map,
                                   dual_var_map);
    dual_gslv->statistics = &slv->dual_statistics;
    res                   = run_parallel (gslv, dual_gslv);
  }
  else
  {
    while (true)
    {
      res = find_model (gslv, skip_exists);
      if (res != BTOR_RESULT_UNKNOWN) break;
      skip_exists = false;
    }
    gslv->result = res;

    if (res == BTOR_RESULT_SAT) print_cur_model (gslv);
  }

  slv->solver_result = gslv->result;

  if (opt_dual_solver)
  {
    slv->dual_solver_result = dual_gslv->result;
    btor_delete_node_map (var_map);
    btor_delete_node_map (dual_var_map);
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
            "cegqi solver refinements: %u",
            slv->statistics.stats.refinements);
  BTOR_MSG (slv->btor->msg,
            1,
            "cegqi solver failed refinements: %u",
            slv->statistics.stats.failed_refinements);
  if (slv->solver_result == BTOR_RESULT_SAT
      || slv->solver_result == BTOR_RESULT_UNKNOWN)
  {
    BTOR_MSG (slv->btor->msg,
              1,
              "model synthesized const: %u (%u)",
              slv->statistics.stats.synthesize_model_const,
              slv->statistics.stats.synthesize_const);
    BTOR_MSG (slv->btor->msg,
              1,
              "model synthesized term: %u (%u)",
              slv->statistics.stats.synthesize_model_term,
              slv->statistics.stats.synthesize_term);
    BTOR_MSG (slv->btor->msg,
              1,
              "model synthesized none: %u (%u)",
              slv->statistics.stats.synthesize_model_none,
              slv->statistics.stats.synthesize_none);
  }
  if (btor_get_opt (slv->btor, BTOR_OPT_EF_DUAL_SOLVER))
  {
    BTOR_MSG (slv->btor->msg,
              1,
              "cegqi dual solver refinements: %u",
              slv->dual_statistics.stats.refinements);
    BTOR_MSG (slv->btor->msg,
              1,
              "cegqi dual solver failed refinements: %u",
              slv->dual_statistics.stats.failed_refinements);
    if (slv->dual_solver_result == BTOR_RESULT_SAT
        || slv->solver_result == BTOR_RESULT_UNKNOWN)
    {
      BTOR_MSG (slv->btor->msg,
                1,
                "dual model synthesized const: %u (%u)",
                slv->dual_statistics.stats.synthesize_model_const,
                slv->dual_statistics.stats.synthesize_const);
      BTOR_MSG (slv->btor->msg,
                1,
                "dual model synthesized term: %u (%u)",
                slv->dual_statistics.stats.synthesize_model_term,
                slv->dual_statistics.stats.synthesize_term);
      BTOR_MSG (slv->btor->msg,
                1,
                "dual model synthesized none: %u (%u)",
                slv->dual_statistics.stats.synthesize_model_none,
                slv->dual_statistics.stats.synthesize_none);
    }
  }
}

static void
print_time_stats_ef_solver (BtorEFSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_EF_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds exists solver",
            slv->statistics.time.e_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds forall solver",
            slv->statistics.time.f_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds synthesizing functions",
            slv->statistics.time.synth);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds find partial model",
            slv->statistics.time.findpm);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds quantifier instantiation",
            slv->statistics.time.qinst);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds check instantiation",
            slv->statistics.time.checkinst);
  if (btor_get_opt (slv->btor, BTOR_OPT_EF_DUAL_SOLVER))
  {
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual exists solver",
              slv->dual_statistics.time.e_solver);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual forall solver",
              slv->dual_statistics.time.f_solver);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual synthesizing functions",
              slv->dual_statistics.time.synth);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual quantifier instantiation",
              slv->dual_statistics.time.qinst);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual find partial model",
              slv->dual_statistics.time.findpm);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual check instantiation",
              slv->dual_statistics.time.checkinst);
  }
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

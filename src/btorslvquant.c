/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvquant.h"
#include "btorabort.h"
#include "btorbeta.h"
#include "btorbv.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btorprintmodel.h"
#include "btorslvfun.h"
#include "btorsynth.h"
#include "normalizer/btornormquant.h"
#include "normalizer/btorskolemize.h"
#include "simplifier/btorder.h"
#include "simplifier/btorminiscope.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

#ifdef BTOR_HAVE_PTHREADS
#include <pthread.h>
#include <signal.h>
#include <unistd.h>
#endif

struct BtorQuantStats
{
  struct
  {
    uint32_t refinements;
    uint32_t failed_refinements;

    /* overall synthesize statistics */
    uint32_t synthesize_const;
    uint32_t synthesize_term;
    uint32_t synthesize_none;

    /* statistics for the currently synthesized model */
    uint32_t synthesize_model_const;
    uint32_t synthesize_model_term;
    uint32_t synthesize_model_none;
  } stats;

  struct
  {
    double e_solver;
    double f_solver;
    double synth;
    double refine;
    double qinst;
    double findpm;
    double checkinst;
  } time;
};

typedef struct BtorQuantStats BtorQuantStats;

struct BtorGroundSolvers
{
  Btor *forall; /* solver for checking the model */
  BtorNode *forall_formula;
  BtorNodeMap *forall_evars;     /* existential vars (map to skolem
                                    constants of exists solver) */
  BtorNodeMap *forall_uvars;     /* universal vars map to fresh bv vars */
  BtorNodeMap *forall_evar_deps; /* existential vars map to argument nodes
                                    of universal vars */
  BtorNodeMap *forall_uvar_deps; /* universal vars map to argument nodes
                                    of existential vars */
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
  BtorNodeMap *exists_cur_qi;
  BtorSolverResult result;

  BtorQuantStats statistics;
};

typedef struct BtorGroundSolvers BtorGroundSolvers;

struct BtorQuantSolver
{
  BTOR_SOLVER_STRUCT;

  BtorGroundSolvers *gslv;  /* two ground solver instances */
  BtorGroundSolvers *dgslv; /* two ground solver instances for dual */
};

typedef struct BtorQuantSolver BtorQuantSolver;

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
    cur = btor_node_real_addr (res->value);
    btor_node_release (cur->btor, cur);
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

  if (btor_node_param_is_exists_var (var))
  {
    i = btor_hashint_map_get (flat_model->evar_index_map, var->id)->as_int;
    if (ce)
    {
      b = btor_hashptr_table_get (flat_model->model, ce);
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
      BtorPtrHashTableIterator it;
      BtorBitVectorTuple *tup;
      btor_iter_hashptr_init (&it, flat_model->model);
      while (btor_iter_hashptr_has_next (&it))
      {
        tup = it.bucket->data.as_ptr;
        (void) btor_iter_hashptr_next (&it);
        assert (btor_bv_compare (res, tup->bv[i]) == 0);
      }
#endif
    }
  }
  else
  {
    assert (ce);
    assert (btor_node_param_is_forall_var (var));
    i   = btor_hashint_map_get (flat_model->uvar_index_map, var->id)->as_int;
    res = ce->bv[i];
  }
  return res;
}

static FlatModel *
flat_model_generate (BtorGroundSolvers *gslv)
{
  bool free_bv;
  uint32_t i, j, pos, nevars;
  Btor *e_solver, *f_solver;
  BtorNode *cur, *e_evar, *f_evar, *args;
  BtorPtrHashTableIterator it;
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
  flat_model->model = btor_hashptr_table_new (
      mm, (BtorHashPtr) btor_bv_hash_tuple, (BtorCmpPtr) btor_bv_compare_tuple);
  flat_model->uvar_index_map = btor_hashint_map_new (mm);
  flat_model->evar_index_map = btor_hashint_map_new (mm);

  nevars = gslv->exists_evars->table->count;

  i = 0;
  btor_iter_nodemap_init (&nit, gslv->forall_uvars);
  while (btor_iter_nodemap_has_next (&nit))
  {
    cur = btor_iter_nodemap_next (&nit);
    btor_hashint_map_add (flat_model->uvar_index_map, cur->id)->as_int = i++;
  }

  i = 0;
  btor_iter_nodemap_init (&nit, gslv->forall_evars);
  while (btor_iter_nodemap_has_next (&nit))
  {
    cur = btor_iter_nodemap_next (&nit);
    btor_hashint_map_add (flat_model->evar_index_map, cur->id)->as_int = i++;
  }

  /* generate model for exists vars/ufs */
  assert (e_solver->last_sat_result == BTOR_RESULT_SAT);
  e_solver->slv->api.generate_model (e_solver->slv, false, false);

  btor_iter_hashptr_init (&it, gslv->forall_ces);
  while (btor_iter_hashptr_has_next (&it))
  {
    ce = btor_iter_hashptr_next (&it);

    pos         = 0;
    evar_values = btor_bv_new_tuple (mm, nevars);
    btor_iter_nodemap_init (&nit, gslv->forall_evars);
    while (btor_iter_nodemap_has_next (&nit))
    {
      e_evar = nit.it.bucket->data.as_ptr;
      f_evar = btor_iter_nodemap_next (&nit);

      free_bv = false;
      if ((args = btor_nodemap_mapped (gslv->forall_evar_deps, f_evar)))
      {
        bv = 0;
        m  = btor_model_get_fun (e_solver, e_evar);
        if (m)
        {
          mtup =
              btor_bv_new_tuple (mm, btor_node_args_get_arity (f_solver, args));
          j = 0;
          btor_iter_args_init (&ait, args);
          while (btor_iter_args_has_next (&ait))
          {
            cur = btor_iter_args_next (&ait);
            i   = btor_hashint_map_get (flat_model->uvar_index_map, cur->id)
                    ->as_int;
            btor_bv_add_to_tuple (mm, mtup, ce->bv[i], j++);
          }
          b = btor_hashptr_table_get ((BtorPtrHashTable *) m, mtup);
          btor_bv_free_tuple (mm, mtup);
          if (b) bv = b->data.as_ptr;
        }
        if (!bv)
        {
          free_bv = true;
          bv      = btor_bv_new (mm, btor_node_bv_get_width (f_solver, f_evar));
        }
      }
      else
      {
        assert (btor_node_param_is_exists_var (f_evar));
        bv = (BtorBitVector *) btor_model_get_bv (
            e_solver, btor_simplify_exp (e_solver, e_evar));
      }
      btor_bv_add_to_tuple (mm, evar_values, bv, pos++);
      if (free_bv) btor_bv_free (mm, bv);
    }
    btor_hashptr_table_add (flat_model->model, ce)->data.as_ptr = evar_values;
  }
  return flat_model;
}

static void
flat_model_free (FlatModel *flat_model)
{
  BtorPtrHashTableIterator it;
  BtorBitVectorTuple *t;
  BtorMemMgr *mm;

  mm = flat_model->mm;

  btor_iter_hashptr_init (&it, flat_model->model);
  while (btor_iter_hashptr_has_next (&it))
  {
    t = it.bucket->data.as_ptr;
    /* not need to free ce in gslv->forall_ces */
    (void) btor_iter_hashptr_next (&it);
    btor_bv_free_tuple (mm, t);
  }
  btor_hashptr_table_delete (flat_model->model);
  btor_hashint_map_delete (flat_model->uvar_index_map);
  btor_hashint_map_delete (flat_model->evar_index_map);
  BTOR_DELETE (mm, flat_model);
}

/*------------------------------------------------------------------------*/

static bool g_measure_thread_time = false;

static double
time_stamp (void)
{
  if (g_measure_thread_time) return btor_util_process_time_thread ();
  return btor_util_time_stamp ();
}

/*------------------------------------------------------------------------*/

static void
delete_model (BtorGroundSolvers *gslv)
{
  BtorNode *cur;
  BtorPtrHashTableIterator it;
  SynthResult *synth_res;

  if (!gslv->forall_synth_model) return;

  btor_iter_hashptr_init (&it, gslv->forall_synth_model);
  while (btor_iter_hashptr_has_next (&it))
  {
    synth_res = it.bucket->data.as_ptr;
    cur       = btor_iter_hashptr_next (&it);
    assert (btor_node_is_uf (cur) || btor_node_param_is_exists_var (cur));
    (void) cur;
    delete_synth_result (gslv->forall->mm, synth_res);
  }
  btor_hashptr_table_delete (gslv->forall_synth_model);
  gslv->forall_synth_model = 0;
}

/* compute dependencies between existential variables and universal variables.
 * 'deps' maps existential variables to a list of universal variables by means
 * of an argument node.
 */
void
compute_var_deps (Btor *btor,
                  BtorNode *root,
                  BtorNodeMap *edeps,
                  BtorNodeMap *udeps)
{
  uint32_t i;
  BtorNode *cur, *real_cur, *q, *args;
  BtorNodePtrStack visit, fquants, equants, vars;
  BtorMemMgr *mm;
  BtorIntHashTable *map;
  BtorHashTableData *d;

  mm = btor->mm;

  BTOR_INIT_STACK (mm, vars);
  BTOR_INIT_STACK (mm, fquants);
  BTOR_INIT_STACK (mm, equants);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  map = btor_hashint_map_new (mm);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (map, real_cur->id);
    if (!d)
    {
      btor_hashint_map_add (map, real_cur->id);

      if (btor_node_is_forall (real_cur)) BTOR_PUSH_STACK (fquants, real_cur);
      if (btor_node_is_exists (real_cur)) BTOR_PUSH_STACK (equants, real_cur);

      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (btor_node_is_exists (real_cur))
      {
        /* create dependency of 'real_cur' with all universal vars of
         * 'fquants' */
        if (BTOR_COUNT_STACK (fquants))
        {
          for (i = 0; i < BTOR_COUNT_STACK (fquants); i++)
          {
            q = BTOR_PEEK_STACK (fquants, i);
            BTOR_PUSH_STACK (vars, btor_node_real_addr (q)->e[0]);
          }
          args = btor_exp_args (btor, vars.start, BTOR_COUNT_STACK (vars));
          btor_nodemap_map (edeps, real_cur->e[0], args);
          btor_node_release (btor, args);
          BTOR_RESET_STACK (vars);
        }
        q = BTOR_POP_STACK (equants);
        assert (q == real_cur);
      }
      else if (btor_node_is_forall (real_cur))
      {
        /* create dependency of 'real_cur' with all universal vars of
         * 'equants' */
        if (BTOR_COUNT_STACK (equants))
        {
          for (i = 0; i < BTOR_COUNT_STACK (equants); i++)
          {
            q = BTOR_PEEK_STACK (equants, i);
            BTOR_PUSH_STACK (vars, btor_node_real_addr (q)->e[0]);
          }
          args = btor_exp_args (btor, vars.start, BTOR_COUNT_STACK (vars));
          btor_nodemap_map (udeps, real_cur->e[0], args);
          btor_node_release (btor, args);
          BTOR_RESET_STACK (vars);
        }
        q = BTOR_POP_STACK (fquants);
        assert (q == real_cur);
      }
    }
  }
  btor_hashint_map_delete (map);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (fquants);
  BTOR_RELEASE_STACK (equants);
  BTOR_RELEASE_STACK (vars);
}

static BtorNode *
mk_dual_formula (Btor *btor, Btor *dual_btor, BtorNode *root)
{
  char *sym;
  size_t j;
  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, **e;
  BtorNodePtrStack stack, args;
  BtorIntHashTable *map;
  BtorHashTableData *d;
  BtorSortId sortid;

  mm  = btor->mm;
  map = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, args);
  BTOR_PUSH_STACK (stack, root);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = btor_node_real_addr (cur);
    d        = btor_hashint_map_get (map, real_cur->id);

    if (!d)
    {
      btor_hashint_table_add (map, real_cur->id);
      BTOR_PUSH_STACK (stack, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (stack, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      /* bit vector variables should be existentially quantified */
      assert (!btor_node_is_bv_var (real_cur));
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_node_is_param (real_cur))
        {
          sym    = btor_node_get_symbol (btor, real_cur);
          sortid = btor_sort_bv (dual_btor,
                                     btor_node_bv_get_width (btor, real_cur));
          result = btor_exp_param (dual_btor, sortid, sym);
          btor_sort_release (dual_btor, sortid);
        }
        else if (btor_node_is_bv_const (real_cur))
        {
          result = btor_exp_bv_const (dual_btor,
                                   btor_node_bv_const_get_bits (real_cur));
        }
        else
        {
          assert (btor_node_is_uf (real_cur));
          sortid = btor_clone_recursively_rebuild_sort (
              btor, dual_btor, real_cur->sort_id);
          result = btor_exp_uf (dual_btor, sortid, 0);
          btor_sort_release (dual_btor, sortid);
        }
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (dual_btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      /* invert quantifiers */
      else if (btor_node_is_forall (real_cur))
        result = btor_exp_exists (dual_btor, e[0], e[1]);
      else if (btor_node_is_exists (real_cur))
        result = btor_exp_forall (dual_btor, e[0], e[1]);
      else
      {
        result =
            btor_exp_create (dual_btor, real_cur->kind, e, real_cur->arity);
      }

      d->as_ptr = btor_node_copy (dual_btor, result);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (dual_btor, e[i]);
    PUSH_RESULT:
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (dual_btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (args);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_node_release (dual_btor, map->data[j].as_ptr);
  }
  btor_hashint_map_delete (map);
  return btor_node_invert (result);
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
  cache = btor_hashint_table_new (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    id = btor_node_is_bv_const (real_cur) ? btor_node_get_id (cur)
                                          : real_cur->id;

    if (btor_hashint_table_contains (cache, id)) continue;

    if (btor_node_is_bv_const (real_cur)) BTOR_PUSH_STACK (*consts, cur);

    btor_hashint_table_add (cache, id);
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (visit, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);
}

static BtorGroundSolvers *
setup_solvers (BtorQuantSolver *slv,
               BtorNode *root,
               bool setup_dual,
               const char *prefix_forall,
               const char *prefix_exists)
{
  uint32_t width;
  char *sym;
  BtorGroundSolvers *res;
  BtorNode *cur, *var, *tmp;
  BtorPtrHashTableIterator it;
  BtorFunSolver *fslv;
  BtorNodeMap *exp_map;
  Btor *btor;
  BtorSortId dsortid, cdsortid, funsortid;
  BtorMemMgr *mm;
  BtorPtrHashTable *forall_ufs;

  btor       = slv->btor;
  mm         = btor->mm;
  forall_ufs = btor_hashptr_table_new (mm, 0, 0);
  BTOR_CNEW (mm, res);

  /* new forall solver */
  res->result = BTOR_RESULT_UNKNOWN;
  res->forall = btor_new ();
  btor_opt_delete_opts (res->forall);
  btor_opt_clone_opts (btor, res->forall);
  btor_set_msg_prefix (res->forall, prefix_forall);

  /* configure options */
  btor_opt_set (res->forall, BTOR_OPT_MODEL_GEN, 1);
  btor_opt_set (res->forall, BTOR_OPT_INCREMENTAL, 1);

  if (setup_dual)
  {
    root =
        mk_dual_formula (btor_node_real_addr (root)->btor, res->forall, root);
  }
  else
  {
    exp_map = btor_nodemap_new (btor);
    tmp     = btor_clone_recursively_rebuild_exp (
        btor,
        res->forall,
        root,
        exp_map,
        btor_opt_get (res->forall, BTOR_OPT_REWRITE_LEVEL));
    /* all bv vars are quantified with exists */
    assert (res->forall->bv_vars->count == 0);
    btor_nodemap_delete (exp_map);
    root = tmp;
  }
  assert (!btor_node_is_proxy (root));

  res->forall_formula   = root;
  res->forall_evar_deps = btor_nodemap_new (res->forall);
  res->forall_uvar_deps = btor_nodemap_new (res->forall);
  compute_var_deps (
      res->forall, root, res->forall_evar_deps, res->forall_uvar_deps);
  res->forall_evars  = btor_nodemap_new (res->forall);
  res->forall_uvars  = btor_nodemap_new (res->forall);
  res->forall_skolem = btor_nodemap_new (res->forall);
  res->forall_ces    = btor_hashptr_table_new (res->forall->mm,
                                            (BtorHashPtr) btor_bv_hash_tuple,
                                            (BtorCmpPtr) btor_bv_compare_tuple);
  BTOR_INIT_STACK (res->forall->mm, res->forall_consts);
  collect_consts (res->forall, res->forall_formula, &res->forall_consts);

  /* store UFs in a separate table for later */
  btor_iter_hashptr_init (&it, res->forall->ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    btor_hashptr_table_add (forall_ufs, cur);
  }

  /* map fresh bit vector vars to universal vars */
  btor_iter_hashptr_init (&it, res->forall->forall_vars);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_param_is_forall_var (cur));
    var = btor_exp_var (res->forall, cur->sort_id, 0);
    btor_nodemap_map (res->forall_uvars, cur, var);
    btor_node_release (res->forall, var);
  }

  /* map fresh skolem constants to existential vars */
  btor_iter_hashptr_init (&it, res->forall->exists_vars);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_param_is_exists_var (cur));

    tmp = btor_nodemap_mapped (res->forall_evar_deps, cur);
    if (tmp)
    {
      funsortid = btor_sort_fun (res->forall, tmp->sort_id, cur->sort_id);
      var       = btor_exp_uf (res->forall, funsortid, 0);
      btor_sort_release (res->forall, funsortid);
    }
    else
      var = btor_exp_var (res->forall, cur->sort_id, 0);

    btor_nodemap_map (res->forall_skolem, cur, var);
    btor_node_release (res->forall, var);
  }

  /* create ground solver for forall */
  assert (!res->forall->slv);
  fslv                = (BtorFunSolver *) btor_new_fun_solver (res->forall);
  fslv->assume_lemmas = true;
  res->forall->slv    = (BtorSolver *) fslv;

  /* new exists solver */
  res->exists = btor_new ();
  btor_opt_delete_opts (res->exists);
  btor_opt_clone_opts (res->forall, res->exists);
  btor_set_msg_prefix (res->exists, prefix_exists);
  btor_opt_set (res->exists, BTOR_OPT_AUTO_CLEANUP_INTERNAL, 1);

  /* create ground solver for exists */
  res->exists->slv  = btor_new_fun_solver (res->exists);
  res->exists_evars = btor_nodemap_new (res->exists);
  res->exists_ufs   = btor_nodemap_new (res->exists);

  /* map evars of exists solver to evars of forall solver */
  btor_iter_hashptr_init (&it, res->forall->exists_vars);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_param_is_exists_var (cur));
    width = btor_node_bv_get_width (res->forall, cur);
    sym   = btor_node_get_symbol (res->forall, cur);

    if ((tmp = btor_nodemap_mapped (res->forall_evar_deps, cur)))
    {
      /* 'tmp' is an argument node that holds all universal dependencies of
       * existential variable 'cur'*/
      assert (btor_node_is_args (tmp));

      cdsortid = btor_sort_bv (res->exists, width);
      dsortid  = btor_clone_recursively_rebuild_sort (
          res->forall, res->exists, tmp->sort_id);
      funsortid = btor_sort_fun (res->exists, dsortid, cdsortid);
      var       = btor_exp_uf (res->exists, funsortid, sym);
      btor_sort_release (res->exists, cdsortid);
      btor_sort_release (res->exists, dsortid);
      btor_sort_release (res->exists, funsortid);
    }
    else
    {
      dsortid = btor_sort_bv (res->exists, width);
      var     = btor_exp_var (res->exists, dsortid, sym);
      btor_sort_release (res->exists, dsortid);
    }
    btor_nodemap_map (res->exists_evars, var, cur);
    btor_nodemap_map (res->forall_evars, cur, var);
    btor_node_release (res->exists, var);
  }

  /* map ufs of exists solver to ufs of forall solver */
  btor_iter_hashptr_init (&it, forall_ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur       = btor_iter_hashptr_next (&it);
    funsortid = btor_clone_recursively_rebuild_sort (
        res->forall, res->exists, cur->sort_id);
    var = btor_exp_uf (
        res->exists, funsortid, btor_node_get_symbol (res->forall, cur));
    btor_sort_release (res->exists, funsortid);
    btor_nodemap_map (res->exists_ufs, var, cur);
    btor_node_release (res->exists, var);
  }
  btor_hashptr_table_delete (forall_ufs);

  return res;
}

static void
delete_ground_solvers (BtorQuantSolver *slv, BtorGroundSolvers *gslv)
{
  BtorPtrHashTableIterator it;
  BtorBitVectorTuple *ce;

  /* delete exists solver */
  btor_nodemap_delete (gslv->exists_evars);
  btor_nodemap_delete (gslv->exists_ufs);

  /* delete forall solver */
  delete_model (gslv);
  btor_nodemap_delete (gslv->forall_evars);
  btor_nodemap_delete (gslv->forall_uvars);
  btor_nodemap_delete (gslv->forall_evar_deps);
  btor_nodemap_delete (gslv->forall_uvar_deps);
  btor_nodemap_delete (gslv->forall_skolem);
  if (gslv->exists_cur_qi) btor_nodemap_delete (gslv->exists_cur_qi);

  btor_iter_hashptr_init (&it, gslv->forall_ces);
  while (btor_iter_hashptr_has_next (&it))
  {
    if (it.bucket->data.as_ptr)
      btor_bv_free_tuple (gslv->forall->mm, it.bucket->data.as_ptr);
    ce = btor_iter_hashptr_next (&it);
    btor_bv_free_tuple (gslv->forall->mm, ce);
  }
  btor_hashptr_table_delete (gslv->forall_ces);
  BTOR_RELEASE_STACK (gslv->forall_consts);

  btor_node_release (gslv->forall, gslv->forall_formula);
  btor_delete (gslv->forall);
  btor_delete (gslv->exists);
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
  BtorSortId sort;

  mm   = btor->mm;
  mark = btor_hashint_map_new (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_PUSH_STACK (visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    assert (!btor_node_is_proxy (real_cur));

    if ((result = btor_nodemap_mapped (map, real_cur)))
    {
      result = btor_node_copy (btor, result);
      goto PUSH_RESULT;
    }

    d = btor_hashint_map_get (mark, real_cur->id);
    if (!d)
    {
      (void) btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (!btor_node_is_param (real_cur)
              || !btor_node_param_is_exists_var (real_cur)
              || !btor_node_param_is_forall_var (real_cur));
      assert (!btor_node_is_bv_var (real_cur));
      assert (!btor_node_is_uf (real_cur));

      args.top -= real_cur->arity;
      e = args.top;

      if (btor_node_is_bv_const (real_cur))
      {
        result = btor_exp_bv_const (btor, btor_node_bv_const_get_bits (real_cur));
      }
      else if (btor_node_is_param (real_cur))
      {
        assert (!btor_node_param_is_exists_var (real_cur));
        assert (!btor_node_param_is_forall_var (real_cur));
        sort = btor_sort_bv (
            btor, btor_node_bv_get_width (real_cur->btor, real_cur));
        result = btor_exp_param (btor, sort, 0);
        btor_sort_release (btor, sort);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      /* universal/existential vars get substituted */
      else if (btor_node_is_quantifier (real_cur))
      {
        assert (!btor_node_is_param (e[0]));
        result = btor_node_copy (btor, e[1]);
      }
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);

    PUSH_RESULT:
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->keys[j]) continue;
    assert (mark->data[j].as_ptr);
    btor_node_release (btor, mark->data[j].as_ptr);
  }
  btor_hashint_map_delete (mark);

  return result;
}

static BtorNode *
instantiate_args (Btor *btor, BtorNode *args, BtorNodeMap *map)
{
  assert (map);
  assert (btor_node_is_args (args));

  BtorNodePtrStack stack;
  BtorArgsIterator it;
  BtorNode *res, *arg, *mapped;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  btor_iter_args_init (&it, args);
  while (btor_iter_args_has_next (&it))
  {
    arg = btor_iter_args_next (&it);
    assert (btor_node_param_is_forall_var (arg));
    mapped = btor_nodemap_mapped (map, arg);
    assert (mapped);
    BTOR_PUSH_STACK (stack, mapped);
  }
  res = btor_exp_args (btor, stack.start, BTOR_COUNT_STACK (stack));
  BTOR_RELEASE_STACK (stack);
  return res;
}

static void
refine_exists_solver (BtorGroundSolvers *gslv, BtorNodeMap *evar_map)
{
  assert (gslv->forall_uvars->table->count > 0);

  uint32_t i;
  Btor *f_solver, *e_solver;
  BtorNodeMap *map;
  BtorNodeMapIterator it;
  BtorNode *var_es, *var_fs, *c, *res, *uvar, *evar, *a;
  const BtorBitVector *bv;
  BtorBitVectorTuple *ce, *evar_tup;

  f_solver = gslv->forall;
  e_solver = gslv->exists;

  map = btor_nodemap_new (f_solver);

  /* generate counter example for universal vars */
  assert (f_solver->last_sat_result == BTOR_RESULT_SAT);
  f_solver->slv->api.generate_model (f_solver->slv, false, false);

  /* instantiate universal vars with counter example */
  i  = 0;
  ce = btor_bv_new_tuple (f_solver->mm, gslv->forall_uvars->table->count);
  btor_iter_nodemap_init (&it, gslv->forall_uvars);
  while (btor_iter_nodemap_has_next (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    uvar   = btor_iter_nodemap_next (&it);
    bv     = btor_model_get_bv (f_solver, btor_simplify_exp (f_solver, var_fs));
    c      = btor_exp_bv_const (e_solver, (BtorBitVector *) bv);
    btor_nodemap_map (map, uvar, c);
    btor_node_release (e_solver, c);
    btor_bv_add_to_tuple (f_solver->mm, ce, bv, i++);
  }

  i        = 0;
  evar_tup = 0;
  if (gslv->forall_evars->table->count)
  {
    evar_tup =
        btor_bv_new_tuple (f_solver->mm, gslv->forall_evars->table->count);
    btor_iter_nodemap_init (&it, gslv->forall_evars);
    while (btor_iter_nodemap_has_next (&it))
    {
      evar   = btor_iter_nodemap_next (&it);
      var_fs = btor_nodemap_mapped (evar_map, evar);
      assert (var_fs);
      bv = btor_model_get_bv (f_solver, btor_simplify_exp (f_solver, var_fs));
      btor_bv_add_to_tuple (f_solver->mm, evar_tup, bv, i++);
    }
  }

  /* map existential variables to skolem constants */
  btor_iter_nodemap_init (&it, gslv->forall_evars);
  while (btor_iter_nodemap_has_next (&it))
  {
    var_es = it.it.bucket->data.as_ptr;
    var_fs = btor_iter_nodemap_next (&it);

    a = btor_nodemap_mapped (gslv->forall_evar_deps, var_fs);
    if (a)
    {
      assert (btor_node_is_uf (var_es));
      a      = instantiate_args (e_solver, a, map);
      var_es = btor_exp_apply (e_solver, var_es, a);
      btor_nodemap_map (map, var_fs, var_es);
      btor_node_release (e_solver, a);
      btor_node_release (e_solver, var_es);
    }
    else
      btor_nodemap_map (map, var_fs, var_es);
  }

  /* map UFs */
  btor_iter_nodemap_init (&it, gslv->exists_ufs);
  while (btor_iter_nodemap_has_next (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var_es = btor_iter_nodemap_next (&it);
    btor_nodemap_map (map, var_fs, var_es);
  }

  res = build_refinement (e_solver, gslv->forall_formula, map);

  btor_nodemap_delete (map);

  assert (res != e_solver->true_exp);
  BTOR_ABORT (res == e_solver->true_exp,
              "invalid refinement '%s'",
              btor_util_node2string (res));
  gslv->statistics.stats.refinements++;

  assert (!btor_hashptr_table_get (gslv->forall_ces, ce));
  btor_hashptr_table_add (gslv->forall_ces, ce)->data.as_ptr = evar_tup;
  gslv->forall_last_ce                                       = ce;

  btor_assert_exp (e_solver, res);
  btor_node_release (e_solver, res);
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
  BtorPtrHashTableIterator it;
  BtorNodePtrStack params, consts;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorSortId dsortid, cdsortid, funsortid;
  BtorSortIdStack tup_sorts;
  BtorPtrHashTable *static_rho;
  BtorMemMgr *mm;

  mm         = btor->mm;
  static_rho = btor_hashptr_table_new (mm, 0, 0);
  BTOR_INIT_STACK (mm, params);
  BTOR_INIT_STACK (mm, consts);
  BTOR_INIT_STACK (mm, tup_sorts);
  opt_synth_complete =
      btor_opt_get (btor, BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE) == 1;

  args_tuple = model->first->key;
  value      = model->first->data.as_ptr;

  /* create params from domain sort */
  for (i = 0; i < args_tuple->arity; i++)
  {
    p = btor_exp_param (btor, args_tuple->bv[i]->width, 0);
    BTOR_PUSH_STACK (params, p);
    BTOR_PUSH_STACK (tup_sorts, p->sort_id);
  }

  dsortid =
      btor_sort_tuple (btor, tup_sorts.start, BTOR_COUNT_STACK (tup_sorts));
  cdsortid  = btor_sort_bv (btor, value->width);
  funsortid = btor_sort_fun (btor, dsortid, cdsortid);
  btor_sort_release (btor, dsortid);
  btor_sort_release (btor, cdsortid);
  BTOR_RELEASE_STACK (tup_sorts);

  if (opt_synth_complete)
    e_else = btor_exp_bv_zero (btor, value->width);
  else
  {
    uf   = btor_exp_uf (btor, funsortid, 0);
    args = btor_exp_args (btor, params.start, BTOR_COUNT_STACK (params));
    assert (args->sort_id == btor_sort_fun_get_domain (btor, uf->sort_id));
    e_else = btor_exp_apply (btor, uf, args);
    assert (btor_node_real_addr (e_else)->sort_id
            == btor_sort_fun_get_codomain (btor, uf->sort_id));
    btor_node_release (btor, args);
    btor_node_release (btor, uf);
  }

  /* generate ITEs */
  ite = 0;
  res = 0;
  btor_iter_hashptr_init (&it, (BtorPtrHashTable *) model);
  while (btor_iter_hashptr_has_next (&it))
  {
    value      = (BtorBitVector *) it.bucket->data.as_ptr;
    args_tuple = btor_iter_hashptr_next (&it);

    /* create condition */
    assert (BTOR_EMPTY_STACK (consts));
    assert (BTOR_COUNT_STACK (params) == args_tuple->arity);
    for (i = 0; i < args_tuple->arity; i++)
    {
      c = btor_exp_bv_const (btor, args_tuple->bv[i]);
      assert (btor_node_real_addr (c)->sort_id
              == BTOR_PEEK_STACK (params, i)->sort_id);
      BTOR_PUSH_STACK (consts, c);
    }

    assert (!BTOR_EMPTY_STACK (params));
    assert (BTOR_COUNT_STACK (params) == BTOR_COUNT_STACK (consts));
    cond = btor_exp_eq (
        btor, BTOR_PEEK_STACK (params, 0), BTOR_PEEK_STACK (consts, 0));
    for (i = 1; i < BTOR_COUNT_STACK (params); i++)
    {
      eq = btor_exp_eq (
          btor, BTOR_PEEK_STACK (params, i), BTOR_PEEK_STACK (consts, i));
      tmp = btor_exp_bv_and (btor, cond, eq);
      btor_node_release (btor, cond);
      btor_node_release (btor, eq);
      cond = tmp;
    }

    /* args for static_rho */
    args = btor_exp_args (btor, consts.start, BTOR_COUNT_STACK (consts));

    while (!BTOR_EMPTY_STACK (consts))
      btor_node_release (btor, BTOR_POP_STACK (consts));

    /* create ITE */
    e_if = btor_exp_bv_const (btor, value);
    ite  = btor_exp_cond (btor, cond, e_if, e_else);

    /* add to static rho */
    btor_hashptr_table_add (static_rho, args)->data.as_ptr =
        btor_node_copy (btor, e_if);

    btor_node_release (btor, cond);
    btor_node_release (btor, e_if);
    btor_node_release (btor, e_else);
    e_else = ite;
  }

  assert (ite);
  if (ite) /* get rid of compiler warning */
  {
    res = btor_exp_fun (btor, params.start, BTOR_COUNT_STACK (params), ite);
    btor_node_release (btor, ite);
  }
  assert (res->sort_id == funsortid);
  btor_sort_release (btor, funsortid);

  while (!BTOR_EMPTY_STACK (params))
    btor_node_release (btor, BTOR_POP_STACK (params));
  BTOR_RELEASE_STACK (params);
  BTOR_RELEASE_STACK (consts);

  /* res already exists */
  if (((BtorLambdaNode *) res)->static_rho)
  {
    btor_iter_hashptr_init (&it, static_rho);
    while (btor_iter_hashptr_has_next (&it))
    {
      btor_node_release (btor, it.bucket->data.as_ptr);
      btor_node_release (btor, btor_iter_hashptr_next (&it));
    }
    btor_hashptr_table_delete (static_rho);
  }
  else
    ((BtorLambdaNode *) res)->static_rho = static_rho;
  return res;
}

BtorNode *
mk_concrete_ite_model (BtorGroundSolvers *gslv,
                       BtorNode *evar,
                       FlatModel *model)

{
  assert (model);

  uint32_t i;
  bool opt_synth_complete;
  BtorNode *uf;
  BtorNode *res, *c, *cond, *e_if, *e_else, *tmp, *eq, *args, *uvar;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack params;
  BtorBitVector *value, *bv;
  BtorBitVectorTuple *ce;
  BtorSortId ufsortid;
  BtorMemMgr *mm;
  Btor *btor;
  BtorArgsIterator ait;

  btor = gslv->forall;
  mm   = btor->mm;
  BTOR_INIT_STACK (mm, params);
  opt_synth_complete =
      btor_opt_get (btor, BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE) == 1;

  args = btor_nodemap_mapped (gslv->forall_evar_deps, evar);
  assert (args);

  /* create params from domain sort */
  btor_iter_args_init (&ait, args);
  while (btor_iter_args_has_next (&ait))
    BTOR_PUSH_STACK (params, btor_iter_args_next (&ait));

  if (opt_synth_complete)
    e_else = btor_exp_bv_zero (btor, evar->sort_id);
  else
  {
    ufsortid = btor_sort_fun (btor, args->sort_id, evar->sort_id);
    uf       = btor_exp_uf (btor, ufsortid, 0);
    btor_sort_release (btor, ufsortid);
    e_else = btor_exp_apply (btor, uf, args);
    assert (btor_node_real_addr (e_else)->sort_id
            == btor_sort_fun_get_codomain (btor, uf->sort_id));
    btor_node_release (btor, uf);
  }

  /* generate ITEs */
  res = 0;
  btor_iter_hashptr_init (&it, gslv->forall_ces);
  while (btor_iter_hashptr_has_next (&it))
  {
    ce    = btor_iter_hashptr_next (&it);
    value = flat_model_get_value (model, evar, ce);

    cond = 0;
    for (i = 0; i < BTOR_COUNT_STACK (params); i++)
    {
      uvar = BTOR_PEEK_STACK (params, i);
      bv   = flat_model_get_value (model, uvar, ce);
      c    = btor_exp_bv_const (btor, bv);

      eq = btor_exp_eq (btor, uvar, c);
      btor_node_release (btor, c);

      if (cond)
      {
        tmp = btor_exp_bv_and (btor, cond, eq);
        btor_node_release (btor, cond);
        btor_node_release (btor, eq);
        cond = tmp;
      }
      else
        cond = eq;
    }
    assert (cond);

    /* create ITE */
    e_if = btor_exp_bv_const (btor, value);
    res  = btor_exp_cond (btor, cond, e_if, e_else);

    btor_node_release (btor, cond);
    btor_node_release (btor, e_if);
    btor_node_release (btor, e_else);
    e_else = res;
  }
  assert (res);

  BTOR_RELEASE_STACK (params);
  return res;
}

/*------------------------------------------------------------------------*/

static BtorQuantSolver *
clone_quant_solver (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  (void) clone;
  (void) btor;
  (void) exp_map;
  return 0;
}

static void
delete_quant_solver (BtorQuantSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_QUANT_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;
  btor = slv->btor;
  delete_ground_solvers (slv, slv->gslv);
  if (slv->dgslv) delete_ground_solvers (slv, slv->dgslv);
  BTOR_DELETE (btor->mm, slv);
  btor->slv = 0;
}

/*------------------------------------------------------------------------*/

static void
build_input_output_values (BtorGroundSolvers *gslv,
                           BtorNode *evar,
                           FlatModel *flat_model,
                           BtorBitVectorTuplePtrStack *value_in,
                           BtorBitVectorPtrStack *value_out)
{
  uint32_t i, pos;
  BtorPtrHashTableIterator it;
  BtorBitVector *out;
  BtorBitVectorTuple *in, *uvar_tup, *evar_tup;
  BtorMemMgr *mm;
  Btor *btor;

  btor = gslv->forall;
  mm   = btor->mm;

  btor_iter_hashptr_init (&it, flat_model->model);
  while (btor_iter_hashptr_has_next (&it))
  {
    evar_tup = it.bucket->data.as_ptr;
    uvar_tup = btor_iter_hashptr_next (&it);

    in = btor_bv_new_tuple (mm, uvar_tup->arity + evar_tup->arity);

    pos = 0;
    for (i = 0; i < uvar_tup->arity; i++)
      btor_bv_add_to_tuple (mm, in, uvar_tup->bv[i], pos++);
    for (i = 0; i < evar_tup->arity; i++)
      btor_bv_add_to_tuple (mm, in, evar_tup->bv[i], pos++);

    out = flat_model_get_value (flat_model, evar, uvar_tup);
    BTOR_PUSH_STACK (*value_in, in);
    BTOR_PUSH_STACK (*value_out, btor_bv_copy (mm, out));
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
  cache = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, arg_stack);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, exp);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (cache, real_cur->id);
    if (!d)
    {
      btor_hashint_map_add (cache, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);

      if (btor_node_is_apply (real_cur)) continue;

      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (!btor_node_is_fun (real_cur));
      assert (!btor_node_is_apply (real_cur));
      assert (!btor_node_is_bv_var (real_cur));

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_CONST_NODE:
          result = btor_bv_copy (mm, btor_node_bv_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
          a      = flat_model_get_value (flat_model, real_cur, ce);
          result = btor_bv_copy (mm, a);
          break;

        case BTOR_BV_SLICE_NODE:
          result = btor_bv_slice (mm,
                                  bv[0],
                                  btor_node_bv_slice_get_upper (real_cur),
                                  btor_node_bv_slice_get_lower (real_cur));
          break;

        case BTOR_BV_AND_NODE: result = btor_bv_and (mm, bv[0], bv[1]); break;

        case BTOR_BV_EQ_NODE: result = btor_bv_eq (mm, bv[0], bv[1]); break;

        case BTOR_BV_ADD_NODE: result = btor_bv_add (mm, bv[0], bv[1]); break;

        case BTOR_BV_MUL_NODE: result = btor_bv_mul (mm, bv[0], bv[1]); break;

        case BTOR_BV_ULT_NODE: result = btor_bv_ult (mm, bv[0], bv[1]); break;

        case BTOR_BV_SLL_NODE: result = btor_bv_sll (mm, bv[0], bv[1]); break;

        case BTOR_BV_SRL_NODE: result = btor_bv_srl (mm, bv[0], bv[1]); break;

        case BTOR_BV_UDIV_NODE: result = btor_bv_udiv (mm, bv[0], bv[1]); break;

        case BTOR_BV_UREM_NODE: result = btor_bv_urem (mm, bv[0], bv[1]); break;

        case BTOR_BV_CONCAT_NODE:
          result = btor_bv_concat (mm, bv[0], bv[1]);
          break;

        case BTOR_EXISTS_NODE:
        case BTOR_FORALL_NODE: result = btor_bv_copy (mm, bv[1]); break;

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_bv_is_true (bv[0]))
            result = btor_bv_copy (mm, bv[1]);
          else
            result = btor_bv_copy (mm, bv[2]);
      }

      if (!btor_node_is_apply (real_cur))
      {
        for (i = 0; i < real_cur->arity; i++) btor_bv_free (mm, bv[i]);
      }

      d->as_ptr = btor_bv_copy (mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (btor_node_is_inverted (cur))
      {
        inv_result = btor_bv_not (mm, result);
        btor_bv_free (mm, result);
        result = inv_result;
      }
      BTOR_PUSH_STACK (arg_stack, result);
    }
    else
    {
      result = btor_bv_copy (mm, d->as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }

  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    btor_bv_free (mm, a);
  }
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (arg_stack);
  btor_hashint_map_delete (cache);

  return result;
}

static void
update_flat_model (BtorGroundSolvers *gslv,
                   FlatModel *flat_model,
                   BtorNode *evar,
                   BtorNode *result)
{
  uint32_t evar_pos;
  BtorPtrHashTableIterator it;
  BtorBitVectorTuple *ce, *evalues;
  BtorBitVector *bv;
  BtorPtrHashBucket *b;
  Btor *btor;
  BtorMemMgr *mm;

  btor = gslv->forall;
  mm   = btor->mm;
  evar_pos =
      btor_hashint_map_get (flat_model->evar_index_map, evar->id)->as_int;

  btor_iter_hashptr_init (&it, flat_model->model);
  while (btor_iter_hashptr_has_next (&it))
  {
    b       = it.bucket;
    evalues = b->data.as_ptr;
    ce      = btor_iter_hashptr_next (&it);
    btor_bv_free (mm, evalues->bv[evar_pos]);
    bv                    = eval_exp (btor, result, flat_model, ce);
    evalues->bv[evar_pos] = bv;
  }
}

static void
select_inputs (BtorGroundSolvers *gslv, BtorNode *var, BtorNodePtrStack *inputs)
{
  BtorNodeMapIterator nit;
  BtorArgsIterator it;
  BtorNode *args, *cur;

  if (btor_node_param_is_exists_var (var))
  {
    args = btor_nodemap_mapped (gslv->forall_evar_deps, var);
    btor_iter_args_init (&it, args);
    while (btor_iter_args_has_next (&it))
    {
      cur = btor_iter_args_next (&it);
      BTOR_PUSH_STACK (*inputs, cur);
    }
  }
  else
  {
    assert (btor_node_param_is_forall_var (var));
    btor_iter_nodemap_init (&nit, gslv->exists_evars);
    while (btor_iter_nodemap_has_next (&nit))
    {
      cur = btor_iter_nodemap_next (&nit);
      BTOR_PUSH_STACK (*inputs, cur);
    }
  }
}

static BtorNode *
synthesize (BtorGroundSolvers *gslv,
            BtorNode *evar,
            FlatModel *flat_model,
            uint32_t limit,
            BtorNode *prev_synth)
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
  reachable      = btor_hashint_table_new (mm);
  cache          = btor_hashint_table_new (mm);
  value_in_map   = btor_hashint_map_new (mm);
  opt_synth_mode = btor_opt_get (gslv->forall, BTOR_OPT_QUANT_SYNTH);

  BTOR_INIT_STACK (mm, value_in);
  BTOR_INIT_STACK (mm, value_out);
  BTOR_INIT_STACK (mm, constraints);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, inputs);

  /* value_in_map maps variables to the position in the assignment vector
   * value_in[k] */
  pos = 0;
  btor_iter_nodemap_init (&nit, gslv->forall_uvars);
  btor_iter_nodemap_queue (&nit, gslv->forall_evars);
  while (btor_iter_nodemap_has_next (&nit))
  {
    cur = btor_iter_nodemap_next (&nit);
    btor_hashint_map_add (value_in_map, cur->id)->as_int = pos++;
  }

  select_inputs (gslv, evar, &inputs);

  /* 'evar' is a special placeholder for constraint evaluation */
  btor_hashint_map_add (value_in_map, evar->id)->as_int = -1;

  build_input_output_values (gslv, evar, flat_model, &value_in, &value_out);

  if (opt_synth_mode == BTOR_QUANT_SYNTH_EL
      || opt_synth_mode == BTOR_QUANT_SYNTH_EL_ELMC)
  {
    result = btor_synthesize_term (gslv->forall,
                                   inputs.start,
                                   BTOR_COUNT_STACK (inputs),
                                   value_in.start,
                                   value_out.start,
                                   BTOR_COUNT_STACK (value_in),
                                   value_in_map,
                                   constraints.start,
                                   BTOR_COUNT_STACK (constraints),
                                   gslv->forall_consts.start,
                                   BTOR_COUNT_STACK (gslv->forall_consts),
                                   limit,
                                   0,
                                   prev_synth);
  }

  if (!result
      && (opt_synth_mode == BTOR_QUANT_SYNTH_ELMC
          || opt_synth_mode == BTOR_QUANT_SYNTH_EL_ELMC))
  {
    /* mark reachable exps */
    BTOR_PUSH_STACK (visit, gslv->forall_formula);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = btor_node_real_addr (BTOR_POP_STACK (visit));

      if (btor_hashint_table_contains (reachable, cur->id)) continue;

      btor_hashint_table_add (reachable, cur->id);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
    }

    assert (btor_hashint_table_contains (reachable, evar->id));

    /* collect constraints in cone of 'evar' */
    BTOR_PUSH_STACK (visit, evar);
    while (!BTOR_EMPTY_STACK (visit))
    {
      cur = btor_node_real_addr (BTOR_POP_STACK (visit));

      if (!btor_hashint_table_contains (reachable, cur->id)
          || btor_hashint_table_contains (cache, cur->id))
        continue;

      /* cut-off at boolean layer */
      if (btor_node_bv_get_width (gslv->forall, cur) == 1)
      {
        BTOR_PUSH_STACK (constraints, cur);
        continue;
      }

      btor_hashint_table_add (cache, cur->id);
      btor_iter_parent_init (&it, cur);
      while (btor_iter_parent_has_next (&it))
      {
        par = btor_iter_parent_next (&it);
        BTOR_PUSH_STACK (visit, par);
      }
    }
  }
  else if (opt_synth_mode == BTOR_QUANT_SYNTH_ELMR)
  {
    assert (opt_synth_mode == BTOR_QUANT_SYNTH_ELMR);
    BTOR_PUSH_STACK (constraints, gslv->forall_formula);
  }

  if (!result)
  {
    result = btor_synthesize_term (gslv->forall,
                                   inputs.start,
                                   BTOR_COUNT_STACK (inputs),
                                   value_in.start,
                                   value_out.start,
                                   BTOR_COUNT_STACK (value_in),
                                   value_in_map,
                                   constraints.start,
                                   BTOR_COUNT_STACK (constraints),
                                   gslv->forall_consts.start,
                                   BTOR_COUNT_STACK (gslv->forall_consts),
                                   limit,
                                   0,
                                   0);
  }

  if (result && btor_opt_get (gslv->forall, BTOR_OPT_QUANT_FIXSYNTH))
    update_flat_model (gslv, flat_model, evar, result);

  while (!BTOR_EMPTY_STACK (value_in))
    btor_bv_free_tuple (mm, BTOR_POP_STACK (value_in));
  while (!BTOR_EMPTY_STACK (value_out))
    btor_bv_free (mm, BTOR_POP_STACK (value_out));

  BTOR_RELEASE_STACK (inputs);

  btor_hashint_map_delete (value_in_map);
  btor_hashint_table_delete (reachable);
  btor_hashint_table_delete (cache);
  BTOR_RELEASE_STACK (value_in);
  BTOR_RELEASE_STACK (value_out);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (constraints);
  return result;
}

static BtorPtrHashTable *
synthesize_model (BtorGroundSolvers *gslv, FlatModel *flat_model)
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
  synth_model      = btor_hashptr_table_new (mm, 0, 0);
  opt_synth_mode   = btor_opt_get (f_solver, BTOR_OPT_QUANT_SYNTH);
  opt_synth_limit  = btor_opt_get (f_solver, BTOR_OPT_QUANT_SYNTH_LIMIT);

  /* reset stats for currently synthesized model */
  gslv->statistics.stats.synthesize_model_const = 0;
  gslv->statistics.stats.synthesize_model_term  = 0;
  gslv->statistics.stats.synthesize_model_none  = 0;

  /* map existential variables to their resp. assignment */
  btor_iter_nodemap_init (&it, gslv->forall_evars);
  // TODO: no UFs supported for now
  //  btor_iter_nodemap_queue (&it, gslv->exists_ufs);
  while (btor_iter_nodemap_has_next (&it))
  {
    evar = btor_iter_nodemap_next (&it);
    assert (btor_node_is_uf (evar) || btor_node_param_is_exists_var (evar));

    if (btor_terminate (gslv->forall)) break;

    synth_res = new_synth_result (mm);
    /* map skolem functions to resp. synthesized functions */
    if (btor_nodemap_mapped (gslv->forall_evar_deps, evar)
        || btor_node_is_uf (evar))
    {
      prev_synth_res = 0;
      prev_synth_fun = 0;
      candidate      = 0;
      if (opt_synth_mode)
      {
        limit = opt_synth_limit;

        /* check previously synthesized function */
        if (prev_synth_model
            && (b = btor_hashptr_table_get (prev_synth_model, evar)))
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
        synth_res->limit = limit;
      }

      assert (!btor_node_is_uf (evar));
      if (candidate)
      {
        synth_res->partial = false;
        if (btor_node_is_bv_const (candidate))
          gslv->statistics.stats.synthesize_const++;
        else
          gslv->statistics.stats.synthesize_model_term++;
        synth_res->value = candidate;
      }
      else
      {
        synth_res->value   = mk_concrete_ite_model (gslv, evar, flat_model);
        synth_res->partial = true;
        gslv->statistics.stats.synthesize_model_none++;
      }
    }
    else
    {
      bv               = flat_model_get_value (flat_model, evar, 0);
      synth_res->value = btor_exp_bv_const (f_solver, (BtorBitVector *) bv);
    }
    assert (synth_res->value);
    btor_hashptr_table_add (synth_model, evar)->data.as_ptr = synth_res;
  }

  /* update overall synthesize statistics */
  gslv->statistics.stats.synthesize_const +=
      gslv->statistics.stats.synthesize_model_const;
  gslv->statistics.stats.synthesize_term +=
      gslv->statistics.stats.synthesize_model_term;
  gslv->statistics.stats.synthesize_none +=
      gslv->statistics.stats.synthesize_model_none;

  return synth_model;
}

static void
update_formula (BtorGroundSolvers *gslv)
{
  Btor *forall;
  BtorNode *f, *g;

  forall = gslv->forall;
  f      = gslv->forall_formula;
  /* update formula if changed via simplifications */
  if (btor_node_is_proxy (f))
  {
    g = btor_node_copy (forall, btor_simplify_exp (forall, f));
    btor_node_release (forall, f);
    gslv->forall_formula = g;
  }
}

/* instantiate each universal variable with the resp. fresh bit vector variable
 * and replace existential variables with the synthesized model.
 * 'model' maps existential variables to synthesized function models. */
static BtorNode *
instantiate_formula (BtorGroundSolvers *gslv,
                     BtorPtrHashTable *model,
                     BtorNodeMap *evar_map)
{
  assert (gslv);
  assert (!btor_node_is_proxy (gslv->forall_formula));

  int32_t i;
  size_t j;
  Btor *btor;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args;
  BtorNode *cur, *real_cur, *result, **e, *a, *fun;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorNodeMap *uvar_map, *skolem;
  BtorPtrHashBucket *b;
  BtorNodeMap *deps;
  SynthResult *synth_res;
  BtorPtrHashTableIterator it;

  btor     = gslv->forall;
  mm       = btor->mm;
  mark     = btor_hashint_map_new (mm);
  uvar_map = gslv->forall_uvars;
  deps     = gslv->forall_evar_deps;
  skolem   = gslv->forall_skolem;

  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_PUSH_STACK (visit, gslv->forall_formula);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (mark, real_cur->id);
    if (!d)
    {
      if (btor_node_is_param (real_cur)
          && btor_node_param_is_exists_var (real_cur) && model
          && (b = btor_hashptr_table_get (model, real_cur)))
      {
        synth_res = b->data.as_ptr;
        assert (synth_res->value);
        BTOR_PUSH_STACK (visit, btor_node_cond_invert (cur, synth_res->value));
        continue;
      }
      btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (d->as_ptr == 0)
    {
      assert (real_cur->arity <= BTOR_COUNT_STACK (args));
      args.top -= real_cur->arity;
      e = args.top;

      if (btor_node_is_uf (real_cur))
      {
        if (model && (b = btor_hashptr_table_get (model, real_cur)))
        {
          synth_res = b->data.as_ptr;
          result    = btor_node_copy (btor, synth_res->value);
        }
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (real_cur->arity == 0)
      {
        /* instantiate universal vars with fresh bv vars in 'uvar_map' */
        if (btor_node_is_param (real_cur))
        {
          if (btor_node_param_is_forall_var (real_cur))
          {
            result = btor_nodemap_mapped (uvar_map, real_cur);
            assert (result);
            result = btor_node_copy (btor, result);
          }
          else
          {
            assert (btor_node_param_is_exists_var (real_cur));
            /* exististential vars will be substituted while
             * traversing down */
            assert (!model || !btor_hashptr_table_get (model, real_cur));
            /* no model -> substitute with skolem constant */
            fun = btor_nodemap_mapped (skolem, real_cur);
            assert (fun);
            if ((a = btor_nodemap_mapped (deps, real_cur)))
            {
              a      = instantiate_args (btor, a, uvar_map);
              result = btor_exp_apply (btor, fun, a);
              btor_node_release (btor, a);
            }
            else
              result = btor_node_copy (btor, fun);
            btor_nodemap_map (evar_map, real_cur, result);
          }
        }
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      /* universal variable got substituted by var in 'uvar_map' */
      else if (btor_node_is_forall (real_cur) || btor_node_is_exists (real_cur))
        result = btor_node_copy (btor, e[1]);
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);
    PUSH_RESULT:
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);

  /* map existential var to resp. substituted term (needed for getting
   * the value for the counterexamples) */
  if (model)
  {
    btor_iter_hashptr_init (&it, model);
    while (btor_iter_hashptr_has_next (&it))
    {
      synth_res = it.bucket->data.as_ptr;
      cur       = btor_iter_hashptr_next (&it);

      a = synth_res->value;
      d = btor_hashint_map_get (mark, btor_node_real_addr (a)->id);
      assert (d);
      btor_nodemap_map (evar_map, cur, btor_node_cond_invert (a, d->as_ptr));
    }
  }

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->keys[j]) continue;
    assert (mark->data[j].as_ptr);
    btor_node_release (btor, mark->data[j].as_ptr);
  }
  btor_hashint_map_delete (mark);

  assert (!btor_node_real_addr (result)->quantifier_below);
  assert (!btor_node_real_addr (result)->parameterized);
  return result;
}

static void
build_input_output_values_quant_inst (BtorGroundSolvers *gslv,
                                      BtorNode *uvar,
                                      BtorBitVectorTuplePtrStack *value_in,
                                      BtorBitVectorPtrStack *value_out)
{
  uint32_t i, pos, uvar_pos;
  BtorPtrHashTableIterator it;
  BtorNodeMapIterator nit;
  BtorBitVector *out;
  BtorBitVectorTuple *in, *uvar_tup, *evar_tup;
  BtorMemMgr *mm;
  Btor *btor;

  btor = gslv->forall;
  mm   = btor->mm;

  uvar_pos = 0;
  btor_iter_nodemap_init (&nit, gslv->forall_uvars);
  while (btor_iter_nodemap_has_next (&nit))
  {
    if (uvar == btor_iter_nodemap_next (&nit)) break;
    uvar_pos++;
  }

  btor_iter_hashptr_init (&it, gslv->forall_ces);
  while (btor_iter_hashptr_has_next (&it))
  {
    evar_tup = it.bucket->data.as_ptr;
    uvar_tup = btor_iter_hashptr_next (&it);

    in = btor_bv_new_tuple (mm, uvar_tup->arity + evar_tup->arity);

    pos = 0;
    for (i = 0; i < uvar_tup->arity; i++)
      btor_bv_add_to_tuple (mm, in, uvar_tup->bv[i], pos++);
    for (i = 0; i < evar_tup->arity; i++)
      btor_bv_add_to_tuple (mm, in, evar_tup->bv[i], pos++);

    out = uvar_tup->bv[uvar_pos];
    BTOR_PUSH_STACK (*value_in, in);
    BTOR_PUSH_STACK (*value_out, btor_bv_copy (mm, out));
  }
  assert (BTOR_COUNT_STACK (*value_in) == BTOR_COUNT_STACK (*value_out));
}

static BtorNode *
build_quant_inst_refinement (BtorGroundSolvers *gslv, BtorNodeMap *map)
{
  uint32_t j, arity;
  int32_t i;
  BtorNodePtrStack visit, args, params;
  BtorIntHashTable *mark;
  BtorArgsIterator ait;
  BtorNode *cur, *real_cur, **e, *result, *a, *evar;
  BtorMemMgr *mm;
  BtorHashTableData *d;
  BtorNodeMap *deps;
  Btor *btor;
  BtorSortId sort;

  btor = gslv->exists;
  mm   = btor->mm;
  mark = btor_hashint_map_new (mm);
  deps = gslv->forall_evar_deps;

  BTOR_INIT_STACK (mm, params);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);

  BTOR_PUSH_STACK (visit, gslv->forall_formula);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (mark, real_cur->id);
    if (!d)
    {
      if (btor_node_is_param (real_cur))
      {
        if (btor_node_param_is_forall_var (real_cur))
        {
          result = btor_nodemap_mapped (map, real_cur);
          assert (result);
          BTOR_PUSH_STACK (visit, btor_node_cond_invert (cur, result));
          continue;
        }
      }

      (void) btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);

      if (btor_node_is_param (real_cur)
          && btor_node_param_is_exists_var (real_cur)
          && (a = btor_nodemap_mapped (deps, real_cur)))
      {
        btor_iter_args_init (&ait, a);
        while (btor_iter_args_has_next (&ait))
          BTOR_PUSH_STACK (params, btor_iter_args_next (&ait));
        while (!BTOR_EMPTY_STACK (params))
          BTOR_PUSH_STACK (visit, BTOR_POP_STACK (params));
      }
    }
    else if (!d->as_ptr)
    {
      assert (!btor_node_is_param (real_cur)
              || !btor_node_param_is_forall_var (real_cur));
      assert (!btor_node_is_bv_var (real_cur));
      assert (!btor_node_is_uf (real_cur));

      args.top -= real_cur->arity;
      e = args.top;

      if (btor_node_is_bv_const (real_cur))
      {
        result = btor_exp_bv_const (btor, btor_node_bv_const_get_bits (real_cur));
      }
      else if (btor_node_is_param (real_cur))
      {
        assert (!btor_node_param_is_forall_var (real_cur));
        if (btor_node_param_is_exists_var (real_cur))
        {
          evar = btor_nodemap_mapped (gslv->forall_evars, real_cur);
          a    = btor_nodemap_mapped (deps, real_cur);
          if (a)
          {
            arity = btor_node_args_get_arity (a->btor, a);
            assert (BTOR_COUNT_STACK (args) >= arity);
            args.top -= arity;
            e      = args.top;
            result = btor_exp_apply_n (btor, evar, e, arity);

            for (j = 0; j < arity; j++) btor_node_release (btor, e[j]);
          }
          else
            result = btor_node_copy (btor, evar);
        }
        else
        {
          sort = btor_sort_bv (
              btor, btor_node_bv_get_width (real_cur->btor, real_cur));
          result = btor_exp_param (btor, sort, 0);
          btor_sort_release (btor, sort);
        }
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      /* universal/existential vars get substituted */
      else if (btor_node_is_quantifier (real_cur))
      {
        assert (!btor_node_is_param (e[0]));
        result = btor_node_copy (btor, e[1]);
      }
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);

    PUSH_RESULT:
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (params);

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->keys[j]) continue;
    assert (mark->data[j].as_ptr);
    btor_node_release (btor, mark->data[j].as_ptr);
  }
  btor_hashint_map_delete (mark);

  return result;
}

static void
synthesize_quant_inst (BtorGroundSolvers *gslv)
{
  uint32_t pos, num_synth = 0;
  BtorNode *cur, *uvar, *result = 0, *uconst, *c;
  BtorNode *a, *prev_synth;
  BtorMemMgr *mm;
  BtorIntHashTable *value_in_map, *input_cache;
  BtorNodePtrStack constraints, inputs, consts;
  BtorBitVectorTuplePtrStack value_in;
  const BtorBitVector *bv;
  BtorBitVectorPtrStack value_out;
  BtorNodeMapIterator it, iit;
  BtorHashTableData *d;
  BtorNodeMap *map, *prev_qi;
  Btor *f_solver, *e_solver;
  BtorArgsIterator ait;

  f_solver     = gslv->forall;
  e_solver     = gslv->exists;
  mm           = f_solver->mm;
  map          = btor_nodemap_new (f_solver);
  value_in_map = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, value_in);
  BTOR_INIT_STACK (mm, value_out);
  BTOR_INIT_STACK (mm, inputs);
  BTOR_INIT_STACK (mm, consts);
  BTOR_INIT_STACK (mm, constraints);
  BTOR_PUSH_STACK (constraints, btor_node_invert (gslv->forall_formula));

  prev_qi             = gslv->exists_cur_qi;
  gslv->exists_cur_qi = btor_nodemap_new (e_solver);

  /* value_in_map maps variables to the position in the assignment vector
   * value_in[k] */
  pos = 0;
  btor_iter_nodemap_init (&it, gslv->forall_uvars);
  btor_iter_nodemap_queue (&it, gslv->forall_evars);
  while (btor_iter_nodemap_has_next (&it))
  {
    cur = btor_iter_nodemap_next (&it);
    btor_hashint_map_add (value_in_map, cur->id)->as_int = pos++;
  }

  btor_iter_nodemap_init (&it, gslv->forall_uvars);
  while (btor_iter_nodemap_has_next (&it))
  {
    uconst = it.it.bucket->data.as_ptr;
    uvar   = btor_iter_nodemap_next (&it);
    a      = btor_nodemap_mapped (gslv->forall_uvar_deps, uvar);

    input_cache = btor_hashint_table_new (mm);
    BTOR_RESET_STACK (inputs);
    if (a)
    {
      btor_iter_args_init (&ait, a);
      while (btor_iter_args_has_next (&ait))
      {
        cur = btor_iter_args_next (&ait);
        assert (btor_node_is_regular (cur));
        assert (!btor_hashint_table_contains (input_cache, cur->id));
        btor_hashint_table_add (input_cache, cur->id);
        BTOR_PUSH_STACK (inputs, cur);
      }
    }
    btor_iter_nodemap_init (&iit, gslv->forall_evars);
    while (btor_iter_nodemap_has_next (&iit))
    {
      cur = btor_iter_nodemap_next (&iit);
      if (!btor_nodemap_mapped (gslv->forall_evar_deps, cur)
          && !btor_hashint_table_contains (input_cache, cur->id))
      {
        btor_hashint_table_add (input_cache, cur->id);
        BTOR_PUSH_STACK (inputs, cur);
      }
    }
    btor_hashint_table_delete (input_cache);

    result = 0;
    if (!BTOR_EMPTY_STACK (inputs))
    {
      build_input_output_values_quant_inst (gslv, uvar, &value_in, &value_out);
      d   = btor_hashint_map_get (value_in_map, uvar->id);
      pos = d->as_int;
      /* 'uvar' is a special placeholder for constraint evaluation */
      d->as_int = -1;

      prev_synth = 0;
      if (prev_qi) prev_synth = btor_nodemap_mapped (prev_qi, uvar);

      result = btor_synthesize_term (f_solver,
                                     inputs.start,
                                     BTOR_COUNT_STACK (inputs),
                                     value_in.start,
                                     value_out.start,
                                     BTOR_COUNT_STACK (value_in),
                                     value_in_map,
                                     constraints.start,
                                     BTOR_COUNT_STACK (constraints),
                                     consts.start,
                                     BTOR_COUNT_STACK (consts),
                                     10000,
                                     0,
                                     prev_synth);

      while (!BTOR_EMPTY_STACK (value_in))
        btor_bv_free_tuple (mm, BTOR_POP_STACK (value_in));
      while (!BTOR_EMPTY_STACK (value_out))
        btor_bv_free (mm, BTOR_POP_STACK (value_out));
      /* restore position of 'uvar' */
      d->as_int = pos;
    }

    if (result)
    {
      btor_nodemap_map (map, uvar, result);
      btor_node_release (f_solver, result);
      num_synth++;
      btor_nodemap_map (gslv->exists_cur_qi, uvar, result);
    }
    else
    {
      bv = btor_model_get_bv (f_solver, btor_simplify_exp (f_solver, uconst));
      c  = btor_exp_bv_const (f_solver, (BtorBitVector *) bv);
      btor_nodemap_map (map, uvar, c);
      btor_node_release (f_solver, c);
    }
  }

  if (num_synth > 0)
  {
    /* map UFs */
#if 0
      btor_iter_nodemap_init (&it, gslv->exists_ufs);
      while (btor_iter_nodemap_has_next (&it))
        {
          var_fs = it.it.bucket->data.as_ptr;
          var_es = btor_iter_nodemap_next (&it);
          btor_nodemap_map (map, var_fs, var_es);
        }
#endif
    result = build_quant_inst_refinement (gslv, map);
    btor_assert_exp (e_solver, result);
    btor_node_release (e_solver, result);
  }

  while (!BTOR_EMPTY_STACK (value_in))
    btor_bv_free_tuple (mm, BTOR_POP_STACK (value_in));
  while (!BTOR_EMPTY_STACK (value_out))
    btor_bv_free (mm, BTOR_POP_STACK (value_out));

  BTOR_RELEASE_STACK (inputs);
  BTOR_RELEASE_STACK (consts);
  BTOR_RELEASE_STACK (constraints);

  if (prev_qi) btor_nodemap_delete (prev_qi);
  btor_hashint_map_delete (value_in_map);
  btor_nodemap_delete (map);
  BTOR_RELEASE_STACK (value_in);
  BTOR_RELEASE_STACK (value_out);
}

static BtorSolverResult
find_model (BtorGroundSolvers *gslv, bool skip_exists)
{
  bool opt_synth_qi;
  double start;
  BtorSolverResult res          = BTOR_RESULT_UNKNOWN, r;
  BtorNode *g                   = 0;
  BtorPtrHashTable *synth_model = 0;
  BtorNodeMap *evar_map         = 0;
  FlatModel *flat_model         = 0;

  evar_map     = btor_nodemap_new (gslv->forall);
  opt_synth_qi = btor_opt_get (gslv->forall, BTOR_OPT_QUANT_SYNTH_QI) == 1;

  /* exists solver does not have any constraints, so it does not make much
   * sense to initialize every variable by zero and ask if the model
   * is correct. */
  if (!skip_exists)
  {
    /* query exists solver */
    start = time_stamp ();
    r     = btor_check_sat (gslv->exists, -1, -1);
    gslv->statistics.time.e_solver += time_stamp () - start;

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

    start      = time_stamp ();
    flat_model = flat_model_generate (gslv);

    /* synthesize model based on 'partial_model' */
    synth_model = synthesize_model (gslv, flat_model);
    flat_model_free (flat_model);

    /* save currently synthesized model */
    delete_model (gslv);
    gslv->forall_synth_model = synth_model;
    gslv->statistics.time.synth += time_stamp () - start;
  }

  start = time_stamp ();
  if (evar_map)
  {
    btor_nodemap_delete (evar_map);
    evar_map = btor_nodemap_new (gslv->forall);
  }
  g = instantiate_formula (gslv, synth_model, evar_map);
  gslv->statistics.time.checkinst += time_stamp () - start;

  /* if there are no universal variables in the formula, we have a simple
   * ground formula */
  if (gslv->forall_uvars->table->count == 0)
  {
    assert (skip_exists);
    btor_assert_exp (gslv->forall, g);
    start = time_stamp ();
    res   = btor_check_sat (gslv->forall, -1, -1);
    gslv->statistics.time.f_solver += time_stamp () - start;
    goto DONE;
  }

  btor_assume_exp (gslv->forall, btor_node_invert (g));

  /* query forall solver */
  start = time_stamp ();
  r     = btor_check_sat (gslv->forall, -1, -1);
  update_formula (gslv);
  assert (!btor_node_is_proxy (gslv->forall_formula));
  gslv->statistics.time.f_solver += time_stamp () - start;

  if (r == BTOR_RESULT_UNSAT) /* formula is SAT */
  {
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
  start = time_stamp ();
  refine_exists_solver (gslv, evar_map);
  gslv->statistics.time.refine += time_stamp () - start;

  if (opt_synth_qi)
  {
    start = time_stamp ();
    synthesize_quant_inst (gslv);
    gslv->statistics.time.qinst += time_stamp () - start;
  }

DONE:
  btor_nodemap_delete (evar_map);
  if (g) btor_node_release (gslv->forall, g);
  return res;
}

#ifdef BTOR_HAVE_PTHREADS
bool thread_found_result            = false;
pthread_mutex_t thread_result_mutex = PTHREAD_MUTEX_INITIALIZER;

void *
thread_work (void *state)
{
  BtorSolverResult res = BTOR_RESULT_UNKNOWN;
  BtorGroundSolvers *gslv;
  bool skip_exists = true;

  gslv = state;
  while (res == BTOR_RESULT_UNKNOWN && !thread_found_result)
  {
    res         = find_model (gslv, skip_exists);
    skip_exists = false;
    gslv->statistics.stats.refinements++;
  }
  pthread_mutex_lock (&thread_result_mutex);
  if (!thread_found_result)
  {
    BTOR_MSG (gslv->exists->msg,
              1,
              "found solution in %.2f seconds",
              btor_util_process_time_thread ());
    thread_found_result = true;
  }
  assert (thread_found_result || res == BTOR_RESULT_UNKNOWN);
  pthread_mutex_unlock (&thread_result_mutex);
  gslv->result = res;
  return NULL;
}

int32_t
thread_terminate (void *state)
{
  (void) state;
  return thread_found_result == true;
}

static BtorSolverResult
run_parallel (BtorGroundSolvers *gslv, BtorGroundSolvers *dgslv)
{
  BtorSolverResult res;
  pthread_t thread_orig, thread_dual;

  g_measure_thread_time = true;
  btor_set_term (gslv->forall, thread_terminate, 0);
  btor_set_term (gslv->exists, thread_terminate, 0);
  btor_set_term (dgslv->forall, thread_terminate, 0);
  btor_set_term (dgslv->exists, thread_terminate, 0);
  pthread_create (&thread_orig, 0, thread_work, gslv);
  pthread_create (&thread_dual, 0, thread_work, dgslv);
  pthread_join (thread_orig, 0);
  pthread_join (thread_dual, 0);

  if (gslv->result != BTOR_RESULT_UNKNOWN)
  {
    res = gslv->result;
  }
  else
  {
    assert (dgslv->result != BTOR_RESULT_UNKNOWN);
    if (dgslv->result == BTOR_RESULT_SAT)
    {
      BTOR_MSG (dgslv->forall->msg,
                1,
                "dual solver result: sat, original formula: unsat");
      res = BTOR_RESULT_UNSAT;
    }
    else
    {
      assert (dgslv->result == BTOR_RESULT_UNSAT);
      res = BTOR_RESULT_SAT;
      BTOR_MSG (dgslv->forall->msg,
                1,
                "dual solver result: unsat, original formula: sat");
    }
  }
  return res;
}
#endif

static BtorNode *
simplify (Btor *btor, BtorNode *g)
{
  BtorNode *tmp;

  if (btor_opt_get (btor, BTOR_OPT_QUANT_MINISCOPE))
  {
    tmp = btor_miniscope_node (btor, g);
    btor_node_release (btor, g);
    g = tmp;
  }
  if (btor_opt_get (btor, BTOR_OPT_QUANT_DER))
  {
    tmp = btor_der_node (btor, g);
    btor_node_release (btor, g);
    g = tmp;
  }
  if (btor_opt_get (btor, BTOR_OPT_QUANT_CER))
  {
    tmp = btor_cer_node (btor, g);
    btor_node_release (btor, g);
    g = tmp;
  }
  return g;
}

static BtorSolverResult
sat_quant_solver (BtorQuantSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_QUANT_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  bool skip_exists = true;
  BtorSolverResult res;
  BtorNode *g;

  BTOR_ABORT (btor_opt_get (slv->btor, BTOR_OPT_INCREMENTAL),
              "incremental mode not supported for BV");

  /* make sure that all quantifiers occur in the correct phase */
  g = btor_normalize_quantifiers (slv->btor);
  g = simplify (slv->btor, g);

  slv->gslv = setup_solvers (slv, g, false, "forall", "exists");
  btor_node_release (slv->btor, g);

#ifdef BTOR_HAVE_PTHREADS
  bool opt_dual_solver;
  opt_dual_solver = btor_opt_get (slv->btor, BTOR_OPT_QUANT_DUAL_SOLVER) == 1;

  /* disable dual solver if UFs are present in the formula */
  if (slv->gslv->exists_ufs->table->count > 0) opt_dual_solver = false;

  if (opt_dual_solver)
  {
    slv->dgslv = setup_solvers (
        slv, slv->gslv->forall_formula, true, "dual_forall", "dual_exists");
    res = run_parallel (slv->gslv, slv->dgslv);
  }
  else
#endif
  {
    while (true)
    {
      res = find_model (slv->gslv, skip_exists);
      if (res != BTOR_RESULT_UNKNOWN) break;
      skip_exists = false;
    }
    slv->gslv->result = res;
  }
  slv->btor->last_sat_result = res;
  return res;
}

static void
generate_model_quant_solver (BtorQuantSolver *slv,
                             bool model_for_all_nodes,
                             bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_QUANT_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  (void) model_for_all_nodes;
  (void) reset;

  btor_model_init_bv (slv->btor, &slv->btor->bv_model);
  btor_model_init_fun (slv->btor, &slv->btor->fun_model);

  // TODO (ma): not supported for now (needs more general model infrastructure)
}

static void
print_stats_quant_solver (BtorQuantSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_QUANT_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);
  assert (slv->gslv);

  BTOR_MSG (slv->btor->msg, 1, "");
  BTOR_MSG (slv->btor->msg,
            1,
            "cegqi solver refinements: %u",
            slv->gslv->statistics.stats.refinements);
  BTOR_MSG (slv->btor->msg,
            1,
            "cegqi solver failed refinements: %u",
            slv->gslv->statistics.stats.failed_refinements);
  if (slv->gslv->result == BTOR_RESULT_SAT
      || slv->gslv->result == BTOR_RESULT_UNKNOWN)
  {
    BTOR_MSG (slv->btor->msg,
              1,
              "model synthesized const: %u (%u)",
              slv->gslv->statistics.stats.synthesize_model_const,
              slv->gslv->statistics.stats.synthesize_const);
    BTOR_MSG (slv->btor->msg,
              1,
              "model synthesized term: %u (%u)",
              slv->gslv->statistics.stats.synthesize_model_term,
              slv->gslv->statistics.stats.synthesize_term);
    BTOR_MSG (slv->btor->msg,
              1,
              "model synthesized none: %u (%u)",
              slv->gslv->statistics.stats.synthesize_model_none,
              slv->gslv->statistics.stats.synthesize_none);
  }
  if (btor_opt_get (slv->btor, BTOR_OPT_QUANT_DUAL_SOLVER))
  {
    assert (slv->dgslv);
    BTOR_MSG (slv->btor->msg,
              1,
              "cegqi dual solver refinements: %u",
              slv->dgslv->statistics.stats.refinements);
    BTOR_MSG (slv->btor->msg,
              1,
              "cegqi dual solver failed refinements: %u",
              slv->dgslv->statistics.stats.failed_refinements);
    if (slv->dgslv->result == BTOR_RESULT_SAT
        || slv->dgslv->result == BTOR_RESULT_UNKNOWN)
    {
      BTOR_MSG (slv->btor->msg,
                1,
                "dual model synthesized const: %u (%u)",
                slv->dgslv->statistics.stats.synthesize_model_const,
                slv->dgslv->statistics.stats.synthesize_const);
      BTOR_MSG (slv->btor->msg,
                1,
                "dual model synthesized term: %u (%u)",
                slv->dgslv->statistics.stats.synthesize_model_term,
                slv->dgslv->statistics.stats.synthesize_term);
      BTOR_MSG (slv->btor->msg,
                1,
                "dual model synthesized none: %u (%u)",
                slv->dgslv->statistics.stats.synthesize_model_none,
                slv->dgslv->statistics.stats.synthesize_none);
    }
  }
}

static void
print_time_stats_quant_solver (BtorQuantSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_QUANT_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds exists solver",
            slv->gslv->statistics.time.e_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds forall solver",
            slv->gslv->statistics.time.f_solver);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds synthesizing functions",
            slv->gslv->statistics.time.synth);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds add refinement",
            slv->gslv->statistics.time.refine);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds quantifier instantiation",
            slv->gslv->statistics.time.qinst);
  BTOR_MSG (slv->btor->msg,
            1,
            "%.2f seconds check instantiation",
            slv->gslv->statistics.time.checkinst);
  if (btor_opt_get (slv->btor, BTOR_OPT_QUANT_DUAL_SOLVER))
  {
    assert (slv->dgslv);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual exists solver",
              slv->dgslv->statistics.time.e_solver);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual forall solver",
              slv->dgslv->statistics.time.f_solver);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual synthesizing functions",
              slv->dgslv->statistics.time.synth);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual add refinement",
              slv->dgslv->statistics.time.refine);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual quantifier instantiation",
              slv->dgslv->statistics.time.qinst);
    BTOR_MSG (slv->btor->msg,
              1,
              "%.2f seconds dual check instantiation",
              slv->dgslv->statistics.time.checkinst);
  }
}

/* Note: Models are always printed in SMT2 format. */
static void
print_model_quant_solver (BtorQuantSolver *slv, const char *format, FILE *file)
{
  BtorNode *cur;
  BtorPtrHashTableIterator it;
  SynthResult *synth_res;

  if (slv->gslv->result == BTOR_RESULT_SAT)
  {
    if (slv->gslv->forall_synth_model)
    {
      fprintf (
          file, "(model%s", slv->gslv->forall_synth_model->count ? "\n" : " ");

      btor_iter_hashptr_init (&it, slv->gslv->forall_synth_model);
      while (btor_iter_hashptr_has_next (&it))
      {
        synth_res = it.bucket->data.as_ptr;
        cur       = btor_iter_hashptr_next (&it);
        assert (btor_node_is_uf (cur) || btor_node_param_is_exists_var (cur));
        btor_print_node_model (
            slv->gslv->forall, cur, synth_res->value, format, file);
      }

      fprintf (file, ")\n");
    }
    else
    {
      // TODO: first check model call is already UNSAT -> any value to
      // existential vars makes formula SAT
    }
  }
  else
  {
    assert (slv->dgslv);
    assert (slv->dgslv->result == BTOR_RESULT_UNSAT);
    assert (btor_opt_get (slv->btor, BTOR_OPT_QUANT_DUAL_SOLVER));
    fprintf (file, "cannot generate model, disable --quant:dual\n");
  }
}

BtorSolver *
btor_new_quantifier_solver (Btor *btor)
{
  assert (btor);

  BtorQuantSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind      = BTOR_QUANT_SOLVER_KIND;
  slv->btor      = btor;
  slv->api.clone = (BtorSolverClone) clone_quant_solver;
  slv->api.delet = (BtorSolverDelete) delete_quant_solver;
  slv->api.sat   = (BtorSolverSat) sat_quant_solver;
  slv->api.generate_model =
      (BtorSolverGenerateModel) generate_model_quant_solver;
  slv->api.print_stats = (BtorSolverPrintStats) print_stats_quant_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_quant_solver;
  slv->api.print_model = (BtorSolverPrintModel) print_model_quant_solver;

  BTOR_MSG (btor->msg, 1, "enabled quant engine");

  return (BtorSolver *) slv;
}

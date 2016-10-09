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

//#define PRINT_DBG

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
  BtorPtrHashTable *forall_cur_model; /* currently synthesized model for
                                         existential vars */
  BtorPtrHashTable *forall_ces;       /* counter examples */
  BtorNodeMap *forall_skolem;         /* skolem functions for evars */

  Btor *exists;              /* solver for computing the model */
  BtorNodeMap *exists_evars; /* skolem constants (map to existential
                                vars of forall solver) */
  BtorNodeMap *exists_ufs;   /* UFs (non-skolem constants), map to UFs
                                of forall solver */
  BtorPtrHashTable *exists_evar_models;
  BtorNodePtrStack exists_last_ref_exps;
  BtorPtrHashTable *exists_refinements;

  BtorSolverResult result;

  BtorEFStats *statistics;
};

typedef struct BtorEFGroundSolvers BtorEFGroundSolvers;

/*------------------------------------------------------------------------*/

struct SynthResult
{
  BtorSynthType type;
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
  res->type = BTOR_SYNTH_TYPE_NONE;
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

static bool g_measure_thread_time = false;

static double
time_stamp (void)
{
  struct timespec ts;
  double res = -1;
  if (g_measure_thread_time)
  {
    if (!clock_gettime (CLOCK_THREAD_CPUTIME_ID, &ts))
      res += (double) ts.tv_sec + (double) ts.tv_nsec / 1000000000;
    return res;
  }
  else
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
      printf ("eq: %s\n", node2string (eq));
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

  if (!gslv->forall_cur_model) return;

  btor_init_node_hash_table_iterator (&it, gslv->forall_cur_model);
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

  if (!gslv->forall_cur_model) return;

  btor_init_node_hash_table_iterator (&it, gslv->forall_cur_model);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    synth_res = it.bucket->data.as_ptr;
    cur       = btor_next_node_hash_table_iterator (&it);
    assert (btor_is_uf_node (cur) || btor_param_is_exists_var (cur));
    delete_synth_result (gslv->forall->mm, synth_res);
  }
  btor_delete_ptr_hash_table (gslv->forall_cur_model);
  gslv->forall_cur_model = 0;
}

#if 1
static void
reset_refinements (BtorEFGroundSolvers *gslv)
{
  BtorNode *cur;
  BtorHashTableIterator it;

  if (!gslv->exists_refinements) return;

  btor_init_node_hash_table_iterator (&it, gslv->exists_refinements);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    btor_release_exp (gslv->exists, cur);
  }
  btor_delete_ptr_hash_table (gslv->exists_refinements);
  gslv->exists_refinements = 0;
}
#endif

#if 0
static void
update_node_map (BtorIntHashTable * node_map, BtorIntHashTable * update)
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
#endif

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
  res->exists->slv        = btor_new_fun_solver (res->exists);
  res->exists_evars       = btor_new_node_map (res->exists);
  res->exists_ufs         = btor_new_node_map (res->exists);
  res->exists_refinements = btor_new_ptr_hash_table (res->exists->mm, 0, 0);
  res->exists_evar_models = btor_new_ptr_hash_table (res->exists->mm, 0, 0);
  sorts                   = &res->exists->sorts_unique_table;

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
  BtorHashTableIterator it, iit;
  BtorPtrHashTable *m;
  BtorBitVectorTuple *ce;

  /* delete exists solver */
  btor_delete_node_map (gslv->exists_evars);
  btor_delete_node_map (gslv->exists_ufs);

  btor_init_hash_table_iterator (&it, gslv->exists_evar_models);
  while (btor_has_next_hash_table_iterator (&it))
  {
    m = it.bucket->data.as_ptr;
    (void) btor_next_hash_table_iterator (&it);
    btor_init_hash_table_iterator (&iit, m);
    while (btor_has_next_hash_table_iterator (&iit))
    {
      btor_free_bv (gslv->exists->mm, iit.bucket->data.as_ptr);
      btor_free_bv_tuple (gslv->exists->mm,
                          btor_next_hash_table_iterator (&iit));
    }
    btor_delete_ptr_hash_table (m);
  }
  btor_delete_ptr_hash_table (gslv->exists_evar_models);
  BTOR_RELEASE_STACK (gslv->exists->mm, gslv->exists_last_ref_exps);

  /* delete forall solver */
  delete_model (gslv);
  reset_refinements (gslv);
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

static void
collect_ref_exps (BtorEFGroundSolvers *gslv, BtorNode *root)
{
  uint32_t i;
  Btor *e_solver;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *mark;
  BtorMemMgr *mm;

  e_solver = gslv->exists;
  mm       = e_solver->mm;

  while (!BTOR_EMPTY_STACK (gslv->exists_last_ref_exps))
    btor_release_exp (e_solver, BTOR_POP_STACK (gslv->exists_last_ref_exps));

  mark = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (mark, cur->id)) continue;

    btor_add_int_hash_table (mark, cur->id);
    BTOR_PUSH_STACK (
        mm, gslv->exists_last_ref_exps, btor_copy_exp (e_solver, cur));

    if (btor_is_apply_node (cur)) continue;

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (mark);
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
    //      printf ("%s = ", btor_get_symbol_exp (f_solver, uvar));
    //      btor_print_bv (bv);
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

  collect_ref_exps (gslv, res);
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

#if 0
static bool
same_model (const BtorPtrHashTable * m_evar, const BtorPtrHashTable * m_input)
{
  bool found;
  uint32_t i, arity;
  BtorHashTableIterator it;
  BtorBitVectorTuple *t0, *t1;
  BtorMemMgr *mm;

  if (m_evar->count != m_input->count)
    return false;

  t0 = m_evar->first->key;
  t1 = m_input->first->key;

  /* 'evar' is more outer to 'input' in the quantifier prefix */
  if (t0->arity < t1->arity)
    return false;

  mm = m_evar->mm;
  arity = t1->arity;
  btor_init_hash_table_iterator (&it, m_evar);
  while (btor_has_next_hash_table_iterator (&it))
    {
      t0 = btor_next_hash_table_iterator (&it);
      t1 = btor_new_bv_tuple (mm, arity); 
      for (i = 0; i < arity; i++)
	btor_add_to_bv_tuple (mm, t1, t0->bv[i], i);
      found = btor_get_ptr_hash_table ((BtorPtrHashTable *) m_input, t1) != 0;
      btor_free_bv_tuple (mm, t1);
      if (!found)
	return false;
    }
  return true;
}

static bool
check_prefix (BtorEFGroundSolvers * gslv, BtorNode * evar, BtorNode * input)
{
  assert (btor_param_is_exists_var (evar));
  assert (btor_param_is_exists_var (input));

  Btor *btor;
  BtorArgsIterator it_evar, it_input;
  BtorNode *deps_evar, *deps_input, *a_evar, *a_input;

  btor = gslv->forall;
  deps_evar = btor_mapped_node (gslv->forall_evar_deps, evar);
  deps_input = btor_mapped_node (gslv->forall_evar_deps, input);
  assert (deps_evar);
  if (!deps_input)
    return true;
  assert (btor_is_args_node (deps_evar));
  assert (btor_is_args_node (deps_input));

  if (btor_get_args_arity (btor, deps_evar)
      < btor_get_args_arity (btor, deps_input))
    return false;

  btor_init_args_iterator (&it_evar, deps_evar);
  btor_init_args_iterator (&it_input, deps_input);
  while (btor_has_next_args_iterator (&it_evar))
    {
      if (!btor_has_next_args_iterator (&it_input))
	break;
      a_evar = btor_next_args_iterator (&it_evar);
      a_input = btor_next_args_iterator (&it_input);
      if (a_evar != a_input)
	return false;
    }
  return true;
}

static void
collect_inputs (BtorEFGroundSolvers * gslv, BtorNode * root, BtorNode * uf,
	        BtorPtrHashTable * inputs, BtorIntHashTable * mark)
{
  uint32_t i;
  Btor *e_solver, *f_solver;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorNode *cur, *mapped, *mapped_uf;
  BtorPtrHashBucket *b;
  const BtorPtrHashTable *m, *model;

  e_solver = gslv->exists;
  f_solver = gslv->forall;
  mm = f_solver->mm;
  mapped_uf = btor_mapped_node (gslv->exists_evars, uf);
  model = btor_get_fun_model (e_solver, uf);
  assert (mapped_uf);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (btor_contains_int_hash_table (mark, cur->id)
	  || btor_is_args_node (cur))
	continue;

      btor_add_int_hash_table (mark, cur->id);

      if (cur->arity == 0 && cur != uf)
	{
	  assert (!btor_get_ptr_hash_table (inputs, cur));
	  mapped = btor_mapped_node (gslv->exists_evars, cur);
	  if (mapped && check_prefix (gslv, mapped_uf, mapped))
	    {
	      if (btor_mapped_node (gslv->forall_evar_deps, mapped))
		{
		  m = btor_get_fun_model (e_solver, cur);
		  if (m && same_model (model, m))
		    {
		      b = btor_add_ptr_hash_table (inputs, mapped);
		      b->data.flag = true;
		      b->data.as_ptr = (BtorPtrHashTable *) m; //btor_get_fun_model (e_solver, cur);
		    }
		}
	      else
		{
		  b = btor_add_ptr_hash_table (inputs, mapped);
		  b->data.as_ptr = (BtorBitVector *) btor_get_bv_model (e_solver, cur);
		}
//	      printf ("  input: %s (%s)\n", node2string (mapped), node2string (mapped_uf));
//	      printf ("  %s %s\n", node2string (btor_param_get_binder (mapped_uf)), node2string (btor_param_get_binder (mapped)));
	    }
	  continue;
	}

      for (i = 0; i < cur->arity; i++)
	BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }
  BTOR_RELEASE_STACK (mm, visit);
}

static BtorPtrHashTable * 
find_inputs (BtorEFGroundSolvers * gslv, BtorNode * uf,
	     const BtorPtrHashTable * model)
{
  uint32_t i;
  Btor *e_solver, *f_solver;
  BtorHashTableIterator it;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *mark, *mark_in;
  BtorMemMgr *mm;
  BtorBitVector *bv;
  BtorPtrHashTable *sigs, *inputs;
//  printf ("find inputs: %s\n", node2string (uf));

  e_solver = gslv->exists;
  f_solver = gslv->forall;
  mm = f_solver->mm;

  if (e_solver->synthesized_constraints->count == 0
      && e_solver->assumptions->count == 0)
    return 0;

  mark = btor_new_int_hash_table (mm);
  mark_in = btor_new_int_hash_table (mm);
  sigs = btor_new_ptr_hash_table (mm,
				  (BtorHashPtr) btor_hash_bv,
				  (BtorCmpPtr) btor_compare_bv);
  inputs = btor_new_ptr_hash_table (mm, 0, 0);
  BTOR_INIT_STACK (visit);
#if 0
  btor_init_node_hash_table_iterator (&it, e_solver->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, e_solver->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      BTOR_PUSH_STACK (mm, visit, cur);
    }
#endif

//  printf ("  signatures:\n");
  btor_init_hash_table_iterator (&it, model);
  while (btor_has_next_hash_table_iterator (&it))
    {
      bv = it.bucket->data.as_ptr;
      (void) btor_next_hash_table_iterator (&it);
      if (!btor_get_ptr_hash_table (sigs, bv))
	{
//	  printf ("    ");
//	  btor_print_bv (bv);
	  btor_add_ptr_hash_table (sigs, bv);
	}
    }

//  printf ("find: %u\n", BTOR_COUNT_STACK (gslv->exists_last_ref_exps));
  for (i = 0; i < BTOR_COUNT_STACK (gslv->exists_last_ref_exps); i++)
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_PEEK_STACK (gslv->exists_last_ref_exps, i));
      bv = btor_get_assignment_bv (mm, cur, 1);
      if (btor_is_bv_var_node (cur) || btor_get_ptr_hash_table (sigs, bv))
	collect_inputs (gslv, cur, uf, inputs, mark_in);
      btor_free_bv (mm, bv);
    }

#if 0
  while (!BTOR_EMPTY_STACK (gslv->exists_last_ref_exps))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (gslv->exists_last_ref_exps));

      if (btor_contains_int_hash_table (mark, cur->id))
	continue;

      btor_add_int_hash_table (mark, cur->id);

      bv = btor_get_assignment_bv (mm, cur, 1);
      if (btor_get_ptr_hash_table (sigs, bv))
	collect_inputs (gslv, cur, uf, inputs, mark_in);
      btor_free_bv (mm, bv);

      if (btor_is_apply_node (cur))
	continue;

      for (i = 0; i < cur->arity; i++)
	BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }
#endif

  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (mark);
  btor_delete_int_hash_table (mark_in);
  btor_delete_ptr_hash_table (sigs);
  if (inputs->count == 0)
    {
      btor_delete_ptr_hash_table (inputs);
      inputs = 0;
    }
  return inputs;
}

static void
check_input_cycle (BtorMemMgr * mm, BtorNode * evar, BtorPtrHashTable * inputs)
{
  BtorNode *cur, *e, *cur_in;
  BtorHashTableIterator it, it2;
  BtorPtrHashTable *evar_in;
  BtorNodePtrStack visit;
  BtorPtrHashBucket *b;
  BtorIntHashTable *cache = 0;

  b = btor_get_ptr_hash_table (inputs, evar);
  if (!b)
    return;
  evar_in = b->data.as_ptr;

  if (!evar_in)
    return;

  BTOR_INIT_STACK (visit);
  cur = evar;
//      printf ("****** %s\n", node2string (cur));
  btor_init_node_hash_table_iterator (&it, evar_in);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur_in = btor_next_node_hash_table_iterator (&it);

      cache = btor_new_int_hash_table (mm);
      BTOR_PUSH_STACK (mm, visit, cur_in);
      while (!BTOR_EMPTY_STACK (visit))
	{
	  cur = BTOR_POP_STACK (visit);
	  assert (BTOR_REAL_ADDR_NODE (cur));

	  if (btor_contains_int_hash_table (cache, cur->id))
	    continue;

	  btor_add_int_hash_table (cache, cur->id);
	  if ((b = btor_get_ptr_hash_table (inputs, cur)) && b->data.as_ptr)
	    {
	      btor_init_node_hash_table_iterator (&it2, b->data.as_ptr);
	      while (btor_has_next_node_hash_table_iterator (&it2))
		{
		  e = btor_next_node_hash_table_iterator (&it2);
		  if (e == evar)
		    {
//		      printf ("CYCLE: remove %s\n", node2string (cur_in));
		      btor_remove_ptr_hash_table (evar_in, cur_in, 0, 0);
		      goto NEXT_IN;
		    }
		  BTOR_PUSH_STACK (mm, visit, e);
		}
	    }
	}
NEXT_IN:
      btor_delete_int_hash_table (cache);
    }
  BTOR_RELEASE_STACK (mm, visit);

#if 0
  btor_init_node_hash_table_iterator (&it, evar_in);
  while (btor_has_next_node_hash_table_iterator (&it))
    printf ("  input: %s\n", node2string (btor_next_node_hash_table_iterator (&it)));
#endif
}

static void
check_inputs_used (BtorMemMgr * mm, BtorNode * synth_fun,
		   BtorPtrHashTable * inputs)
{
  uint32_t i;
  BtorNodePtrStack visit;
  BtorNode *cur;
  BtorIntHashTable *cache;
  BtorHashTableIterator it;

  if (!inputs)
    return;

  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, synth_fun);
  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

      if (btor_contains_int_hash_table (cache, cur->id)
	  || !cur->parameterized)
	continue;

      btor_add_int_hash_table (cache, cur->id);
      for (i = 0; i < cur->arity; i++)
	BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }
  BTOR_RELEASE_STACK (mm, visit);

  btor_init_node_hash_table_iterator (&it, inputs);
  while (btor_has_next_node_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));

      if (!btor_contains_int_hash_table (cache, cur->id))
	{
//	  printf ("remove unused: %s\n", node2string (cur));
	  btor_remove_ptr_hash_table (inputs, cur, 0, 0);
	}
    }
  btor_delete_int_hash_table (cache);
}
#endif

/*------------------------------------------------------------------------*/

static BtorPtrHashTable *
generate_model (BtorEFGroundSolvers *gslv)
{
  Btor *e_solver;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;
  const BtorPtrHashTable *fun_model;
  BtorBitVectorTuple *tup;
  BtorPtrHashTable *res, *t;
  BtorNode *e_uf_fs, *e_uf;
  BtorHashTableIterator hit;

  e_solver = gslv->exists;
  res      = btor_new_ptr_hash_table (e_solver->mm, 0, 0);

  /* generate model for exists vars/ufs */
  assert (e_solver->last_sat_result == BTOR_RESULT_SAT);
  e_solver->slv->api.generate_model (e_solver->slv, false, false);

  btor_init_node_map_iterator (&it, gslv->exists_evars);
  btor_queue_node_map_iterator (&it, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    e_uf_fs = it.it.bucket->data.as_ptr;
    e_uf    = btor_next_node_map_iterator (&it);
    assert (btor_is_uf_node (e_uf_fs) || btor_param_is_exists_var (e_uf_fs));

    /* map skolem functions to resp. synthesized functions */
    if (btor_mapped_node (gslv->forall_evar_deps, e_uf_fs)
        || btor_is_uf_node (e_uf_fs))
    {
      fun_model = btor_get_fun_model (e_solver, e_uf);
      if (!fun_model) continue;

      t = btor_new_ptr_hash_table (e_solver->mm,
                                   (BtorHashPtr) btor_hash_bv_tuple,
                                   (BtorCmpPtr) btor_compare_bv_tuple);
      btor_init_hash_table_iterator (&hit, fun_model);
      while (btor_has_next_hash_table_iterator (&hit))
      {
        bv  = hit.bucket->data.as_ptr;
        tup = btor_next_hash_table_iterator (&hit);
        btor_add_ptr_hash_table (t, btor_copy_bv_tuple (e_solver->mm, tup))
            ->data.as_ptr = btor_copy_bv (e_solver->mm, bv);
      }
      btor_add_ptr_hash_table (res, e_uf_fs)->data.as_ptr = t;
    }
    else
    {
      assert (btor_is_bitvec_sort (&e_solver->sorts_unique_table,
                                   BTOR_REAL_ADDR_NODE (e_uf)->sort_id));
      bv = btor_get_bv_model (e_solver, btor_simplify_exp (e_solver, e_uf));
      btor_add_ptr_hash_table (res, e_uf_fs)->data.as_ptr =
          btor_copy_bv (e_solver->mm, bv);
    }
  }
  return res;
}

static void
update_model (Btor *btor,
              BtorMemMgr *mm,
              BtorNode *evar,
              BtorPtrHashTable *models)
{
  const BtorPtrHashTable *m;
  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;
  const BtorBitVector *bv;
  BtorBitVectorTuple *tup;
  BtorHashTableIterator it;

  b = btor_get_ptr_hash_table (models, evar);
  if (btor_is_uf_node (evar))
  {
    m = btor_get_fun_model (btor, btor_simplify_exp (btor, evar));
    if (!m) return;

    if (b->data.as_ptr)
      t = b->data.as_ptr;
    else
    {
      t              = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_bv_tuple,
                                   (BtorCmpPtr) btor_compare_bv_tuple);
      b->data.as_ptr = t;
    }
    btor_init_hash_table_iterator (&it, m);
    while (btor_has_next_hash_table_iterator (&it))
    {
      bv  = it.bucket->data.as_ptr;
      tup = btor_next_hash_table_iterator (&it);
      if (btor_get_ptr_hash_table (t, tup)) continue;
      btor_add_ptr_hash_table (t, btor_copy_bv_tuple (mm, tup))->data.as_ptr =
          btor_copy_bv (mm, bv);
    }
  }
  else
  {
    if (b->data.as_ptr) return;
    bv             = btor_get_bv_model (btor, btor_simplify_exp (btor, evar));
    b->data.as_ptr = btor_copy_bv (mm, bv);
  }
}

#if 0
static BtorNode *
extract_branch (Btor * btor, BtorNode * root)
{
  int32_t i;
  uint32_t j;
  BtorNode *cur, *real_cur, **e, *result;
  const BtorBitVector *bv;
  BtorNodePtrStack visit, args;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;

  mm = btor->mm;
  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_PUSH_STACK (mm, visit, root);

  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_POP_STACK (visit);
      real_cur = BTOR_REAL_ADDR_NODE (cur);

      d = btor_get_int_hash_map (mark, real_cur->id);
      if (!d)
	{
	  btor_add_int_hash_map (mark, real_cur->id);
	  BTOR_PUSH_STACK (mm, visit, cur);
	  for (i = real_cur->arity - 1; i >= 0; i--)
	    BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
	}
      else if (!d->as_ptr)
	{
	  assert (BTOR_COUNT_STACK (args) >= real_cur->arity);

	  args.top -= real_cur->arity;
	  e = args.top;

	  if (real_cur->arity == 0)
	    {
	      if (btor_is_param_node (real_cur))
		{
		  result =
		    btor_param_exp (btor,
			btor_get_exp_width (btor, real_cur), 0);
		}
	      else
		{
		  result = btor_copy_exp (btor, real_cur);
		}
	    }
	  else if (btor_is_slice_node (real_cur))
	    {
	      result = btor_slice_exp (btor, e[0],
				       btor_slice_get_upper (real_cur),
				       btor_slice_get_lower (real_cur));
	    }
	  else if (btor_is_and_node (real_cur)
		   && btor_get_exp_width (btor, real_cur) == 1
		   && (bv = btor_get_bv_model (btor, real_cur))
		   && btor_is_zero_bv (bv))
	    {
	      bv = btor_get_bv_model (btor, real_cur->e[0]);
	      if (btor_is_zero_bv (bv))
		result = btor_copy_exp (btor, e[0]);
	      else
		result = btor_copy_exp (btor, e[1]);
#if 0
	      bv = btor_get_bv_model (btor, real_cur->e[1]);
	      if (btor_is_zero_bv (bv))
		{
		  printf ("branch 1 is zero\n");
		  result = btor_copy_exp (btor, e[1]);
		}
#endif
	    }
	  else
	    {
	      result =
		btor_create_exp (btor, real_cur->kind, e, real_cur->arity);
	    }

	  for (i = 0; i < real_cur->arity; i++)
	    btor_release_exp (btor, e[i]);

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
#endif

static BtorPtrHashTable *
find_partial_model (BtorEFGroundSolvers *gslv)
{
  uint32_t i, opt_pmfind_mode;
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
  BtorPtrHashTable *r_evars_ufs, *result;
  BtorMemMgr *mm;
  BtorSolverResult r;
  BtorSortId sort_id;
  BtorHashTableIterator ce_it, hit;
  BtorPtrHashBucket *b;

  r_solver = btor_new_btor ();
  f_solver = gslv->forall;
  e_solver = gslv->exists;
  btor_delete_opts (r_solver);
  btor_clone_opts (e_solver, r_solver);
  opt_pmfind_mode = btor_get_opt (r_solver, BTOR_OPT_EF_FINDPM_MODE);
  assert (opt_pmfind_mode == BTOR_EF_FINDPM_REF);

  mm = e_solver->mm;

  map         = btor_new_node_map (r_solver);
  varmap      = btor_new_node_map (r_solver);
  rev_varmap  = btor_new_node_map (r_solver);
  rev_evars   = btor_new_node_map (r_solver);
  r_evars_ufs = btor_new_ptr_hash_table (mm, 0, 0);
  result      = btor_new_ptr_hash_table (mm, 0, 0);
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
  i  = 0;
  ce = gslv->forall_ces->last->key;
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
    //      printf ("%s = %zu ", btor_get_symbol_exp (f_solver, uvar),
    //      btor_bv_to_uint64_bv (bv)); btor_print_bv (bv);
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

    a = btor_mapped_node (gslv->forall_evar_deps, var_fs);
    if (a)
    {
      assert (btor_is_uf_node (var_es));
      a      = instantiate_args (r_solver, a, varmap);
      r_evar = btor_uf_exp (r_solver, sort_id, 0);
      var_es = btor_apply_exp (r_solver, r_evar, a);
      btor_map_node (varmap, var_fs, var_es);
      btor_release_exp (r_solver, a);
      btor_release_exp (r_solver, var_es);
    }
    else
    {
      r_evar =
          btor_var_exp (r_solver, btor_get_exp_width (e_solver, var_es), 0);
      btor_map_node (varmap, var_fs, r_evar);
      BTOR_PUSH_STACK (mm, outer_evars, r_evar);
    }
    btor_add_ptr_hash_table (r_evars_ufs, r_evar);
    btor_map_node (rev_evars, r_evar, var_fs);
    btor_release_sort (&r_solver->sorts_unique_table, sort_id);
  }

  /* map UFs */
  btor_init_node_map_iterator (&it, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs  = it.it.bucket->data.as_ptr;
    var_es  = btor_next_node_map_iterator (&it);
    sort_id = btor_recursively_rebuild_sort_clone (
        e_solver, r_solver, var_es->sort_id);
    var_es = btor_uf_exp (r_solver, sort_id, 0);
    btor_release_sort (&r_solver->sorts_unique_table, sort_id);
    btor_map_node (varmap, var_fs, var_es);
    btor_map_node (rev_evars, var_es, var_fs);
    btor_add_ptr_hash_table (r_evars_ufs, var_es);
  }

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
  btor_init_node_map_iterator (&it, gslv->exists_evars);
  while (btor_has_next_node_map_iterator (&it))
  {
    var_fs = it.it.bucket->data.as_ptr;
    var_es = btor_next_node_map_iterator (&it);
    if (btor_mapped_node (gslv->forall_evar_deps, var_fs)) continue;
    bv     = btor_get_bv_model (e_solver, btor_simplify_exp (e_solver, var_es));
    r_evar = btor_mapped_node (varmap, var_fs);
    assert (r_evar);
    c  = btor_const_exp (r_solver, (BtorBitVector *) bv);
    eq = btor_eq_exp (r_solver, r_evar, c);
    btor_release_exp (r_solver, c);
    btor_assert_exp (r_solver, eq);
  }

  /* initial SAT call */
#if 1
  btor_assert_exp (r_solver, ref);
  btor_release_exp (r_solver, ref);
#else
  // extract branch code
  btor_assume_exp (r_solver, ref);
#endif

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
#if 0
      // extract branch code
      root = extract_branch (r_solver, ref);
      btor_release_exp (r_solver, ref);
      printf ("extracted branch: \n");
      btor_dump_smt2_node (r_solver, stdout, root, -1);
#else
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
#endif

    /* fix assignments of outermost existential variables */
    for (i = 0; i < BTOR_COUNT_STACK (outer_evars); i++)
    {
      r_evar = BTOR_PEEK_STACK (outer_evars, i);
      bv = btor_get_bv_model (r_solver, btor_simplify_exp (r_solver, r_evar));
      c  = btor_const_exp (r_solver, (BtorBitVector *) bv);
      eq = btor_eq_exp (r_solver, r_evar, c);
      btor_release_exp (r_solver, c);
      BTOR_POKE_STACK (outer_evars, i, eq);
    }

    /* NOTE: this needs to be done in a second step since asserting will
     * delete the model via 'btor_reset_incremental_usage' */
    for (i = 0; i < BTOR_COUNT_STACK (outer_evars); i++)
    {
      eq = BTOR_PEEK_STACK (outer_evars, i);
      btor_assert_exp (r_solver, eq);
      btor_release_exp (r_solver, eq);
    }

#if 0
      // extract branch code
      btor_assert_exp (r_solver, root);
      btor_release_exp (r_solver, root);
#endif

    btor_init_hash_table_iterator (&ce_it, gslv->forall_ces);
    while (btor_has_next_hash_table_iterator (&ce_it))
    {
      i  = 0;
      ce = btor_next_hash_table_iterator (&ce_it);
      btor_init_node_map_iterator (&it, gslv->forall_uvars);
      while (btor_has_next_node_map_iterator (&it))
      {
        var = btor_mapped_node (varmap, btor_next_node_map_iterator (&it));
        bv  = ce->bv[i++];
        c   = btor_const_exp (r_solver, (BtorBitVector *) bv);
        //		  printf ("check CE = "); btor_print_bv (bv);
        eq = btor_eq_exp (r_solver, var, c);
        btor_assume_exp (r_solver, eq);
        btor_release_exp (r_solver, c);
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
      if (r == BTOR_RESULT_UNSAT) continue;

      assert (r == BTOR_RESULT_SAT);
      btor_init_node_hash_table_iterator (&hit, r_evars_ufs);
      while (btor_has_next_node_hash_table_iterator (&hit))
      {
        r_evar = btor_next_node_hash_table_iterator (&hit);
        update_model (r_solver, mm, r_evar, r_evars_ufs);
      }
    }
  }

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

  /* generate model */
  btor_init_node_hash_table_iterator (&hit, r_evars_ufs);
  while (btor_has_next_node_hash_table_iterator (&hit))
  {
    b      = hit.bucket;
    r_evar = btor_next_node_hash_table_iterator (&hit);
    if (!b->data.as_ptr) continue;
    btor_add_ptr_hash_table (result, btor_mapped_node (rev_evars, r_evar))
        ->data.as_ptr = b->data.as_ptr;
  }

  btor_delete_node_map (map);
  btor_delete_node_map (varmap);
  btor_delete_node_map (rev_varmap);
  btor_delete_node_map (rev_evars);
  btor_delete_ptr_hash_table (r_evars_ufs);
  btor_delete_int_hash_table (cache);

  btor_delete_btor (r_solver);
  return result;
}

static bool
check_constraint_inputs (Btor *btor,
                         BtorNode *root,
                         BtorIntHashTable *allowed_inputs)
{
  uint32_t i;
  bool res = true;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;

  mm    = btor->mm;
  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cache, cur->id)) continue;

    if (cur->arity == 0 && !btor_is_bv_const_node (cur)
        && !btor_contains_int_hash_table (allowed_inputs, cur->id))
    {
      res = false;
      break;
    }

    btor_add_int_hash_table (cache, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (cache);
  return res;
}

static BtorNode *
synthesize_modulo_constraints (BtorEFGroundSolvers *gslv,
                               BtorNode *evar,
                               const BtorPtrHashTable *uf_model,
                               uint32_t limit,
                               BtorNode *prev_synth_fun)
{
  uint32_t i;
  BtorNode *cur, *par, *result = 0, *args;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *reachable, *cache, *allowed_inputs;
  BtorNodeIterator it;
  BtorNodePtrStack constraints, cinputs;
  BtorArgsIterator ait;

  mm             = gslv->forall->mm;
  reachable      = btor_new_int_hash_table (mm);
  cache          = btor_new_int_hash_table (mm);
  allowed_inputs = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (cinputs);
  BTOR_INIT_STACK (constraints);
  BTOR_INIT_STACK (visit);

  args = btor_mapped_node (gslv->forall_evar_deps, evar);
  assert (args);
  btor_init_args_iterator (&ait, args);
  while (btor_has_next_args_iterator (&ait))
  {
    cur = btor_next_args_iterator (&ait);
    btor_add_int_hash_table (allowed_inputs, cur->id);
    BTOR_PUSH_STACK (mm, cinputs, cur);
  }
  btor_add_int_hash_table (allowed_inputs, evar->id);

  BTOR_PUSH_STACK (mm, visit, gslv->forall_formula);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (reachable, cur->id)) continue;

    btor_add_int_hash_table (reachable, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  assert (btor_contains_int_hash_table (reachable, evar->id));

  BTOR_PUSH_STACK (mm, visit, evar);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (!btor_contains_int_hash_table (reachable, cur->id)
        || btor_contains_int_hash_table (cache, cur->id))
      continue;

    if (btor_is_bv_eq_node (cur) || btor_is_ult_node (cur))
    {
      printf ("constraint: %s\n", node2string (cur));
      if (check_constraint_inputs (gslv->forall, cur, allowed_inputs))
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

  if (BTOR_COUNT_STACK (constraints) > 0)
  {
    result =
        btor_synthesize_fun_constraints (gslv->forall,
                                         uf_model,
                                         prev_synth_fun,
                                         evar,
                                         constraints.start,
                                         BTOR_COUNT_STACK (constraints),
                                         cinputs.start,
                                         BTOR_COUNT_STACK (cinputs),
                                         gslv->forall_consts.start,
                                         BTOR_COUNT_STACK (gslv->forall_consts),
                                         limit,
                                         0);
  }

  btor_delete_int_hash_table (allowed_inputs);
  btor_delete_int_hash_table (reachable);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, constraints);
  BTOR_RELEASE_STACK (mm, cinputs);
  return result;
}

static BtorPtrHashTable *
synthesize_model (BtorEFGroundSolvers *gslv, BtorPtrHashTable *uf_models)
{
  uint32_t limit;
  uint32_t opt_synth_limit, opt_synth_mode;
  BtorPtrHashTable *model, *prev_model;
  Btor *e_solver, *f_solver;
  BtorNode *e_uf, *e_uf_fs, *prev_synth_fun, *candidate;
  BtorNodeMapIterator it;
  const BtorBitVector *bv;
  const BtorPtrHashTable *uf_model;
  SynthResult *synth_res, *prev_synth_res;
  BtorPtrHashBucket *b;
  BtorMemMgr *mm;

  e_solver        = gslv->exists;
  f_solver        = gslv->forall;
  mm              = f_solver->mm;
  prev_model      = gslv->forall_cur_model;
  model           = btor_new_ptr_hash_table (mm, 0, 0);
  opt_synth_mode  = btor_get_opt (f_solver, BTOR_OPT_EF_SYNTH);
  opt_synth_limit = btor_get_opt (f_solver, BTOR_OPT_EF_SYNTH_LIMIT);
#if 0
  inputs = btor_new_ptr_hash_table (mm, 0, 0);
#endif

  /* reset stats for currently synthesized model */
  gslv->statistics->stats.synthesize_model_const = 0;
  gslv->statistics->stats.synthesize_model_term  = 0;
  gslv->statistics->stats.synthesize_model_none  = 0;

  /* map existential variables to their resp. assignment */
  btor_init_node_map_iterator (&it, gslv->exists_evars);
  btor_queue_node_map_iterator (&it, gslv->exists_ufs);
  while (btor_has_next_node_map_iterator (&it))
  {
    e_uf_fs = it.it.bucket->data.as_ptr;
    e_uf    = btor_next_node_map_iterator (&it);
    assert (btor_is_uf_node (e_uf_fs) || btor_param_is_exists_var (e_uf_fs));

    /* map skolem functions to resp. synthesized functions */
    if (btor_mapped_node (gslv->forall_evar_deps, e_uf_fs)
        || btor_is_uf_node (e_uf_fs))
    {
      /* 'e_uf_fs' is an existential variable */
      assert (btor_is_fun_sort (&e_solver->sorts_unique_table,
                                BTOR_REAL_ADDR_NODE (e_uf)->sort_id));
      assert (btor_is_uf_node (e_uf));

      b = btor_get_ptr_hash_table (uf_models, e_uf_fs);
      if (!b) continue;

      uf_model = b->data.as_ptr;
      if (!uf_model) continue;

      synth_res      = new_synth_result (mm);
      prev_synth_res = 0;
      prev_synth_fun = 0;
      candidate      = 0;
      if (opt_synth_mode)
      {
        limit = opt_synth_limit;

        /* check previously synthesized function */
        if (prev_model && (b = btor_get_ptr_hash_table (prev_model, e_uf_fs)))
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
        if (limit > 100000) limit = opt_synth_limit;

#if 0
	      b = btor_add_ptr_hash_table (inputs, e_uf_fs);
	      // TODO: disable for now (not required)
	      if (false && !btor_is_uf_node (e_uf_fs))
		{
		  assert (btor_param_is_exists_var (e_uf_fs));
		  in = find_inputs (gslv, e_uf, uf_model);
		}
	      else
		in = 0;
	      b->data.as_ptr = in;
	      check_input_cycle (mm, e_uf_fs, inputs);
#endif
        //	      printf ("synthesize model for %s\n", btor_get_symbol_exp
        //(f_solver, e_uf_fs));
        if (opt_synth_mode == BTOR_EF_SYNTH_EL
            || opt_synth_mode == BTOR_EF_SYNTH_EL_ELMC)
        {
          candidate =
              btor_synthesize_fun (f_solver,
                                   uf_model,
                                   prev_synth_fun,
                                   0,
                                   gslv->forall_consts.start,
                                   BTOR_COUNT_STACK (gslv->forall_consts),
                                   limit,
                                   0);
        }
        if (!candidate
            && (opt_synth_mode == BTOR_EF_SYNTH_ELMC
                || opt_synth_mode == BTOR_EF_SYNTH_EL_ELMC))
        {
          candidate = synthesize_modulo_constraints (
              gslv, e_uf_fs, uf_model, limit, prev_synth_fun);
        }
        synth_res->limit = limit;
      }

      if (btor_is_uf_node (e_uf_fs))
        synth_res->type = BTOR_SYNTH_TYPE_UF;
      else
        synth_res->type = BTOR_SYNTH_TYPE_SK_UF;

      if (candidate)
      {
        synth_res->partial = false;
        assert (btor_is_lambda_node (candidate));
        if (btor_is_bv_const_node (btor_binder_get_body (candidate)))
          gslv->statistics->stats.synthesize_const++;
        else
          gslv->statistics->stats.synthesize_model_term++;
#if 0
	      if (!btor_is_uf_node (e_uf_fs))
		check_inputs_used (mm, candidate, in);
#endif
        synth_res->value = candidate;
      }
      else
      {
        synth_res->value   = mk_concrete_lambda_model (f_solver, uf_model);
        synth_res->partial = true;
        gslv->statistics->stats.synthesize_model_none++;
      }
      btor_add_ptr_hash_table (model, e_uf_fs)->data.as_ptr = synth_res;
    }
    else
    {
      assert (btor_is_bitvec_sort (&e_solver->sorts_unique_table,
                                   BTOR_REAL_ADDR_NODE (e_uf)->sort_id));

      b = btor_get_ptr_hash_table (uf_models, e_uf_fs);
      assert (b);
      assert (b->data.as_ptr);
      bv = b->data.as_ptr;
#ifdef PRINT_DBG
      printf ("exists %s := ", node2string (e_uf));
      btor_print_bv (bv);
#endif
      synth_res        = new_synth_result (mm);
      synth_res->type  = BTOR_SYNTH_TYPE_SK_VAR;
      synth_res->value = btor_const_exp (f_solver, (BtorBitVector *) bv);
      btor_add_ptr_hash_table (model, e_uf_fs)->data.as_ptr = synth_res;
    }
  }

  /* update overall synthesize statistics */
  gslv->statistics->stats.synthesize_const +=
      gslv->statistics->stats.synthesize_model_const;
  gslv->statistics->stats.synthesize_term +=
      gslv->statistics->stats.synthesize_model_term;
  gslv->statistics->stats.synthesize_none +=
      gslv->statistics->stats.synthesize_model_none;

#if 0
  btor_init_node_hash_table_iterator (&hit, inputs);
  while (btor_has_next_node_hash_table_iterator (&hit))
    {
      if (hit.bucket->data.as_ptr)
	btor_delete_ptr_hash_table (hit.bucket->data.as_ptr);
      (void) btor_next_node_hash_table_iterator (&hit);
    }
  btor_delete_ptr_hash_table (inputs);
#endif
#if 0
  BTOR_RELEASE_STACK (mm, evars);
#endif
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

static BtorNode *
substitute_evar (Btor *btor, BtorNode *root, BtorNode *evar, BtorNode *subst)
{
  int32_t i;
  size_t j;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args;
  BtorNode *cur, *real_cur, *result, **e;
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

    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (d->as_ptr == 0)
    {
      assert (!btor_is_quantifier_node (real_cur));
      assert (real_cur->arity <= BTOR_COUNT_STACK (args));
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        /* substitute evar */
        if (real_cur == evar)
        {
          assert (btor_param_is_exists_var (real_cur));
          result = btor_copy_exp (btor, subst);
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
  return result;
}

static BtorNode *
expand_evars (Btor *btor, BtorNode *exp, BtorPtrHashTable *model)
{
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_lambda_node (exp));
  assert (exp->parameterized);
  assert (model);

  int32_t i;
  size_t j;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args, cleanup;
  BtorNode *cur, *real_cur, *result, **e, *tmp, *subst;
  BtorNode *l0, *l1;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorPtrHashBucket *b;
  BtorNodeMap *funs;
  SynthResult *synth_res;
  BtorNodeIterator nit0, nit1;

  mm   = btor->mm;
  mark = btor_new_int_hash_map (mm);
  funs = btor_new_node_map (btor);

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (cleanup);
  BTOR_PUSH_STACK (mm, visit, exp);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
      if ((b = btor_get_ptr_hash_table (model, real_cur)))
      {
        synth_res = b->data.as_ptr;
        if (synth_res->type == BTOR_SYNTH_TYPE_SK_UF)
        {
          tmp = synth_res->value;

          btor_init_lambda_iterator (&nit0, tmp);
          btor_init_lambda_iterator (&nit1, exp);
          while (btor_has_next_lambda_iterator (&nit0))
          {
            assert (btor_has_next_lambda_iterator (&nit1));
            l0 = btor_next_lambda_iterator (&nit0);
            l1 = btor_next_lambda_iterator (&nit1);
            btor_assign_param (btor, l0, l1->e[0]);
          }
          subst = btor_beta_reduce_full (btor, btor_binder_get_body (tmp));
          btor_unassign_params (btor, tmp);
          BTOR_PUSH_STACK (mm, cleanup, subst);
        }
        else
          subst = synth_res->value;
        BTOR_PUSH_STACK (mm, visit, BTOR_COND_INVERT_NODE (cur, subst));
      }
      else
      {
        btor_add_int_hash_map (mark, real_cur->id);
        BTOR_PUSH_STACK (mm, visit, cur);
        for (i = real_cur->arity - 1; i >= 0; i--)
          BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
      }
    }
    else if (d->as_ptr == 0)
    {
      assert (!btor_get_ptr_hash_table (model, real_cur));
      assert (real_cur->arity <= BTOR_COUNT_STACK (args));
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_is_param_node (real_cur))
          result =
              btor_param_exp (btor, btor_get_exp_width (btor, real_cur), 0);
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

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_release_exp (btor, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (mm, cleanup);

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->data[j].as_ptr) continue;
    btor_release_exp (btor, mark->data[j].as_ptr);
  }
  btor_delete_int_hash_map (mark);
  btor_delete_node_map (funs);

  assert (!BTOR_REAL_ADDR_NODE (result)->quantifier_below);
  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);
  return result;
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
  BtorNode *cur, *real_cur, *result, **e, *subst, *evar, *a, *app;
  BtorNode *fun;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorNodeMap *uvar_map, *skolem;
  BtorPtrHashBucket *b;
  BtorNodeMap *deps, *funs;
  SynthResult *synth_res;
  BtorHashTableIterator it;

  btor     = gslv->forall;
  mm       = btor->mm;
  mark     = btor_new_int_hash_map (mm);
  uvar_map = gslv->forall_uvars;
  deps     = gslv->forall_evar_deps;
  skolem   = gslv->forall_skolem;
  funs     = btor_new_node_map (btor);

  /* instantiate synthesized functions that still contain existential variables
   */
  if (model)
  {
    btor_init_node_hash_table_iterator (&it, model);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      synth_res = it.bucket->data.as_ptr;
      cur       = btor_next_node_hash_table_iterator (&it);
      if (synth_res->type == BTOR_SYNTH_TYPE_SK_UF)
      {
        cur = synth_res->value;
        assert (BTOR_IS_REGULAR_NODE (cur));
        if (cur->parameterized)
        {
          //		  printf ("parameterized: %s\n", node2string (cur));
          subst = expand_evars (btor, cur, model);
          assert (!BTOR_REAL_ADDR_NODE (subst)->parameterized);
        }
        else
          subst = btor_copy_exp (btor, cur);
        if (!btor_mapped_node (funs, cur)) btor_map_node (funs, cur, subst);
        btor_release_exp (btor, subst);
      }
    }
  }

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);

  //  uint32_t num_exps = 0;
  //  for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++)
  //    num_exps += gslv->forall->ops[i].cur;
  BTOR_PUSH_STACK (mm, visit, gslv->forall_formula);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
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
          assert (synth_res->type == BTOR_SYNTH_TYPE_UF);
          result = btor_copy_exp (btor, synth_res->value);
        }
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (real_cur->arity == 0)
      {
        /* instantiate universal vars with fresh bv vars in 'uvar_map' */
        if (btor_is_param_node (real_cur)
            && btor_param_is_forall_var (real_cur))
        {
          result = btor_mapped_node (uvar_map, real_cur);
          assert (result);
          result = btor_copy_exp (btor, result);
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
      else if (btor_is_forall_node (real_cur))
      {
        result = btor_copy_exp (btor, e[1]);
      }
      /* substitute existential variable with either the synthesized model
       * or a fresh skolem constant */
      else if (btor_is_exists_node (real_cur))
      {
        evar = real_cur->e[0];

        if (model && (b = btor_get_ptr_hash_table (model, evar)))
        {
          synth_res = b->data.as_ptr;
          if (synth_res->type == BTOR_SYNTH_TYPE_SK_UF)
          {
            a = btor_mapped_node (deps, evar);
            assert (a);
            a   = instantiate_args (btor, a, uvar_map);
            fun = btor_mapped_node (funs, synth_res->value);
            assert (fun);
            assert (btor_is_lambda_node (fun));
            app = btor_apply_exp (btor, fun, a);
            // TODO: try to beta reduce fun and measure performance
            result = substitute_evar (btor, e[1], evar, app);
            btor_release_exp (btor, app);
            btor_release_exp (btor, a);
            assert (result);
          }
          else
          {
            assert (synth_res->type == BTOR_SYNTH_TYPE_SK_VAR);
            assert (btor_is_bv_const_node (synth_res->value));
            result = substitute_evar (btor, e[1], evar, synth_res->value);
          }
        }
        /* no model -> substitute with skolem constant */
        else
        {
          fun = btor_mapped_node (skolem, evar);
          assert (fun);
          if ((a = btor_mapped_node (deps, evar)))
          {
            a     = instantiate_args (btor, a, uvar_map);
            subst = btor_apply_exp (btor, fun, a);
            btor_release_exp (btor, a);
          }
          else
            subst = btor_copy_exp (btor, fun);
          result = substitute_evar (btor, e[1], evar, subst);
          btor_release_exp (btor, subst);
        }
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
  btor_delete_node_map (funs);

  for (j = 0; j < mark->size; j++)
  {
    if (!mark->keys[j]) continue;
    assert (mark->data[j].as_ptr);
    btor_release_exp (btor, mark->data[j].as_ptr);
  }
  btor_delete_int_hash_map (mark);

  assert (!BTOR_REAL_ADDR_NODE (result)->quantifier_below);
  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);

  //  uint32_t num_exps2 = 0;
  //  for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++)
  //    num_exps2 += gslv->forall->ops[i].cur;
  //
  //  printf ("num_ops: %u -> %u\n", num_exps, num_exps2);

  return result;
}

static void
free_cur_model (BtorEFGroundSolvers *gslv, BtorPtrHashTable *uf_models)
{
  BtorNode *cur;
  BtorHashTableIterator it, mit;
  BtorBitVector *bv;
  BtorBitVectorTuple *tup;
  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;
  BtorMemMgr *mm;

  mm = gslv->exists->mm;

  btor_init_node_hash_table_iterator (&it, uf_models);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    b   = it.bucket;
    cur = btor_next_node_hash_table_iterator (&it);
    assert (btor_is_uf_node (cur) || btor_param_is_exists_var (cur));

    assert (b->data.as_ptr);
    if (btor_is_uf_node (cur)
        || (btor_param_is_exists_var (cur)
            && btor_mapped_node (gslv->forall_evar_deps, cur)))
    {
      t = b->data.as_ptr;
      btor_init_hash_table_iterator (&mit, t);
      while (btor_has_next_hash_table_iterator (&mit))
      {
        bv  = mit.bucket->data.as_ptr;
        tup = btor_next_hash_table_iterator (&mit);
        btor_free_bv (mm, bv);
        btor_free_bv_tuple (mm, tup);
      }
      btor_delete_ptr_hash_table (t);
    }
    else
    {
      assert (btor_param_is_exists_var (cur));
      bv = b->data.as_ptr;
      btor_free_bv (mm, bv);
    }
  }
  btor_delete_ptr_hash_table (uf_models);
}

static BtorSolverResult
find_model (BtorEFGroundSolvers *gslv, bool skip_exists)
{
  bool opt_underapprox;
  uint32_t opt_pmfind_mode;
  double start;
  BtorSolverResult res          = BTOR_RESULT_UNKNOWN, r;
  BtorNode *g                   = 0;
  BtorPtrHashTable *synth_model = 0, *cur_model;
  BtorPtrHashTable *assumptions = 0, *vars = 0;
  BtorNodeMapIterator it;

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

    if (opt_pmfind_mode == BTOR_EF_FINDPM_NONE
        || (gslv->forall_evar_deps->table->count == 0
            && gslv->forall->ufs->count == 0))
    {
    RESTART:
      cur_model = generate_model (gslv);
    }
    else
    {
      start     = time_stamp ();
      cur_model = find_partial_model (gslv);
      gslv->statistics->time.findpm += time_stamp () - start;
    }

    /* synthesize model based on 'cur_model' */
    start       = time_stamp ();
    synth_model = synthesize_model (gslv, cur_model);
    free_cur_model (gslv, cur_model);
    gslv->statistics->time.synth += time_stamp () - start;

    /* save currently synthesized model */
    delete_model (gslv);
    gslv->forall_cur_model = synth_model;
  }

  g = instantiate_formula (gslv, synth_model);

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
  if (!refine_exists_solver (gslv))
  {
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
 * the universal variables of 'gslv->exists' with 'dual_gslv->forall_cur_model'.
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

  if (!dual_gslv->forall_cur_model)
    return;

  btor = gslv->exists;
  subst_map = btor_new_node_map (btor);
  deps = dual_gslv->forall_evar_deps;

  btor_init_node_hash_table_iterator (&it, dual_gslv->forall_cur_model);
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
    BTOR_MSG (gslv->exists->msg, 1, "found solution");
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

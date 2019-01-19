/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *  Copyright (C) 2014-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormodel.h"

#include "btorbeta.h"
#include "btorclone.h"
#include "btordbg.h"
#include "btorlog.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/
/* BV model                                                               */
/*------------------------------------------------------------------------*/

void
btor_model_delete_bv (Btor *btor, BtorIntHashTable **bv_model)
{
  assert (btor);
  assert (bv_model);

  BtorBitVector *bv;
  BtorNode *cur;
  BtorIntHashTableIterator it;

  if (!*bv_model) return;

  btor_iter_hashint_init (&it, *bv_model);
  while (btor_iter_hashint_has_next (&it))
  {
    bv  = (BtorBitVector *) (*bv_model)->data[it.cur_pos].as_ptr;
    cur = btor_node_get_by_id (btor, btor_iter_hashint_next (&it));
    btor_bv_free (btor->mm, bv);
    btor_node_release (btor, cur);
  }
  btor_hashint_map_delete (*bv_model);
  *bv_model = 0;
}

/*------------------------------------------------------------------------*/

void
btor_model_init_bv (Btor *btor, BtorIntHashTable **bv_model)
{
  assert (btor);
  assert (bv_model);

  if (*bv_model) btor_model_delete_bv (btor, bv_model);

  *bv_model = btor_hashint_map_new (btor->mm);
}

/*------------------------------------------------------------------------*/

BtorIntHashTable *
btor_model_clone_bv (Btor *btor, BtorIntHashTable *bv_model, bool inc_ref_cnt)
{
  assert (btor);
  assert (bv_model);

  BtorIntHashTable *res;
  BtorIntHashTableIterator it;
  BtorNode *exp;

  res =
      btor_hashint_map_clone (btor->mm, bv_model, btor_clone_data_as_bv_ptr, 0);

  btor_iter_hashint_init (&it, res);
  while (btor_iter_hashint_has_next (&it))
  {
    exp = btor_node_get_by_id (btor, btor_iter_hashint_next (&it));
    assert (exp);
    if (inc_ref_cnt) btor_node_copy (btor, exp);
  }
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_model_add_to_bv (Btor *btor,
                      BtorIntHashTable *bv_model,
                      BtorNode *exp,
                      const BtorBitVector *assignment)
{
  assert (btor);
  assert (bv_model);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (assignment);

  assert (!btor_hashint_map_contains (bv_model, btor_node_real_addr (exp)->id));
  btor_node_copy (btor, exp);
  btor_hashint_map_add (bv_model, btor_node_real_addr (exp)->id)->as_ptr =
      btor_bv_copy (btor->mm, assignment);
}

/*------------------------------------------------------------------------*/

void
btor_model_remove_from_bv (Btor *btor,
                           BtorIntHashTable *bv_model,
                           BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (exp);

  BtorHashTableData d;
  uint32_t id;

  id = btor_node_get_id (exp);
  assert (btor_hashint_map_contains (bv_model, id));
  btor_hashint_map_remove (bv_model, id, &d);
  btor_bv_free (btor->mm, d.as_ptr);
  btor_node_release (btor, exp);
  if (btor_hashint_map_contains (bv_model, -id))
  {
    btor_hashint_map_remove (bv_model, id, &d);
    btor_bv_free (btor->mm, d.as_ptr);
    btor_node_release (btor, exp);
  }
}

/*------------------------------------------------------------------------*/

static void
add_to_fun_model (Btor *btor,
                  BtorIntHashTable *fun_model,
                  BtorNode *exp,
                  BtorBitVectorTuple *t,
                  BtorBitVector *value)
{
  assert (btor);
  assert (fun_model);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (t);
  assert (value);

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  if (btor_hashint_map_contains (fun_model, exp->id))
    model = btor_hashint_map_get (fun_model, exp->id)->as_ptr;
  else
  {
    model = btor_hashptr_table_new (btor->mm,
                                    (BtorHashPtr) btor_bv_hash_tuple,
                                    (BtorCmpPtr) btor_bv_compare_tuple);
    btor_node_copy (btor, exp);
    btor_hashint_map_add (fun_model, exp->id)->as_ptr = model;
  }
  /* do not overwrite model if already present (model is computed top-down)
   * and therefore only the top-most 't' with the same assignment
   * needs to be considered */
  if (btor_hashptr_table_get (model, t)) return;
  b = btor_hashptr_table_add (model, btor_bv_copy_tuple (btor->mm, t));
  b->data.as_ptr = btor_bv_copy (btor->mm, value);
}

/*------------------------------------------------------------------------*/

static BtorBitVector *
get_value_from_fun_model (Btor *btor,
                          BtorIntHashTable *fun_model,
                          BtorNode *exp,
                          BtorBitVectorTuple *t)
{
  assert (btor);
  assert (fun_model);
  assert (exp);
  assert (t);
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_fun (exp));

  BtorPtrHashTable *model;
  BtorHashTableData *d;
  BtorPtrHashBucket *b;

  d = btor_hashint_map_get (fun_model, exp->id);
  if (!d) return 0;
  model = (BtorPtrHashTable *) d->as_ptr;
  b     = btor_hashptr_table_get (model, t);
  if (!b) return 0;
  return btor_bv_copy (btor->mm, (BtorBitVector *) b->data.as_ptr);
}

/*------------------------------------------------------------------------*/

static BtorBitVectorTuple *
mk_bv_tuple_from_args (Btor *btor,
                       BtorNode *args,
                       BtorIntHashTable *bv_model,
                       BtorIntHashTable *fun_model)
{
  uint32_t pos;
  BtorBitVectorTuple *t;
  BtorMemMgr *mm;
  BtorArgsIterator it;
  BtorNode *arg;
  BtorBitVector *bv;

  mm = btor->mm;

  pos = 0;
  t   = btor_bv_new_tuple (mm, btor_node_args_get_arity (btor, args));

  btor_iter_args_init (&it, args);
  while (btor_iter_args_has_next (&it))
  {
    arg = btor_iter_args_next (&it);
    bv  = btor_model_recursively_compute_assignment (
        btor, bv_model, fun_model, arg);
    btor_bv_add_to_tuple (mm, t, bv, pos++);
    btor_bv_free (mm, bv);
  }

  return t;
}

static void
add_rho_to_model (Btor *btor,
                  BtorNode *fun,
                  BtorPtrHashTable *rho,
                  BtorIntHashTable *bv_model,
                  BtorIntHashTable *fun_model)
{
  BtorNode *value, *args;
  BtorBitVectorTuple *t;
  BtorBitVector *bv_value;
  BtorPtrHashTableIterator it;

  btor_iter_hashptr_init (&it, rho);
  while (btor_iter_hashptr_has_next (&it))
  {
    value = (BtorNode *) it.bucket->data.as_ptr;
    args  = btor_iter_hashptr_next (&it);
    assert (!btor_node_real_addr (value)->parameterized);
    assert (btor_node_is_regular (args));
    assert (btor_node_is_args (args));
    assert (!args->parameterized);

    t        = mk_bv_tuple_from_args (btor, args, bv_model, fun_model);
    bv_value = btor_model_recursively_compute_assignment (
        btor, bv_model, fun_model, value);

    add_to_fun_model (btor, fun_model, fun, t, bv_value);
    btor_bv_free (btor->mm, bv_value);
    btor_bv_free_tuple (btor->mm, t);
  }
}

static void
recursively_compute_function_model (Btor *btor,
                                    BtorIntHashTable *bv_model,
                                    BtorIntHashTable *fun_model,
                                    BtorNode *fun)
{
  assert (btor);
  assert (fun_model);
  assert (fun);
  assert (btor_node_is_regular (fun));
  assert (btor_node_is_fun (fun));

  int32_t i;
  BtorNode *value, *cur_fun, *cur;
  BtorPtrHashTable *static_rho;
  BtorBitVectorTuple *t;
  BtorBitVector *bv_value;
  BtorMemMgr *mm;
  BtorNodePtrStack stack;

  mm      = btor->mm;
  cur_fun = fun;
  while (cur_fun)
  {
    assert (btor_node_is_fun (cur_fun));

    if (cur_fun->rho)
      add_rho_to_model (btor, fun, cur_fun->rho, bv_model, fun_model);

    if (btor_node_is_lambda (cur_fun)
        && (static_rho = btor_node_lambda_get_static_rho (cur_fun)))
      add_rho_to_model (btor, fun, static_rho, bv_model, fun_model);

    if (btor_node_is_lambda (cur_fun))
    {
      if (btor_node_lambda_get_static_rho (cur_fun))
      {
        BTOR_INIT_STACK (mm, stack);
        BTOR_PUSH_STACK (stack, btor_node_binder_get_body (cur_fun));
        cur_fun = 0;
        while (!BTOR_EMPTY_STACK (stack))
        {
          cur = btor_node_real_addr (BTOR_POP_STACK (stack));

          if (btor_node_is_fun (cur))
          {
            cur_fun = cur;
            break;
          }

          if (!cur->parameterized || !cur->apply_below) continue;

          for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (stack, cur->e[i]);
        }
        BTOR_RELEASE_STACK (stack);
      }
      else
      {
        /* only compute models for array lambdas */
        cur_fun = 0;
      }
    }
    else if (btor_node_is_update (cur_fun))
    {
      t = mk_bv_tuple_from_args (btor, cur_fun->e[1], bv_model, fun_model);
      bv_value = btor_model_recursively_compute_assignment (
          btor, bv_model, fun_model, cur_fun->e[2]);

      add_to_fun_model (btor, fun_model, fun, t, bv_value);
      btor_bv_free (btor->mm, bv_value);
      btor_bv_free_tuple (btor->mm, t);
      cur_fun = cur_fun->e[0];
    }
    else if (btor_node_is_fun_cond (cur_fun))
    {
      if (cur_fun->parameterized)
      {
        cur_fun = 0;
        // TODO: print warning that branch cannot be selected
      }
      else
      {
        assert (!btor_node_real_addr (cur_fun->e[0])->parameterized);
        value    = cur_fun->e[0];
        bv_value = btor_model_recursively_compute_assignment (
            btor, bv_model, fun_model, value);

        if (btor_bv_is_true (bv_value))
          cur_fun = cur_fun->e[1];
        else
        {
          assert (btor_bv_is_false (bv_value));
          cur_fun = cur_fun->e[2];
        }
        btor_bv_free (mm, bv_value);
      }
    }
    else
    {
      assert (btor_node_is_uf (cur_fun));
      cur_fun = 0;
    }
  }
}

const BtorPtrHashTable *
btor_model_get_fun_aux (Btor *btor,
                        BtorIntHashTable *bv_model,
                        BtorIntHashTable *fun_model,
                        BtorNode *exp)
{
  assert (btor);
  assert (fun_model);
  assert (btor_node_is_regular (exp));

  BtorHashTableData *d;

  /* Do not use btor_simplify_exp here! btor_simplify_exp always simplifies
   * constraints to true (regardless of the actual input assignments).
   * However, when querying assignments, we want to get the actual assignments,
   * depending on the current input assignments. In particular during local
   * search (engines PROP, AIGPROP, SLS), assignment queries may be issued
   * when the current model is non satisfying (all intermediate models during
   * local search are non-satisfying). */
  exp = btor_pointer_chase_simplified_exp (btor, exp);

  assert (btor_node_is_fun (exp));
  d = btor_hashint_map_get (fun_model, exp->id);

  /* if exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is now
   * a proxy and was therefore regenerated when querying it's assignment via
   * get-value in SMT-LIB v2) */
  if (!d) recursively_compute_function_model (btor, bv_model, fun_model, exp);
  d = btor_hashint_map_get (fun_model, exp->id);
  if (!d) return 0;

  return (BtorPtrHashTable *) d->as_ptr;
}

const BtorPtrHashTable *
btor_model_get_fun (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_model_get_fun_aux (btor, btor->bv_model, btor->fun_model, exp);
}

/*------------------------------------------------------------------------*/

static void
compute_model_values (Btor *btor,
                      BtorIntHashTable *bv_model,
                      BtorIntHashTable *fun_model,
                      BtorNode *nodes[],
                      size_t num_nodes)
{
  size_t i;
  BtorNode *cur;
  BtorBitVector *bv;

  qsort (
      nodes, num_nodes, sizeof (BtorNode *), btor_node_compare_by_id_qsort_asc);

  for (i = 0; i < num_nodes; i++)
  {
    cur = btor_node_real_addr (nodes[i]);
    assert (!cur->parameterized);
    BTORLOG (3, "generate model for %s", btor_util_node2string (cur));
    if (btor_node_is_fun (cur))
      recursively_compute_function_model (btor, bv_model, fun_model, cur);
    else
    {
      bv = btor_model_recursively_compute_assignment (
          btor, bv_model, fun_model, cur);
      btor_bv_free (btor->mm, bv);
    }
  }
}

/* Ensure that all terms in 'exp' have a model value. Collect all terms in
 * 'exp' that don't have a model value and call corresponding
 * recursively_compute_* functions. */
static void
ensure_model (Btor *btor,
              BtorIntHashTable *bv_model,
              BtorIntHashTable *fun_model,
              BtorNode *exp)
{
  assert (exp);
  assert (!btor_node_is_proxy (exp));

  double start;
  uint32_t i;
  BtorNode *cur;
  BtorNodePtrStack visit, nodes;
  BtorIntHashTable *cache;

  start = btor_util_time_stamp ();
  cache = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, nodes);

  BTOR_INIT_STACK (btor->mm, visit);
  BTOR_PUSH_STACK (visit, exp);
  do
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)
        || btor_hashint_map_contains (bv_model, cur->id)
        || btor_hashint_map_contains (fun_model, cur->id))
      continue;

    btor_hashint_table_add (cache, cur->id);

    if (!cur->parameterized && !btor_node_is_args (cur))
    {
      BTOR_PUSH_STACK (nodes, cur);
    }

    for (i = 0; i < cur->arity; i++)
    {
      BTOR_PUSH_STACK (visit, cur->e[i]);
    }
  } while (!BTOR_EMPTY_STACK (visit));
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);

  compute_model_values (
      btor, bv_model, fun_model, nodes.start, BTOR_COUNT_STACK (nodes));

  BTOR_RELEASE_STACK (nodes);
  btor->time.model_gen += btor_util_time_stamp () - start;
}

/* Note: no need to free returned bit vector,
 *       all bit vectors are maintained via btor->bv_model */
const BtorBitVector *
btor_model_get_bv_aux (Btor *btor,
                       BtorIntHashTable *bv_model,
                       BtorIntHashTable *fun_model,
                       BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (exp);

  BtorBitVector *result;
  BtorHashTableData *d;

  /* Note: btor_model_generate generates assignments for all nodes
   *       as non-inverted nodes. Their inverted assignments, however,
   *       are cached (when requested) on demand (see below)! */

  /* Do not use btor_simplify_exp here! btor_simplify_exp always simplifies
   * constraints to true (regardless of the actual input assignments).
   * However, when querying assignments, we want to get the actual assignments,
   * depending on the current input assignments. In particular during local
   * search (engines PROP, AIGPROP, SLS), assignment queries may be issued
   * when the current model is non satisfying (all intermediate models during
   * local search are non-satisfying). */
  exp = btor_pointer_chase_simplified_exp (btor, exp);

  /* Check if we already generated the assignment of exp
   * -> inverted if exp is inverted */
  if ((d = btor_hashint_map_get (bv_model, btor_node_get_id (exp))))
    return d->as_ptr;

  /* If not, check if we already generated the assignment of non-inverted exp
   * (i.e., check if we generated it at all) */
  if (btor_node_is_inverted (exp))
    d = btor_hashint_map_get (bv_model, btor_node_real_addr (exp)->id);

  /* If exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is
   * now a proxy and was therefore regenerated when querying it's
   * assignment via get-value in SMT-LIB v2) */
  if (!d)
  {
    ensure_model (btor, bv_model, fun_model, exp);
    d = btor_hashint_map_get (bv_model, btor_node_real_addr (exp)->id);
  }
  if (!d) return 0;

  result = (BtorBitVector *) d->as_ptr;

  /* Cache assignments of inverted expressions on demand */
  if (btor_node_is_inverted (exp))
  {
    /* we don't use add_to_bv_model in order to avoid redundant
     * hash table queries and copying/freeing of the resulting bv */
    result = btor_bv_not (btor->mm, result);
    btor_node_copy (btor, exp);
    btor_hashint_map_add (bv_model, btor_node_get_id (exp))->as_ptr = result;
  }

  return result;
}

const BtorBitVector *
btor_model_get_bv (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_model_get_bv_aux (btor, btor->bv_model, btor->fun_model, exp);
}

/*------------------------------------------------------------------------*/
/* Fun model                                                              */
/*------------------------------------------------------------------------*/

static void
delete_fun_model (Btor *btor, BtorIntHashTable **fun_model)
{
  assert (btor);
  assert (fun_model);

  BtorBitVectorTuple *tup;
  BtorBitVector *value;
  BtorNode *cur;
  BtorIntHashTableIterator it1;
  BtorPtrHashTable *t;
  BtorPtrHashTableIterator it2;

  if (!*fun_model) return;

  btor_iter_hashint_init (&it1, *fun_model);
  while (btor_iter_hashint_has_next (&it1))
  {
    t   = (BtorPtrHashTable *) (*fun_model)->data[it1.cur_pos].as_ptr;
    cur = btor_node_get_by_id (btor, btor_iter_hashint_next (&it1));
    btor_iter_hashptr_init (&it2, t);
    while (btor_iter_hashptr_has_next (&it2))
    {
      value = (BtorBitVector *) it2.bucket->data.as_ptr;
      tup   = (BtorBitVectorTuple *) btor_iter_hashptr_next (&it2);
      btor_bv_free_tuple (btor->mm, tup);
      btor_bv_free (btor->mm, value);
    }
    btor_node_release (btor, cur);
    btor_hashptr_table_delete (t);
  }
  btor_hashint_map_delete (*fun_model);
  *fun_model = 0;
}

/*------------------------------------------------------------------------*/

void
btor_model_init_fun (Btor *btor, BtorIntHashTable **fun_model)
{
  assert (btor);
  assert (fun_model);

  if (*fun_model) delete_fun_model (btor, fun_model);

  *fun_model = btor_hashint_map_new (btor->mm);
}

/*------------------------------------------------------------------------*/

BtorIntHashTable *
btor_model_clone_fun (Btor *btor, BtorIntHashTable *fun_model, bool inc_ref_cnt)
{
  assert (btor);
  assert (fun_model);

  BtorIntHashTable *res;
  BtorIntHashTableIterator it;
  BtorNode *exp;

  res = btor_hashint_map_clone (
      btor->mm, fun_model, btor_clone_data_as_bv_ptr_htable, 0);

  btor_iter_hashint_init (&it, res);
  while (btor_iter_hashint_has_next (&it))
  {
    exp = btor_node_get_by_id (btor, btor_iter_hashint_next (&it));
    assert (exp);
    if (inc_ref_cnt) btor_node_copy (btor, exp);
  }
  return res;
}

/*------------------------------------------------------------------------*/
/* Model                                                                  */
/*------------------------------------------------------------------------*/

static BtorBitVector *
get_apply_value (Btor *btor,
                 BtorNode *app,
                 BtorNode *fun,
                 BtorIntHashTable *bv_model,
                 BtorIntHashTable *fun_model,
                 BtorIntHashTable *bv_param_model)
{
  assert (btor_node_is_apply (app));

  uint32_t i;
  BtorArgsIterator it;
  BtorBitVectorTuple *t;
  BtorNode *arg, *real_arg;
  BtorHashTableData *d;
  BtorBitVector *bv, *bv_inv, *result;
  BtorMemMgr *mm;

  mm = btor->mm;
  t  = btor_bv_new_tuple (mm, btor_node_args_get_arity (btor, app->e[1]));

  i = 0;
  btor_iter_args_init (&it, app->e[1]);
  while (btor_iter_args_has_next (&it))
  {
    arg      = btor_iter_args_next (&it);
    real_arg = btor_node_real_addr (arg);

    if (btor_node_is_param (real_arg))
    {
      real_arg = btor_node_param_get_assigned_exp (real_arg);
      assert (real_arg);
    }
    if (real_arg->parameterized)
      d = btor_hashint_map_get (bv_param_model, real_arg->id);
    else
      d = btor_hashint_map_get (bv_model, real_arg->id);

    if (btor_node_is_apply (real_arg) && !d)
    {
      bv = get_apply_value (
          btor, real_arg, real_arg->e[0], bv_model, fun_model, bv_param_model);
    }
    else
    {
      assert (d);
      bv = btor_bv_copy (mm, d->as_ptr);
    }

    if (btor_node_is_inverted (arg))
    {
      bv_inv = btor_bv_not (mm, bv);
      btor_bv_add_to_tuple (mm, t, bv_inv, i);
      btor_bv_free (mm, bv_inv);
    }
    else
      btor_bv_add_to_tuple (mm, t, bv, i);
    btor_bv_free (mm, bv);
    i++;
  }
  /* check if there is already a value for given arguments */
  result = get_value_from_fun_model (btor, fun_model, fun, t);
  btor_bv_free_tuple (mm, t);
  return result;
}

/* Note: don't forget to free resulting bit vector! */
BtorBitVector *
btor_model_recursively_compute_assignment (Btor *btor,
                                           BtorIntHashTable *bv_model,
                                           BtorIntHashTable *fun_model,
                                           BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (exp);

  uint32_t i, num_args, pos;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack, reset;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next, *cur_parent;
  BtorHashTableData *d, dd;
  BtorIntHashTable *assigned, *reset_st, *param_model_cache;
  BtorBitVector *result = 0, *inv_result, **e;
  BtorBitVectorTuple *t;
  BtorIntHashTable *mark;
  BtorHashTableData *md;

  mm = btor->mm;

  assigned = btor_hashint_map_new (mm);

  /* model cache for parameterized nodes */
  param_model_cache = btor_hashint_map_new (mm);

  /* 'reset_st' remembers the stack position of 'reset' in case a lambda is
   * assigned. when the resp. lambda is unassigned, the 'eval_mark' flag of all
   * parameterized nodes up to the saved position of stack 'reset' will be
   * reset to 0. */
  reset_st = btor_hashint_map_new (mm);

  mark = btor_hashint_map_new (mm);
  BTOR_INIT_STACK (mm, work_stack);
  BTOR_INIT_STACK (mm, arg_stack);
  BTOR_INIT_STACK (mm, reset);

  BTOR_PUSH_STACK (work_stack, exp);
  BTOR_PUSH_STACK (work_stack, 0);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur_parent = BTOR_POP_STACK (work_stack);
    cur        = BTOR_POP_STACK (work_stack);
    real_cur   = btor_node_real_addr (cur);
    assert (!real_cur->simplified);

    if (btor_hashint_map_contains (bv_model, real_cur->id)
        || btor_hashint_map_contains (param_model_cache, real_cur->id))
      goto PUSH_CACHED;

    /* check if we already have an assignment for this function application */
    if (btor_node_is_lambda (real_cur) && cur_parent
        && btor_node_is_apply (cur_parent)
        /* if real_cur was assigned by cur_parent, we are not allowed to use
         * a cached result, but instead rebuild cur_parent */
        && (!(d = btor_hashint_map_get (assigned, real_cur->id))
            || d->as_ptr != cur_parent))
    {
      num_args = btor_node_args_get_arity (btor, cur_parent->e[1]);
      e        = (BtorBitVector **) arg_stack.top - num_args;

      t = btor_bv_new_tuple (mm, num_args);
      for (i = 0; i < num_args; i++)
        btor_bv_add_to_tuple (mm, t, e[i], num_args - 1 - i);

      /* check if there is already a value for given arguments */
      result = get_value_from_fun_model (btor, fun_model, cur_parent->e[0], t);
      btor_bv_free_tuple (mm, t);

      if (result) goto PUSH_RESULT;
    }

    md = btor_hashint_map_get (mark, real_cur->id);
    if (!md)
    {
      /* add assignment of bv var to model (creates new assignment, if
       * it doesn't have one) */
      if (btor_node_is_bv_var (real_cur) || btor_node_is_fun_eq (real_cur))
      {
        result = btor_bv_get_assignment (mm, real_cur);
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (btor_node_is_bv_const (real_cur))
      {
        result = btor_bv_copy (mm, btor_node_bv_const_get_bits (real_cur));
        goto CACHE_AND_PUSH_RESULT;
      }
      /* substitute param with its assignment */
      else if (btor_node_is_param (real_cur))
      {
        next = btor_node_param_get_assigned_exp (real_cur);
        assert (next);
        next = btor_node_cond_invert (cur, next);
        BTOR_PUSH_STACK (work_stack, next);
        BTOR_PUSH_STACK (work_stack, cur_parent);
        continue;
      }
      else if (btor_node_is_lambda (real_cur) && cur_parent
               && btor_node_is_apply (cur_parent))
      {
        btor_beta_assign_args (btor, real_cur, cur_parent->e[1]);
        assert (!btor_hashint_map_contains (assigned, real_cur->id));
        btor_hashint_map_add (assigned, real_cur->id)->as_ptr = cur_parent;

        /* save 'reset' stack position */
        btor_hashint_map_add (reset_st, real_cur->id)->as_int =
            BTOR_COUNT_STACK (reset);
      }

      BTOR_PUSH_STACK (work_stack, cur);
      BTOR_PUSH_STACK (work_stack, cur_parent);
      md = btor_hashint_map_add (mark, real_cur->id);

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (btor_node_is_cond (real_cur))
      {
        md->as_int = 2;
        BTOR_PUSH_STACK (work_stack, real_cur->e[0]);
        BTOR_PUSH_STACK (work_stack, real_cur);
      }
      else if (btor_node_is_update (real_cur))
      {
        BTOR_PUSH_STACK (work_stack, real_cur->e[0]);
        BTOR_PUSH_STACK (work_stack, cur_parent);
        BTOR_PUSH_STACK (work_stack, real_cur->e[1]);
        BTOR_PUSH_STACK (work_stack, real_cur);
        BTOR_PUSH_STACK (work_stack, real_cur->e[2]);
        BTOR_PUSH_STACK (work_stack, real_cur);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BTOR_PUSH_STACK (work_stack, real_cur->e[i]);
          BTOR_PUSH_STACK (work_stack, real_cur);
        }
      }
    }
    else if (md->as_int == 0 || md->as_int == 2)
    {
      assert (!btor_node_is_param (real_cur));
      assert (real_cur->arity <= 3);

      num_args = 0;

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (btor_node_is_cond (real_cur))
      {
        /* only the condition is on the stack */
        assert (BTOR_COUNT_STACK (arg_stack) >= 1);
        arg_stack.top -= 1;
      }
      else if (btor_node_is_apply (real_cur))
      {
        num_args = btor_node_args_get_arity (btor, real_cur->e[1]);
        arg_stack.top -= 1;        /* value of apply */
        arg_stack.top -= num_args; /* arguments of apply */
        md->as_int = 1;
      }
      /* leave arguments on stack, we need them later for apply */
      else if (btor_node_is_args (real_cur))
      {
        assert (md->as_int == 0);
        btor_hashint_map_remove (mark, real_cur->id, 0);
        continue;
      }
      else
      {
        assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);
        arg_stack.top -= real_cur->arity;
        md->as_int = 1;
      }

      e = (BtorBitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_BV_SLICE_NODE:
          result = btor_bv_slice (mm,
                                  e[0],
                                  btor_node_bv_slice_get_upper (real_cur),
                                  btor_node_bv_slice_get_lower (real_cur));
          btor_bv_free (mm, e[0]);
          break;
        case BTOR_BV_AND_NODE:
          result = btor_bv_and (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_EQ_NODE:
          result = btor_bv_eq (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_ADD_NODE:
          result = btor_bv_add (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_MUL_NODE:
          result = btor_bv_mul (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_ULT_NODE:
          result = btor_bv_ult (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_SLL_NODE:
          result = btor_bv_sll (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_SRL_NODE:
          result = btor_bv_srl (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_UDIV_NODE:
          result = btor_bv_udiv (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_UREM_NODE:
          result = btor_bv_urem (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;
        case BTOR_BV_CONCAT_NODE:
          result = btor_bv_concat (mm, e[1], e[0]);
          btor_bv_free (mm, e[0]);
          btor_bv_free (mm, e[1]);
          break;

        case BTOR_APPLY_NODE:
          assert (num_args);
          t = btor_bv_new_tuple (mm, num_args);
          for (i = 0; i < num_args; i++)
          {
            btor_bv_add_to_tuple (mm, t, e[i], num_args - 1 - i);
            btor_bv_free (mm, e[i]);
          }

          /* check if there is already a value for given arguments */
          result =
              get_value_from_fun_model (btor, fun_model, real_cur->e[0], t);
          if (!result)
          {
            /* value of apply is at last index of e */
            result = e[num_args];
            add_to_fun_model (btor, fun_model, real_cur->e[0], t, result);
          }
          else
            btor_bv_free (mm, e[num_args]);

          btor_bv_free_tuple (mm, t);
          break;

        case BTOR_LAMBDA_NODE:
          result = e[0];
          btor_bv_free (mm, e[1]);
          if (btor_node_is_lambda (real_cur) && cur_parent
              && btor_node_is_apply (cur_parent))
          {
            assert (btor_hashint_map_contains (assigned, real_cur->id));
            btor_beta_unassign_params (btor, real_cur);
            btor_hashint_map_remove (assigned, real_cur->id, 0);

            /* reset 'eval_mark' of all parameterized nodes
             * instantiated by 'real_cur' */
            btor_hashint_map_remove (reset_st, real_cur->id, &dd);
            pos = dd.as_int;
            while (BTOR_COUNT_STACK (reset) > pos)
            {
              next = BTOR_POP_STACK (reset);
              assert (btor_node_is_regular (next));
              assert (next->parameterized);
              btor_hashint_map_remove (mark, next->id, 0);
              btor_hashint_map_remove (param_model_cache, next->id, &dd);
              btor_bv_free (mm, dd.as_ptr);
            }
          }
          break;

        case BTOR_UF_NODE:
          assert (btor_node_is_apply (cur_parent));
          result = btor_bv_get_assignment (mm, cur_parent);
          break;

        case BTOR_UPDATE_NODE:
          result = get_apply_value (btor,
                                    cur_parent,
                                    real_cur,
                                    bv_model,
                                    fun_model,
                                    param_model_cache);
          if (!result)
            result = e[2];
          else
            btor_bv_free (mm, e[2]);
          btor_bv_free (mm, e[1]);
          btor_bv_free (mm, e[0]);
          break;

        default:
          assert (btor_node_is_cond (real_cur));

          /* evaluate condition and select branch */
          if (md->as_int == 2)
          {
            /* select branch w.r.t. condition */
            next = btor_bv_is_true (e[0]) ? real_cur->e[1] : real_cur->e[2];
            BTOR_PUSH_STACK (work_stack, cur);
            BTOR_PUSH_STACK (work_stack, cur_parent);
            /* for function conditionals we push the function and the
             * apply */
            BTOR_PUSH_STACK (work_stack, next);
            BTOR_PUSH_STACK (work_stack, cur_parent);
            btor_bv_free (mm, e[0]);
            /* no result yet, we need to evaluate the selected function
             */
            md->as_int = 0;
            continue;
          }
          /* cache result */
          else
          {
            assert (md->as_int == 0);
            result     = e[0];
            md->as_int = 1;
          }
      }

      /* function nodes are never cached (assignment always depends on the
       * given arguments) */
      if (btor_node_is_fun (real_cur))
      {
        assert (result);
        /* not inserted into cache */
        btor_hashint_map_remove (mark, real_cur->id, 0);
        goto PUSH_RESULT;
      }
      else if (btor_node_is_apply (real_cur))
      {
        /* not inserted into cache */
        btor_hashint_map_remove (mark, real_cur->id, 0);
        if (real_cur->parameterized) goto PUSH_RESULT;
      }

    CACHE_AND_PUSH_RESULT:
      assert (!btor_node_is_fun (real_cur));
      /* remember parameterized nodes for resetting 'eval_mark' later */
      if (real_cur->parameterized)
      {
        BTOR_PUSH_STACK (reset, real_cur);
        /* temporarily cache model for paramterized nodes, is only
         * valid under current parameter assignment and will be reset
         * when parameters are unassigned */
        assert (!btor_hashint_map_contains (param_model_cache, real_cur->id));
        btor_hashint_map_add (param_model_cache, real_cur->id)->as_ptr =
            btor_bv_copy (mm, result);
      }
      else
      {
        assert (!btor_hashint_map_contains (bv_model, real_cur->id));
        btor_model_add_to_bv (btor, bv_model, real_cur, result);
      }

    PUSH_RESULT:
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
      assert (md->as_int == 1);
    PUSH_CACHED:
      if (real_cur->parameterized)
        d = btor_hashint_map_get (param_model_cache, real_cur->id);
      else
        d = btor_hashint_map_get (bv_model, real_cur->id);
      result = btor_bv_copy (mm, (BtorBitVector *) d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (param_model_cache->count == 0);
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  BTOR_RELEASE_STACK (work_stack);
  BTOR_RELEASE_STACK (arg_stack);
  BTOR_RELEASE_STACK (reset);
  btor_hashint_map_delete (assigned);
  btor_hashint_map_delete (reset_st);
  btor_hashint_map_delete (param_model_cache);
  btor_hashint_map_delete (mark);

  return result;
}

/*------------------------------------------------------------------------*/

static void
collect_nodes (Btor *btor,
               BtorNode *roots[],
               uint32_t num_roots,
               BtorNodePtrStack *nodes)
{
  uint32_t i;
  BtorNodePtrStack visit;
  BtorNode *cur;
  BtorIntHashTable *cache;

  BTOR_INIT_STACK (btor->mm, visit);
  cache = btor_hashint_table_new (btor->mm);

  for (i = 0; i < num_roots; i++) BTOR_PUSH_STACK (visit, roots[i]);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)) continue;

    if (!cur->parameterized && !btor_node_is_args (cur))
      BTOR_PUSH_STACK (*nodes, cur);
    btor_hashint_table_add (cache, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);
}

void
btor_model_generate (Btor *btor,
                     BtorIntHashTable *bv_model,
                     BtorIntHashTable *fun_model,
                     bool model_for_all_nodes)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);

  uint32_t i;
  double start;
  BtorNode *cur;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack roots, nodes;

  start = btor_util_time_stamp ();

  BTOR_INIT_STACK (btor->mm, nodes);

  if (model_for_all_nodes)
  {
    for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
    {
      cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
      if (!cur || btor_node_is_args (cur) || btor_node_is_proxy (cur)
          || cur->parameterized)
        continue;
      BTOR_PUSH_STACK (nodes, cur);
    }
  }
  else /* push nodes reachable from roots only */
  {
    BTOR_INIT_STACK (btor->mm, roots);
    /* NOTE: adding fun_rhs is only needed for extensional benchmarks */
    btor_iter_hashptr_init (&it, btor->fun_rhs);
    btor_iter_hashptr_queue (&it, btor->var_rhs);
    btor_iter_hashptr_queue (&it, btor->unsynthesized_constraints);
    btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
    btor_iter_hashptr_queue (&it, btor->assumptions);
    while (btor_iter_hashptr_has_next (&it))
    {
      cur = btor_iter_hashptr_next (&it);
      cur = btor_pointer_chase_simplified_exp (btor, cur);
      BTOR_PUSH_STACK (roots, cur);
    }
    collect_nodes (btor, roots.start, BTOR_COUNT_STACK (roots), &nodes);
    BTOR_RELEASE_STACK (roots);
  }

  compute_model_values (
      btor, bv_model, fun_model, nodes.start, BTOR_COUNT_STACK (nodes));

  BTOR_RELEASE_STACK (nodes);

  btor->time.model_gen += btor_util_time_stamp () - start;
}

/*------------------------------------------------------------------------*/

void
btor_model_delete (Btor *btor)
{
  assert (btor);
  btor_model_delete_bv (btor, &btor->bv_model);
  delete_fun_model (btor, &btor->fun_model);
}

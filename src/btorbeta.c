/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2013 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbeta.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btorrewrite.h"
#include "btorslvfun.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

#define BETA_RED_LAMBDA_MERGE -2
#define BETA_RED_FULL 0
#define BETA_RED_BOUNDED 1

static void
cache_beta_result (Btor *btor,
                   BtorPtrHashTable *cache,
                   BtorNode *lambda,
                   BtorNode *exp,
                   BtorNode *result)
{
  assert (btor);
  assert (cache);
  assert (lambda);
  assert (exp);
  assert (result);
  assert (!btor_node_is_proxy (lambda));
  assert (!btor_node_is_proxy (exp));
  assert (!btor_node_is_proxy (result));
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair   = btor_node_pair_new (btor, lambda, exp);
  bucket = btor_hashptr_table_get (cache, pair);
  if (bucket)
  {
    btor_node_pair_delete (btor, pair);
    assert ((BtorNode *) bucket->data.as_ptr == result);
  }
  else
    btor_hashptr_table_add (cache, pair)->data.as_ptr =
        btor_node_copy (btor, result);
  BTORLOG (3,
           "%s: (%s, %s) -> %s",
           __FUNCTION__,
           btor_util_node2string (lambda),
           btor_util_node2string (exp),
           btor_util_node2string (result));
}

static BtorNode *
cached_beta_result (Btor *btor,
                    BtorPtrHashTable *cache,
                    BtorNode *lambda,
                    BtorNode *exp)
{
  assert (btor);
  assert (lambda);
  assert (exp);
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair   = btor_node_pair_new (btor, lambda, exp);
  bucket = btor_hashptr_table_get (cache, pair);
  btor_node_pair_delete (btor, pair);

  if (bucket)
  {
    BTORLOG (3,
             "%s: (%s, %s) -> %s",
             __FUNCTION__,
             btor_util_node2string (lambda),
             btor_util_node2string (exp),
             btor_util_node2string (bucket->data.as_ptr));
    return (BtorNode *) bucket->data.as_ptr;
  }

  return 0;
}

void
btor_beta_assign_args (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor_node_is_regular (fun));
  assert (btor_node_is_regular (args));
  assert (btor_node_is_lambda (fun));
  assert (btor_node_is_args (args));

  //  BTORLOG ("%s: %s (%d params, %d args)", __FUNCTION__,
  //  btor_util_node2string (fun),
  //	   ((BtorLambdaNode *) fun)->num_params,
  //	   ((BtorArgsNode *) args)->num_args);

  BtorNode *cur_lambda, *cur_arg;
  BtorNodeIterator it;
  BtorArgsIterator ait;

  btor_iter_args_init (&ait, args);
  btor_iter_lambda_init (&it, fun);

  while (btor_iter_args_has_next (&ait))
  {
    assert (btor_iter_lambda_has_next (&it));
    cur_arg    = btor_iter_args_next (&ait);
    cur_lambda = btor_iter_lambda_next (&it);
    btor_beta_assign_param (btor, cur_lambda, cur_arg);
  }
}

void
btor_beta_assign_param (Btor *btor, BtorNode *lambda, BtorNode *arg)
{
  (void) btor;
  assert (btor);
  assert (lambda);
  assert (arg);
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));
  assert (!btor_node_param_get_assigned_exp (lambda->e[0]));
  btor_node_param_set_assigned_exp (lambda->e[0], arg);
}

void
btor_beta_unassign_params (Btor *btor, BtorNode *lambda)
{
  (void) btor;
  assert (lambda);
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));
  assert (btor_node_is_param (lambda->e[0]));

  do
  {
    if (!btor_node_param_get_assigned_exp (lambda->e[0])) break;

    btor_node_param_set_assigned_exp (lambda->e[0], 0);
    lambda = btor_node_real_addr (lambda->e[1]);
  } while (btor_node_is_lambda (lambda));
}

/* We distinguish the following options for (un)bounded reduction:
 *
 *   BETA_RED_LAMBDA_MERGE: merge lambda chains
 *
 *   BETA_RED_FULL:   full reduction,
 *		      do not evaluate conditionals
 *
 *   BETA_RED_BOUNDED (bound): bounded reduction, stop reduction at 'bound'
 *			       lambdas
 */
static BtorNode *
beta_reduce (Btor *btor,
             BtorNode *exp,
             int32_t mode,
             int32_t bound,
             BtorPtrHashTable *merge_lambdas,
             BtorPtrHashTable *cache)
{
  assert (btor);
  assert (exp);
  assert (mode == BETA_RED_LAMBDA_MERGE || mode == BETA_RED_FULL
          || mode == BETA_RED_BOUNDED);
  assert (bound >= 0);
  assert (bound == 0 || mode == BETA_RED_BOUNDED);
  assert (mode != BETA_RED_LAMBDA_MERGE || merge_lambdas);

  uint32_t i;
  int32_t cur_lambda_depth = 0;
  double start;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args;
  BtorNode *cached;
  BtorNodePtrStack stack, arg_stack, cleanup_stack, reset;
  BtorIntHashTable *mark;
  BtorHashTableData *d, md;
#ifndef NDEBUG
  BtorNodePtrStack unassign_stack;
  BTOR_INIT_STACK (btor->mm, unassign_stack);
#endif

  start = btor_util_time_stamp ();
  btor->stats.beta_reduce_calls++;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, arg_stack);
  BTOR_INIT_STACK (mm, cleanup_stack);
  BTOR_INIT_STACK (mm, reset);
  mark = btor_hashint_map_new (mm);

  real_cur = btor_node_real_addr (exp);

  BTOR_PUSH_STACK (stack, exp);
  BTOR_PUSH_STACK (stack, 0);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_parent = BTOR_POP_STACK (stack);
    cur        = BTOR_POP_STACK (stack);
    /* we do not want the simplification of top level apply constraints */
    if (btor_node_real_addr (cur)->constraint && btor_node_is_apply (cur))
      cur = btor_pointer_chase_simplified_exp (btor, cur);
    else
      cur = btor_simplify_exp (btor, cur);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (mark, real_cur->id);

    if (!d)
    {
      assert (!btor_node_is_lambda (real_cur) || !real_cur->e[0]->simplified);

      if (btor_node_is_lambda (real_cur)
          && !real_cur->parameterized
          /* only count head lambdas (in case of curried lambdas) */
          && (!cur_parent || !btor_node_is_lambda (cur_parent)))
        cur_lambda_depth++;

      /* stop at given bound */
      if (bound > 0 && btor_node_is_lambda (real_cur)
          && cur_lambda_depth == bound)
      {
        assert (!real_cur->parameterized);
        assert (!cur_parent || !btor_node_is_lambda (cur_parent));
        cur_lambda_depth--;
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cur));
        continue;
      }
      /* skip all lambdas that are not marked for merge */
      else if (mode == BETA_RED_LAMBDA_MERGE && btor_node_is_lambda (real_cur)
               && !btor_hashptr_table_get (merge_lambdas, real_cur)
               /* do not stop at parameterized lambdas, otherwise the
                * result may contain parameters that are not bound by any
                * lambda anymore */
               && !real_cur->parameterized
               /* do not stop at non-parameterized curried lambdas */
               && (!cur_parent || !btor_node_is_lambda (cur_parent)))
      {
        cur_lambda_depth--;
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cur));
        continue;
      }
      /* stop at nodes that do not need to be rebuilt */
      else if (!real_cur->lambda_below && !real_cur->parameterized)
      {
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (btor_node_is_param (real_cur))
      {
        next = btor_node_param_get_assigned_exp (real_cur);
        if (!next) next = real_cur;
        if (btor_node_is_inverted (cur)) next = btor_node_invert (next);
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, next));
        continue;
      }
      /* assign params of lambda expression */
      else if (btor_node_is_lambda (real_cur) && cur_parent
               && btor_node_is_apply (cur_parent)
               /* check if we have arguments on the stack */
               && !BTOR_EMPTY_STACK (arg_stack)
               /* if it is nested, its parameter is already assigned */
               && !btor_node_param_get_assigned_exp (real_cur->e[0]))
      {
        args = BTOR_TOP_STACK (arg_stack);
        assert (btor_node_is_regular (args));
        assert (btor_node_is_args (args));

        if (cache)
        {
          cached = cached_beta_result (btor, cache, real_cur, args);
          if (cached)
          {
            assert (!real_cur->parameterized);
            if (btor_node_is_inverted (cur)) cached = btor_node_invert (cached);
            BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cached));
            cur_lambda_depth--;
            continue;
          }
        }

#ifndef NDEBUG
        BTOR_PUSH_STACK (unassign_stack, real_cur);
#endif
        btor_beta_assign_args (btor, real_cur, args);
        BTOR_PUSH_STACK (reset, real_cur);
      }
      /* do not try to reduce lambdas below equalities as lambdas cannot
       * be eliminated. further, it may produce lambdas that break lemma
       * generation for extensionality */
      else if (btor_node_is_lambda (real_cur) && cur_parent
               && (btor_node_is_fun_eq (cur_parent)
                   || btor_node_is_fun_cond (cur_parent)))
      {
        assert (!btor_node_param_get_assigned_exp (real_cur->e[0]));
        cur_lambda_depth--;
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cur));
        continue;
      }
      /* do not try to reduce conditionals on functions below equalities
       * as they cannot be eliminated. */
      else if (btor_node_is_fun_cond (real_cur)
               && btor_node_is_fun_eq (cur_parent))
      {
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cur));
        continue;
      }

      btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (stack, cur);
      BTOR_PUSH_STACK (stack, cur_parent);
      BTOR_PUSH_STACK (cleanup_stack, real_cur);
      for (i = 0; i < real_cur->arity; i++)
      {
        BTOR_PUSH_STACK (stack, btor_simplify_exp (btor, real_cur->e[i]));
        BTOR_PUSH_STACK (stack, real_cur);
      }
    }
    else if (!d->as_ptr)
    {
      assert (real_cur->arity >= 1);
      assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);

      arg_stack.top -= real_cur->arity;
      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_BV_SLICE_NODE:
          result = btor_exp_bv_slice (btor,
                                      e[0],
                                      btor_node_bv_slice_get_upper (real_cur),
                                      btor_node_bv_slice_get_lower (real_cur));
          btor_node_release (btor, e[0]);
          break;
        case BTOR_BV_AND_NODE:
          result = btor_exp_bv_and (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_EQ_NODE:
        case BTOR_FUN_EQ_NODE:
          result = btor_exp_eq (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_ADD_NODE:
          result = btor_exp_bv_add (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_MUL_NODE:
          result = btor_exp_bv_mul (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_ULT_NODE:
          result = btor_exp_bv_ult (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_SLL_NODE:
          result = btor_exp_bv_sll (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_SRL_NODE:
          result = btor_exp_bv_srl (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_UDIV_NODE:
          result = btor_exp_bv_udiv (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_UREM_NODE:
          result = btor_exp_bv_urem (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_CONCAT_NODE:
          result = btor_exp_bv_concat (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_ARGS_NODE:
          assert (real_cur->arity >= 1);
          assert (real_cur->arity <= 3);
          if (real_cur->arity == 2)
          {
            next = e[0];
            e[0] = e[1];
            e[1] = next;
          }
          else if (real_cur->arity == 3)
          {
            next = e[0];
            e[0] = e[2];
            e[2] = next;
          }
          result = btor_exp_args (btor, e, real_cur->arity);
          btor_node_release (btor, e[0]);
          if (real_cur->arity >= 2) btor_node_release (btor, e[1]);
          if (real_cur->arity >= 3) btor_node_release (btor, e[2]);
          break;
        case BTOR_APPLY_NODE:
          if (btor_node_is_fun (e[1]))
          {
            assert (btor_node_is_args (e[0]));
            /* NOTE: do not use btor_exp_apply here since
             * beta reduction is used in btor_rewrite_apply_exp. */
            result = btor_node_create_apply (btor, e[1], e[0]);
          }
          else
          {
            result = btor_node_copy (btor, e[1]);
          }

          if (cache && mode == BETA_RED_FULL
              && btor_node_is_lambda (real_cur->e[0]))
            cache_beta_result (btor, cache, real_cur->e[0], e[0], result);

          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_LAMBDA_NODE:
          /* function equalities and conditionals always expect a lambda
           * as argument */
          if (cur_parent
              && (btor_node_is_fun_eq (cur_parent)
                  || (btor_node_is_fun_cond (cur_parent)
                      && !btor_node_param_get_assigned_exp (real_cur->e[0]))))
          {
            assert (btor_node_is_param (e[1]));
            result = btor_exp_lambda (btor, e[1], e[0]);
            if (real_cur->is_array) result->is_array = 1;
            if (btor_node_lambda_get_static_rho (real_cur)
                && !btor_node_lambda_get_static_rho (result))
              btor_node_lambda_set_static_rho (
                  result, btor_node_lambda_copy_static_rho (btor, real_cur));
          }
          /* special case: lambda not reduced (not instantiated)
           *		 and is not constant */
          else if (real_cur->e[0] == e[1] && real_cur->e[1] == e[0]
                   && btor_node_real_addr (e[0])->parameterized)
          {
            result = btor_node_copy (btor, real_cur);
          }
          /* main case: lambda reduced to some term without e[1] */
          else
          {
            result = btor_node_copy (btor, e[0]);
          }
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_UPDATE_NODE:
          result = btor_exp_update (btor, e[2], e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          btor_node_release (btor, e[2]);
          break;
        default:
          assert (btor_node_is_cond (real_cur));
          result = btor_exp_cond (btor, e[2], e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          btor_node_release (btor, e[2]);
      }

      d->as_ptr = btor_node_copy (btor, result);
      if (real_cur->parameterized || btor_node_is_lambda (real_cur))
        BTOR_PUSH_STACK (reset, real_cur);

      if (btor_node_is_lambda (real_cur) && cur_parent
          && btor_node_is_apply (cur_parent)
          && btor_node_param_get_assigned_exp (real_cur->e[0]))
      {
        btor_beta_unassign_params (btor, real_cur);
#ifndef NDEBUG
        (void) BTOR_POP_STACK (unassign_stack);
#endif
        next = BTOR_POP_STACK (reset);
        do
        {
          btor_hashint_map_remove (mark, next->id, &md);
          btor_node_release (btor, md.as_ptr);
          next = BTOR_POP_STACK (reset);
        } while (next != real_cur);
      }

      if (btor_node_is_lambda (real_cur)
          && !real_cur->parameterized
          /* only count head lambdas (in case of curried lambdas) */
          && (!cur_parent || !btor_node_is_lambda (cur_parent)))
        cur_lambda_depth--;

    BETA_REDUCE_PUSH_RESULT:
      if (btor_node_is_inverted (cur)) result = btor_node_invert (result);

      BTOR_PUSH_STACK (arg_stack, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto BETA_REDUCE_PUSH_RESULT;
    }
  }
  assert (BTOR_EMPTY_STACK (unassign_stack));
  assert (cur_lambda_depth == 0);
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  while (!BTOR_EMPTY_STACK (cleanup_stack))
  {
    cur = BTOR_POP_STACK (cleanup_stack);
    assert (btor_node_is_regular (cur));
  }

  /* cleanup cache */
  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    btor_node_release (btor, mark->data[i].as_ptr);
  }

  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (arg_stack);
  BTOR_RELEASE_STACK (cleanup_stack);
  BTOR_RELEASE_STACK (reset);
#ifndef NDEBUG
  BTOR_RELEASE_STACK (unassign_stack);
#endif
  btor_hashint_map_delete (mark);

  BTORLOG (2,
           "%s: result %s (%d)",
           __FUNCTION__,
           btor_util_node2string (result),
           btor_node_is_inverted (result));
  btor->time.beta += btor_util_time_stamp () - start;
  return result;
}

static BtorNode *
beta_reduce_partial_aux (Btor *btor,
                         BtorNode *exp,
                         BtorPtrHashTable *cond_sel_if,
                         BtorPtrHashTable *cond_sel_else,
                         BtorPtrHashTable *conds,
                         BtorNodePtrStack *conds_stack,
                         BtorIntHashTable *conds_cache)
{
  assert (btor);
  assert (exp);
  assert (!cond_sel_if || cond_sel_else);
  assert (!cond_sel_else || cond_sel_if);

  uint32_t i;
  double start;
  BtorBitVector *eval_res;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args, *tmp;
  BtorNodePtrStack stack, arg_stack, reset;
  BtorPtrHashTable *t;
  BtorIntHashTable *mark;
  BtorHashTableData *d, md;

  if (!btor_node_real_addr (exp)->parameterized && !btor_node_is_lambda (exp))
    return btor_node_copy (btor, exp);

  start = btor_util_time_stamp ();
  btor->stats.betap_reduce_calls++;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, arg_stack);
  BTOR_INIT_STACK (mm, reset);
  mark = btor_hashint_map_new (mm);

  real_cur = btor_node_real_addr (exp);

  /* skip all curried lambdas */
  if (btor_node_is_lambda (real_cur))
    exp = btor_node_binder_get_body (real_cur);

  BTOR_PUSH_STACK (stack, exp);
  BTOR_PUSH_STACK (stack, 0);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_parent = BTOR_POP_STACK (stack);
    cur        = BTOR_POP_STACK (stack);
    real_cur   = btor_node_real_addr (cur);

    d = btor_hashint_map_get (mark, real_cur->id);

    if (!d)
    {
      /* stop at non-parameterized nodes */
      if (!real_cur->parameterized)
      {
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (btor_node_is_param (real_cur))
      {
        next = btor_node_param_get_assigned_exp (real_cur);
        assert (next);
        next = btor_node_cond_invert (cur, next);
        BTOR_PUSH_STACK (arg_stack, btor_node_copy (btor, next));
        continue;
      }
      /* assign params of lambda expression */
      else if (btor_node_is_lambda (real_cur)
               && btor_node_is_apply (cur_parent)
               /* check if we have arguments on the stack */
               && !BTOR_EMPTY_STACK (arg_stack)
               /* if it is nested, its parameter is already assigned */
               && !btor_node_param_get_assigned_exp (real_cur->e[0]))
      {
        // TODO: there are no nested lambdas anymore is this still possible?
        args = BTOR_TOP_STACK (arg_stack);
        assert (btor_node_is_args (args));
        btor_beta_assign_args (btor, real_cur, args);
        BTOR_PUSH_STACK (reset, real_cur);
      }

      btor_hashint_map_add (mark, real_cur->id);
      BTOR_PUSH_STACK (stack, cur);
      BTOR_PUSH_STACK (stack, cur_parent);

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (btor_node_is_cond (real_cur))
      {
        BTOR_PUSH_STACK (stack, real_cur->e[0]);
        BTOR_PUSH_STACK (stack, real_cur);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BTOR_PUSH_STACK (stack, real_cur->e[i]);
          BTOR_PUSH_STACK (stack, real_cur);
        }
      }
    }
    else if (!d->as_ptr)
    {
      assert (real_cur->parameterized);
      assert (real_cur->arity >= 1);

      if (btor_node_is_cond (real_cur))
        arg_stack.top -= 1;
      else
      {
        assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);
        arg_stack.top -= real_cur->arity;
      }

      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_BV_SLICE_NODE:
          result = btor_exp_bv_slice (btor,
                                      e[0],
                                      btor_node_bv_slice_get_upper (real_cur),
                                      btor_node_bv_slice_get_lower (real_cur));
          btor_node_release (btor, e[0]);
          break;
        case BTOR_BV_AND_NODE:
          result = btor_exp_bv_and (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_EQ_NODE:
        case BTOR_FUN_EQ_NODE:
          result = btor_exp_eq (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_ADD_NODE:
          result = btor_exp_bv_add (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_MUL_NODE:
          result = btor_exp_bv_mul (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_ULT_NODE:
          result = btor_exp_bv_ult (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_SLL_NODE:
          result = btor_exp_bv_sll (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_SRL_NODE:
          result = btor_exp_bv_srl (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_UDIV_NODE:
          result = btor_exp_bv_udiv (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_UREM_NODE:
          result = btor_exp_bv_urem (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_BV_CONCAT_NODE:
          result = btor_exp_bv_concat (btor, e[1], e[0]);
          btor_node_release (btor, e[0]);
          btor_node_release (btor, e[1]);
          break;
        case BTOR_ARGS_NODE:
          assert (real_cur->arity >= 1);
          assert (real_cur->arity <= 3);
          if (real_cur->arity == 2)
          {
            next = e[0];
            e[0] = e[1];
            e[1] = next;
          }
          else if (real_cur->arity == 3)
          {
            next = e[0];
            e[0] = e[2];
            e[2] = next;
          }
          result = btor_exp_args (btor, e, real_cur->arity);
          btor_node_release (btor, e[0]);
          if (real_cur->arity >= 2) btor_node_release (btor, e[1]);
          if (real_cur->arity >= 3) btor_node_release (btor, e[2]);
          break;
        case BTOR_APPLY_NODE:
          if (btor_node_is_fun (e[1]))
          {
            result = btor_node_create_apply (btor, e[1], e[0]);
            btor_node_release (btor, e[1]);
          }
          else
            result = e[1];
          btor_node_release (btor, e[0]);
          break;
        case BTOR_LAMBDA_NODE:
          /* lambdas are always reduced to some term without e[1] */
          assert (!btor_node_real_addr (e[0])->parameterized);
          result = e[0];
          btor_node_release (btor, e[1]);
          break;
        default:
          assert (btor_node_is_cond (real_cur));
          /* only condition rebuilt, evaluate and choose branch */
          assert (!btor_node_real_addr (e[0])->parameterized);
          eval_res = btor_eval_exp (btor, e[0]);
          assert (eval_res);

          /* save condition for consistency checking */
          if (conds
              && !btor_hashptr_table_get (conds, btor_node_real_addr (e[0])))
          {
            btor_hashptr_table_add (
                conds, btor_node_copy (btor, btor_node_real_addr (e[0])));
          }

          t = 0;
          if (btor_bv_is_true (eval_res))
          {
            if (cond_sel_if) t = cond_sel_if;
            next = real_cur->e[1];
            tmp  = e[0];
          }
          else
          {
            assert (btor_bv_is_false (eval_res));
            if (cond_sel_else) t = cond_sel_else;
            next = real_cur->e[2];
            tmp  = btor_node_invert (e[0]);
          }

          if (conds_cache
              && !btor_hashint_table_contains (conds_cache,
                                               btor_node_get_id (tmp)))
          {
            assert (conds_stack);
            BTOR_PUSH_STACK (*conds_stack, btor_node_copy (btor, tmp));
          }

          if (t && !btor_hashptr_table_get (t, e[0]))
            btor_hashptr_table_add (t, btor_node_copy (btor, e[0]));

          btor_bv_free (btor->mm, eval_res);
          btor_node_release (btor, e[0]);

          assert (next);
          next = btor_node_cond_invert (cur, next);
          BTOR_PUSH_STACK (stack, next);
          BTOR_PUSH_STACK (stack, real_cur);
          /* conditionals are not cached (e[0] is cached, and thus, the
           * resp. branch can always be selected without further
           * overhead. */
          btor_hashint_map_remove (mark, real_cur->id, 0);
          continue;
      }

      d->as_ptr = btor_node_copy (btor, result);
      if (real_cur->parameterized || btor_node_is_lambda (real_cur))
        BTOR_PUSH_STACK (reset, real_cur);

      if (btor_node_is_lambda (real_cur))
      {
        btor_beta_unassign_params (btor, real_cur);
        next = BTOR_POP_STACK (reset);
        do
        {
          btor_hashint_map_remove (mark, next->id, &md);
          btor_node_release (btor, md.as_ptr);
          next = BTOR_POP_STACK (reset);
        } while (next != real_cur);
      }

    BETA_REDUCE_PARTIAL_PUSH_RESULT:
      if (btor_node_is_inverted (cur)) result = btor_node_invert (result);

      BTOR_PUSH_STACK (arg_stack, result);
    }
    else
    {
      assert (real_cur->parameterized);
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      assert (!btor_node_is_lambda (result));
      goto BETA_REDUCE_PARTIAL_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  /* cleanup cache */
  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    btor_node_release (btor, mark->data[i].as_ptr);
  }

  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (arg_stack);
  BTOR_RELEASE_STACK (reset);
  btor_hashint_map_delete (mark);

  BTORLOG (2,
           "%s: result %s (%d)",
           __FUNCTION__,
           btor_util_node2string (result),
           btor_node_is_inverted (result));
  btor->time.betap += btor_util_time_stamp () - start;

  return result;
}

BtorNode *
btor_beta_reduce_full (Btor *btor, BtorNode *exp, BtorPtrHashTable *cache)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));
  return beta_reduce (btor, exp, BETA_RED_FULL, 0, 0, cache);
}

BtorNode *
btor_beta_reduce_merge (Btor *btor,
                        BtorNode *exp,
                        BtorPtrHashTable *merge_lambdas)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));
  return beta_reduce (btor, exp, BETA_RED_LAMBDA_MERGE, 0, merge_lambdas, 0);
}

BtorNode *
btor_beta_reduce_bounded (Btor *btor, BtorNode *exp, int32_t bound)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));
  return beta_reduce (btor, exp, BETA_RED_BOUNDED, bound, 0, 0);
}

BtorNode *
btor_beta_reduce_partial (Btor *btor, BtorNode *exp, BtorPtrHashTable *conds)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));
  return beta_reduce_partial_aux (btor, exp, 0, 0, conds, 0, 0);
}

BtorNode *
btor_beta_reduce_partial_collect (Btor *btor,
                                  BtorNode *exp,
                                  BtorPtrHashTable *cond_sel_if,
                                  BtorPtrHashTable *cond_sel_else)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));
  return beta_reduce_partial_aux (
      btor, exp, cond_sel_if, cond_sel_else, 0, 0, 0);
}

BtorNode *
btor_beta_reduce_partial_collect_new (Btor *btor,
                                      BtorNode *exp,
                                      BtorNodePtrStack *exps,
                                      BtorIntHashTable *cache)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, btor_util_node2string (exp));
  return beta_reduce_partial_aux (btor, exp, 0, 0, 0, exps, cache);
}

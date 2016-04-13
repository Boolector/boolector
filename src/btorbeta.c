/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2016 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2013 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbeta.h"
#include "btorlog.h"
#include "btorrewrite.h"
#include "btorslvfun.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorparamcache.h"
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
  assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (lambda)));
  assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (!BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (result)));
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair   = btor_new_exp_pair (btor, lambda, exp);
  bucket = btor_get_ptr_hash_table (cache, pair);
  if (bucket)
  {
    btor_delete_exp_pair (btor, pair);
    assert ((BtorNode *) bucket->data.as_ptr == result);
  }
  else
    btor_add_ptr_hash_table (cache, pair)->data.as_ptr =
        btor_copy_exp (btor, result);
  BTORLOG (3,
           "%s: (%s, %s) -> %s",
           __FUNCTION__,
           node2string (lambda),
           node2string (exp),
           node2string (result));
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
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair   = btor_new_exp_pair (btor, lambda, exp);
  bucket = btor_get_ptr_hash_table (cache, pair);
  btor_delete_exp_pair (btor, pair);

  if (bucket)
  {
    BTORLOG (3,
             "%s: (%s, %s) -> %s",
             __FUNCTION__,
             node2string (lambda),
             node2string (exp),
             node2string (bucket->data.as_ptr));
    return (BtorNode *) bucket->data.as_ptr;
  }

  return 0;
}

void
btor_assign_args (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_REGULAR_NODE (args));
  assert (BTOR_IS_LAMBDA_NODE (fun));
  assert (BTOR_IS_ARGS_NODE (args));

  //  BTORLOG ("%s: %s (%d params, %d args)", __FUNCTION__, node2string (fun),
  //	   ((BtorLambdaNode *) fun)->num_params,
  //	   ((BtorArgsNode *) args)->num_args);

  BtorNode *cur_lambda, *cur_arg;
  BtorNodeIterator it;
  BtorArgsIterator ait;

  btor_init_args_iterator (&ait, args);
  btor_init_lambda_iterator (&it, fun);

  while (btor_has_next_args_iterator (&ait))
  {
    assert (btor_has_next_lambda_iterator (&it));
    cur_arg    = btor_next_args_iterator (&ait);
    cur_lambda = btor_next_lambda_iterator (&it);
    btor_assign_param (btor, cur_lambda, cur_arg);
  }
}

void
btor_assign_param (Btor *btor, BtorNode *lambda, BtorNode *arg)
{
  (void) btor;
  assert (btor);
  assert (lambda);
  assert (arg);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (!btor_param_get_assigned_exp (lambda->e[0]));
  btor_param_set_assigned_exp (lambda->e[0], arg);
}

void
btor_unassign_params (Btor *btor, BtorNode *lambda)
{
  (void) btor;
  assert (lambda);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (BTOR_IS_PARAM_NODE (lambda->e[0]));

  do
  {
    if (!btor_param_get_assigned_exp (lambda->e[0])) break;

    btor_param_set_assigned_exp (lambda->e[0], 0);
    lambda = BTOR_REAL_ADDR_NODE (lambda->e[1]);
  } while (BTOR_IS_LAMBDA_NODE (lambda));
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
btor_beta_reduce (Btor *btor,
                  BtorNode *exp,
                  int mode,
                  int bound,
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

  int i, cur_lambda_depth = 0;
  double start;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args;
  BtorNode *cached;
  BtorNodePtrStack stack, arg_stack, cleanup_stack;
  BtorPtrHashTable *param_cache;
  BtorParamCacheTuple *t;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorIntHashTable *mark;
  BtorIntHashTableData *d;
#ifndef NDEBUG
  BtorNodePtrStack unassign_stack;
  BTOR_INIT_STACK (unassign_stack);
#endif

  start = btor_time_stamp ();
  btor->stats.beta_reduce_calls++;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (cleanup_stack);
  param_cache =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_param_cache_tuple,
                               (BtorCmpPtr) btor_compare_param_cache_tuple);
  mark = btor_new_int_hash_map (mm);

  real_cur = BTOR_REAL_ADDR_NODE (exp);

  BTOR_PUSH_STACK (mm, stack, exp);
  BTOR_PUSH_STACK (mm, stack, 0);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_parent = BTOR_POP_STACK (stack);
    cur        = BTOR_POP_STACK (stack);
    /* we do not want the simplification of top level apply constraints */
    if (BTOR_REAL_ADDR_NODE (cur)->constraint
        && BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (cur)))
      cur = btor_pointer_chase_simplified_exp (btor, cur);
    else
      cur = btor_simplify_exp (btor, cur);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (mark, real_cur->id);

    if (!d)
    {
    BETA_REDUCE_START:
      assert (!BTOR_IS_LAMBDA_NODE (real_cur) || !real_cur->e[0]->simplified);

      if (BTOR_IS_LAMBDA_NODE (real_cur)
          && !real_cur->parameterized
          /* only count head lambdas (in case of curried lambdas) */
          && (!cur_parent || !BTOR_IS_LAMBDA_NODE (cur_parent)))
        cur_lambda_depth++;

      /* stop at given bound */
      if (bound > 0 && BTOR_IS_LAMBDA_NODE (real_cur)
          && cur_lambda_depth == bound)
      {
        assert (!real_cur->parameterized);
        assert (!cur_parent || !BTOR_IS_LAMBDA_NODE (cur_parent));
        cur_lambda_depth--;
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }
      /* skip all lambdas that are not marked for merge */
      else if (mode == BETA_RED_LAMBDA_MERGE && BTOR_IS_LAMBDA_NODE (real_cur)
               && !btor_get_ptr_hash_table (merge_lambdas, real_cur)
               /* do not stop at parameterized lambdas, otherwise the
                * result may contain parameters that are not bound by any
                * lambda anymore */
               && !real_cur->parameterized
               /* do not stop at non-parameterized curried lambdas */
               && (!cur_parent || !BTOR_IS_LAMBDA_NODE (cur_parent)))
      {
        cur_lambda_depth--;
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }
      /* stop at nodes that do not need to be rebuilt */
      else if (!real_cur->lambda_below && !real_cur->parameterized)
      {
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        next = btor_param_get_assigned_exp (real_cur);
        if (!next) next = real_cur;
        if (BTOR_IS_INVERTED_NODE (cur)) next = BTOR_INVERT_NODE (next);
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, next));
        continue;
      }
      /* assign params of lambda expression */
      else if (BTOR_IS_LAMBDA_NODE (real_cur)
               && BTOR_IS_APPLY_NODE (cur_parent)
               /* check if we have arguments on the stack */
               && !BTOR_EMPTY_STACK (arg_stack)
               /* if it is nested, its parameter is already assigned */
               && !btor_param_get_assigned_exp (real_cur->e[0]))
      {
        args = BTOR_TOP_STACK (arg_stack);
        assert (BTOR_IS_REGULAR_NODE (args));
        assert (BTOR_IS_ARGS_NODE (args));

        if (cache)
        {
          cached = cached_beta_result (btor, cache, real_cur, args);
          if (cached)
          {
            assert (!real_cur->parameterized);
            if (BTOR_IS_INVERTED_NODE (cur)) cached = BTOR_INVERT_NODE (cached);
            BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cached));
            cur_lambda_depth--;
            continue;
          }
        }

#ifndef NDEBUG
        BTOR_PUSH_STACK (mm, unassign_stack, real_cur);
#endif
        btor_assign_args (btor, real_cur, args);
      }
      /* do not try to reduce lambdas below equalities as lambdas cannot
       * be eliminated. further, it may produce lambdas that break lemma
       * generation for extensionality */
      else if (BTOR_IS_LAMBDA_NODE (real_cur)
               && (BTOR_IS_FEQ_NODE (cur_parent)
                   || BTOR_IS_FUN_COND_NODE (cur_parent)))
      {
        assert (!btor_param_get_assigned_exp (real_cur->e[0]));
        cur_lambda_depth--;
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }
      /* do not try to reduce conditionals on functions below equalities
       * as they cannot be eliminated. */
      else if (BTOR_IS_FUN_COND_NODE (real_cur)
               && BTOR_IS_FEQ_NODE (cur_parent))
      {
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }

      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, stack, cur);
      BTOR_PUSH_STACK (mm, stack, cur_parent);
      BTOR_PUSH_STACK (mm, cleanup_stack, real_cur);
      for (i = 0; i < real_cur->arity; i++)
      {
        BTOR_PUSH_STACK (mm, stack, btor_simplify_exp (btor, real_cur->e[i]));
        BTOR_PUSH_STACK (mm, stack, real_cur);
      }
    }
    else if (d->as_int == 0)
    {
      assert (real_cur->arity >= 1);
      assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);

      d->as_int = 1;
      arg_stack.top -= real_cur->arity;
      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_exp (btor,
                                   e[0],
                                   btor_slice_get_upper (real_cur),
                                   btor_slice_get_lower (real_cur));
          btor_release_exp (btor, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_BEQ_NODE:
        case BTOR_FEQ_NODE:
          result = btor_eq_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
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
          result = btor_args_exp (btor, e, real_cur->arity);
          btor_release_exp (btor, e[0]);
          if (real_cur->arity >= 2) btor_release_exp (btor, e[1]);
          if (real_cur->arity >= 3) btor_release_exp (btor, e[2]);
          break;
        case BTOR_APPLY_NODE:
          if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e[1])))
          {
            assert (BTOR_IS_ARGS_NODE (e[0]));
            /* NOTE: do not use btor_apply_exp here since
             * beta reduction is used in btor_rewrite_apply_exp. */
            result = btor_apply_exp_node (btor, e[1], e[0]);
          }
          else
          {
            result = btor_copy_exp (btor, e[1]);
          }

          if (cache && mode == BETA_RED_FULL
              && BTOR_IS_LAMBDA_NODE (real_cur->e[0]))
            cache_beta_result (btor, cache, real_cur->e[0], e[0], result);

          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_LAMBDA_NODE:
          /* function equalities and conditionals always expect a lambda
           * as argument */
          if (BTOR_IS_FEQ_NODE (cur_parent)
              || (BTOR_IS_FUN_COND_NODE (cur_parent)
                  && !btor_param_get_assigned_exp (real_cur->e[0])))
          {
            assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (e[1])));
            result = btor_lambda_exp (btor, e[1], e[0]);
            if (real_cur->is_array) result->is_array = 1;
            if (btor_lambda_get_static_rho (real_cur)
                && !btor_lambda_get_static_rho (result))
              btor_lambda_set_static_rho (
                  result, btor_lambda_copy_static_rho (btor, real_cur));
          }
          /* special case: lambda not reduced (not instantiated)
           *		 and is not constant */
          else if (real_cur->e[0] == e[1] && real_cur->e[1] == e[0]
                   && BTOR_REAL_ADDR_NODE (e[0])->parameterized)
          {
            result = btor_copy_exp (btor, real_cur);
          }
          /* main case: lambda reduced to some term without e[1] */
          else
          {
            result = btor_copy_exp (btor, e[0]);
          }
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        default:
          assert (BTOR_IS_COND_NODE (real_cur));
          result = btor_cond_exp (btor, e[2], e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          btor_release_exp (btor, e[2]);
      }

      /* cache rebuilt parameterized node with current arguments */
      if ((BTOR_IS_LAMBDA_NODE (real_cur)
           && btor_param_get_assigned_exp (real_cur->e[0]))
          || real_cur->parameterized)
      {
        t = btor_new_param_cache_tuple (btor, real_cur);
        assert (!btor_get_ptr_hash_table (param_cache, t));
        btor_add_ptr_hash_table (param_cache, t)->data.as_ptr =
            btor_copy_exp (btor, result);
      }

      if (BTOR_IS_LAMBDA_NODE (real_cur) && BTOR_IS_APPLY_NODE (cur_parent)
          && btor_param_get_assigned_exp (real_cur->e[0]))
      {
        btor_unassign_params (btor, real_cur);
#ifndef NDEBUG
        (void) BTOR_POP_STACK (unassign_stack);
#endif
      }

      if (BTOR_IS_LAMBDA_NODE (real_cur)
          && !real_cur->parameterized
          /* only count head lambdas (in case of curried lambdas) */
          && (!cur_parent || !BTOR_IS_LAMBDA_NODE (cur_parent)))
        cur_lambda_depth--;

    BETA_REDUCE_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur)) result = BTOR_INVERT_NODE (result);

      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (d->as_int == 1);
      /* check cache if parameterized expressions was already instantiated
       * with current assignment */
      if (BTOR_IS_LAMBDA_NODE (real_cur) || real_cur->parameterized)
      {
        if (BTOR_IS_LAMBDA_NODE (real_cur))
        {
          assert (cur_parent);
          args = 0;
          /* instantiate lambda in order to create a param cache tuple.
           * we only do this if there are arguments to instantiate on
           * the 'arg_stack', which is only the case if the current
           * parent is an apply node. */
          // TODO (ma): check why !cur_parent here?
          // why not checking cur_parent && ...
          if (!cur_parent || BTOR_IS_APPLY_NODE (cur_parent))
          {
            assert (!btor_param_get_assigned_exp (real_cur->e[0]));
            args = BTOR_TOP_STACK (arg_stack);
            assert (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (args)));
            btor_assign_args (btor, real_cur, args);
          }
          t = btor_new_param_cache_tuple (btor, real_cur);
          if (args) btor_unassign_params (btor, real_cur);
        }
        else
          t = btor_new_param_cache_tuple (btor, real_cur);

        b = btor_get_ptr_hash_table (param_cache, t);
        btor_delete_param_cache_tuple (btor, t);
        /* real_cur not yet cached with current param assignment, rebuild
         * expression */
        if (!b)
        {
          btor_remove_int_hash_map (mark, real_cur->id, 0);
          goto BETA_REDUCE_START;
        }
        assert (b);
        result = btor_copy_exp (btor, (BtorNode *) b->data.as_ptr);
      }
      else
        result = btor_copy_exp (btor, real_cur);
      goto BETA_REDUCE_PUSH_RESULT;
    }
  }
  assert (BTOR_EMPTY_STACK (unassign_stack));
  assert (cur_lambda_depth == 0);
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  /* release cache */
  btor_init_hash_table_iterator (&it, param_cache);
  while (btor_has_next_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.as_ptr);
    t        = (BtorParamCacheTuple *) btor_next_node_hash_table_iterator (&it);
    real_cur = t->exp;
    assert (BTOR_IS_REGULAR_NODE (real_cur));
    btor_delete_param_cache_tuple (btor, t);
  }

  while (!BTOR_EMPTY_STACK (cleanup_stack))
  {
    cur = BTOR_POP_STACK (cleanup_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
  }

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  BTOR_RELEASE_STACK (mm, cleanup_stack);
#ifndef NDEBUG
  BTOR_RELEASE_STACK (mm, unassign_stack);
#endif
  btor_delete_ptr_hash_table (param_cache);
  btor_delete_int_hash_map (mark);

  BTORLOG (2,
           "%s: result %s (%d)",
           __FUNCTION__,
           node2string (result),
           BTOR_IS_INVERTED_NODE (result));
  btor->time.beta += btor_time_stamp () - start;
  return result;
}

static BtorNode *
btor_beta_reduce_partial_aux (Btor *btor,
                              BtorNode *exp,
                              BtorPtrHashTable *cond_sel_if,
                              BtorPtrHashTable *cond_sel_else,
                              BtorPtrHashTable *conds)
{
  assert (btor);
  assert (exp);
  assert (!cond_sel_if || cond_sel_else);
  assert (!cond_sel_else || cond_sel_if);

  int i;
  double start;
  BtorBitVector *eval_res;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args, *cur_args;
  BtorNodePtrStack stack, arg_stack;
  BtorPtrHashTable *cache, *t;
  BtorPtrHashBucket *b;
  BtorParamCacheTuple *tup;
  BtorHashTableIterator it;
  BtorIntHashTable *mark;
  BtorIntHashTableData *d;

  if (!BTOR_REAL_ADDR_NODE (exp)->parameterized
      && !BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp)))
    return btor_copy_exp (btor, exp);

  start = btor_time_stamp ();
  btor->stats.beta_reduce_calls++;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (arg_stack);
  cache = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_param_cache_tuple,
                                   (BtorCmpPtr) btor_compare_param_cache_tuple);
  mark  = btor_new_int_hash_map (mm);

  real_cur = BTOR_REAL_ADDR_NODE (exp);

  /* skip all nested lambdas */
  if (BTOR_IS_LAMBDA_NODE (real_cur)) exp = btor_binder_get_body (real_cur);

  BTOR_PUSH_STACK (mm, stack, exp);
  BTOR_PUSH_STACK (mm, stack, 0);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_parent = BTOR_POP_STACK (stack);
    cur        = BTOR_POP_STACK (stack);
    real_cur   = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (mark, real_cur->id);

    if (!d)
    {
    BETA_REDUCE_PARTIAL_START:
      /* stop at non-parameterized nodes */
      if (!real_cur->parameterized)
      {
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        next = btor_param_get_assigned_exp (real_cur);
        assert (next);
        next = BTOR_COND_INVERT_NODE (cur, next);
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, next));
        continue;
      }
      /* assign params of lambda expression */
      else if (BTOR_IS_LAMBDA_NODE (real_cur)
               && BTOR_IS_APPLY_NODE (cur_parent)
               /* check if we have arguments on the stack */
               && !BTOR_EMPTY_STACK (arg_stack)
               /* if it is nested, its parameter is already assigned */
               && !btor_param_get_assigned_exp (real_cur->e[0]))
      {
        args = BTOR_TOP_STACK (arg_stack);
        assert (BTOR_IS_ARGS_NODE (args));
        btor_assign_args (btor, real_cur, args);
      }

      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, stack, cur);
      BTOR_PUSH_STACK (mm, stack, cur_parent);

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (BTOR_IS_COND_NODE (real_cur))
      {
        BTOR_PUSH_STACK (mm, stack, real_cur->e[0]);
        BTOR_PUSH_STACK (mm, stack, real_cur);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
          BTOR_PUSH_STACK (mm, stack, real_cur);
        }
      }
    }
    else if (d->as_int == 0)
    {
      assert (real_cur->parameterized);
      assert (real_cur->arity >= 1);

      if (BTOR_IS_COND_NODE (real_cur))
        arg_stack.top -= 1;
      else
      {
        assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);
        arg_stack.top -= real_cur->arity;
      }

      d->as_int = 1;
      e         = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_exp (btor,
                                   e[0],
                                   btor_slice_get_upper (real_cur),
                                   btor_slice_get_lower (real_cur));
          btor_release_exp (btor, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_BEQ_NODE:
        case BTOR_FEQ_NODE:
          result = btor_eq_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_exp (btor, e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
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
          result = btor_args_exp (btor, e, real_cur->arity);
          btor_release_exp (btor, e[0]);
          if (real_cur->arity >= 2) btor_release_exp (btor, e[1]);
          if (real_cur->arity >= 3) btor_release_exp (btor, e[2]);
          break;
        case BTOR_APPLY_NODE:
          if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e[1])))
          {
            result = btor_apply_exp_node (btor, e[1], e[0]);
            btor_release_exp (btor, e[1]);
          }
          else
            result = e[1];
          btor_release_exp (btor, e[0]);
          break;
        case BTOR_LAMBDA_NODE:
          /* lambdas are always reduced to some term without e[1] */
          assert (!BTOR_REAL_ADDR_NODE (e[0])->parameterized);
          result = e[0];
          btor_release_exp (btor, e[1]);
          break;
        default:
          assert (BTOR_IS_COND_NODE (real_cur));
          /* only condition rebuilt, evaluate and choose branch */
          assert (!BTOR_REAL_ADDR_NODE (e[0])->parameterized);
          eval_res = btor_eval_exp (btor, e[0]);
          assert (eval_res);

          /* save condition for consistency checking */
          if (conds
              && !btor_get_ptr_hash_table (conds, BTOR_REAL_ADDR_NODE (e[0])))
          {
            btor_add_ptr_hash_table (
                conds, btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (e[0])));
          }

          t = 0;
          if (btor_is_true_bv (eval_res))
          {
            if (cond_sel_if) t = cond_sel_if;
            next = real_cur->e[1];
          }
          else
          {
            assert (btor_is_false_bv (eval_res));
            if (cond_sel_else) t = cond_sel_else;
            next = real_cur->e[2];
          }

          if (t && !btor_get_ptr_hash_table (t, e[0]))
            btor_add_ptr_hash_table (t, btor_copy_exp (btor, e[0]));

          btor_free_bv (btor->mm, eval_res);
          btor_release_exp (btor, e[0]);

          assert (next);
          next = BTOR_COND_INVERT_NODE (cur, next);
          BTOR_PUSH_STACK (mm, stack, next);
          BTOR_PUSH_STACK (mm, stack, real_cur);
          /* conditionals are not cached (e[0] is cached, and thus, the
           * resp. branch can always be selected without further
           * overhead. */
          btor_remove_int_hash_map (mark, real_cur->id, 0);
          continue;
      }

      /* cache rebuilt parameterized node with current arguments */
      tup = btor_new_param_cache_tuple (btor, real_cur);
      assert (!btor_get_ptr_hash_table (cache, tup));
      btor_add_ptr_hash_table (cache, tup)->data.as_ptr =
          btor_copy_exp (btor, result);

      /* we still need the assigned argument for caching */
      if (BTOR_IS_LAMBDA_NODE (real_cur)) btor_unassign_params (btor, real_cur);

    BETA_REDUCE_PARTIAL_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur)) result = BTOR_INVERT_NODE (result);

      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (real_cur->parameterized);
      assert (d->as_int == 1);
      if (BTOR_IS_LAMBDA_NODE (real_cur))
      {
        cur_args = BTOR_TOP_STACK (arg_stack);
        assert (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (cur_args)));
        btor_assign_args (btor, real_cur, cur_args);
        tup = btor_new_param_cache_tuple (btor, real_cur);
        btor_unassign_params (btor, real_cur);
      }
      else
        tup = btor_new_param_cache_tuple (btor, real_cur);

      b = btor_get_ptr_hash_table (cache, tup);
      btor_delete_param_cache_tuple (btor, tup);
      /* real_cur not yet cached with current param assignment, rebuild
       * expression */
      if (!b)
      {
        btor_remove_int_hash_map (mark, real_cur->id, 0);
        goto BETA_REDUCE_PARTIAL_START;
      }
      assert (b);
      result = btor_copy_exp (btor, (BtorNode *) b->data.as_ptr);
      assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (result)));
      goto BETA_REDUCE_PARTIAL_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  /* release cache */
  btor_init_hash_table_iterator (&it, cache);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.as_ptr);
    tup      = (BtorParamCacheTuple *) btor_next_node_hash_table_iterator (&it);
    real_cur = tup->exp;
    assert (BTOR_IS_REGULAR_NODE (real_cur));
    btor_delete_param_cache_tuple (btor, tup);
  }

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_ptr_hash_table (cache);
  btor_delete_int_hash_map (mark);

  BTORLOG (2,
           "%s: result %s (%d)",
           __FUNCTION__,
           node2string (result),
           BTOR_IS_INVERTED_NODE (result));
  btor->time.beta += btor_time_stamp () - start;

  return result;
}

BtorNode *
btor_beta_reduce_full (Btor *btor, BtorNode *exp)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_FULL, 0, 0, 0);
}

BtorNode *
btor_beta_reduce_full_cached (Btor *btor,
                              BtorNode *exp,
                              BtorPtrHashTable *cache)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_FULL, 0, 0, cache);
}

BtorNode *
btor_beta_reduce_merge (Btor *btor,
                        BtorNode *exp,
                        BtorPtrHashTable *merge_lambdas)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (
      btor, exp, BETA_RED_LAMBDA_MERGE, 0, merge_lambdas, 0);
}

BtorNode *
btor_beta_reduce_bounded (Btor *btor, BtorNode *exp, int bound)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_BOUNDED, bound, 0, 0);
}

BtorNode *
btor_beta_reduce_partial (Btor *btor, BtorNode *exp, BtorPtrHashTable *conds)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce_partial_aux (btor, exp, 0, 0, conds);
}

BtorNode *
btor_beta_reduce_partial_collect (Btor *btor,
                                  BtorNode *exp,
                                  BtorPtrHashTable *cond_sel_if,
                                  BtorPtrHashTable *cond_sel_else)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce_partial_aux (
      btor, exp, cond_sel_if, cond_sel_else, 0);
}

BtorNode *
btor_apply_and_reduce (Btor *btor, int argc, BtorNode *args[], BtorNode *lambda)
{
  assert (btor);
  assert (argc >= 0);
  assert (argc < 1 || args);
  assert (lambda);

  int i;
  BtorNode *result, *cur;
  BtorNodePtrStack unassign;
  BtorMemMgr *mm;

  mm = btor->mm;

  BTOR_INIT_STACK (unassign);

  cur = lambda;
  for (i = 0; i < argc; i++)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_LAMBDA_NODE (cur));
    btor_assign_param (btor, cur, args[i]);
    BTOR_PUSH_STACK (mm, unassign, cur);
    cur = BTOR_REAL_ADDR_NODE (cur->e[1]);
  }

  result = btor_beta_reduce_full (btor, lambda);

  while (!BTOR_EMPTY_STACK (unassign))
  {
    cur = BTOR_POP_STACK (unassign);
    btor_unassign_params (btor, cur);
  }

  BTOR_RELEASE_STACK (mm, unassign);

  return result;
}

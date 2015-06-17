/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2014 Aina Niemetz.
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
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorparamcache.h"
#include "utils/btorutil.h"

#define BETA_RED_LAMBDA_MERGE -2
#define BETA_RED_FULL 0
#define BETA_RED_BOUNDED 1

#ifndef NDEBUG
static int
check_unique_table_beta_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      if (cur->beta_mark != 0) return 0;
  return 1;
}
#endif

static void
cache_beta_result (Btor *btor,
                   BtorNode *lambda,
                   BtorNode *exp,
                   BtorNode *result)
{
  assert (btor);
  assert (lambda);
  assert (exp);
  assert (result);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair = new_exp_pair (btor, lambda, exp);

  bucket = btor_find_in_ptr_hash_table (btor->cache, pair);
  if (bucket)
  {
    delete_exp_pair (btor, pair);
    assert ((BtorNode *) bucket->data.asPtr == result);
  }
  else
    btor_insert_in_ptr_hash_table (btor->cache, pair)->data.asPtr =
        btor_copy_exp (btor, result);
  BTORLOG (2,
           "%s: (%s, %s) -> %s",
           __FUNCTION__,
           node2string (lambda),
           node2string (exp),
           node2string (result));
}

static BtorNode *
cached_beta_result (Btor *btor, BtorNode *lambda, BtorNode *exp)
{
  assert (btor);
  assert (lambda);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair   = new_exp_pair (btor, lambda, exp);
  bucket = btor_find_in_ptr_hash_table (btor->cache, pair);
  delete_exp_pair (btor, pair);

  if (bucket) return (BtorNode *) bucket->data.asPtr;

  return 0;
}

BtorNode *
btor_param_cur_assignment (BtorNode *param)
{
  assert (param);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  param = BTOR_REAL_ADDR_NODE (param);
  return ((BtorParamNode *) param)->assigned_exp;
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

  init_args_iterator (&ait, args);
  init_lambda_iterator (&it, fun);

  while (has_next_args_iterator (&ait))
  {
    assert (has_next_lambda_iterator (&it));
    cur_arg    = next_args_iterator (&ait);
    cur_lambda = next_lambda_iterator (&it);
    btor_assign_param (btor, cur_lambda, cur_arg);
  }
}

static void
assign_new_params (Btor *btor, BtorNode *fun)
{
  BtorNode *lambda, *param, *arg;
  BtorNodeIterator it;

  init_lambda_iterator (&it, fun);
  while (has_next_lambda_iterator (&it))
  {
    lambda = next_lambda_iterator (&it);
    param  = lambda->e[0];
    arg    = btor_param_exp (btor, btor_get_exp_width (btor, param), 0);
    btor_assign_param (btor, lambda, arg);
  }
}

static void
unassign_new_params (Btor *btor, BtorNode *fun)
{
  BtorNode *lambda;
  BtorNodeIterator it;
  BtorParamNode *param;

  init_lambda_iterator (&it, fun);
  while (has_next_lambda_iterator (&it))
  {
    lambda = next_lambda_iterator (&it);
    param  = (BtorParamNode *) lambda->e[0];
    if (!param->assigned_exp) break;
    btor_release_exp (btor, param->assigned_exp);
    param->assigned_exp = 0;
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

  BtorParamNode *param;

  param = BTOR_LAMBDA_GET_PARAM (lambda);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_REAL_ADDR_NODE (arg)->sort_id == param->sort_id);
  //  BTORLOG ("  assign: %s (%s)", node2string (lambda), node2string (arg));
  assert (!param->assigned_exp);
  param->assigned_exp = arg;
}

void
btor_unassign_params (Btor *btor, BtorNode *lambda)
{
  (void) btor;
  assert (lambda);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (BTOR_IS_PARAM_NODE (lambda->e[0]));

  BtorParamNode *param;

  do
  {
    param = (BtorParamNode *) lambda->e[0];

    if (!param->assigned_exp) break;

    param->assigned_exp = 0;
    lambda              = BTOR_REAL_ADDR_NODE (lambda->e[1]);
  } while (BTOR_IS_LAMBDA_NODE (lambda));
}

#define BETA_REDUCE_PUSH_RESULT_IF_CACHED(lambda, assignment)              \
  {                                                                        \
    cached = cached_beta_result (btor, lambda, assignment);                \
    if (cached)                                                            \
    {                                                                      \
      if (BTOR_IS_INVERTED_NODE (cur)) cached = BTOR_INVERT_NODE (cached); \
      BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cached));       \
      continue;                                                            \
    }                                                                      \
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
                  BtorPtrHashTable *merge_lambdas)
{
  assert (btor);
  assert (exp);
  assert (mode == BETA_RED_LAMBDA_MERGE || mode == BETA_RED_FULL
          || mode == BETA_RED_BOUNDED);
  assert (bound >= 0);
  assert (bound == 0 || mode == BETA_RED_BOUNDED);
  assert (check_unique_table_beta_mark_unset_dbg (btor));
  assert (mode != BETA_RED_LAMBDA_MERGE || merge_lambdas);

  //  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  int i, cur_lambda_depth = 0;
  double start;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args;
  BtorNode *cached;
  BtorNodePtrStack stack, arg_stack, cleanup_stack;
  BtorPtrHashTable *cache;
  BtorPtrHashTable *param_cache;
  BtorParamCacheTuple *t;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
#ifndef NDEBUG
  BtorNodePtrStack unassign_stack;
  BTOR_INIT_STACK (unassign_stack);
#endif

  start = btor_time_stamp ();
  btor->stats.beta_reduce_calls++;

  mm    = btor->mm;
  cache = btor->cache;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (cleanup_stack);
  param_cache =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_param_cache_tuple,
                               (BtorCmpPtr) btor_compare_param_cache_tuple);

  real_cur = BTOR_REAL_ADDR_NODE (exp);

  BTOR_PUSH_STACK (mm, stack, exp);
  BTOR_PUSH_STACK (mm, stack, 0);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_parent = BTOR_POP_STACK (stack);
    cur        = BTOR_POP_STACK (stack);
    // TODO: directly push simplified exp onto stack at the beginning
    /* we do not want the simplification of top level apply constraints */
    if (BTOR_REAL_ADDR_NODE (cur)->constraint
        && BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (cur)))
      cur = btor_pointer_chase_simplified_exp (btor, cur);
    else
      cur = btor_simplify_exp (btor, cur);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->beta_mark == 0)
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
               && !btor_find_in_ptr_hash_table (merge_lambdas, real_cur)
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
        next = btor_param_cur_assignment (real_cur);
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
               && !btor_param_cur_assignment (real_cur->e[0]))
      {
        args = BTOR_TOP_STACK (arg_stack);
        assert (BTOR_IS_REGULAR_NODE (args));
        assert (BTOR_IS_ARGS_NODE (args));

        if (cache)
        {
          cached = cached_beta_result (btor, real_cur, args);
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
      else if (BTOR_IS_LAMBDA_NODE (real_cur) && BTOR_IS_FEQ_NODE (cur_parent))
      {
        assert (!btor_param_cur_assignment (real_cur->e[0]));
#ifndef NDEBUG
        BTOR_PUSH_STACK (mm, unassign_stack, real_cur);
#endif
        assign_new_params (btor, real_cur);
      }

      real_cur->beta_mark = 1;
      BTOR_PUSH_STACK (mm, stack, cur);
      BTOR_PUSH_STACK (mm, stack, cur_parent);
      BTOR_PUSH_STACK (mm, cleanup_stack, real_cur);

      for (i = 0; i < real_cur->arity; i++)
      {
        BTOR_PUSH_STACK (mm, stack, btor_simplify_exp (btor, real_cur->e[i]));
        BTOR_PUSH_STACK (mm, stack, real_cur);
      }
    }
    else if (real_cur->beta_mark == 1)
    {
      assert (real_cur->arity >= 1);
      assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);

      real_cur->beta_mark = 2;
      arg_stack.top -= real_cur->arity;
      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result =
              btor_slice_exp (btor, e[0], real_cur->upper, real_cur->lower);
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
          result = btor_args_exp (btor, real_cur->arity, e);
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

          if (cache
              && (mode == BETA_RED_FULL
                  || (!btor->options.beta_reduce_all.val
                      && mode == BETA_RED_BOUNDED))
              && BTOR_IS_LAMBDA_NODE (real_cur->e[0])
              /* only cache results of applications on non-parameterized
               * lambdas (all arguments given) */
              && !real_cur->e[0]->parameterized
              /* if we reached the bound at real_cur->e[0], we push
               * real_cur->e[0] onto the argument stack. in this case
               * we are not allowed to cache the result, as we only
               * cache results for beta reduced lambdas.
               */
              && (mode != BETA_RED_BOUNDED || real_cur->e[0] != e[1]))
          {
            assert (!real_cur->e[0]->simplified || cur == exp);
            assert (!BTOR_REAL_ADDR_NODE (real_cur->e[1])->simplified
                    || cur == exp);
            cache_beta_result (btor,
                               btor_simplify_exp (btor, real_cur->e[0]),
                               btor_simplify_exp (btor, e[0]),
                               result);
          }
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          break;
        case BTOR_LAMBDA_NODE:
          /* function equalities always expect a lambda as argument */
          if (BTOR_IS_FEQ_NODE (cur_parent))
          {
            assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (e[1])));
            result = btor_lambda_exp (btor, e[1], e[0]);
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
        case BTOR_BCOND_NODE:
          result = btor_cond_exp (btor, e[2], e[1], e[0]);
          btor_release_exp (btor, e[0]);
          btor_release_exp (btor, e[1]);
          btor_release_exp (btor, e[2]);
          break;
        default:
          printf ("%s\n", node2string (real_cur));
          result = 0;
          /* not reachable */
          assert (0);
          // TODO: abort
      }

      /* cache rebuilt parameterized node with current arguments */
      if ((BTOR_IS_LAMBDA_NODE (real_cur)
           && btor_param_cur_assignment (real_cur->e[0]))
          || real_cur->parameterized)
      {
        t = btor_new_param_cache_tuple (btor, real_cur);
        assert (!btor_find_in_ptr_hash_table (param_cache, t));
        btor_insert_in_ptr_hash_table (param_cache, t)->data.asPtr =
            btor_copy_exp (btor, result);
      }

      if (BTOR_IS_LAMBDA_NODE (real_cur) && BTOR_IS_APPLY_NODE (cur_parent)
          && btor_param_cur_assignment (real_cur->e[0]))
      {
        btor_unassign_params (btor, real_cur);
#ifndef NDEBUG
        (void) BTOR_POP_STACK (unassign_stack);
#endif
      }
      else if (BTOR_IS_LAMBDA_NODE (real_cur) && BTOR_IS_FEQ_NODE (cur_parent))
      {
        assert (btor_param_cur_assignment (real_cur->e[0]));
        unassign_new_params (btor, real_cur);
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
      assert (real_cur->beta_mark == 2);

      /* check cache if parameterized expressions was already instantiated
       * with current assignment */
      if (BTOR_IS_LAMBDA_NODE (real_cur) || real_cur->parameterized)
      {
        if (BTOR_IS_LAMBDA_NODE (real_cur))
        {
          args = 0;
          /* assign parameters of lambdas in order to create
           * a param cache tuple. if the parent is either a lambda
           * ('real_cur' is a curried lambda) or a function
           * equality we do not assign the parameters. */
          if (!cur_parent
              || (!BTOR_IS_LAMBDA_NODE (cur_parent)
                  && !BTOR_IS_FEQ_NODE (cur_parent)))
          {
            assert (!btor_param_cur_assignment (real_cur->e[0]));
            args = BTOR_TOP_STACK (arg_stack);
            assert (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (args)));
            btor_assign_args (btor, real_cur, args);
          }
          t = btor_new_param_cache_tuple (btor, real_cur);
          if (args) btor_unassign_params (btor, real_cur);
        }
        else
          t = btor_new_param_cache_tuple (btor, real_cur);

        b = btor_find_in_ptr_hash_table (param_cache, t);
        btor_delete_param_cache_tuple (btor, t);
        /* real_cur not yet cached with current param assignment, rebuild
         * expression */
        if (!b)
        {
          real_cur->beta_mark = 0;
          goto BETA_REDUCE_START;
        }
        assert (b);
        result = btor_copy_exp (btor, (BtorNode *) b->data.asPtr);
      }
      else
        result = btor_copy_exp (btor, real_cur);
      assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (result)));
      goto BETA_REDUCE_PUSH_RESULT;
    }
  }
  assert (BTOR_EMPTY_STACK (unassign_stack));
  assert (cur_lambda_depth == 0);
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  /* release cache and reset beta_mark flags */
  init_hash_table_iterator (&it, param_cache);
  while (has_next_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.asPtr);
    t        = (BtorParamCacheTuple *) next_node_hash_table_iterator (&it);
    real_cur = t->exp;
    assert (BTOR_IS_REGULAR_NODE (real_cur));
    btor_delete_param_cache_tuple (btor, t);
  }

  while (!BTOR_EMPTY_STACK (cleanup_stack))
  {
    cur = BTOR_POP_STACK (cleanup_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    cur->beta_mark = 0;
  }
  assert (check_unique_table_beta_mark_unset_dbg (btor));

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  BTOR_RELEASE_STACK (mm, cleanup_stack);
#ifndef NDEBUG
  BTOR_RELEASE_STACK (mm, unassign_stack);
#endif
  btor_delete_ptr_hash_table (param_cache);

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
                              int *evalerr,
                              BtorPtrHashTable *to_prop,
                              BtorPtrHashTable *conds)
{
  assert (btor);
  assert (exp);
  assert (!cond_sel_if || cond_sel_else);
  assert (!cond_sel_else || cond_sel_if);
  //  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  int i, rwl;
  double start;
  const char *eval_res;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args, *cur_args;
  BtorNodePtrStack stack, arg_stack;
  BtorPtrHashTable *cache, *mark, *tmp;
  BtorPtrHashBucket *b;
  BtorParamCacheTuple *t0;
  BtorHashTableIterator it;

  if (evalerr) *evalerr = 0;

  if (!BTOR_REAL_ADDR_NODE (exp)->parameterized
      && !BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp)))
    return btor_copy_exp (btor, exp);

  start = btor_time_stamp ();
  btor->stats.beta_reduce_calls++;

  rwl = btor->options.rewrite_level.val;
  if (btor->options.rewrite_level.val > 0)
    btor->options.rewrite_level.val = btor->options.rewrite_level_pbr.val;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (arg_stack);
  cache = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_param_cache_tuple,
                                   (BtorCmpPtr) btor_compare_param_cache_tuple);
  mark  = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);

  real_cur = BTOR_REAL_ADDR_NODE (exp);

  /* skip all nested lambdas */
  if (BTOR_IS_LAMBDA_NODE (real_cur)) exp = BTOR_LAMBDA_GET_BODY (real_cur);

  BTOR_PUSH_STACK (mm, stack, exp);
  BTOR_PUSH_STACK (mm, stack, 0);
  // TODO: intially we do not have args (assigned from outside)

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_parent = BTOR_POP_STACK (stack);
    cur        = BTOR_POP_STACK (stack);
    real_cur   = BTOR_REAL_ADDR_NODE (cur);

    if (real_cur->beta_mark == 0)
    {
    BETA_REDUCE_PARTIAL_START:
      /* stop at non-parameterized nodes */
      if (!real_cur->parameterized)
      {
        assert (BTOR_IS_FUN_NODE (real_cur) || BTOR_IS_ARGS_NODE (real_cur)
                || real_cur->tseitin);
        BTOR_PUSH_STACK (mm, arg_stack, btor_copy_exp (btor, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        next = btor_param_cur_assignment (real_cur);
        assert (next);
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
               && !btor_param_cur_assignment (real_cur->e[0]))
      {
        args = BTOR_TOP_STACK (arg_stack);
        assert (BTOR_IS_ARGS_NODE (args));
        btor_assign_args (btor, real_cur, args);
      }

      real_cur->beta_mark = 1;
      BTOR_PUSH_STACK (mm, stack, cur);
      BTOR_PUSH_STACK (mm, stack, cur_parent);

      if (BTOR_IS_BV_COND_NODE (real_cur))
      {
        real_cur->beta_mark = 3;
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
    else if (real_cur->beta_mark == 1 || real_cur->beta_mark == 3)
    {
      assert (real_cur->parameterized);
      assert (real_cur->arity >= 1);

      if (real_cur->beta_mark == 1)
      {
        assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);
        real_cur->beta_mark = 2;
        arg_stack.top -= real_cur->arity;
      }
      else
      {
        assert (BTOR_IS_BV_COND_NODE (real_cur));
        arg_stack.top -= 1;
      }

      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result =
              btor_slice_exp (btor, e[0], real_cur->upper, real_cur->lower);
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
          result = btor_args_exp (btor, real_cur->arity, e);
          btor_release_exp (btor, e[0]);
          if (real_cur->arity >= 2) btor_release_exp (btor, e[1]);
          if (real_cur->arity >= 3) btor_release_exp (btor, e[2]);
          break;
        case BTOR_APPLY_NODE:
          if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e[1])))
          {
            result = btor_apply_exp_node (btor, e[1], e[0]);
            btor_release_exp (btor, e[1]);
            if (to_prop && BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (result)))
            {
              if (!btor_find_in_ptr_hash_table (to_prop,
                                                BTOR_REAL_ADDR_NODE (result)))
                btor_insert_in_ptr_hash_table (
                    to_prop,
                    btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (result)));
            }
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
        case BTOR_BCOND_NODE:
          /* only condition rebuilt, evaluate and choose branch */
          if (real_cur->beta_mark == 3)
          {
            eval_res = btor_eval_exp (btor, e[0]);
            if (eval_res)
            {
              // TODO: result for real_cur not cached anymore as we
              //       skip the bv_cond

              if (conds
                  && !btor_find_in_ptr_hash_table (conds,
                                                   BTOR_REAL_ADDR_NODE (e[0])))
              {
                btor_insert_in_ptr_hash_table (
                    conds, btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (e[0])));
              }

              tmp                 = 0;
              real_cur->beta_mark = 2;
              if (eval_res[0] == '1')
              {
                if (cond_sel_if) tmp = cond_sel_if;
                next = real_cur->e[1];
              }
              else
              {
                assert (eval_res[0] == '0');
                if (cond_sel_else) tmp = cond_sel_else;
                next = real_cur->e[2];
              }
              if (tmp)
              {
                t0 = btor_new_param_cache_tuple (btor,
                                                 BTOR_REAL_ADDR_NODE (e[0]));
                if (!btor_find_in_ptr_hash_table (tmp, t0))
                  btor_insert_in_ptr_hash_table (tmp, t0)->data.asPtr = e[0];
                else
                  btor_delete_param_cache_tuple (btor, t0);
              }
              assert (next);
              btor_freestr (mm, (char *) eval_res);

              real_cur->beta_mark = 0;
              if (BTOR_IS_INVERTED_NODE (cur)) next = BTOR_INVERT_NODE (next);
              BTOR_PUSH_STACK (mm, stack, next);
              BTOR_PUSH_STACK (mm, stack, real_cur);
              btor_release_exp (btor, e[0]);
            }
            /* rebuild complete bv conditional, push both branches */
            else
            {
              /* build bv cond */
              real_cur->beta_mark = 1;
              BTOR_PUSH_STACK (mm, arg_stack, e[0]);
              BTOR_PUSH_STACK (mm, stack, cur);
              BTOR_PUSH_STACK (mm, stack, cur_parent);
              BTOR_PUSH_STACK (mm, stack, real_cur->e[2]);
              BTOR_PUSH_STACK (mm, stack, real_cur);
              BTOR_PUSH_STACK (mm, stack, real_cur->e[1]);
              BTOR_PUSH_STACK (mm, stack, real_cur);
            }
            continue;
          }
          else
          {
            assert (real_cur->beta_mark = 2);
            result = btor_cond_exp (btor, e[0], e[1], e[2]);
            /* if result is indeed a bv conditional it could not have
             * been evaluated due to not encoded inputs.
             * this is not always the case since rewriting may yield
             * simplified expressions. */
            if (evalerr && BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (result)))
            {
              assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e[0])));
              next = BTOR_REAL_ADDR_NODE (result);

              if (!btor_find_in_ptr_hash_table (mark, next))
                btor_insert_in_ptr_hash_table (mark,
                                               btor_copy_exp (btor, next));
            }
            btor_release_exp (btor, e[0]);
            btor_release_exp (btor, e[1]);
            btor_release_exp (btor, e[2]);
          }
          break;
        default:
          printf ("%s\n", node2string (real_cur));
          result = 0;
          /* not reachable */
          assert (0);
          // TODO: abort
      }

      next = BTOR_REAL_ADDR_NODE (result);
      for (i = 0; mark->count > 0 && i < next->arity; i++)
      {
        if (btor_find_in_ptr_hash_table (mark,
                                         BTOR_REAL_ADDR_NODE (next->e[i])))
        {
          if (!btor_find_in_ptr_hash_table (mark, next))
            btor_insert_in_ptr_hash_table (mark, btor_copy_exp (btor, next));
          break;
        }
      }

      /* cache rebuilt parameterized node with current arguments */
      t0 = btor_new_param_cache_tuple (btor, real_cur);
      assert (!btor_find_in_ptr_hash_table (cache, t0));
      btor_insert_in_ptr_hash_table (cache, t0)->data.asPtr =
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
      assert (real_cur->beta_mark == 2);
      if (BTOR_IS_LAMBDA_NODE (real_cur))
      {
        cur_args = BTOR_TOP_STACK (arg_stack);
        assert (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (cur_args)));
        btor_assign_args (btor, real_cur, cur_args);
        t0 = btor_new_param_cache_tuple (btor, real_cur);
        btor_unassign_params (btor, real_cur);
      }
      else
        t0 = btor_new_param_cache_tuple (btor, real_cur);

      b = btor_find_in_ptr_hash_table (cache, t0);
      btor_delete_param_cache_tuple (btor, t0);
      /* real_cur not yet cached with current param assignment, rebuild
       * expression */
      if (!b)
      {
        real_cur->beta_mark = 0;
        goto BETA_REDUCE_PARTIAL_START;
      }
      assert (b);
      result = btor_copy_exp (btor, (BtorNode *) b->data.asPtr);
      assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (result)));
      goto BETA_REDUCE_PARTIAL_PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  /* release cache and reset beta_mark flags */
  init_hash_table_iterator (&it, cache);
  while (has_next_node_hash_table_iterator (&it))
  {
    btor_release_exp (btor, (BtorNode *) it.bucket->data.asPtr);
    t0       = (BtorParamCacheTuple *) next_node_hash_table_iterator (&it);
    real_cur = t0->exp;
    assert (BTOR_IS_REGULAR_NODE (real_cur));
    real_cur->beta_mark = 0;
    btor_delete_param_cache_tuple (btor, t0);
  }

  /* check if result contains bv conditions that couldn't be evaluated */
  if (evalerr)
  {
    if (btor_find_in_ptr_hash_table (mark, BTOR_REAL_ADDR_NODE (result)))
      *evalerr = 1;
  }

  init_node_hash_table_iterator (&it, mark);
  while (has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, next_node_hash_table_iterator (&it));

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_ptr_hash_table (cache);
  btor_delete_ptr_hash_table (mark);
  btor->options.rewrite_level.val = rwl;

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
  return btor_beta_reduce (btor, exp, BETA_RED_FULL, 0, 0);
}

BtorNode *
btor_beta_reduce_merge (Btor *btor,
                        BtorNode *exp,
                        BtorPtrHashTable *merge_lambdas)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_LAMBDA_MERGE, 0, merge_lambdas);
}

BtorNode *
btor_beta_reduce_bounded (Btor *btor, BtorNode *exp, int bound)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_BOUNDED, bound, 0);
}

BtorNode *
btor_beta_reduce_partial (Btor *btor,
                          BtorNode *exp,
                          int *evalerr,
                          BtorPtrHashTable *to_prop,
                          BtorPtrHashTable *conds)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce_partial_aux (
      btor, exp, 0, 0, evalerr, to_prop, conds);
}

BtorNode *
btor_beta_reduce_partial_collect (Btor *btor,
                                  BtorNode *exp,
                                  BtorPtrHashTable *cond_sel_if,
                                  BtorPtrHashTable *cond_sel_else)
{
  BTORLOG (2, "%s: %s", __FUNCTION__, node2string (exp));
#ifndef NDEBUG
  int evalerr;
  BtorNode *res;
  res = btor_beta_reduce_partial_aux (
      btor, exp, cond_sel_if, cond_sel_else, &evalerr, 0, 0);
  //  assert (!evalerr);
  return res;
#else
  return btor_beta_reduce_partial_aux (
      btor, exp, cond_sel_if, cond_sel_else, 0, 0, 0);
#endif
}

BtorNode *
btor_apply_and_reduce (Btor *btor, int argc, BtorNode **args, BtorNode *lambda)
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

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbeta.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormisc.h"
#include "btorrewrite.h"
#include "btorutil.h"

#define BETA_RED_LAMBDA_CHAINS -2
#define BETA_RED_CUTOFF -1
#define BETA_RED_FULL 0
#define BETA_RED_BOUNDED 1

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
  BTORLOG ("%s: (%s, %s) -> %s",
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
  if (BTOR_EMPTY_STACK (((BtorParamNode *) param)->assigned_exp)) return 0;

  return BTOR_TOP_STACK (((BtorParamNode *) param)->assigned_exp);
}

#if 1
void
btor_assign_params (Btor *btor, int argc, BtorNode **args, BtorNode *fun)
{
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);

  BTORLOG ("%s: %s", __FUNCTION__, node2string (fun));

  int i;
  BtorNode *cur_lambda, *cur_arg;
  BtorParamNode *cur_param;

  cur_lambda = fun;
  for (i = 0; i < argc; i++)
  {
    assert (BTOR_IS_REGULAR_NODE (cur_lambda));
    assert (BTOR_IS_LAMBDA_NODE (cur_lambda));
    assert (BTOR_IS_PARAM_NODE (cur_lambda->e[0]));

    cur_arg   = args[i];
    cur_param = (BtorParamNode *) BTOR_REAL_ADDR_NODE (cur_lambda->e[0]);

    assert (cur_arg);
    assert (BTOR_REAL_ADDR_NODE (cur_arg)->len == cur_param->len);
    BTORLOG (
        "  assign: %s (%s)", node2string (cur_lambda), node2string (cur_arg));
    BTOR_PUSH_STACK (btor->mm, cur_param->assigned_exp, cur_arg);
    cur_lambda = cur_lambda->e[1];
  }
}

void
btor_assign_args (Btor *btor, BtorNode *fun, BtorNode *arg)
{
  assert (btor);
  assert (fun);
  assert (arg);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_REGULAR_NODE (arg));
  assert (BTOR_IS_LAMBDA_NODE (fun));
  assert (BTOR_IS_ARGS_NODE (arg));

  btor_assign_params (btor, arg->arity, arg->e, fun);
}

void
btor_assign_param (Btor *btor, BtorNode *fun, BtorNode *arg)
{
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (arg)));
  btor_assign_params (btor, 1, &arg, fun);
}
#else
void
btor_assign_param (Btor *btor, BtorNode *lambda, BtorNode *arg)
{
  assert (lambda);
  assert (arg);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (BTOR_IS_PARAM_NODE (lambda->e[0]));

  BTORLOG ("%s: %s", __FUNCTION__, node2string (lambda));
  BTORLOG ("  assigned exp: %s", node2string (arg));

  int upper, lower;
  BtorNode *cur_lambda, *cur_arg;
  BtorParamNode *param;

  param = (BtorParamNode *) BTOR_REAL_ADDR_NODE (lambda->e[0]);

  /* apply multiple arguments */
  if (param->len < BTOR_REAL_ADDR_NODE (arg)->len)
  {
    assert (BTOR_REAL_ADDR_NODE (arg)->kind == BTOR_CONCAT_NODE);

    cur_lambda = lambda;
    upper      = arg->len - 1;
    do
    {
      assert (BTOR_IS_NESTED_LAMBDA_NODE (cur_lambda));
      param = (BtorParamNode *) BTOR_REAL_ADDR_NODE (cur_lambda->e[0]);
      lower = upper - param->len + 1;
      assert (lower >= 0);
      assert (upper >= 0);
      cur_arg = btor_rewrite_slice_exp (btor, arg, upper, lower);
      assert (cur_arg->refs > 1);
      btor_release_exp (btor, cur_arg); /* still referenced afterwards */

      assert (param->len == BTOR_REAL_ADDR_NODE (cur_arg)->len);

      BTORLOG (
          "  assign: %s (%s)", node2string (cur_lambda), node2string (cur_arg));
      BTOR_PUSH_STACK (btor->mm, param->assigned_exp, cur_arg);
      cur_lambda = cur_lambda->e[1];
      upper      = lower - 1;
    } while (BTOR_IS_LAMBDA_NODE (cur_lambda));
    assert (lower == 0);
  }
  else
  {
    BTOR_PUSH_STACK (btor->mm, param->assigned_exp, arg);
  }
}
#endif

// TODO: rename to btor_unassign_params
void
btor_unassign_param (Btor *btor, BtorNode *lambda)
{
  assert (lambda);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (BTOR_IS_PARAM_NODE (lambda->e[0]));

  BtorParamNode *param;

  do
  {
    BTORLOG ("%s: %s", __FUNCTION__, node2string (lambda));
    param = (BtorParamNode *) lambda->e[0];

    if (BTOR_EMPTY_STACK (param->assigned_exp)) break;

    (void) BTOR_POP_STACK (param->assigned_exp);
    lambda = BTOR_REAL_ADDR_NODE (lambda->e[1]);
  } while (BTOR_IS_LAMBDA_NODE (lambda));
}

#define BETA_REDUCE_OPEN_NEW_SCOPE(lambda)                                     \
  do                                                                           \
  {                                                                            \
    BTOR_PUSH_STACK (mm, scopes, cur_scope);                                   \
    BTOR_PUSH_STACK (mm, scope_results, cur_scope_results);                    \
    BTOR_PUSH_STACK (mm, scope_lambdas, cur_scope_lambda);                     \
    cur_scope = btor_new_ptr_hash_table (mm,                                   \
                                         (BtorHashPtr) btor_hash_exp_by_id,    \
                                         (BtorCmpPtr) btor_compare_exp_by_id); \
    cur_scope_results =                                                        \
        btor_new_ptr_hash_table (mm,                                           \
                                 (BtorHashPtr) btor_hash_exp_by_id,            \
                                 (BtorCmpPtr) btor_compare_exp_by_id);         \
    cur_scope_lambda = lambda;                                                 \
  } while (0)

#define BETA_REDUCE_CLOSE_SCOPE()                                            \
  do                                                                         \
  {                                                                          \
    assert (cur_scope);                                                      \
    assert (cur_scope_lambda);                                               \
    /* delete current scope */                                               \
    btor_delete_ptr_hash_table (cur_scope);                                  \
    for (b = cur_scope_results->first; b; b = b->next)                       \
      btor_release_exp (btor, (BtorNode *) b->data.asPtr);                   \
    btor_delete_ptr_hash_table (cur_scope_results);                          \
    /* pop previous scope */                                                 \
    cur_scope         = (BtorPtrHashTable *) BTOR_POP_STACK (scopes);        \
    cur_scope_results = (BtorPtrHashTable *) BTOR_POP_STACK (scope_results); \
    cur_scope_lambda  = BTOR_POP_STACK (scope_lambdas);                      \
  } while (0)

#define BETA_REDUCE_PUSH_RESULT_IF_CACHED(lambda, assignment)            \
  do                                                                     \
  {                                                                      \
    cached = cached_beta_result (btor, lambda, assignment);              \
    if (cached)                                                          \
    {                                                                    \
      result               = btor_copy_exp (btor, cached);               \
      result_parameterized = BTOR_REAL_ADDR_NODE (cached)->parameterized \
                                 ? BTOR_REAL_ADDR_NODE (cached)          \
                                 : 0;                                    \
      goto BETA_REDUCE_PUSH_ARG_STACK;                                   \
    }                                                                    \
  } while (0)

/* We distinguish the following options for (un)bounded reduction:
 *
 *   BETA_RED_LAMBDA_CHAINS: merge lambda chains
 *
 *   BETA_RED_CUTOFF: cut off at subsequent lambda and write nodes,
 *		      evaluate conditionals
 *
 *   BETA_RED_FULL:   full reduction,
 *		      do not evaluate conditionals
 *
 *   BETA_RED_BOUNDED (bound): bounded reduction, bound by (bound > 0) number
 *			       of lambdas
 */
static BtorNode *
btor_beta_reduce (
    Btor *btor, BtorNode *exp, int mode, BtorNode **parameterized, int bound)
{
  assert (btor);
  assert (exp);
  assert (mode == BETA_RED_CUTOFF || mode == BETA_RED_FULL
          || mode == BETA_RED_LAMBDA_CHAINS || mode == BETA_RED_BOUNDED);
  assert (bound >= 0);
  assert (bound == 0 || mode == BETA_RED_CUTOFF || mode == BETA_RED_BOUNDED);
  assert (mode != BETA_RED_CUTOFF || bound == 2);

  int i, aux_rewrite_level = 0;
  const char *eval_res;
  double start;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *next, *result, *param, *cached, *args;
  BtorNode *result_parameterized, *cur_scope_lambda, *cur_parent;
  BtorNodePtrStack work_stack, arg_stack, parameterized_stack;
  BtorPtrHashBucket *mbucket, *b;
  BtorPtrHashTable *cache, *cur_scope, *cur_scope_results;
  BtorVoidPtrStack scopes, scope_results;
  BtorNodePtrStack scope_lambdas, e, p;
#ifndef NDEBUG
  BtorNodePtrStack unassign_stack;
#endif

  mm    = btor->mm;
  cache = btor->cache;
  start = btor_time_stamp ();
  btor->stats.beta_reduce_calls++;

  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  /* we have to disable rewriting in case we beta reduce during read propagation
   * as otherwise we might lose lazily synthesized and encoded nodes */
  if (mode == BETA_RED_CUTOFF)
  {
    aux_rewrite_level   = btor->rewrite_level;
    btor->rewrite_level = 0;
  }

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (parameterized_stack);
  BTOR_INIT_STACK (scopes);
  BTOR_INIT_STACK (scope_results);
  BTOR_INIT_STACK (scope_lambdas);
  BTOR_INIT_STACK (e);
  BTOR_INIT_STACK (p);
#ifndef NDEBUG
  BTOR_INIT_STACK (unassign_stack);
#endif

  BTOR_PUSH_STACK (mm, work_stack, exp);
  BTOR_PUSH_STACK (mm, work_stack, 0);

  cur_scope = btor_new_ptr_hash_table (mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  cur_scope_results =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  cur_scope_lambda = 0;

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur_parent = BTOR_POP_STACK (work_stack);
    cur        = BTOR_POP_STACK (work_stack);
    // TODO: directly push simplified exp onto stack at the beginning
    /* we do not want the simplification of top level read contraints */
    if (BTOR_REAL_ADDR_NODE (cur)->constraint
        && BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (cur)))
      //      if (BTOR_REAL_ADDR_NODE (cur)->constraint
      //	  && BTOR_IS_READ_NODE (BTOR_REAL_ADDR_NODE (cur)))
      cur = btor_pointer_chase_simplified_exp (btor, cur);
    else
      cur = btor_simplify_exp (btor, cur);

    real_cur = BTOR_REAL_ADDR_NODE (cur);
    mbucket  = btor_find_in_ptr_hash_table (cur_scope, real_cur);

    if (!mbucket)
    {
      if (BTOR_IS_LAMBDA_NODE (real_cur)
          /* only open new scope at first lambda of nested lambdas */
          && (!BTOR_IS_NESTED_LAMBDA_NODE (real_cur)
              || ((BtorLambdaNode *) real_cur)->nested == real_cur))
        BETA_REDUCE_OPEN_NEW_SCOPE (real_cur);

      /* initialize mark in current scope */
      mbucket             = btor_insert_in_ptr_hash_table (cur_scope, real_cur);
      mbucket->data.asInt = 0;
    }
    //      printf ("visit: %s (%d)\n", node2string (real_cur),
    //      mbucket->data.asInt);

    if (mbucket->data.asInt == 0)
    {
      assert (!real_cur->beta_mark || BTOR_IS_LAMBDA_NODE (real_cur));
      mbucket->data.asInt = 1;

      BTOR_RESET_STACK (e);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, e, btor_simplify_exp (btor, real_cur->e[i]));

      /* bounded reduction (BETA_RED_BOUNDED, BETA_RED_CUTOFF) */
      if (bound > 0 && BTOR_IS_LAMBDA_NODE (real_cur)
          && BTOR_COUNT_STACK (scopes) >= bound)
      {
        assert (real_cur == cur_scope_lambda);
        goto BETA_REDUCE_PREPARE_PUSH_ARG_STACK;
      }

      if (mode == BETA_RED_LAMBDA_CHAINS
          /* skip all arrays that are not part of the lambda chain */
          && ((BTOR_IS_ARRAY_NODE (real_cur) && !BTOR_IS_LAMBDA_NODE (real_cur))
              /* skip all nodes that are not parameterized as we can't merge
               * lambdas that might be below */
              || (!BTOR_IS_ARRAY_NODE (real_cur) && !real_cur->parameterized)))
      {
        goto BETA_REDUCE_PREPARE_PUSH_ARG_STACK;
      }
      else if (mode == BETA_RED_CUTOFF
               /* do not skip expression to be beta reduced */
               && real_cur != BTOR_REAL_ADDR_NODE (exp)
               /* cut off at nodes that are already encoded */
               && (real_cur->tseitin
                   /* cut off at non-lambda array nodes
                    * (lambda nodes are cut off via bound) */
                   || (BTOR_IS_ARRAY_NODE (real_cur)
                       && !BTOR_IS_LAMBDA_NODE (real_cur))))
      {
        goto BETA_REDUCE_PREPARE_PUSH_ARG_STACK;
      }

      /* do not beta-reduce nodes that will not change anyway */
      if ((!real_cur->lambda_below && !real_cur->parameterized))
      // FIXME: assignment is not yet assigned, we have to check if
      //	      something is on the arg stack
      //	      || (BTOR_IS_LAMBDA_NODE (real_cur)
      //		  && !btor_param_cur_assignment (e[0])
      //		  && BTOR_REAL_ADDR_NODE (e[1])->parameterized))
      {
      BETA_REDUCE_PREPARE_PUSH_ARG_STACK:
        result               = btor_copy_exp (btor, real_cur);
        result_parameterized = real_cur->parameterized ? real_cur : 0;
        goto BETA_REDUCE_PUSH_ARG_STACK;
      }

      next = 0;
      if (BTOR_IS_PARAM_NODE (real_cur))
      {
        /* we allow unassigned params (next == 0) */
        if ((next = btor_param_cur_assignment (real_cur)))
        {
          result               = btor_copy_exp (btor, next);
          result_parameterized = real_cur;
          goto BETA_REDUCE_PUSH_ARG_STACK;
        }
        else
          next = real_cur;
      }
      /* evaluate conditionals if condition is encoded or parameterized */
      else if (mode == BETA_RED_CUTOFF
               && BTOR_IS_ARRAY_OR_BV_COND_NODE (real_cur))
      {
        assert (BTOR_REAL_ADDR_NODE (e.start[0])->tseitin
                || BTOR_REAL_ADDR_NODE (e.start[0])->parameterized
                || BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e.start[0])));
        eval_res = btor_eval_exp (btor, e.start[0]);
        next     = eval_res[0] == '1' ? e.start[1] : e.start[2];
        assert (next);
        btor_freestr (mm, (char *) eval_res);
        mbucket->data.asInt = 0;
      }

      if (next)
      {
        if (BTOR_IS_INVERTED_NODE (cur)) next = BTOR_INVERT_NODE (next);

        if (mode == BETA_RED_FULL || mode == BETA_RED_BOUNDED)
          BTOR_REAL_ADDR_NODE (next)->parent = real_cur;

        BTOR_PUSH_STACK (mm, work_stack, next);
        BTOR_PUSH_STACK (mm, work_stack, real_cur);
      }
      else
      {
        /* assign params of lambda expression */
        if (BTOR_IS_LAMBDA_NODE (real_cur)
            /* if there is no argument on the stack, we have no
             * assignment for the parameter */
            && !BTOR_EMPTY_STACK (arg_stack)
            /* if it is nested, its parameter is already assigned */
            && !btor_param_cur_assignment (e.start[0])
            /* we have an assignment if there is a lambda application */
            && BTOR_IS_APPLY_NODE (cur_parent))
        {
          assert (!btor_find_in_ptr_hash_table (
              cur_scope, BTOR_REAL_ADDR_NODE (e.start[0])));

          args = BTOR_TOP_STACK (arg_stack);
          assert (BTOR_IS_ARGS_NODE (args));

          if (cache) BETA_REDUCE_PUSH_RESULT_IF_CACHED (real_cur, args);

          btor_assign_args (btor, real_cur, args);
#ifndef NDEBUG
          BTOR_PUSH_STACK (mm, unassign_stack, real_cur);
#endif
        }

        BTOR_PUSH_STACK (mm, work_stack, cur);
        BTOR_PUSH_STACK (mm, work_stack, cur_parent);

        /* NOTE: all arguments of an apply have to be visited first
         *       in order to get a correct assignment for the parameter
         *       of a lambda. */
        for (i = 0; i < real_cur->arity; i++)
        {
          BTOR_PUSH_STACK (mm, work_stack, e.start[i]);
          BTOR_PUSH_STACK (mm, work_stack, real_cur);
        }
      }
    }
    else if (mbucket->data.asInt == 1)
    {
      assert (mbucket);
      result_parameterized = (real_cur->parameterized) ? real_cur : 0;

      /* copy "leaves" or expression that were cut off */
      if (BTOR_IS_BV_CONST_NODE (real_cur) || BTOR_IS_BV_VAR_NODE (real_cur)
          || BTOR_IS_ARRAY_VAR_NODE (real_cur) || BTOR_IS_PARAM_NODE (real_cur)
          || (mode == BETA_RED_CUTOFF && real_cur != BTOR_REAL_ADDR_NODE (exp)
              && (real_cur->tseitin
                  || (BTOR_IS_ARRAY_NODE (real_cur)
                      && !BTOR_IS_LAMBDA_NODE (real_cur))))
          /* we reached given bound */
          || (bound > 0 && BTOR_IS_LAMBDA_NODE (real_cur)
              && BTOR_COUNT_STACK (scopes) >= bound))
      {
        result = btor_copy_exp (btor, real_cur);
      }
      else
      {
        assert (BTOR_IS_UNARY_NODE (real_cur) || BTOR_IS_BINARY_NODE (real_cur)
                || BTOR_IS_TERNARY_NODE (real_cur)
                // TODO: make apply binary node
                || BTOR_IS_APPLY_NODE (real_cur)
                || BTOR_IS_ARGS_NODE (real_cur));
        assert (mode != BETA_RED_CUTOFF
                || !BTOR_IS_ARRAY_OR_BV_COND_NODE (real_cur));
        assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);

        BTOR_RESET_STACK (e);
        BTOR_RESET_STACK (p);
        for (i = 0; i < real_cur->arity; i++)
        {
          BTOR_PUSH_STACK (mm, e, BTOR_POP_STACK (arg_stack));
          BTOR_PUSH_STACK (mm, p, BTOR_POP_STACK (parameterized_stack));
        }
        switch (real_cur->kind)
        {
          case BTOR_SLICE_NODE:
            result = btor_slice_exp (
                btor, e.start[0], real_cur->upper, real_cur->lower);
            break;
          case BTOR_AND_NODE:
            result = btor_and_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_BEQ_NODE:
          case BTOR_AEQ_NODE:
            result = btor_eq_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_ADD_NODE:
            result = btor_add_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_MUL_NODE:
            result = btor_mul_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_ULT_NODE:
            result = btor_ult_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_SLL_NODE:
            result = btor_sll_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_SRL_NODE:
            result = btor_srl_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_UDIV_NODE:
            result = btor_udiv_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_UREM_NODE:
            result = btor_urem_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_CONCAT_NODE:
            result = btor_concat_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_READ_NODE:
            result = btor_read_exp (btor, e.start[0], e.start[1]);
            break;
          case BTOR_ARGS_NODE:
            result = btor_args_exp (btor, real_cur->arity, e.start);
            break;

          case BTOR_APPLY_NODE:
            /* array exp has been beta-reduced to read value */
            if (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e.start[0])))
            {
              assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e.start[0])));
              result = btor_copy_exp (btor, e.start[0]);
            }
            else
            {
              assert (BTOR_IS_FUN_NODE (e.start[0]));
              assert (BTOR_IS_ARGS_NODE (e.start[1]));
              /* NOTE: do not use btor_apply_exp here since
               * beta reduction is used in btor_rewrite_apply_exp. */
              result = btor_apply_exp_node (btor, e.start[0], e.start[1]);
            }

            if (cache && BTOR_IS_LAMBDA_NODE (real_cur->e[0])
                && mode == BETA_RED_FULL)
            {
              assert (!BTOR_REAL_ADDR_NODE (real_cur->e[0])->simplified
                      || cur == exp);
              assert (!BTOR_REAL_ADDR_NODE (real_cur->e[1])->simplified
                      || cur == exp);
              cache_beta_result (btor,
                                 btor_simplify_exp (btor, real_cur->e[0]),
                                 btor_simplify_exp (btor, e.start[1]),
                                 result);
            }
            break;

          case BTOR_LAMBDA_NODE:
            /* lambda expression not reduced, nothing changed
             * NOTE: lambda may be constant and thus, we return e[1] */
            if (real_cur->e[0] == e.start[0] && real_cur->e[1] == e.start[1]
                && BTOR_REAL_ADDR_NODE (e.start[1])->parameterized)
            {
              assert (!real_cur->beta_mark);
              result = btor_copy_exp (btor, real_cur);
            }
            /* lambda reduced to some term with e[0] due to rewriting */
            else if (real_cur->beta_mark == 1
                     || (real_cur->e[0] == e.start[0]
                         && BTOR_REAL_ADDR_NODE (e.start[1])->parameterized))
            {
              if (real_cur->beta_mark == 0)
              {
                assert (BTOR_IS_REGULAR_NODE (e.start[0]));
                param = btor_param_exp (btor, e.start[0]->len, "");

                /* mark lambda as to-be-rebuilt in 2nd pass */
                real_cur->beta_mark = 1;
                btor_assign_param (btor, real_cur, param);

#ifndef NDEBUG
                BTOR_PUSH_STACK (mm, unassign_stack, real_cur);
#endif
                /* open new scope in order to discard all
                 * built expressions under 'real_cur' */
                BETA_REDUCE_OPEN_NEW_SCOPE (real_cur);

                /* add lambda to cur_scope (otherwise a new scope
                 * will be opened) */
                btor_insert_in_ptr_hash_table (cur_scope, real_cur)
                    ->data.asInt = 0;
                BTOR_PUSH_STACK (mm, work_stack, real_cur);
                BTOR_PUSH_STACK (mm, work_stack, cur_parent);

                for (i = 0; i < real_cur->arity; i++)
                  btor_release_exp (btor, e.start[i]);

                /* rebuild lambda */
                continue;
              }
              /* build new lambda with new param 2nd pass */
              else
              {
                assert (real_cur->beta_mark == 1);
                assert (BTOR_IS_REGULAR_NODE (e.start[0]));
                assert (BTOR_IS_PARAM_NODE (e.start[0]));
                result = btor_lambda_exp (btor, e.start[0], e.start[1]);
                /* decrement ref counter of param e[0] created in
                 * 1st pass */
                btor_release_exp (btor, e.start[0]);
                real_cur->beta_mark = 0;

                assert (btor_param_cur_assignment (real_cur->e[0]));
                btor_unassign_param (btor, real_cur);

#ifndef NDEBUG
                (void) BTOR_POP_STACK (unassign_stack);
#endif

                /* close scope that was opened in first pass */
                BETA_REDUCE_CLOSE_SCOPE ();
                /* restore mark of previous scope */
                mbucket = btor_find_in_ptr_hash_table (cur_scope, real_cur);
                assert (mbucket);
              }
            }
            /* lambda reduced to some term without e[0] */
            else
            {
              assert (!real_cur->beta_mark);
              /* if a lambda is reduced to a constant term and
               * its parent expects an array, we have to create a
               * constant lambda expression instead of a constant
               * term. this can only occur with bounded or full
               * reduction */
              if ((mode == BETA_RED_FULL || mode == BETA_RED_BOUNDED)
                  && (BTOR_IS_WRITE_NODE (cur_parent)
                      || BTOR_IS_ARRAY_COND_NODE (cur_parent)))
              {
                assert (!BTOR_REAL_ADDR_NODE (e.start[1])->parameterized);
                param = btor_param_exp (
                    btor, BTOR_REAL_ADDR_NODE (e.start[0])->len, "");
                result = btor_lambda_exp (btor, param, e.start[1]);
                btor_release_exp (btor, param);
              }
              else
              {
                result               = btor_copy_exp (btor, e.start[1]);
                result_parameterized = p.start[1];
              }
            }
            break;
          case BTOR_WRITE_NODE:
            result = btor_write_exp (btor, e.start[0], e.start[1], e.start[2]);
            break;
          case BTOR_BCOND_NODE:
          case BTOR_ACOND_NODE:
            result = btor_cond_exp (btor, e.start[0], e.start[1], e.start[2]);
            break;
          default:
            /* not reachable */
            assert (0);
        }

        for (i = 0; i < real_cur->arity; i++)
          btor_release_exp (btor, e.start[i]);
      }

    BETA_REDUCE_PUSH_ARG_STACK:
      assert (mbucket->data.asInt != 2);
      mbucket->data.asInt = 2;

      /* only cache parameterized nodes */
      if (real_cur->parameterized)
      {
        /* store result in current scope results */
        assert (!btor_find_in_ptr_hash_table (cur_scope_results, real_cur));
        btor_insert_in_ptr_hash_table (cur_scope_results, real_cur)
            ->data.asPtr = btor_copy_exp (btor, result);
      }

      /* close scope */
      if (real_cur == cur_scope_lambda)
      {
        BETA_REDUCE_CLOSE_SCOPE ();
#ifndef NDEBUG
        if (!BTOR_EMPTY_STACK (unassign_stack)
            && BTOR_TOP_STACK (unassign_stack) == real_cur)
          (void) BTOR_POP_STACK (unassign_stack);
#endif
        if (btor_param_cur_assignment (real_cur->e[0]))
          btor_unassign_param (btor, real_cur);
      }

    BETA_REDUCE_PUSH_ARG_STACK_WITHOUT_CLOSE_SCOPE:
      if (BTOR_IS_INVERTED_NODE (cur)) result = BTOR_INVERT_NODE (result);

      //	  printf ("  result: %s\n", node2string (result));
      BTOR_PUSH_STACK (mm, arg_stack, result);
      BTOR_PUSH_STACK (mm, parameterized_stack, result_parameterized);
    }
    else
    {
      assert (mbucket->data.asInt == 2);
      assert (cur_scope_results);

      /* only parameterized nodes are cached */
      if (real_cur->parameterized)
      {
        mbucket = btor_find_in_ptr_hash_table (cur_scope_results, real_cur);
        assert (mbucket);
        result = btor_copy_exp (btor, (BtorNode *) mbucket->data.asPtr);
      }
      else
        result = btor_copy_exp (btor, real_cur);
      assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (result)));
      goto BETA_REDUCE_PUSH_ARG_STACK_WITHOUT_CLOSE_SCOPE;
    }
  }
  assert (cur_scope);
  assert (cur_scope_results);
  assert (!cur_scope_lambda);
  assert (BTOR_EMPTY_STACK (scopes));
  assert (BTOR_EMPTY_STACK (scope_results));
  assert (BTOR_EMPTY_STACK (scope_lambdas));
  assert (BTOR_EMPTY_STACK (unassign_stack));
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  assert (BTOR_COUNT_STACK (parameterized_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  if (parameterized) *parameterized = BTOR_POP_STACK (parameterized_stack);

  /* cleanup */
  btor_delete_ptr_hash_table (cur_scope);
  for (b = cur_scope_results->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
  btor_delete_ptr_hash_table (cur_scope_results);
  BTOR_RELEASE_STACK (mm, scopes);
  BTOR_RELEASE_STACK (mm, scope_results);
  BTOR_RELEASE_STACK (mm, scope_lambdas);
  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  BTOR_RELEASE_STACK (mm, parameterized_stack);
  BTOR_RELEASE_STACK (mm, e);
  BTOR_RELEASE_STACK (mm, p);
#ifndef NDEBUG
  BTOR_RELEASE_STACK (mm, unassign_stack);
#endif

  if (aux_rewrite_level)
  {
    assert (mode == BETA_RED_CUTOFF);
    assert (!btor->rewrite_level);
    btor->rewrite_level = aux_rewrite_level;
  }

  BTORLOG ("beta_reduce: result %s", node2string (result));
  btor->time.beta += btor_time_stamp () - start;

  return result;
}

BtorNode *
btor_beta_reduce_full (Btor *btor, BtorNode *exp)
{
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_FULL, 0, 0);
}

BtorNode *
btor_beta_reduce_chains (Btor *btor, BtorNode *exp)
{
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_LAMBDA_CHAINS, 0, 0);
}

BtorNode *
btor_beta_reduce_cutoff (Btor *btor, BtorNode *exp, BtorNode **parameterized)
{
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_CUTOFF, parameterized, 2);
}

BtorNode *
btor_beta_reduce_bounded (Btor *btor, BtorNode *exp, int bound)
{
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));
  return btor_beta_reduce (btor, exp, BETA_RED_BOUNDED, 0, bound);
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
  // TODO: use btor_assign_params
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
    btor_unassign_param (btor, cur);
  }

  BTOR_RELEASE_STACK (mm, unassign);

  return result;
}

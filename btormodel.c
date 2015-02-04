/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormodel.h"
#include "btorbeta.h"
#include "btorexit.h"
#include "btoriter.h"
#include "btormem.h"
#include "btorutil.h"

#define BTOR_ABORT_MODEL(cond, msg)                   \
  do                                                  \
  {                                                   \
    if (cond)                                         \
    {                                                 \
      printf ("[btormodel] %s: %s\n", __func__, msg); \
      fflush (stdout);                                \
      exit (BTOR_ERR_EXIT);                           \
    }                                                 \
  } while (0)

static void
delete_bv_model (Btor *btor)
{
  assert (btor);

  BitVector *bv;
  BtorNode *cur;
  BtorHashTableIterator it;

  if (!btor->bv_model) return;

  init_node_hash_table_iterator (&it, btor->bv_model);
  while (has_next_node_hash_table_iterator (&it))
  {
    bv  = (BitVector *) it.bucket->data.asPtr;
    cur = next_node_hash_table_iterator (&it);
    btor_free_bv (btor, bv);
    btor_release_exp (btor, cur);
  }

  btor_delete_ptr_hash_table (btor->bv_model);
  btor->bv_model = 0;
}

static void
init_bv_model (Btor *btor)
{
  assert (btor);

  if (btor->bv_model) delete_bv_model (btor);

  btor->bv_model =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
add_to_bv_model (Btor *btor, BtorNode *exp, BitVector *assignment)
{
  assert (btor);
  assert (exp);
  assert (assignment);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashBucket *b;

  if (btor_find_in_ptr_hash_table (btor->bv_model, exp)) return;

  b = btor_insert_in_ptr_hash_table (btor->bv_model, btor_copy_exp (btor, exp));
  b->data.asPtr = btor_copy_bv (btor, assignment);
}

static void
delete_fun_model (Btor *btor)
{
  assert (btor);

  BitVectorTuple *tup;
  BitVector *value;
  BtorNode *cur;
  BtorHashTableIterator it1, it2;
  BtorPtrHashTable *t;

  if (!btor->fun_model) return;

  init_node_hash_table_iterator (&it1, btor->fun_model);
  while (has_next_node_hash_table_iterator (&it1))
  {
    t   = (BtorPtrHashTable *) it1.bucket->data.asPtr;
    cur = next_node_hash_table_iterator (&it1);
    init_hash_table_iterator (&it2, t);
    while (has_next_hash_table_iterator (&it2))
    {
      value = (BitVector *) it2.bucket->data.asPtr;
      tup   = (BitVectorTuple *) next_hash_table_iterator (&it2);
      btor_free_bv_tuple (btor, tup);
      btor_free_bv (btor, value);
    }
    btor_release_exp (btor, cur);
    btor_delete_ptr_hash_table (t);
  }

  btor_delete_ptr_hash_table (btor->fun_model);
  btor->fun_model = 0;
}

static void
init_fun_model (Btor *btor)
{
  assert (btor);

  if (btor->fun_model) delete_fun_model (btor);

  btor->fun_model =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
add_to_fun_model (Btor *btor,
                  BtorNode *exp,
                  BitVectorTuple *t,
                  BitVector *value)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (t);
  assert (value);

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->fun_model, exp);

  if (b)
    model = (BtorPtrHashTable *) b->data.asPtr;
  else
  {
    model = btor_new_ptr_hash_table (btor->mm,
                                     (BtorHashPtr) btor_hash_bv_tuple,
                                     (BtorCmpPtr) btor_compare_bv_tuple);
    btor_insert_in_ptr_hash_table (btor->fun_model, btor_copy_exp (btor, exp))
        ->data.asPtr = model;
  }
  assert (!btor_find_in_ptr_hash_table (model, t));

  b = btor_insert_in_ptr_hash_table (model, btor_copy_bv_tuple (btor, t));
  b->data.asPtr = btor_copy_bv (btor, value);
}

static BitVector *
get_value_from_fun_model (Btor *btor, BtorNode *exp, BitVectorTuple *t)
{
  assert (btor);
  assert (exp);
  assert (t);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_FUN_NODE (exp));

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->fun_model, exp);

  if (!b) return 0;

  model = (BtorPtrHashTable *) b->data.asPtr;
  b     = btor_find_in_ptr_hash_table (model, t);

  if (!b) return 0;

  return btor_copy_bv (btor, (BitVector *) b->data.asPtr);
}

static BitVector *
recursively_compute_assignment (Btor *btor,
                                BtorNode *exp,
                                BtorPtrHashTable *assignments)
{
  assert (btor);
  assert (exp);

  int i, num_args;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack, cleanup, reset;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next, *cur_parent;
  BtorPtrHashData d;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *assigned, *reset_st;
  BitVector *result = 0, *inv_result, **e;
  BitVectorTuple *t;

  mm = btor->mm;

  assigned = btor_new_ptr_hash_table (mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);

  /* 'reset_st' remembers the stack position of 'reset' in case a lambda is
   * assigned. when the resp. lambda is unassigned, the 'eval_mark' flag of all
   * parameterized nodes up to the saved position of stack 'reset' will be
   * reset to 0. */
  reset_st = btor_new_ptr_hash_table (mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (cleanup);
  BTOR_INIT_STACK (reset);

  BTOR_PUSH_STACK (mm, work_stack, exp);
  BTOR_PUSH_STACK (mm, work_stack, 0);
  assert (!BTOR_REAL_ADDR_NODE (exp)->eval_mark);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur_parent = BTOR_POP_STACK (work_stack);
    cur        = BTOR_POP_STACK (work_stack);
    real_cur   = BTOR_REAL_ADDR_NODE (cur);
    assert (!real_cur->simplified);

    if (btor_find_in_ptr_hash_table (assignments, real_cur)) goto PUSH_CACHED;

    /* check if we already have an assignment for this function application */
    if (BTOR_IS_LAMBDA_NODE (real_cur) && cur_parent
        && BTOR_IS_APPLY_NODE (cur_parent)
        /* if real_cur was assigned by cur_parent, we are not allowed to use
         * a cached result, but instead rebuild cur_parent */
        && (!(b = btor_find_in_ptr_hash_table (assigned, real_cur))
            || b->data.asPtr != cur_parent))
    {
      num_args = ((BtorArgsNode *) cur_parent->e[1])->num_args;
      e        = (BitVector **) arg_stack.top - num_args;

      t = btor_new_bv_tuple (btor, num_args);
      for (i = 0; i < num_args; i++)
        btor_add_to_bv_tuple (btor, t, e[i], num_args - 1 - i);

      /* check if there is already a value for given arguments */
      result = get_value_from_fun_model (btor, cur_parent->e[0], t);
      btor_free_bv_tuple (btor, t);

      if (result) goto PUSH_RESULT;
    }

    if (real_cur->eval_mark == 0)
    {
      /* add assignment of bv var to model (creates new assignment, if
       * it doesn't have one) */
      if (BTOR_IS_BV_VAR_NODE (real_cur))
      {
        result = btor_assignment_bv (btor, real_cur, 1);
        add_to_bv_model (btor, real_cur, result);
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_char_to_bv (btor, real_cur->bits);
        goto CACHE_AND_PUSH_RESULT;
      }
      /* substitute param with its assignment */
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        next = btor_param_cur_assignment (real_cur);
        assert (next);
        next = BTOR_COND_INVERT_NODE (cur, next);
        BTOR_PUSH_STACK (mm, work_stack, next);
        BTOR_PUSH_STACK (mm, work_stack, cur_parent);
        continue;
      }
      else if (BTOR_IS_LAMBDA_NODE (real_cur) && cur_parent
               && BTOR_IS_APPLY_NODE (cur_parent))
      {
        btor_assign_args (btor, real_cur, cur_parent->e[1]);
        assert (!btor_find_in_ptr_hash_table (assigned, real_cur));
        btor_insert_in_ptr_hash_table (assigned, real_cur)->data.asPtr =
            cur_parent;
        /* save 'reset' stack position */
        btor_insert_in_ptr_hash_table (reset_st, real_cur)->data.asInt =
            BTOR_COUNT_STACK (reset);
      }

      BTOR_PUSH_STACK (mm, work_stack, cur);
      BTOR_PUSH_STACK (mm, work_stack, cur_parent);
      real_cur->eval_mark = 1;
      BTOR_PUSH_STACK (mm, cleanup, real_cur);

      for (i = 0; i < real_cur->arity; i++)
      {
        BTOR_PUSH_STACK (mm, work_stack, real_cur->e[i]);
        BTOR_PUSH_STACK (mm, work_stack, real_cur);
      }
    }
    else if (real_cur->eval_mark == 1)
    {
      assert (!BTOR_IS_PARAM_NODE (real_cur));
      assert (real_cur->arity <= 3);
      assert (real_cur->arity <= BTOR_COUNT_STACK (arg_stack));

      /* leave arguments on stack, we need them later for apply */
      if (BTOR_IS_ARGS_NODE (real_cur))
      {
        real_cur->eval_mark = 0;
        continue;
      }

      num_args            = 0;
      real_cur->eval_mark = 2;

      if (BTOR_IS_APPLY_NODE (real_cur))
      {
        num_args = ((BtorArgsNode *) real_cur->e[1])->num_args;
        arg_stack.top -= 1;        /* value of apply */
        arg_stack.top -= num_args; /* arguments of apply */
      }
      else
        arg_stack.top -= real_cur->arity;

      e = (BitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_bv (btor, e[0], real_cur->upper, real_cur->lower);
          btor_free_bv (btor, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_BEQ_NODE:
          result = btor_eq_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (btor, e[1], e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          break;
        case BTOR_BCOND_NODE:
          if (btor_is_true_bv (e[2]))
            result = btor_copy_bv (btor, e[1]);
          else
            result = btor_copy_bv (btor, e[0]);
          btor_free_bv (btor, e[0]);
          btor_free_bv (btor, e[1]);
          btor_free_bv (btor, e[2]);
          break;
        case BTOR_APPLY_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          assert (num_args);
          t = btor_new_bv_tuple (btor, num_args);
          for (i = 0; i < num_args; i++)
          {
            btor_add_to_bv_tuple (btor, t, e[i], num_args - 1 - i);
            btor_free_bv (btor, e[i]);
          }

          /* check if there is already a value for given arguments */
          result = get_value_from_fun_model (btor, real_cur->e[0], t);
          if (!result)
          {
            /* value of apply is at last index of e */
            result = e[num_args];
            add_to_fun_model (btor, real_cur->e[0], t, result);
          }
          else
            btor_free_bv (btor, e[num_args]);

          btor_free_bv_tuple (btor, t);
          goto PUSH_RESULT;
        case BTOR_LAMBDA_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          result              = e[0];
          btor_free_bv (btor, e[1]);
          goto PUSH_RESULT_AND_UNASSIGN;
        case BTOR_UF_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          result              = btor_assignment_bv (btor, cur_parent, 1);
          goto PUSH_RESULT;
        default:
          /* should be unreachable */
          BTOR_ABORT_MODEL (1, "invalid node type");
      }
    CACHE_AND_PUSH_RESULT:
      /* remember parameterized nodes for resetting 'eval_mark' later */
      if (real_cur->parameterized) BTOR_PUSH_STACK (mm, reset, real_cur);

      assert (!btor_find_in_ptr_hash_table (assignments, real_cur));
      btor_insert_in_ptr_hash_table (assignments, real_cur)->data.asPtr =
          btor_copy_bv (btor, result);

    PUSH_RESULT_AND_UNASSIGN:
      if (BTOR_IS_LAMBDA_NODE (real_cur) && cur_parent
          && BTOR_IS_APPLY_NODE (cur_parent))
      {
        assert (btor_find_in_ptr_hash_table (assigned, real_cur));
        btor_unassign_params (btor, real_cur);
        btor_remove_from_ptr_hash_table (assigned, real_cur, 0, 0);

        /* reset 'eval_mark' of all parameterized nodes instantiated by
         * 'real_cur' */
        btor_remove_from_ptr_hash_table (reset_st, real_cur, 0, &d);
        while (BTOR_COUNT_STACK (reset) > d.asInt)
        {
          next = BTOR_POP_STACK (reset);
          assert (BTOR_IS_REGULAR_NODE (next));
          assert (next->parameterized);
          next->eval_mark = 0;
        }
      }
    PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (btor, result);
        btor_free_bv (btor, result);
        result = inv_result;
      }
      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (real_cur->eval_mark == 2);
    PUSH_CACHED:
      b = btor_find_in_ptr_hash_table (assignments, real_cur);
      assert (b);
      result = btor_copy_bv (btor, (BitVector *) b->data.asPtr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  for (i = 0; i < BTOR_COUNT_STACK (cleanup); i++)
  {
    real_cur            = BTOR_PEEK_STACK (cleanup, i);
    real_cur->eval_mark = 0;
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  BTOR_RELEASE_STACK (mm, cleanup);
  BTOR_RELEASE_STACK (mm, reset);
  btor_delete_ptr_hash_table (assigned);
  btor_delete_ptr_hash_table (reset_st);

  return result;
}

static void
find_candidates_for_param (Btor *btor,
                           BtorNode *param,
                           BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (param);
  assert (candidates);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  int pos;
  BtorNode *parent;
  BtorMemMgr *mm;
  BtorNodeIterator it;

  mm = btor->mm;

  init_full_parent_iterator (&it, param);
  while (has_next_parent_full_parent_iterator (&it))
  {
    pos    = BTOR_GET_TAG_NODE (it.cur);
    parent = next_parent_full_parent_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (parent));

    switch (parent->kind)
    {
      case BTOR_BEQ_NODE:
        pos = pos == 0 ? 1 : 0;
        BTOR_PUSH_STACK (mm, *candidates, parent->e[pos]);
        BTOR_PUSH_STACK (mm, *candidates, BTOR_INVERT_NODE (parent->e[pos]));
        break;
    }
  }
}

// TODO: works for arrays only
static void
compute_lambda_model (Btor *btor, BtorNode *exp, BtorPtrHashTable *assignments)
{
  assert (btor);
  assert (exp);
  assert (assignments);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_LAMBDA_NODE (exp));

  int i;
  BitVector *value, *index;
  BtorNode *c, *r, *real_c, *real_r, *parent;
  BtorNodePtrStack candidates;
  BtorNodeIterator it;
  BitVectorTuple *t;

  /* if we already have a model for 'exp', we don't need to compute one */
  if (exp->rho) return;

  /* if lambda is reachable through a reachable apply, we do not need to
   * construct a model right now since it will be done via those applies. */
  init_apply_parent_iterator (&it, exp);
  while (has_next_parent_apply_parent_iterator (&it))
  {
    parent = next_parent_apply_parent_iterator (&it);
    if (parent->reachable) return;
  }

  /* right now, we only support array models */
  if (((BtorLambdaNode *) exp)->num_params > 1) return;

  BTOR_INIT_STACK (candidates);

  find_candidates_for_param (btor, exp->e[0], &candidates);
  for (i = 0; i < BTOR_COUNT_STACK (candidates); i++)
  {
    // TODO: can we do this with recursively_compute_assignment?
    c      = BTOR_PEEK_STACK (candidates, i);
    real_c = BTOR_REAL_ADDR_NODE (c);

    btor_assign_param (btor, exp, c);
    r      = btor_beta_reduce_bounded (btor, exp, 2);
    real_r = BTOR_REAL_ADDR_NODE (r);

    // TODO: continue from here on, check which conditions are needed here
    if ((BTOR_IS_SYNTH_NODE (real_c) || BTOR_IS_BV_CONST_NODE (real_c)
         || btor_find_in_ptr_hash_table (assignments, real_c))
        && (BTOR_IS_SYNTH_NODE (real_r) || BTOR_IS_BV_CONST_NODE (real_r)
            || btor_find_in_ptr_hash_table (assignments, real_r)))
    {
      // TODO: multiple args
      t     = btor_new_bv_tuple (btor, 1);
      index = recursively_compute_assignment (btor, c, assignments);
      btor_add_to_bv_tuple (btor, t, index, 0);
      value = recursively_compute_assignment (btor, r, assignments);
      add_to_fun_model (btor, exp, t, value);
      btor_free_bv (btor, index);
      btor_free_bv (btor, value);
      btor_free_bv_tuple (btor, t);
    }

    btor_release_exp (btor, r);
    btor_unassign_params (btor, exp);
  }
  BTOR_RELEASE_STACK (btor->mm, candidates);
}

static void
extract_models_from_functions_with_model (Btor *btor)
{
  assert (btor);

  int i, pos;
  BtorNode *cur, *arg, *value, *args;
  BitVector *bv_arg, *bv_value;
  BitVectorTuple *t;
  BtorHashTableIterator it;
  BtorArgsIterator ait;

  for (i = 0; i < BTOR_COUNT_STACK (btor->functions_with_model); i++)
  {
    cur = BTOR_PEEK_STACK (btor->functions_with_model, i);
    assert (cur->rho);

    init_node_hash_table_iterator (&it, cur->rho);
    while (has_next_node_hash_table_iterator (&it))
    {
      value = (BtorNode *) it.bucket->data.asPtr;
      args  = next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (args));
      assert (BTOR_IS_ARGS_NODE (args));

      t = btor_new_bv_tuple (btor, ((BtorArgsNode *) args)->num_args);

      pos = 0;
      init_args_iterator (&ait, args);
      while (has_next_args_iterator (&ait))
      {
        arg    = next_args_iterator (&ait);
        bv_arg = btor_assignment_bv (btor, arg, 0);
        btor_add_to_bv_tuple (btor, t, bv_arg, pos++);
        btor_free_bv (btor, bv_arg);
      }

      bv_value = btor_assignment_bv (btor, value, 0);

      add_to_fun_model (btor, cur, t, bv_value);
      btor_free_bv (btor, bv_value);
      btor_free_bv_tuple (btor, t);
    }
  }
}

void
btor_generate_model (Btor *btor, int model_for_all_nodes)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_SAT);

  int i;
  double start;
  BitVector *bv;
  BtorNode *cur;
  BtorHashTableIterator it;
  BtorPtrHashTable *assignments;
  BtorNodePtrStack stack;

  start = btor_time_stamp ();
  init_bv_model (btor);
  init_fun_model (btor);

  BTOR_INIT_STACK (stack);
  assignments = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  extract_models_from_functions_with_model (btor);

  /* NOTE: adding fun_rhs is only needed for extensional benchmarks */
  init_node_hash_table_iterator (&it, btor->fun_rhs);
  if (!model_for_all_nodes)
  {
    queue_node_hash_table_iterator (&it, btor->var_rhs);
    queue_node_hash_table_iterator (&it, btor->bv_vars);
  }
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = btor_simplify_exp (btor, next_node_hash_table_iterator (&it));
    /* models for UFs are constructed from 'rho' via
     * 'extract_models_from_functions_with_model' and hence, don't need to be
     * pushed onto 'stack' */
    if (BTOR_IS_UF_NODE (BTOR_REAL_ADDR_NODE (cur))) continue;
    BTOR_PUSH_STACK (btor->mm, stack, BTOR_REAL_ADDR_NODE (cur));
  }

  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (!cur || BTOR_IS_FUN_NODE (cur) || BTOR_IS_ARGS_NODE (cur)
        || BTOR_IS_PROXY_NODE (cur)
        || cur->parameterized
        /* generate model for all expressions (includes non-reachable) */
        || (!model_for_all_nodes && !cur->reachable))
      continue;
    BTOR_PUSH_STACK (btor->mm, stack, cur);
  }

  qsort (stack.start,
         BTOR_COUNT_STACK (stack),
         sizeof (BtorNode *),
         btor_cmp_exp_by_id_qsort_asc);

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur = BTOR_PEEK_STACK (stack, i);
    assert (!BTOR_IS_UF_NODE (cur));

    // TODO: only required in extensional case (not fully supported yet)
    if (BTOR_IS_LAMBDA_NODE (cur))
      compute_lambda_model (btor, cur, assignments);
    else
    {
      bv = recursively_compute_assignment (btor, cur, assignments);
      add_to_bv_model (btor, cur, bv);
      btor_free_bv (btor, bv);
    }
  }
  BTOR_RELEASE_STACK (btor->mm, stack);

  init_node_hash_table_iterator (&it, assignments);
  while (has_next_node_hash_table_iterator (&it))
  {
    bv = (BitVector *) it.bucket->data.asPtr;
    btor_free_bv (btor, bv);
    (void) next_node_hash_table_iterator (&it);
  }
  btor_delete_ptr_hash_table (assignments);

  btor->time.model_gen += btor_time_stamp () - start;
}

void
btor_delete_model (Btor *btor)
{
  assert (btor);
  delete_bv_model (btor);
  delete_fun_model (btor);
}

const BitVector *
btor_get_bv_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BitVector *result;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->bv_model, BTOR_REAL_ADDR_NODE (exp));

  /* if exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is now
   * a proxy and was therefore regenerated when querying it's assignment via
   * get-value in SMT-LIB v2) */
  if (!b) btor_generate_model (btor, 1);
  b = btor_find_in_ptr_hash_table (btor->bv_model, BTOR_REAL_ADDR_NODE (exp));
  if (!b) return 0;

  result = (BitVector *) b->data.asPtr;
  if (BTOR_IS_INVERTED_NODE (exp)) result = BTOR_INVERT_BV (result);
  return result;
}

const BtorPtrHashTable *
btor_get_fun_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashBucket *b;

  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_FUN_NODE (exp));
  b = btor_find_in_ptr_hash_table (btor->fun_model, exp);

  /* if exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is now
   * a proxy and was therefore regenerated when querying it's assignment via
   * get-value in SMT-LIB v2) */
  if (!b) btor_generate_model (btor, 0);
  b = btor_find_in_ptr_hash_table (btor->fun_model, exp);
  if (!b) return 0;

  return (BtorPtrHashTable *) b->data.asPtr;
}

static BtorNode *
const_from_bv (Btor *btor, BitVector *bv)
{
  assert (btor);
  assert (bv);

  char *val;
  BtorNode *res;

  val = btor_bv_to_char_bv (btor, bv);
  res = btor_const_exp (btor, val);
  btor_release_bv_assignment_str (btor, val);
  return res;
}

BtorNode *
btor_generate_lambda_model_from_fun_model (Btor *btor,
                                           BtorNode *exp,
                                           const BtorPtrHashTable *model)
{
  assert (btor);
  assert (exp);
  assert (model);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_FUN_NODE (exp));

  int i;
  BtorUFNode *uf;
  BtorNode *res, *c, *p, *cond, *e_if, *e_else, *tmp, *eq, *ite;
  BtorHashTableIterator it;
  BtorSort *sort, *domain;
  BtorNodePtrStack params, consts;
  BitVector *value;
  BitVectorTuple *args;

  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (consts);

  sort = btor_fun_sort_from_fun (&btor->sorts_unique_table, exp);
  uf   = (BtorUFNode *) btor_uf_exp (btor, sort, 0);
  btor_release_sort (&btor->sorts_unique_table, sort);
  domain = sort->fun.domain;

  /* generate params */
  if (uf->num_params > 1)
  {
    assert (domain->kind == BTOR_TUPLE_SORT);
    for (i = 0; i < domain->tuple.num_elements; i++)
    {
      p = btor_param_exp (btor, domain->tuple.elements[i]->bitvec.len, 0);
      BTOR_PUSH_STACK (btor->mm, params, p);
    }
  }
  else
  {
    assert (domain->kind == BTOR_BITVEC_SORT);
    p = btor_param_exp (btor, domain->bitvec.len, 0);
    BTOR_PUSH_STACK (btor->mm, params, p);
  }

  e_else = btor_apply_exps (
      btor, BTOR_COUNT_STACK (params), params.start, (BtorNode *) uf);
  btor_release_exp (btor, (BtorNode *) uf);

  /* generate ITEs */
  ite = 0;
  res = 0;
  init_hash_table_iterator (&it, (BtorPtrHashTable *) model);
  while (has_next_hash_table_iterator (&it))
  {
    value = (BitVector *) it.bucket->data.asPtr;
    args  = next_hash_table_iterator (&it);

    /* create condition */
    assert (uf->num_params == args->arity);
    assert (BTOR_EMPTY_STACK (consts));
    assert (BTOR_COUNT_STACK (params) == args->arity);
    for (i = 0; i < args->arity; i++)
    {
      c = const_from_bv (btor, args->bv[i]);
      assert (BTOR_REAL_ADDR_NODE (c)->len == BTOR_PEEK_STACK (params, i)->len);
      assert (args->arity <= 1
              || BTOR_REAL_ADDR_NODE (c)->len
                     == domain->tuple.elements[i]->bitvec.len);
      assert (args->arity > 1
              || BTOR_REAL_ADDR_NODE (c)->len == domain->bitvec.len);
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

    while (!BTOR_EMPTY_STACK (consts))
      btor_release_exp (btor, BTOR_POP_STACK (consts));

    /* create ITE */
    e_if = const_from_bv (btor, value);
    ite  = btor_cond_exp (btor, cond, e_if, e_else);
    btor_release_exp (btor, cond);
    btor_release_exp (btor, e_if);
    btor_release_exp (btor, e_else);
    e_else = ite;
  }

  assert (ite);
  if (ite) /* get rid of compiler warning */
  {
    res = btor_fun_exp (btor, BTOR_COUNT_STACK (params), params.start, ite);
    btor_release_exp (btor, ite);
  }

  while (!BTOR_EMPTY_STACK (params))
    btor_release_exp (btor, BTOR_POP_STACK (params));
  BTOR_RELEASE_STACK (btor->mm, params);
  BTOR_RELEASE_STACK (btor->mm, consts);

  return res;
}

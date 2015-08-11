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
#include "btorlog.h"
#include "utils/btoriter.h"
#include "utils/btormem.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

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

void
btor_delete_bv_model (Btor *btor, BtorPtrHashTable **bv_model)
{
  assert (btor);
  assert (bv_model);

  BtorBitVector *bv;
  BtorNode *cur;
  BtorHashTableIterator it;

  if (!*bv_model) return;

  btor_init_node_hash_table_iterator (&it, *bv_model);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    bv  = (BtorBitVector *) it.bucket->data.asPtr;
    cur = btor_next_node_hash_table_iterator (&it);
    btor_free_bv (btor->mm, bv);
    btor_release_exp (btor, cur);
  }

  btor_delete_ptr_hash_table (*bv_model);
  *bv_model = 0;
}

void
btor_init_bv_model (Btor *btor, BtorPtrHashTable **bv_model)
{
  assert (btor);
  assert (bv_model);

  if (*bv_model) btor_delete_bv_model (btor, bv_model);

  *bv_model = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
}

void
btor_add_to_bv_model (Btor *btor,
                      BtorPtrHashTable *bv_model,
                      BtorNode *exp,
                      BtorBitVector *assignment)
{
  assert (btor);
  assert (exp);
  assert (assignment);

  BtorPtrHashBucket *b;

  assert (!btor_find_in_ptr_hash_table (bv_model, exp));
  b = btor_insert_in_ptr_hash_table (bv_model, btor_copy_exp (btor, exp));
  b->data.asPtr = btor_copy_bv (btor->mm, assignment);
}

static void
delete_fun_model (Btor *btor, BtorPtrHashTable **fun_model)
{
  assert (btor);
  assert (fun_model);

  BtorBitVectorTuple *tup;
  BtorBitVector *value;
  BtorNode *cur;
  BtorHashTableIterator it1, it2;
  BtorPtrHashTable *t;

  if (!*fun_model) return;

  btor_init_node_hash_table_iterator (&it1, *fun_model);
  while (btor_has_next_node_hash_table_iterator (&it1))
  {
    t   = (BtorPtrHashTable *) it1.bucket->data.asPtr;
    cur = btor_next_node_hash_table_iterator (&it1);
    btor_init_hash_table_iterator (&it2, t);
    while (btor_has_next_hash_table_iterator (&it2))
    {
      value = (BtorBitVector *) it2.bucket->data.asPtr;
      tup   = (BtorBitVectorTuple *) btor_next_hash_table_iterator (&it2);
      btor_free_bv_tuple (btor->mm, tup);
      btor_free_bv (btor->mm, value);
    }
    btor_release_exp (btor, cur);
    btor_delete_ptr_hash_table (t);
  }

  btor_delete_ptr_hash_table (*fun_model);
  *fun_model = 0;
}

void
btor_init_fun_model (Btor *btor, BtorPtrHashTable **fun_model)
{
  assert (btor);
  assert (fun_model);

  if (*fun_model) delete_fun_model (btor, fun_model);

  *fun_model = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
add_to_fun_model (Btor *btor,
                  BtorPtrHashTable *fun_model,
                  BtorNode *exp,
                  BtorBitVectorTuple *t,
                  BtorBitVector *value)
{
  assert (btor);
  assert (fun_model);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (t);
  assert (value);

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (fun_model, exp);

  if (b)
    model = (BtorPtrHashTable *) b->data.asPtr;
  else
  {
    model = btor_new_ptr_hash_table (btor->mm,
                                     (BtorHashPtr) btor_hash_bv_tuple,
                                     (BtorCmpPtr) btor_compare_bv_tuple);
    btor_insert_in_ptr_hash_table (fun_model, btor_copy_exp (btor, exp))
        ->data.asPtr = model;
  }
  if ((b = btor_find_in_ptr_hash_table (model, t)))
  {
    assert (btor_compare_bv (b->data.asPtr, value) == 0);
    return;
  }
  b = btor_insert_in_ptr_hash_table (model, btor_copy_bv_tuple (btor->mm, t));
  b->data.asPtr = btor_copy_bv (btor->mm, value);
}

static BtorBitVector *
get_value_from_fun_model (Btor *btor,
                          BtorPtrHashTable *fun_model,
                          BtorNode *exp,
                          BtorBitVectorTuple *t)
{
  assert (btor);
  assert (fun_model);
  assert (exp);
  assert (t);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_FUN_NODE (exp));

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (fun_model, exp);

  if (!b) return 0;

  model = (BtorPtrHashTable *) b->data.asPtr;
  b     = btor_find_in_ptr_hash_table (model, t);

  if (!b) return 0;

  return btor_copy_bv (btor->mm, (BtorBitVector *) b->data.asPtr);
}

/* Note: don't forget to free resulting bit vector! */
BtorBitVector *
btor_recursively_compute_assignment (Btor *btor,
                                     BtorPtrHashTable *bv_model,
                                     BtorPtrHashTable *fun_model,
                                     BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (exp);

  int i, num_args, pos;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack, cleanup, reset;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next, *cur_parent;
  BtorPtrHashData d;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *assigned, *reset_st, *param_model_cache;
  BtorBitVector *result = 0, *inv_result, **e;
  BtorBitVectorTuple *t;

  mm = btor->mm;

  assigned = btor_new_ptr_hash_table (mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);
  /* model cache for parameterized nodes */
  param_model_cache = btor_new_ptr_hash_table (mm, 0, 0);

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

    if (btor_find_in_ptr_hash_table (bv_model, real_cur)
        || btor_find_in_ptr_hash_table (param_model_cache, real_cur))
      goto PUSH_CACHED;

    /* check if we already have an assignment for this function application */
    if (BTOR_IS_LAMBDA_NODE (real_cur) && cur_parent
        && BTOR_IS_APPLY_NODE (cur_parent)
        /* if real_cur was assigned by cur_parent, we are not allowed to use
         * a cached result, but instead rebuild cur_parent */
        && (!(b = btor_find_in_ptr_hash_table (assigned, real_cur))
            || b->data.asPtr != cur_parent))
    {
      num_args = btor_get_args_arity (btor, cur_parent->e[1]);
      e        = (BtorBitVector **) arg_stack.top - num_args;

      t = btor_new_bv_tuple (btor->mm, num_args);
      for (i = 0; i < num_args; i++)
        btor_add_to_bv_tuple (btor->mm, t, e[i], num_args - 1 - i);

      /* check if there is already a value for given arguments */
      result = get_value_from_fun_model (btor, fun_model, cur_parent->e[0], t);
      btor_free_bv_tuple (btor->mm, t);

      if (result) goto PUSH_RESULT;
    }

    if (real_cur->eval_mark == 0)
    {
      /* add assignment of bv var to model (creates new assignment, if
       * it doesn't have one) */
      if (BTOR_IS_BV_VAR_NODE (real_cur))
      {
        result = btor_assignment_bv (btor->mm, real_cur, 1);
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_char_to_bv (btor->mm, btor_const_get_bits (real_cur));
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
      else if (BTOR_IS_FEQ_NODE (real_cur))
      {
        result = btor_assignment_bv (btor->mm, real_cur, 1);
        goto CACHE_AND_PUSH_RESULT;
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
        num_args = btor_get_args_arity (btor, real_cur->e[1]);
        arg_stack.top -= 1;        /* value of apply */
        arg_stack.top -= num_args; /* arguments of apply */
      }
      else
        arg_stack.top -= real_cur->arity;

      e = (BtorBitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BTOR_SLICE_NODE:
          result = btor_slice_bv (btor->mm,
                                  e[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          btor_free_bv (btor->mm, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_BEQ_NODE:
          result = btor_eq_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (btor->mm, e[1], e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          break;
        case BTOR_BCOND_NODE:
          if (btor_is_true_bv (e[2]))
            result = btor_copy_bv (btor->mm, e[1]);
          else
            result = btor_copy_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[0]);
          btor_free_bv (btor->mm, e[1]);
          btor_free_bv (btor->mm, e[2]);
          break;
        case BTOR_APPLY_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          assert (num_args);
          t = btor_new_bv_tuple (btor->mm, num_args);
          for (i = 0; i < num_args; i++)
          {
            btor_add_to_bv_tuple (btor->mm, t, e[i], num_args - 1 - i);
            btor_free_bv (btor->mm, e[i]);
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
            btor_free_bv (btor->mm, e[num_args]);

          btor_free_bv_tuple (btor->mm, t);
          if (real_cur->parameterized)
            goto PUSH_RESULT;
          else
            break;
        case BTOR_LAMBDA_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          result              = e[0];
          btor_free_bv (btor->mm, e[1]);
          if (BTOR_IS_LAMBDA_NODE (real_cur) && cur_parent
              && BTOR_IS_APPLY_NODE (cur_parent))
          {
            assert (btor_find_in_ptr_hash_table (assigned, real_cur));
            btor_unassign_params (btor, real_cur);
            btor_remove_from_ptr_hash_table (assigned, real_cur, 0, 0);

            /* reset 'eval_mark' of all parameterized nodes
             * instantiated by 'real_cur' */
            btor_remove_from_ptr_hash_table (reset_st, real_cur, 0, &d);
            pos = d.asInt;
            while (BTOR_COUNT_STACK (reset) > pos)
            {
              next = BTOR_POP_STACK (reset);
              assert (BTOR_IS_REGULAR_NODE (next));
              assert (next->parameterized);
              next->eval_mark = 0;
              btor_remove_from_ptr_hash_table (param_model_cache, next, 0, &d);
              btor_free_bv (mm, d.asPtr);
            }
          }
          goto PUSH_RESULT;
        case BTOR_UF_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          result              = btor_assignment_bv (btor->mm, cur_parent, 1);
          goto PUSH_RESULT;
        default:
          /* should be unreachable */
          BTOR_ABORT_MODEL (1, "invalid node type");
      }
    CACHE_AND_PUSH_RESULT:
      /* remember parameterized nodes for resetting 'eval_mark' later */
      if (real_cur->parameterized)
      {
        BTOR_PUSH_STACK (mm, reset, real_cur);
        /* temporarily cache model for paramterized nodes, is only
         * valid under current parameter assignment and will be reset
         * when parameters are unassigned */
        assert (!btor_find_in_ptr_hash_table (param_model_cache, real_cur));
        btor_insert_in_ptr_hash_table (param_model_cache, real_cur)
            ->data.asPtr = btor_copy_bv (mm, result);
      }
      else
      {
        assert (!btor_find_in_ptr_hash_table (bv_model, real_cur));
        btor_add_to_bv_model (btor, bv_model, real_cur, result);
      }

    PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (btor->mm, result);
        btor_free_bv (btor->mm, result);
        result = inv_result;
      }
      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      assert (real_cur->eval_mark == 2);
    PUSH_CACHED:
      if (real_cur->parameterized)
        b = btor_find_in_ptr_hash_table (param_model_cache, real_cur);
      else
        b = btor_find_in_ptr_hash_table (bv_model, real_cur);
      assert (b);
      result = btor_copy_bv (btor->mm, (BtorBitVector *) b->data.asPtr);
      goto PUSH_RESULT;
    }
  }
  assert (param_model_cache->count == 0);
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
  btor_delete_ptr_hash_table (param_model_cache);

  return result;
}

static void
extract_model_from_rhos (Btor *btor,
                         BtorPtrHashTable *bv_model,
                         BtorPtrHashTable *fun_model,
                         BtorNode *fun)
{
  int pos;
  BtorNode *arg, *value, *args;
  BtorBitVector *bv_arg, *bv_value;
  BtorBitVectorTuple *t;
  BtorHashTableIterator it;
  BtorPtrHashTable *model = 0;
  BtorArgsIterator ait;
  BtorPtrHashBucket *b;

  if (!fun->rho
      && (!BTOR_IS_LAMBDA_NODE (fun) || !btor_lambda_get_static_rho (fun)))
    return;

  b = btor_find_in_ptr_hash_table (fun_model, fun);
  if (b) model = b->data.asPtr;

  if (fun->rho)
  {
    btor_init_node_hash_table_iterator (&it, fun->rho);
    if (BTOR_IS_LAMBDA_NODE (fun) && btor_lambda_get_static_rho (fun))
      btor_queue_node_hash_table_iterator (&it,
                                           btor_lambda_get_static_rho (fun));
  }
  else if (BTOR_IS_LAMBDA_NODE (fun) && btor_lambda_get_static_rho (fun))
    btor_init_node_hash_table_iterator (&it, btor_lambda_get_static_rho (fun));

  while (btor_has_next_node_hash_table_iterator (&it))
  {
    value = (BtorNode *) it.bucket->data.asPtr;
    args  = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (args));
    assert (BTOR_IS_ARGS_NODE (args));

    t = btor_new_bv_tuple (btor->mm, btor_get_args_arity (btor, args));

    pos = 0;
    btor_init_args_iterator (&ait, args);
    while (btor_has_next_args_iterator (&ait))
    {
      arg = btor_next_args_iterator (&ait);
      /* all arguments in 'rho' are encoded, however some arguments in
       * 'static_rho' might not be encoded and thus we have to obtain the
       * assignment from the constructed model. */
      if (btor_is_encoded_exp (arg))
        bv_arg = btor_assignment_bv (btor->mm, arg, 0);
      else
        bv_arg = btor_copy_bv (btor->mm, btor_get_bv_model (btor, arg));
      btor_add_to_bv_tuple (btor->mm, t, bv_arg, pos++);
      btor_free_bv (btor->mm, bv_arg);
    }

    /* values in 'rho' are encoded, however some values in 'static_rho' might
     * not be encoded and thus we have to obtain the assignment from the
     * constructed model. */
    if (btor_is_encoded_exp (value))
      bv_value = btor_assignment_bv (btor->mm, value, 0);
    else
      bv_value = btor_copy_bv (btor->mm, btor_get_bv_model (btor, value));

    if (!model)
    {
      add_to_fun_model (btor, fun_model, fun, t, bv_value);
      b = btor_find_in_ptr_hash_table (fun_model, fun);
      assert (b);
      model = b->data.asPtr;
    }
    /* if static_rho contains arguments with the same assignments, but map
     * to different values, we consider the argument which occurs
     * earlier in static_rho. */
    else if (!btor_find_in_ptr_hash_table (model, t))
      add_to_fun_model (btor, fun_model, fun, t, bv_value);

    btor_free_bv (btor->mm, bv_value);
    btor_free_bv_tuple (btor->mm, t);
  }
}

void
btor_generate_model (Btor *btor,
                     BtorPtrHashTable *bv_model,
                     BtorPtrHashTable *fun_model,
                     int model_for_all_nodes)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);

  int i;
  double start;
  BtorNode *cur;
  BtorHashTableIterator it;
  BtorNodePtrStack stack;
  BtorBitVector *bv;

  start = btor_time_stamp ();

  BTOR_INIT_STACK (stack);

  /* NOTE: adding fun_rhs is only needed for extensional benchmarks */
  btor_init_node_hash_table_iterator (&it, btor->fun_rhs);
  if (!model_for_all_nodes)
  {
    btor_queue_node_hash_table_iterator (&it, btor->var_rhs);
    btor_queue_node_hash_table_iterator (&it, btor->bv_vars);
    btor_queue_node_hash_table_iterator (&it, btor->ufs);
  }
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_simplify_exp (btor, btor_next_node_hash_table_iterator (&it));
    BTOR_PUSH_STACK (btor->mm, stack, BTOR_REAL_ADDR_NODE (cur));
  }

  if (model_for_all_nodes)
  {
    for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
    {
      cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
      if (!cur || BTOR_IS_ARGS_NODE (cur) || BTOR_IS_PROXY_NODE (cur)
          || cur->parameterized)
        continue;
      BTOR_PUSH_STACK (btor->mm, stack, cur);
    }
  }
  else /* push roots only */
  {
    btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
    btor_queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
    btor_queue_node_hash_table_iterator (&it, btor->assumptions);
    while (btor_has_next_node_hash_table_iterator (&it))
      BTOR_PUSH_STACK (
          btor->mm, stack, btor_next_node_hash_table_iterator (&it));
  }

  qsort (stack.start,
         BTOR_COUNT_STACK (stack),
         sizeof (BtorNode *),
         btor_cmp_exp_by_id_qsort_asc);

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur = BTOR_PEEK_STACK (stack, i);
    BTORLOG (1, "generate model for %s", node2string (cur));
    if (BTOR_IS_FUN_NODE (cur))
      extract_model_from_rhos (btor, bv_model, fun_model, cur);
    else
    {
      bv = btor_recursively_compute_assignment (btor, bv_model, fun_model, cur);
      btor_free_bv (btor->mm, bv);
    }
  }
  BTOR_RELEASE_STACK (btor->mm, stack);

  btor->time.model_gen += btor_time_stamp () - start;
}

void
btor_delete_model (Btor *btor)
{
  assert (btor);
  btor_delete_bv_model (btor, &btor->bv_model);
  delete_fun_model (btor, &btor->fun_model);
}

/* Note: no need to free returned bit vector,
 *       all bit vectors are maintained via btor->bv_model */
const BtorBitVector *
btor_get_bv_model_aux (Btor *btor,
                       BtorPtrHashTable **bv_model,
                       BtorPtrHashTable **fun_model,
                       BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (*bv_model);
  assert (fun_model);
  assert (*fun_model);
  assert (exp);

  BtorBitVector *result;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (*bv_model, exp);

  if (!b)
  {
    b = btor_find_in_ptr_hash_table (*bv_model, BTOR_REAL_ADDR_NODE (exp));

    /* if exp has no assignment, regenerate model in case that it is an exp
     * that previously existed but was simplified (i.e. the original exp is
     * now a proxy and was therefore regenerated when querying it's
     * assignment via get-value in SMT-LIB v2) */
    if (!b)
    {
      result = btor_recursively_compute_assignment (
          btor, *bv_model, *fun_model, exp);
      btor_free_bv (btor->mm, result);
    }
    b = btor_find_in_ptr_hash_table (*bv_model, BTOR_REAL_ADDR_NODE (exp));
    if (!b) return 0;
  }

  result = (BtorBitVector *) b->data.asPtr;
  /* Note: we cache assignments of inverted expressions on demand */
  if (BTOR_IS_INVERTED_NODE (exp))
  {
    if ((b = btor_find_in_ptr_hash_table (*bv_model, exp)))
      result = b->data.asPtr;
    else
    {
      /* we don't use add_to_bv_model in order to avoid redundant
       * hash table queries and copying/freeing of the resulting bv */
      result = btor_not_bv (btor->mm, result);
      b = btor_insert_in_ptr_hash_table (*bv_model, btor_copy_exp (btor, exp));
      b->data.asPtr = result;
    }
  }
  return result;
}

const BtorBitVector *
btor_get_bv_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_get_bv_model_aux (btor, &btor->bv_model, &btor->fun_model, exp);
}

const BtorPtrHashTable *
btor_get_fun_model_aux (Btor *btor,
                        BtorPtrHashTable **bv_model,
                        BtorPtrHashTable **fun_model,
                        BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (*bv_model);
  assert (fun_model);
  assert (*fun_model);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashBucket *b;

  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_FUN_NODE (exp));
  b = btor_find_in_ptr_hash_table (*fun_model, exp);

  /* if exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is now
   * a proxy and was therefore regenerated when querying it's assignment via
   * get-value in SMT-LIB v2) */
  if (!b) extract_model_from_rhos (btor, *bv_model, *fun_model, exp);
  b = btor_find_in_ptr_hash_table (*fun_model, exp);
  if (!b) return 0;

  return (BtorPtrHashTable *) b->data.asPtr;
}

const BtorPtrHashTable *
btor_get_fun_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_get_fun_model_aux (btor, &btor->bv_model, &btor->fun_model, exp);
}

static BtorNode *
const_from_bv (Btor *btor, BtorBitVector *bv)
{
  assert (btor);
  assert (bv);

  char *val;
  BtorNode *res;

  val = btor_bv_to_char_bv (btor->mm, bv);
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
  uf   = btor_uf_exp (btor, exp->sort_id, 0);
  args = btor_args_exp (btor, BTOR_COUNT_STACK (params), params.start);
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
    value      = (BtorBitVector *) it.bucket->data.asPtr;
    args_tuple = btor_next_hash_table_iterator (&it);

    /* create condition */
    assert (btor_get_fun_arity (btor, uf) == args_tuple->arity);
    assert (BTOR_EMPTY_STACK (consts));
    assert (BTOR_COUNT_STACK (params) == args_tuple->arity);
    for (i = 0; i < args_tuple->arity; i++)
    {
      c = const_from_bv (btor, args_tuple->bv[i]);
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
    args = btor_args_exp (btor, BTOR_COUNT_STACK (consts), consts.start);

    while (!BTOR_EMPTY_STACK (consts))
      btor_release_exp (btor, BTOR_POP_STACK (consts));

    /* create ITE */
    e_if = const_from_bv (btor, value);
    ite  = btor_cond_exp (btor, cond, e_if, e_else);

    /* add to static rho */
    btor_insert_in_ptr_hash_table (static_rho, args)->data.asPtr =
        btor_copy_exp (btor, e_if);

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

  /* res already exists */
  if (((BtorLambdaNode *) res)->static_rho)
  {
    btor_init_node_hash_table_iterator (&it, static_rho);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      btor_release_exp (btor, it.bucket->data.asPtr);
      btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
    }
    btor_delete_ptr_hash_table (static_rho);
  }
  else
    ((BtorLambdaNode *) res)->static_rho = static_rho;
  assert (res->sort_id == exp->sort_id);
  return res;
}

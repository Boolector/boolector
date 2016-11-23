/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormodel.h"

#include "btorbeta.h"
#include "btorclone.h"
#include "btordbg.h"
#include "btorlog.h"
#include "utils/btorexpiter.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

void
btor_add_to_bv_model (Btor *btor,
                      BtorIntHashTable *bv_model,
                      BtorNode *exp,
                      BtorBitVector *assignment)
{
  assert (btor);
  assert (bv_model);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (assignment);

  assert (
      !btor_contains_int_hash_map (bv_model, BTOR_REAL_ADDR_NODE (exp)->id));
  btor_copy_exp (btor, exp);
  btor_add_int_hash_map (bv_model, BTOR_REAL_ADDR_NODE (exp)->id)->as_ptr =
      btor_copy_bv (btor->mm, assignment);
}

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
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (t);
  assert (value);

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  if (btor_contains_int_hash_map (fun_model, exp->id))
    model = btor_get_int_hash_map (fun_model, exp->id)->as_ptr;
  else
  {
    model = btor_new_ptr_hash_table (btor->mm,
                                     (BtorHashPtr) btor_hash_bv_tuple,
                                     (BtorCmpPtr) btor_compare_bv_tuple);
    btor_copy_exp (btor, exp);
    btor_add_int_hash_map (fun_model, exp->id)->as_ptr = model;
  }
  if ((b = btor_get_ptr_hash_table (model, t)))
  {
    assert (btor_compare_bv (b->data.as_ptr, value) == 0);
    return;
  }
  b = btor_add_ptr_hash_table (model, btor_copy_bv_tuple (btor->mm, t));
  b->data.as_ptr = btor_copy_bv (btor->mm, value);
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
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_fun_node (exp));

  BtorPtrHashTable *model;
  BtorHashTableData *d;
  BtorPtrHashBucket *b;

  d = btor_get_int_hash_map (fun_model, exp->id);
  if (!d) return 0;
  model = (BtorPtrHashTable *) d->as_ptr;
  b     = btor_get_ptr_hash_table (model, t);
  if (!b) return 0;
  return btor_copy_bv (btor->mm, (BtorBitVector *) b->data.as_ptr);
}

/* Note: don't forget to free resulting bit vector! */
BtorBitVector *
btor_recursively_compute_assignment (Btor *btor,
                                     BtorIntHashTable *bv_model,
                                     BtorIntHashTable *fun_model,
                                     BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (exp);

  int i, num_args, pos;
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

  assigned = btor_new_int_hash_map (mm);

  /* model cache for parameterized nodes */
  param_model_cache = btor_new_int_hash_map (mm);

  /* 'reset_st' remembers the stack position of 'reset' in case a lambda is
   * assigned. when the resp. lambda is unassigned, the 'eval_mark' flag of all
   * parameterized nodes up to the saved position of stack 'reset' will be
   * reset to 0. */
  reset_st = btor_new_int_hash_map (mm);

  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (mm, work_stack);
  BTOR_INIT_STACK (mm, arg_stack);
  BTOR_INIT_STACK (mm, reset);

  BTOR_PUSH_STACK (work_stack, exp);
  BTOR_PUSH_STACK (work_stack, 0);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur_parent = BTOR_POP_STACK (work_stack);
    cur        = BTOR_POP_STACK (work_stack);
    real_cur   = BTOR_REAL_ADDR_NODE (cur);
    assert (!real_cur->simplified);

    if (btor_contains_int_hash_map (bv_model, real_cur->id)
        || btor_contains_int_hash_map (param_model_cache, real_cur->id))
      goto PUSH_CACHED;

    /* check if we already have an assignment for this function application */
    if (btor_is_lambda_node (real_cur) && cur_parent
        && btor_is_apply_node (cur_parent)
        /* if real_cur was assigned by cur_parent, we are not allowed to use
         * a cached result, but instead rebuild cur_parent */
        && (!(d = btor_get_int_hash_map (assigned, real_cur->id))
            || d->as_ptr != cur_parent))
    {
      num_args = btor_get_args_arity (btor, cur_parent->e[1]);
      e        = (BtorBitVector **) arg_stack.top - num_args;

      t = btor_new_bv_tuple (mm, num_args);
      for (i = 0; i < num_args; i++)
        btor_add_to_bv_tuple (mm, t, e[i], num_args - 1 - i);

      /* check if there is already a value for given arguments */
      result = get_value_from_fun_model (btor, fun_model, cur_parent->e[0], t);
      btor_free_bv_tuple (mm, t);

      if (result) goto PUSH_RESULT;
    }

    md = btor_get_int_hash_map (mark, real_cur->id);
    if (!md)
    {
      /* add assignment of bv var to model (creates new assignment, if
       * it doesn't have one) */
      if (btor_is_bv_var_node (real_cur))
      {
        result = btor_get_assignment_bv (mm, real_cur, true);
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (btor_is_bv_const_node (real_cur))
      {
        result = btor_copy_bv (mm, btor_const_get_bits (real_cur));
        goto CACHE_AND_PUSH_RESULT;
      }
      /* substitute param with its assignment */
      else if (btor_is_param_node (real_cur))
      {
        next = btor_param_get_assigned_exp (real_cur);
        assert (next);
        next = BTOR_COND_INVERT_NODE (cur, next);
        BTOR_PUSH_STACK (work_stack, next);
        BTOR_PUSH_STACK (work_stack, cur_parent);
        continue;
      }
      else if (btor_is_fun_eq_node (real_cur))
      {
        result = btor_get_assignment_bv (mm, real_cur, true);
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (btor_is_lambda_node (real_cur) && cur_parent
               && btor_is_apply_node (cur_parent))
      {
        btor_assign_args (btor, real_cur, cur_parent->e[1]);
        assert (!btor_contains_int_hash_map (assigned, real_cur->id));
        btor_add_int_hash_map (assigned, real_cur->id)->as_ptr = cur_parent;

        /* save 'reset' stack position */
        btor_add_int_hash_map (reset_st, real_cur->id)->as_int =
            BTOR_COUNT_STACK (reset);
      }

      BTOR_PUSH_STACK (work_stack, cur);
      BTOR_PUSH_STACK (work_stack, cur_parent);
      md = btor_add_int_hash_map (mark, real_cur->id);

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (btor_is_cond_node (real_cur))
      {
        md->as_int = 2;
        BTOR_PUSH_STACK (work_stack, real_cur->e[0]);
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
      assert (!btor_is_param_node (real_cur));
      assert (real_cur->arity <= 3);

      /* leave arguments on stack, we need them later for apply */
      if (btor_is_args_node (real_cur))
      {
        assert (md->as_int == 0);
        btor_remove_int_hash_map (mark, real_cur->id, 0);
        continue;
      }

      num_args = 0;

      if (btor_is_apply_node (real_cur))
      {
        num_args = btor_get_args_arity (btor, real_cur->e[1]);
        arg_stack.top -= 1;        /* value of apply */
        arg_stack.top -= num_args; /* arguments of apply */
        md->as_int = 1;
      }
      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      else if (btor_is_cond_node (real_cur))
      {
        /* only the condition is on the stack */
        assert (BTOR_COUNT_STACK (arg_stack) >= 1);
        arg_stack.top -= 1;
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
        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  e[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          btor_free_bv (mm, e[0]);
          break;
        case BTOR_AND_NODE:
          result = btor_and_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_BV_EQ_NODE:
          result = btor_eq_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_ADD_NODE:
          result = btor_add_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_MUL_NODE:
          result = btor_mul_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_ULT_NODE:
          result = btor_ult_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_SLL_NODE:
          result = btor_sll_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_SRL_NODE:
          result = btor_srl_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_UDIV_NODE:
          result = btor_udiv_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_UREM_NODE:
          result = btor_urem_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (mm, e[1], e[0]);
          btor_free_bv (mm, e[0]);
          btor_free_bv (mm, e[1]);
          break;
        case BTOR_APPLY_NODE:
          assert (num_args);
          t = btor_new_bv_tuple (mm, num_args);
          for (i = 0; i < num_args; i++)
          {
            btor_add_to_bv_tuple (mm, t, e[i], num_args - 1 - i);
            btor_free_bv (mm, e[i]);
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
            btor_free_bv (mm, e[num_args]);

          btor_free_bv_tuple (mm, t);
          break;
        case BTOR_LAMBDA_NODE:
          result = e[0];
          btor_free_bv (mm, e[1]);
          if (btor_is_lambda_node (real_cur) && cur_parent
              && btor_is_apply_node (cur_parent))
          {
            assert (btor_contains_int_hash_map (assigned, real_cur->id));
            btor_unassign_params (btor, real_cur);
            btor_remove_int_hash_map (assigned, real_cur->id, 0);

            /* reset 'eval_mark' of all parameterized nodes
             * instantiated by 'real_cur' */
            btor_remove_int_hash_map (reset_st, real_cur->id, &dd);
            pos = dd.as_int;
            while (BTOR_COUNT_STACK (reset) > pos)
            {
              next = BTOR_POP_STACK (reset);
              assert (BTOR_IS_REGULAR_NODE (next));
              assert (next->parameterized);
              btor_remove_int_hash_map (mark, next->id, 0);
              btor_remove_int_hash_map (param_model_cache, next->id, &dd);
              btor_free_bv (mm, dd.as_ptr);
            }
          }
          break;
        case BTOR_UF_NODE:
          result = btor_get_assignment_bv (mm, cur_parent, true);
          break;
        default:
          assert (btor_is_cond_node (real_cur));

          /* evaluate condition and select branch */
          if (md->as_int == 2)
          {
            /* select branch w.r.t. condition */
            next = btor_is_true_bv (e[0]) ? real_cur->e[1] : real_cur->e[2];
            BTOR_PUSH_STACK (work_stack, cur);
            BTOR_PUSH_STACK (work_stack, cur_parent);
            /* for function conditionals we push the function and the
             * apply */
            BTOR_PUSH_STACK (work_stack, next);
            BTOR_PUSH_STACK (work_stack, cur_parent);
            btor_free_bv (mm, e[0]);
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
      if (btor_is_fun_node (real_cur))
      {
        assert (result);
        /* not inserted into cache */
        btor_remove_int_hash_map (mark, real_cur->id, 0);
        goto PUSH_RESULT;
      }
      else if (btor_is_apply_node (real_cur))
      {
        /* not inserted into cache */
        btor_remove_int_hash_map (mark, real_cur->id, 0);
        if (real_cur->parameterized) goto PUSH_RESULT;
      }
    CACHE_AND_PUSH_RESULT:
      assert (!btor_is_fun_node (real_cur));
      /* remember parameterized nodes for resetting 'eval_mark' later */
      if (real_cur->parameterized)
      {
        BTOR_PUSH_STACK (reset, real_cur);
        /* temporarily cache model for paramterized nodes, is only
         * valid under current parameter assignment and will be reset
         * when parameters are unassigned */
        assert (!btor_contains_int_hash_map (param_model_cache, real_cur->id));
        btor_add_int_hash_map (param_model_cache, real_cur->id)->as_ptr =
            btor_copy_bv (mm, result);
      }
      else
      {
        assert (!btor_contains_int_hash_map (bv_model, real_cur->id));
        btor_add_to_bv_model (btor, bv_model, real_cur, result);
      }

    PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (mm, result);
        btor_free_bv (mm, result);
        result = inv_result;
      }
      BTOR_PUSH_STACK (arg_stack, result);
    }
    else
    {
      assert (md->as_int == 1);
    PUSH_CACHED:
      if (real_cur->parameterized)
        d = btor_get_int_hash_map (param_model_cache, real_cur->id);
      else
        d = btor_get_int_hash_map (bv_model, real_cur->id);
      result = btor_copy_bv (mm, (BtorBitVector *) d->as_ptr);
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
  btor_delete_int_hash_map (assigned);
  btor_delete_int_hash_map (reset_st);
  btor_delete_int_hash_map (param_model_cache);
  btor_delete_int_hash_map (mark);

  return result;
}

/*------------------------------------------------------------------------*/

static void
recursively_compute_function_model (Btor *btor,
                                    BtorIntHashTable *bv_model,
                                    BtorIntHashTable *fun_model,
                                    BtorNode *fun)
{
  assert (btor);
  assert (fun_model);
  assert (fun);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (btor_is_fun_node (fun));

  int i;
  unsigned pos;
  BtorNode *value, *args, *arg, *cur_fun, *cur;
  BtorArgsIterator ait;
  BtorPtrHashTableIterator it;
  BtorPtrHashTable *model, *static_rho;
  BtorHashTableData *d;
  BtorBitVectorTuple *t;
  BtorBitVector *bv_arg, *bv_value;
  BtorMemMgr *mm;
  BtorNodePtrStack stack;

  mm = btor->mm;

  if (!fun->rho
      && (!btor_is_lambda_node (fun) || !btor_lambda_get_static_rho (fun)))
    return;

  d     = btor_get_int_hash_map (fun_model, fun->id);
  model = d ? d->as_ptr : 0;

  cur_fun = fun;
  while (cur_fun)
  {
    assert (btor_is_fun_node (cur_fun));

    if (cur_fun->rho) btor_init_ptr_hash_table_iterator (&it, cur_fun->rho);
    if (btor_is_lambda_node (cur_fun)
        && (static_rho = btor_lambda_get_static_rho (cur_fun)))
    {
      if (cur_fun->rho)
        btor_queue_ptr_hash_table_iterator (&it, static_rho);
      else
        btor_init_ptr_hash_table_iterator (&it, static_rho);
    }

    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      value = (BtorNode *) it.bucket->data.as_ptr;
      args  = btor_next_ptr_hash_table_iterator (&it);
      assert (!BTOR_REAL_ADDR_NODE (value)->parameterized);
      assert (BTOR_IS_REGULAR_NODE (args));
      assert (btor_is_args_node (args));
      assert (!args->parameterized);

      t   = btor_new_bv_tuple (mm, btor_get_args_arity (btor, args));
      pos = 0;
      btor_init_args_iterator (&ait, args);
      while (btor_has_next_args_iterator (&ait))
      {
        arg    = btor_next_args_iterator (&ait);
        bv_arg = btor_recursively_compute_assignment (
            btor, bv_model, fun_model, arg);
        btor_add_to_bv_tuple (mm, t, bv_arg, pos++);
        btor_free_bv (mm, bv_arg);
      }
      bv_value = btor_recursively_compute_assignment (
          btor, bv_model, fun_model, value);

      /* if static_rho contains arguments with the same assignments, but map
       * to different values, we consider the argument which occurs
       * earlier in static_rho. */
      if (!model || !btor_get_ptr_hash_table (model, t))
      {
        add_to_fun_model (btor, fun_model, fun, t, bv_value);
        if (!model)
        {
          assert (btor_contains_int_hash_map (fun_model, fun->id));
          model = btor_get_int_hash_map (fun_model, fun->id)->as_ptr;
        }
      }
      else if (!btor_get_ptr_hash_table (model, t))
        add_to_fun_model (btor, fun_model, fun, t, bv_value);

      btor_free_bv (btor->mm, bv_value);
      btor_free_bv_tuple (btor->mm, t);
    }

    if (btor_is_lambda_node (cur_fun))
    {
      if (btor_lambda_get_static_rho (cur_fun))
      {
        BTOR_INIT_STACK (mm, stack);
        BTOR_PUSH_STACK (stack, btor_lambda_get_body (cur_fun));
        cur_fun = 0;
        while (!BTOR_EMPTY_STACK (stack))
        {
          cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

          if (btor_is_fun_node (cur))
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
        cur_fun = 0;
        // TODO: what do we have to do here?
      }
    }
    else if (btor_is_fun_cond_node (cur_fun))
    {
      if (cur_fun->parameterized)
      {
        cur_fun = 0;
        // TODO: print warning that branch cannot be selected
      }
      else
      {
        assert (!BTOR_REAL_ADDR_NODE (cur_fun->e[0])->parameterized);
        value    = cur_fun->e[0];
        bv_value = btor_recursively_compute_assignment (
            btor, bv_model, fun_model, value);

        if (btor_is_true_bv (bv_value))
          cur_fun = cur_fun->e[1];
        else
        {
          assert (btor_is_false_bv (bv_value));
          cur_fun = cur_fun->e[2];
        }
        btor_free_bv (mm, bv_value);
      }
    }
    else
    {
      assert (btor_is_uf_node (cur_fun));
      cur_fun = 0;
    }
  }
}

void
btor_generate_model (Btor *btor,
                     BtorIntHashTable *bv_model,
                     BtorIntHashTable *fun_model,
                     bool model_for_all_nodes)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);

  int i;
  double start;
  BtorNode *cur;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack stack;
  BtorBitVector *bv;

  start = btor_time_stamp ();

  BTOR_INIT_STACK (btor->mm, stack);

  /* NOTE: adding fun_rhs is only needed for extensional benchmarks */
  btor_init_ptr_hash_table_iterator (&it, btor->fun_rhs);
  if (!model_for_all_nodes)
  {
    btor_queue_ptr_hash_table_iterator (&it, btor->var_rhs);
    btor_queue_ptr_hash_table_iterator (&it, btor->bv_vars);
    btor_queue_ptr_hash_table_iterator (&it, btor->ufs);
  }
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_simplify_exp (btor, btor_next_ptr_hash_table_iterator (&it));
    BTOR_PUSH_STACK (stack, BTOR_REAL_ADDR_NODE (cur));
  }

  if (model_for_all_nodes)
  {
    for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
    {
      cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
      if (!cur || btor_is_args_node (cur) || btor_is_proxy_node (cur)
          || cur->parameterized)
        continue;
      BTOR_PUSH_STACK (stack, cur);
    }
  }
  else /* push roots only */
  {
    btor_init_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
    btor_queue_ptr_hash_table_iterator (&it, btor->synthesized_constraints);
    btor_queue_ptr_hash_table_iterator (&it, btor->assumptions);
    while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      cur = btor_next_ptr_hash_table_iterator (&it);
      BTOR_PUSH_STACK (stack, cur);
    }
  }

  qsort (stack.start,
         BTOR_COUNT_STACK (stack),
         sizeof (BtorNode *),
         btor_compare_exp_by_id_qsort_asc);

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_PEEK_STACK (stack, i));
    assert (!cur->parameterized);
    BTORLOG (3, "generate model for %s", node2string (cur));
    if (btor_is_fun_node (cur))
      recursively_compute_function_model (btor, bv_model, fun_model, cur);
    else
    {
      bv = btor_recursively_compute_assignment (btor, bv_model, fun_model, cur);
      btor_free_bv (btor->mm, bv);
    }
  }
  BTOR_RELEASE_STACK (stack);

  btor->time.model_gen += btor_time_stamp () - start;
}

/*------------------------------------------------------------------------*/

void
btor_delete_bv_model (Btor *btor, BtorIntHashTable **bv_model)
{
  assert (btor);
  assert (bv_model);

  BtorBitVector *bv;
  BtorNode *cur;
  BtorIntHashTableIterator it;

  if (!*bv_model) return;

  btor_init_int_hash_table_iterator (&it, *bv_model);
  while (btor_has_next_int_hash_table_iterator (&it))
  {
    bv  = (BtorBitVector *) (*bv_model)->data[it.cur_pos].as_ptr;
    cur = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&it));
    btor_free_bv (btor->mm, bv);
    btor_release_exp (btor, cur);
  }
  btor_delete_int_hash_map (*bv_model);
  *bv_model = 0;
}

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

  btor_init_int_hash_table_iterator (&it1, *fun_model);
  while (btor_has_next_int_hash_table_iterator (&it1))
  {
    t   = (BtorPtrHashTable *) (*fun_model)->data[it1.cur_pos].as_ptr;
    cur = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&it1));
    btor_init_ptr_hash_table_iterator (&it2, t);
    while (btor_has_next_ptr_hash_table_iterator (&it2))
    {
      value = (BtorBitVector *) it2.bucket->data.as_ptr;
      tup   = (BtorBitVectorTuple *) btor_next_ptr_hash_table_iterator (&it2);
      btor_free_bv_tuple (btor->mm, tup);
      btor_free_bv (btor->mm, value);
    }
    btor_release_exp (btor, cur);
    btor_delete_ptr_hash_table (t);
  }
  btor_delete_int_hash_map (*fun_model);
  *fun_model = 0;
}

void
btor_delete_model (Btor *btor)
{
  assert (btor);
  btor_delete_bv_model (btor, &btor->bv_model);
  delete_fun_model (btor, &btor->fun_model);
}

/*------------------------------------------------------------------------*/

void
btor_init_bv_model (Btor *btor, BtorIntHashTable **bv_model)
{
  assert (btor);
  assert (bv_model);

  if (*bv_model) btor_delete_bv_model (btor, bv_model);

  *bv_model = btor_new_int_hash_map (btor->mm);
}

void
btor_init_fun_model (Btor *btor, BtorIntHashTable **fun_model)
{
  assert (btor);
  assert (fun_model);

  if (*fun_model) delete_fun_model (btor, fun_model);

  *fun_model = btor_new_int_hash_map (btor->mm);
}

/*------------------------------------------------------------------------*/

BtorIntHashTable *
btor_clone_bv_model (Btor *btor, BtorIntHashTable *bv_model)
{
  assert (btor);
  assert (bv_model);

  BtorIntHashTable *res;
  BtorIntHashTableIterator it;
  BtorNode *exp;

  res = btor_clone_int_hash_map (
      btor->mm, bv_model, btor_clone_data_as_bv_ptr, 0);

  btor_init_int_hash_table_iterator (&it, res);
  while (btor_has_next_int_hash_table_iterator (&it))
  {
    exp = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&it));
    assert (exp);
    btor_copy_exp (btor, exp);
  }
  return res;
}

BtorIntHashTable *
btor_clone_fun_model (Btor *btor, BtorIntHashTable *fun_model)
{
  assert (btor);
  assert (fun_model);

  BtorIntHashTable *res;
  BtorIntHashTableIterator it;
  BtorNode *exp;

  res = btor_clone_int_hash_map (
      btor->mm, fun_model, btor_clone_data_as_bv_ptr_htable, 0);

  btor_init_int_hash_table_iterator (&it, res);
  while (btor_has_next_int_hash_table_iterator (&it))
  {
    exp = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&it));
    assert (exp);
    btor_copy_exp (btor, exp);
  }
  return res;
}

/*------------------------------------------------------------------------*/

/* Note: no need to free returned bit vector,
 *       all bit vectors are maintained via btor->bv_model */
const BtorBitVector *
btor_get_bv_model_aux (Btor *btor,
                       BtorIntHashTable *bv_model,
                       BtorIntHashTable *fun_model,
                       BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (exp);
  assert (!btor_is_proxy_node (exp));

  BtorBitVector *result;
  BtorHashTableData *d;

  /* Note: btor_generate_model generates assignments for all nodes
   *       as non-inverted nodes. Their inverted assignments, however,
   *       are cached (when requested) on demand (see below)! */

  /* Check if we already generated the assignment of exp
   * -> inverted if exp is inverted */
  if ((d = btor_get_int_hash_map (bv_model, btor_exp_get_id (exp))))
    return d->as_ptr;

  /* If not, check if we already generated the assignment of non-inverted exp
   * (i.e., check if we generated it at all) */
  if (BTOR_IS_INVERTED_NODE (exp))
    d = btor_get_int_hash_map (bv_model, BTOR_REAL_ADDR_NODE (exp)->id);

  /* If exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is
   * now a proxy and was therefore regenerated when querying it's
   * assignment via get-value in SMT-LIB v2) */
  if (!d)
  {
    result =
        btor_recursively_compute_assignment (btor, bv_model, fun_model, exp);
    btor_free_bv (btor->mm, result);
    d = btor_get_int_hash_map (bv_model, BTOR_REAL_ADDR_NODE (exp)->id);
  }
  if (!d) return 0;

  result = (BtorBitVector *) d->as_ptr;

  /* Cache assignments of inverted expressions on demand */
  if (BTOR_IS_INVERTED_NODE (exp))
  {
    /* we don't use add_to_bv_model in order to avoid redundant
     * hash table queries and copying/freeing of the resulting bv */
    result = btor_not_bv (btor->mm, result);
    btor_copy_exp (btor, exp);
    btor_add_int_hash_map (bv_model, btor_exp_get_id (exp))->as_ptr = result;
  }

  return result;
}

const BtorBitVector *
btor_get_bv_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_get_bv_model_aux (btor, btor->bv_model, btor->fun_model, exp);
}

const BtorPtrHashTable *
btor_get_fun_model_aux (Btor *btor,
                        BtorIntHashTable *bv_model,
                        BtorIntHashTable *fun_model,
                        BtorNode *exp)
{
  assert (btor);
  assert (fun_model);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!btor_is_proxy_node (exp));

  BtorHashTableData *d;

  assert (btor_is_fun_node (exp));
  d = btor_get_int_hash_map (fun_model, exp->id);

  /* if exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is now
   * a proxy and was therefore regenerated when querying it's assignment via
   * get-value in SMT-LIB v2) */
  if (!d) recursively_compute_function_model (btor, bv_model, fun_model, exp);
  d = btor_get_int_hash_map (fun_model, exp->id);
  if (!d) return 0;

  return (BtorPtrHashTable *) d->as_ptr;
}

const BtorPtrHashTable *
btor_get_fun_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return btor_get_fun_model_aux (btor, btor->bv_model, btor->fun_model, exp);
}

/*------------------------------------------------------------------------*/

void
btor_remove_from_bv_model (Btor *btor,
                           BtorIntHashTable *bv_model,
                           BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (exp);

  BtorHashTableData d;
  uint32_t id;

  id = btor_exp_get_id (exp);
  assert (btor_contains_int_hash_map (bv_model, id));
  btor_remove_int_hash_map (bv_model, id, &d);
  btor_free_bv (btor->mm, d.as_ptr);
  btor_release_exp (btor, exp);
  if (btor_contains_int_hash_map (bv_model, -id))
  {
    btor_remove_int_hash_map (bv_model, id, &d);
    btor_free_bv (btor->mm, d.as_ptr);
    btor_release_exp (btor, exp);
  }
}

/*------------------------------------------------------------------------*/

#if 0
static void
extract_model_from_rhos (Btor * btor, BtorPtrHashTable * fun_model,
			 BtorNode * fun)
{
  int pos;
  BtorNode *arg, *value, *args;
  BtorBitVector *bv_arg, *bv_value;
  BtorBitVectorTuple *t;
  BtorPtrHashTableIterator it;
  BtorPtrHashTable *model = 0;
  BtorArgsIterator ait;
  BtorPtrHashBucket *b;

  if (!fun->rho
      && (!btor_is_lambda_node (fun) || !btor_lambda_get_static_rho (fun)))
    return;

  b = btor_get_ptr_hash_table (fun_model, fun);
  if (b)
    model = b->data.as_ptr;
  
  if (fun->rho)
    {
      btor_init_ptr_hash_table_iterator (&it, fun->rho);
      if (btor_is_lambda_node (fun) && btor_lambda_get_static_rho (fun))
	btor_queue_ptr_hash_table_iterator (&it,
					     btor_lambda_get_static_rho (fun));
    }
  else if (btor_is_lambda_node (fun) && btor_lambda_get_static_rho (fun))
    btor_init_ptr_hash_table_iterator (&it, btor_lambda_get_static_rho (fun));

  while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      value = (BtorNode *) it.bucket->data.as_ptr;
      assert (!BTOR_REAL_ADDR_NODE (value)->parameterized);
      args = btor_next_ptr_hash_table_iterator (&it); 
      assert (BTOR_IS_REGULAR_NODE (args));
      assert (btor_is_args_node (args));
      assert (!args->parameterized);

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
	    bv_arg = btor_get_assignment_bv (btor->mm, arg, 0);
	  else
	    bv_arg = btor_copy_bv (btor->mm, btor_get_bv_model (btor, arg));
	  btor_add_to_bv_tuple (btor->mm, t, bv_arg, pos++);
	  btor_free_bv (btor->mm, bv_arg);
	}

      /* values in 'rho' are encoded, however some values in 'static_rho' might
       * not be encoded and thus we have to obtain the assignment from the
       * constructed model. */
      if (btor_is_encoded_exp (value))
	bv_value = btor_get_assignment_bv (btor->mm, value, 0);
      else
	bv_value = btor_copy_bv (btor->mm, btor_get_bv_model (btor, value));

      if (!model)
	{
	  add_to_fun_model (btor, fun_model, fun, t, bv_value);
	  b = btor_get_ptr_hash_table (fun_model, fun);
	  assert (b);
	  model = b->data.as_ptr;
	}
      /* if static_rho contains arguments with the same assignments, but map
       * to different values, we consider the argument which occurs
       * earlier in static_rho. */
      else if (!btor_get_ptr_hash_table (model, t))
	add_to_fun_model (btor, fun_model, fun, t, bv_value);

      btor_free_bv (btor->mm, bv_value);
      btor_free_bv_tuple (btor->mm, t);
    }
}
#endif

#if 0
BtorNode *
btor_generate_lambda_model_from_fun_model (Btor * btor,
					   BtorNode * exp,
					   const BtorPtrHashTable * model)
{
  assert (btor);
  assert (exp);
  assert (model);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_fun_node (exp));

  uint32_t i;
  BtorNode *uf, *res, *c, *p, *cond, *e_if, *e_else, *tmp, *eq, *ite, *args;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack params, consts;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorTupleSortIterator iit;
  BtorSortId sort;
  BtorPtrHashTable *static_rho;

  static_rho = btor_new_ptr_hash_table (btor->mm, 0, 0);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (consts);

  /* create params from domain sort */
  btor_init_tuple_sort_iterator (&iit, btor,
    btor_get_domain_fun_sort (btor, btor_exp_get_sort_id (exp)));
  while (btor_has_next_tuple_sort_iterator (&iit))
    {
      sort = btor_next_tuple_sort_iterator (&iit);
      p = btor_param_exp (btor, btor_get_width_bitvec_sort (btor, sort), 0); 
      BTOR_PUSH_STACK (btor->mm, params, p);
    }
  uf = btor_uf_exp (btor, btor_exp_get_sort_id (exp), 0);
  args = btor_args_exp (btor, params.start, BTOR_COUNT_STACK (params));
  assert (btor_exp_get_sort_id (args) == btor_get_domain_fun_sort (btor, btor_exp_get_sort_id (uf)));
  e_else = btor_apply_exp (btor, uf, args);
  assert (btor_exp_get_sort_id (e_else)
	  == btor_get_codomain_fun_sort (btor, btor_exp_get_sort_id (uf)));
  btor_release_exp (btor, args);
  btor_release_exp (btor, uf);

  /* generate ITEs */
  ite = 0; res = 0;
  btor_init_ptr_hash_table_iterator (&it, (BtorPtrHashTable *) model);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    {
      value = (BtorBitVector *) it.bucket->data.as_ptr;
      args_tuple = btor_next_ptr_hash_table_iterator (&it);

      /* create condition */
      assert (btor_get_fun_arity (btor, uf) == args_tuple->arity);
      assert (BTOR_EMPTY_STACK (consts));
      assert (BTOR_COUNT_STACK (params) == args_tuple->arity);
      for (i = 0; i < args_tuple->arity; i++)
	{
	  c = btor_const_exp (btor, args_tuple->bv[i]);
	  assert (btor_exp_get_sort_id (c) ==
		  btor_exp_get_sort_id (BTOR_PEEK_STACK (params, i)));
	  BTOR_PUSH_STACK (btor->mm, consts, c);
	}

      assert (!BTOR_EMPTY_STACK (params));
      assert (BTOR_COUNT_STACK (params) == BTOR_COUNT_STACK (consts));
      cond = btor_eq_exp (btor, BTOR_PEEK_STACK (params, 0),
			  BTOR_PEEK_STACK (consts, 0));
      for (i = 1; i < BTOR_COUNT_STACK (params); i++)
	{
	  eq = btor_eq_exp (btor, BTOR_PEEK_STACK (params, i),
			    BTOR_PEEK_STACK (consts, i));
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
      ite = btor_cond_exp (btor, cond, e_if, e_else);

      /* add to static rho */
      btor_add_ptr_hash_table (static_rho, args)->data.as_ptr =
	btor_copy_exp (btor, e_if);

      btor_release_exp (btor, cond);
      btor_release_exp (btor, e_if);
      btor_release_exp (btor, e_else);
      e_else = ite;
    }

  assert (ite);
  if (ite)  /* get rid of compiler warning */
    {
      res = btor_fun_exp (btor, params.start, BTOR_COUNT_STACK (params), ite);
      btor_release_exp (btor, ite);
    }

  while (!BTOR_EMPTY_STACK (params))
    btor_release_exp (btor, BTOR_POP_STACK (params));
  BTOR_RELEASE_STACK (btor->mm, params);
  BTOR_RELEASE_STACK (btor->mm, consts);

  /* res already exists */
  if (((BtorLambdaNode *) res)->static_rho)
    {
      btor_init_ptr_hash_table_iterator (&it, static_rho);
      while (btor_has_next_ptr_hash_table_iterator (&it))
	{
	  btor_release_exp (btor, it.bucket->data.as_ptr);
	  btor_release_exp (btor, btor_next_ptr_hash_table_iterator (&it));
	}
      btor_delete_ptr_hash_table (static_rho);
    }
  else
    ((BtorLambdaNode *) res)->static_rho = static_rho;
  assert (btor_exp_get_sort_id (res) == btor_exp_get_sort_id (exp));
  return res;
}
#endif

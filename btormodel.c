/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
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
delete_array_model (Btor *btor)
{
  assert (btor);

  BitVectorTuple *tup;
  BitVector *value;
  BtorNode *cur;
  BtorHashTableIterator it1, it2;
  BtorPtrHashTable *t;

  if (!btor->array_model) return;

  init_node_hash_table_iterator (&it1, btor->array_model);
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

  btor_delete_ptr_hash_table (btor->array_model);
  btor->array_model = 0;
}

static void
init_array_model (Btor *btor)
{
  assert (btor);

  if (btor->array_model) delete_array_model (btor);

  btor->array_model =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
add_to_array_model (Btor *btor,
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

  b = btor_find_in_ptr_hash_table (btor->array_model, exp);

  if (b)
    model = (BtorPtrHashTable *) b->data.asPtr;
  else
  {
    model = btor_new_ptr_hash_table (btor->mm,
                                     (BtorHashPtr) btor_hash_bv_tuple,
                                     (BtorCmpPtr) btor_compare_bv_tuple);
    btor_insert_in_ptr_hash_table (btor->array_model, btor_copy_exp (btor, exp))
        ->data.asPtr = model;
  }

#if 0
  if (btor_find_in_ptr_hash_table (model, t))
    {
      /* values have to be the same with the same arguments */
      assert (btor_compare_bv (
	(BitVector *) btor_find_in_ptr_hash_table (model, t)->data.asPtr,
	value) == 0);
      return;
    }
#endif
  assert (!btor_find_in_ptr_hash_table (model, t));

  b = btor_insert_in_ptr_hash_table (model, btor_copy_bv_tuple (btor, t));
  b->data.asPtr = btor_copy_bv (btor, value);
}

static BitVector *
get_value_from_array_model (Btor *btor, BtorNode *exp, BitVectorTuple *t)
{
  assert (btor);
  assert (exp);
  assert (t);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_FUN_NODE (exp));

  BtorPtrHashTable *model;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->array_model, exp);

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
  BtorNodePtrStack work_stack, cleanup;
  BtorVoidPtrStack arg_stack;
  BtorNode *cur, *real_cur, *next, *cur_parent;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *assigned;
  BitVector *result = 0, *inv_result, **e;
  BitVectorTuple *t;

  mm = btor->mm;

  assigned = btor_new_ptr_hash_table (mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (cleanup);

  BTOR_PUSH_STACK (mm, work_stack, exp);
  BTOR_PUSH_STACK (mm, work_stack, 0);
  assert (!BTOR_REAL_ADDR_NODE (exp)->eval_mark);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur_parent = BTOR_POP_STACK (work_stack);
    cur        = BTOR_POP_STACK (work_stack);
    real_cur   = BTOR_REAL_ADDR_NODE (cur);
    assert (!real_cur->simplified);

    //      printf ("visit: %s (%d)\n", node2string (cur), real_cur->eval_mark);

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
      result = get_value_from_array_model (btor, cur_parent->e[0], t);
      btor_free_bv_tuple (btor, t);

      if (result)
      {
        //	      printf ("CACHED: %s\n", node2string (cur_parent))
        //	      printf ("fun: %s\n", node2string (real_cur));
        //	      printf ("top: %s\n", node2string (BTOR_TOP_STACK
        //(work_stack)));
        goto PUSH_RESULT;
      }
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
        //	      printf ("NEXT: %s\n", node2string (next));

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
        //	      printf ("ASSIGN: %s (%s)\n", node2string (real_cur),
        // node2string (cur_parent));
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
      //	  assert (!BTOR_IS_ARGS_NODE (real_cur));
      //	  assert (!BTOR_IS_FUN_NODE (real_cur));
      //	  assert (real_cur->arity >= 1);
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
          result = get_value_from_array_model (btor, real_cur->e[0], t);
          if (!result)
          {
            /* value of apply is at last index of e */
            result = e[num_args];
            add_to_array_model (btor, real_cur->e[0], t, result);
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
        case BTOR_ARRAY_VAR_NODE:
          real_cur->eval_mark = 0; /* not inserted into cache */
          result              = btor_assignment_bv (btor, cur_parent, 1);
          goto PUSH_RESULT;
        default:
          /* should be unreachable */
          BTOR_ABORT_MODEL (1, "invalid node type");
      }
    CACHE_AND_PUSH_RESULT:
      if (!real_cur->parameterized)
      {
        assert (!btor_find_in_ptr_hash_table (assignments, real_cur));
        btor_insert_in_ptr_hash_table (assignments, real_cur)->data.asPtr =
            btor_copy_bv (btor, result);
      }
      else
        real_cur->eval_mark = 0;

    PUSH_RESULT_AND_UNASSIGN:
      if (BTOR_IS_LAMBDA_NODE (real_cur) && cur_parent
          && BTOR_IS_APPLY_NODE (cur_parent))
      {
        assert (btor_find_in_ptr_hash_table (assigned, real_cur));
        btor_unassign_params (btor, real_cur);
        btor_remove_from_ptr_hash_table (assigned, real_cur, 0, 0);
        //	    printf ("UNASSIGN: %s (%s)\n", node2string (real_cur),
        // node2string (cur_parent));
      }

    PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (btor, result);
        btor_free_bv (btor, result);
        result = inv_result;
      }

      //	  printf ("  result: "); btor_print_bv (result);
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
  btor_delete_ptr_hash_table (assigned);

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

    //      printf ("p: %s (%d)\n", node2string (parent), pos);

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
      add_to_array_model (btor, exp, t, value);
      btor_free_bv (btor, index);
      btor_free_bv (btor, value);
      btor_free_bv_tuple (btor, t);
    }

    btor_release_exp (btor, r);
    btor_unassign_params (btor, exp);
  }
  BTOR_RELEASE_STACK (btor->mm, candidates);

#if 0
  init_apply_parent_iterator (&it, exp);
  while (has_next_parent_apply_parent_iterator (&it))
    {
      parent = next_parent_apply_parent_iterator (&it);

      if (parent->parameterized)
	continue;

      value = btor_assignment_bv (btor, parent, 1);
      add_to_bv_model (btor, parent, value);

      assert (((BtorArgsNode *) parent->e[1])->arity == 1); 

      tmp = ((BtorArgsNode *) parent->e[1])->e[0]; 
      index = recursively_compute_assignment (btor, tmp, assignments);

      assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (tmp))
	      || btor_find_in_ptr_hash_table (assignments,
		     BTOR_REAL_ADDR_NODE (tmp)));

      add_to_array_model (btor, exp, index, value);

      btor_free_bv (btor, index);
      btor_free_bv (btor, value);
    }
#endif
}

#if 0
static void
compute_array_model (Btor * btor, BtorNode * exp,
		     BtorPtrHashTable * assignments)
{
  assert (btor);
  assert (exp);
  assert (assignments);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARRAY_VAR_NODE (exp));

  BitVector *index, *value;
  BtorNode *parent, *tmp;
  BtorNodeIterator it;
  BitVectorTuple *t;

  init_apply_parent_iterator (&it, exp);
  while (has_next_parent_apply_parent_iterator (&it))
    {
      parent = next_parent_apply_parent_iterator (&it);

      if (parent->parameterized)
	continue;

      value = btor_assignment_bv (btor, parent, 1);
      add_to_bv_model (btor, parent, value);

      assert (((BtorArgsNode *) parent->e[1])->arity == 1); 

      tmp = ((BtorArgsNode *) parent->e[1])->e[0]; 
      index = recursively_compute_assignment (btor, tmp, assignments);

      assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (tmp))
	      || btor_find_in_ptr_hash_table (assignments,
		     BTOR_REAL_ADDR_NODE (tmp)));

      t = new_bv_tuple (btor, 1);
      add_to_bv_tuple (btor, t, index, 0);
      add_to_array_model (btor, exp, t, value);

      btor_free_bv (btor, index);
      btor_free_bv (btor, value);
      free_bv_tuple (btor, t);
    }
}
#endif

static int
cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return BTOR_REAL_ADDR_NODE (a)->id - BTOR_REAL_ADDR_NODE (b)->id;
}

static void
extract_models_from_array_with_model (Btor *btor)
{
  assert (btor);

  int i, pos;
  BtorNode *cur, *arg, *value, *args;
  BitVector *bv_arg, *bv_value;
  BitVectorTuple *t;
  BtorHashTableIterator it;
  BtorArgsIterator ait;

  for (i = 0; i < BTOR_COUNT_STACK (btor->arrays_with_model); i++)
  {
    cur = BTOR_PEEK_STACK (btor->arrays_with_model, i);
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

      add_to_array_model (btor, cur, t, bv_value);
      btor_free_bv (btor, bv_value);
      btor_free_bv_tuple (btor, t);
    }
  }
}

void
btor_generate_model (Btor *btor)
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
  init_array_model (btor);

  BTOR_INIT_STACK (stack);
  assignments = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  extract_models_from_array_with_model (btor);

  init_node_hash_table_iterator (&it, btor->var_rhs);
  queue_node_hash_table_iterator (&it, btor->bv_vars);
  queue_node_hash_table_iterator (&it, btor->array_rhs);
  queue_node_hash_table_iterator (&it, btor->array_vars);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = btor_simplify_exp (btor, next_node_hash_table_iterator (&it));
    BTOR_PUSH_STACK (btor->mm, stack, BTOR_REAL_ADDR_NODE (cur));
  }

  qsort (
      stack.start, BTOR_COUNT_STACK (stack), sizeof (BtorNode *), cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur = BTOR_PEEK_STACK (stack, i);

    // TODO: may be obsolete
    if (BTOR_IS_ARRAY_VAR_NODE (cur))
    {
      //	  printf ("array: %s\n", node2string (cur));
      //	  compute_array_model (btor, cur, assignments);
    }
    // TODO: some parts may be obsolete
    else if (BTOR_IS_LAMBDA_NODE (cur))
    {
      //	  printf ("lambda: %s\n", node2string (cur));
      compute_lambda_model (btor, cur, assignments);
    }
    else
    {
      //	  printf ("bv: %s\n", node2string (cur));
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
  delete_array_model (btor);
}

int
btor_has_bv_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));

  if (!btor->bv_model) return 0;

  return btor_find_in_ptr_hash_table (btor->bv_model, BTOR_REAL_ADDR_NODE (exp))
         != 0;
}

int
btor_has_array_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_FUN_NODE (exp));

  if (!btor->array_model) return 0;

  return btor_find_in_ptr_hash_table (btor->array_model, exp) != 0;
}

static BitVector *
btor_get_bv_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BitVector *result;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->bv_model, BTOR_REAL_ADDR_NODE (exp));

  if (!b) return 0;

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_not_bv (btor, (BitVector *) b->data.asPtr);
  else
    result = btor_copy_bv (btor, (BitVector *) b->data.asPtr);

  return result;
}

static BtorPtrHashTable *
btor_get_array_model (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->array_model, exp);

  if (!b) return 0;

  return (BtorPtrHashTable *) b->data.asPtr;
}

const char *
btor_get_bv_model_str (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_has_bv_model (btor, exp));

  const char *res;
  BitVector *bv;
  // TODO: return 'xxxxx' if we do not have a model for exp

  bv  = btor_get_bv_model (btor, exp);
  res = btor_bv_to_char_bv (btor, bv);
  btor_free_bv (btor, bv);
  return res;
}

void
btor_get_array_model_str (
    Btor *btor, BtorNode *exp, char ***indices, char ***values, int *size)
{
  assert (btor);
  assert (exp);
  assert (indices);
  assert (values);
  assert (size);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_FUN_NODE (exp));

  int i;
  BtorHashTableIterator it;
  BtorPtrHashTable *model;
  BitVector *value;
  BitVectorTuple *t;

  if ((!BTOR_IS_ARRAY_VAR_NODE (exp)
       && ((BtorLambdaNode *) exp)->num_params > 1)
      || !btor->array_model || !btor_has_array_model (btor, exp))
  {
    *size = 0;
    return;
  }

  model = btor_get_array_model (btor, exp);
  assert (model->count > 0);

  *size = (int) model->count;
  BTOR_NEWN (btor->mm, *indices, *size);
  BTOR_NEWN (btor->mm, *values, *size);

  i = 0;
  init_hash_table_iterator (&it, model);
  while (has_next_hash_table_iterator (&it))
  {
    value = (BitVector *) it.bucket->data.asPtr;

    t = (BitVectorTuple *) next_hash_table_iterator (&it);
    assert (t->arity == 1);
    (*indices)[i] = (char *) btor_bv_to_char_bv (btor, t->bv[0]);
    (*values)[i]  = (char *) btor_bv_to_char_bv (btor, value);
    i++;
  }
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2013 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoriter.h"

void
init_apply_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->last_parent;
}

void
init_aeq_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->first_aeq_acond_parent;
}

void
init_acond_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->last_aeq_acond_parent;
}

void
init_full_parent_iterator (BtorFullParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->exp = exp;
  if (BTOR_REAL_ADDR_NODE (exp)->first_parent)
  {
    it->regular_parents_done = 0;
    it->cur                  = BTOR_REAL_ADDR_NODE (exp)->first_parent;
  }
  else
  {
    it->regular_parents_done = 1;
    if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)))
      it->cur = BTOR_REAL_ADDR_NODE (exp)->first_aeq_acond_parent;
    else
      it->cur = 0;
  }
}

BtorNode *
next_parent_apply_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_REAL_ADDR_NODE (BTOR_PREV_PARENT (result));
  assert (BTOR_IS_REGULAR_NODE (result));
  assert (BTOR_IS_APPLY_NODE (result));
  return result;
}

BtorNode *
next_parent_aeq_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_NEXT_AEQ_ACOND_PARENT (result);
  assert (BTOR_IS_ARRAY_EQ_NODE (BTOR_REAL_ADDR_NODE (result)));
  return BTOR_REAL_ADDR_NODE (result);
}

BtorNode *
next_parent_acond_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_PREV_AEQ_ACOND_PARENT (result);
  assert (BTOR_IS_ARRAY_COND_NODE (BTOR_REAL_ADDR_NODE (result)));
  return BTOR_REAL_ADDR_NODE (result);
}

BtorNode *
next_parent_full_parent_iterator (BtorFullParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  if (!it->regular_parents_done)
  {
    it->cur = BTOR_NEXT_PARENT (result);
    /* reached end of regular parent list ? */
    if (!it->cur)
    {
      it->regular_parents_done = 1;
      /* traverse aeq acond parent list */
      if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (it->exp)))
        it->cur = BTOR_REAL_ADDR_NODE (it->exp)->first_aeq_acond_parent;
    }
  }
  else
    it->cur = BTOR_NEXT_AEQ_ACOND_PARENT (result);
  return BTOR_REAL_ADDR_NODE (result);
}

int
has_next_parent_apply_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  /* function child of apply is at position 0, so cur is not tagged */
  return it->cur && BTOR_IS_APPLY_NODE (it->cur);
}

int
has_next_parent_aeq_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  return it->cur && BTOR_IS_ARRAY_EQ_NODE (BTOR_REAL_ADDR_NODE (it->cur));
}

int
has_next_parent_acond_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  return it->cur && BTOR_IS_ARRAY_COND_NODE (BTOR_REAL_ADDR_NODE (it->cur));
}

int
has_next_parent_full_parent_iterator (BtorFullParentIterator *it)
{
  assert (it);
  return it->cur != 0;
}

void
init_args_iterator (BtorArgsIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARGS_NODE (exp));

  it->pos = 0;
  it->exp = exp;
  it->cur = exp->e[0];
}

BtorNode *
next_args_iterator (BtorArgsIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;

  result = it->cur;

  /* end of this args node, continue with next */
  if (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (result)))
  {
    assert (it->pos == 2);
    assert (BTOR_IS_REGULAR_NODE (result));
    it->pos = 0;
    it->exp = result;
    it->cur = result->e[0];
    result  = it->cur;
  }

  /* prepare next argument */
  it->pos++;
  if (it->pos < it->exp->arity)
    it->cur = it->exp->e[it->pos];
  else
    it->cur = 0;

  assert (!BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (result)));
  return result;
}

int
has_next_args_iterator (BtorArgsIterator *it)
{
  assert (it);
  return it->cur != 0;
}

void
init_lambda_iterator (BtorIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_LAMBDA_NODE (exp));

  it->cur = exp;
}

BtorNode *
next_lambda_iterator (BtorIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;
  result  = it->cur;
  it->cur = result->e[1];
  return result;
}

int
has_next_lambda_iterator (BtorIterator *it)
{
  assert (it);
  assert (it->cur);
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (it->cur));
}

void
init_parameterized_iterator (Btor *btor,
                             BtorParameterizedIterator *it,
                             BtorNode *exp)
{
  assert (btor);
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashBucket *b;

  if (BTOR_IS_PARAM_NODE (exp))
  {
    it->num_params = 1;
    it->cur        = exp;
    it->bucket     = 0;
    return;
  }

  b = btor_find_in_ptr_hash_table (btor->parameterized, exp);
  if (b)
  {
    assert (b->data.asPtr);
    it->bucket     = ((BtorPtrHashTable *) b->data.asPtr)->first;
    it->cur        = (BtorNode *) it->bucket->key;
    it->num_params = ((BtorPtrHashTable *) b->data.asPtr)->count;
  }
  else
  {
    it->cur        = 0;
    it->bucket     = 0;
    it->num_params = 0;
  }
}

BtorNode *
next_parameterized_iterator (BtorParameterizedIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;
  result = it->cur;
  if (it->bucket) it->bucket = it->bucket->next;
  it->cur = it->bucket ? (BtorNode *) it->bucket->key : 0;
  return result;
}

int
has_next_parameterized_iterator (BtorParameterizedIterator *it)
{
  assert (it);
  return it->cur != 0;
}

void
init_reversed_node_hash_table_iterator (Btor *btor,
                                        BtorHashTableIterator *it,
                                        BtorPtrHashTable *t)
{
  assert (btor);
  assert (it);
  assert (t);

  it->bucket     = t->last;
  it->cur        = it->bucket ? it->bucket->key : 0;
  it->reversed   = 1;
  it->num_queued = 0;
  it->pos        = 0;
}

void
init_node_hash_table_iterator (Btor *btor,
                               BtorHashTableIterator *it,
                               BtorPtrHashTable *t)
{
  assert (btor);
  assert (it);
  assert (t);

  it->bucket     = t->first;
  it->cur        = it->bucket ? it->bucket->key : 0;
  it->reversed   = 0;
  it->num_queued = 0;
  it->pos        = 0;
}

void
queue_node_hash_table_iterator (BtorHashTableIterator *it, BtorPtrHashTable *t)
{
  assert (it);
  assert (t);
  assert (it->num_queued < BTOR_HASH_TABLE_ITERATOR_STACK_SIZE);

  it->stack[it->num_queued++] = t;
}

BtorNode *
next_node_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);

  BtorNode *res;
  res = (BtorNode *) it->cur;
  if (it->bucket)
    it->bucket = it->reversed ? it->bucket->prev : it->bucket->next;
  if (!it->bucket && it->pos < it->num_queued)
    it->bucket =
        it->reversed ? it->stack[it->pos++]->last : it->stack[it->pos++]->first;

  it->cur = it->bucket ? it->bucket->key : 0;
  return res;
}

int
has_next_node_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  return it->cur != 0;
}

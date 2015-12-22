/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btoriter.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/
/* node iterators					                  */
/*------------------------------------------------------------------------*/

void
btor_init_apply_parent_iterator (BtorNodeIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->last_parent);
}

int
btor_has_next_apply_parent_iterator (BtorNodeIterator *it)
{
  assert (it);
  assert (BTOR_IS_REGULAR_NODE (it->cur));
  /* function child of apply is at position 0, so cur is not tagged */
  return it->cur && BTOR_IS_APPLY_NODE (it->cur);
}

BtorNode *
btor_next_apply_parent_iterator (BtorNodeIterator *it)
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

/*------------------------------------------------------------------------*/

void
btor_init_parent_iterator (BtorNodeIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->first_parent;
}

int
btor_has_next_parent_iterator (BtorNodeIterator *it)
{
  assert (it);
  return it->cur != 0;
}

BtorNode *
btor_next_parent_iterator (BtorNodeIterator *it)
{
  assert (it);

  BtorNode *result;
  result = it->cur;
  assert (result);
  it->cur = BTOR_NEXT_PARENT (result);

  return BTOR_REAL_ADDR_NODE (result);
}

/*------------------------------------------------------------------------*/

void
btor_init_args_iterator (BtorArgsIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARGS_NODE (exp));

  it->pos = 0;
  it->exp = exp;
  it->cur = exp->e[0];
}

int
btor_has_next_args_iterator (BtorArgsIterator *it)
{
  assert (it);
  return it->cur != 0;
}

BtorNode *
btor_next_args_iterator (BtorArgsIterator *it)
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

/*------------------------------------------------------------------------*/

void
btor_init_lambda_iterator (BtorNodeIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_LAMBDA_NODE (exp));

  it->cur = exp;
}

BtorNode *
btor_next_lambda_iterator (BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;
  result  = it->cur;
  it->cur = result->e[1];
  return result;
}

int
btor_has_next_lambda_iterator (BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (it->cur));
}

void
btor_init_param_iterator (BtorNodeIterator *it, BtorNode *exp)
{
  btor_init_lambda_iterator (it, exp);
}

BtorNode *
btor_next_param_iterator (BtorNodeIterator *it)
{
  BtorNode *result;
  result = btor_next_lambda_iterator (it);
  assert (BTOR_IS_PARAM_NODE (result->e[0]));
  return result->e[0];
}

int
btor_has_next_param_iterator (BtorNodeIterator *it)
{
  return btor_has_next_lambda_iterator (it);
}

/*------------------------------------------------------------------------*/

void
btor_init_parameterized_iterator (BtorParameterizedIterator *it,
                                  Btor *btor,
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

  b = btor_get_ptr_hash_table (btor->parameterized, exp);
  if (b)
  {
    assert (b->data.as_ptr);
    it->bucket     = ((BtorPtrHashTable *) b->data.as_ptr)->first;
    it->cur        = (BtorNode *) it->bucket->key;
    it->num_params = ((BtorPtrHashTable *) b->data.as_ptr)->count;
  }
  else
  {
    it->cur        = 0;
    it->bucket     = 0;
    it->num_params = 0;
  }
}

BtorNode *
btor_next_parameterized_iterator (BtorParameterizedIterator *it)
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
btor_has_next_parameterized_iterator (BtorParameterizedIterator *it)
{
  assert (it);
  return it->cur != 0;
}

/*------------------------------------------------------------------------*/

static void
find_next_unique_node (BtorNodeIterator *it)
{
  while (!it->cur && it->pos < it->btor->nodes_unique_table.size)
    it->cur = it->btor->nodes_unique_table.chains[it->pos++];
  assert (it->cur
          || it->num_elements == it->btor->nodes_unique_table.num_elements);
}

void
btor_init_unique_table_iterator (BtorNodeIterator *it, Btor *btor)
{
  assert (btor);
  assert (it);

  it->btor = btor;
  it->pos  = 0;
#ifndef NDEBUG
  it->num_elements = 0;
#endif
  it->cur = 0;
  find_next_unique_node (it);
}

int
btor_has_next_unique_table_iterator (BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur || it->pos >= it->btor->nodes_unique_table.size);
  return it->cur != 0;
}

BtorNode *
btor_next_unique_table_iterator (BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;

  result = it->cur;
#ifndef NDEBUG
  it->num_elements++;
  assert (it->num_elements <= it->btor->nodes_unique_table.num_elements);
  assert (result);
#endif
  it->cur = it->cur->next;
  if (!it->cur) find_next_unique_node (it);
  return result;
}

/*------------------------------------------------------------------------*/
/* hash table iterators						          */
/*------------------------------------------------------------------------*/

void
btor_init_hash_table_iterator (BtorHashTableIterator *it, BtorPtrHashTable *t)
{
  assert (it);
  assert (t);

  it->bucket                  = t->first;
  it->cur                     = it->bucket ? it->bucket->key : 0;
  it->reversed                = false;
  it->num_queued              = 0;
  it->pos                     = 0;
  it->stack[it->num_queued++] = t;
}

void
btor_init_reversed_hash_table_iterator (BtorHashTableIterator *it,
                                        BtorPtrHashTable *t)
{
  assert (it);
  assert (t);

  it->bucket                  = t->last;
  it->cur                     = it->bucket ? it->bucket->key : 0;
  it->reversed                = true;
  it->num_queued              = 0;
  it->pos                     = 0;
  it->stack[it->num_queued++] = t;
}

void
btor_queue_hash_table_iterator (BtorHashTableIterator *it, BtorPtrHashTable *t)
{
  assert (it);
  assert (t);
  assert (it->num_queued < BTOR_HASH_TABLE_ITERATOR_STACK_SIZE);

  /* if initial table is empty, initialize with queued table */
  if (!it->bucket)
  {
    it->bucket = it->reversed ? t->last : t->first;
    it->cur    = it->bucket ? it->bucket->key : 0;
    it->pos += 1;
  }
  else
  {
    it->stack[it->num_queued++] = t;
  }
}

int
btor_has_next_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  return it->cur != 0;
}

void *
btor_next_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);

  void *res;
  res = it->cur;
  if (it->bucket)
    it->bucket = it->reversed ? it->bucket->prev : it->bucket->next;

  while (!it->bucket)
  {
    it->pos += 1;
    if (it->pos >= it->num_queued) break;
    it->bucket =
        it->reversed ? it->stack[it->pos]->last : it->stack[it->pos]->first;
  }

  it->cur = it->bucket ? it->bucket->key : 0;
  return res;
}

BtorPtrHashData *
btor_next_data_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);

  void *res;

  res = &it->bucket->data;
  btor_next_hash_table_iterator (it);
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_init_node_hash_table_iterator (BtorHashTableIterator *it,
                                    BtorPtrHashTable *t)
{
  assert (it);
  assert (t);
  btor_init_hash_table_iterator (it, t);
}

void
btor_init_reversed_node_hash_table_iterator (BtorHashTableIterator *it,
                                             BtorPtrHashTable *t)
{
  assert (it);
  assert (t);
  btor_init_reversed_hash_table_iterator (it, t);
}

void
btor_queue_node_hash_table_iterator (BtorHashTableIterator *it,
                                     BtorPtrHashTable *t)
{
  assert (it);
  assert (t);
  assert (it->num_queued < BTOR_HASH_TABLE_ITERATOR_STACK_SIZE);
  btor_queue_hash_table_iterator (it, t);
}

int
btor_has_next_node_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  return btor_has_next_hash_table_iterator (it);
}

BtorNode *
btor_next_node_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);
  return (BtorNode *) btor_next_hash_table_iterator (it);
}

BtorPtrHashData *
btor_next_data_node_hash_table_iterator (BtorHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);
  return btor_next_data_hash_table_iterator (it);
}

/*------------------------------------------------------------------------*/
/* map iterators							  */
/*------------------------------------------------------------------------*/

void
btor_init_node_map_iterator (BtorNodeMapIterator *it, BtorNodeMap *map)
{
  assert (map);
  btor_init_node_hash_table_iterator (&it->it, map->table);
}

void
btor_init_reversed_node_map_iterator (BtorNodeMapIterator *it, BtorNodeMap *map)
{
  assert (map);
  btor_init_reversed_node_hash_table_iterator (&it->it, map->table);
}

int
btor_has_next_node_map_iterator (BtorNodeMapIterator *it)
{
  return btor_has_next_node_hash_table_iterator (&it->it);
}

void
btor_queue_node_map_iterator (BtorNodeMapIterator *it, BtorNodeMap *map)
{
  assert (map);
  btor_queue_node_hash_table_iterator (&it->it, map->table);
}

BtorNode *
btor_next_node_map_iterator (BtorNodeMapIterator *it)
{
  return btor_next_node_hash_table_iterator (&it->it);
}

BtorPtrHashData *
btor_next_data_node_map_iterator (BtorNodeMapIterator *it)
{
  return btor_next_data_node_hash_table_iterator (&it->it);
}

/*------------------------------------------------------------------------*/

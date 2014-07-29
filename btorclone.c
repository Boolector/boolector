/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2014 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbeta.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormap.h"
#include "btorsat.h"
#include "btorsort.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (BtorNodePtrStackPtr, BtorNodePtrStack *);
BTOR_DECLARE_STACK (BtorPtrHashTablePtrPtr, BtorPtrHashTable **);

static BtorSort *
find_sort (BtorSortUniqueTable *table, BtorSort *sort)
{
  assert (table);
  assert (sort);

  BtorSort *res = 0;

  switch (sort->kind)
  {
    case BTOR_BOOL_SORT: res = btor_bool_sort (table); break;

    case BTOR_BITVEC_SORT:
      res = btor_bitvec_sort (table, sort->bitvec.len);
      break;

    case BTOR_LST_SORT:
      res = btor_lst_sort (table, sort->lst.head, sort->lst.tail);
      break;

    case BTOR_ARRAY_SORT:
      res = btor_array_sort (table, sort->array.index, sort->array.element);
      break;

    case BTOR_FUN_SORT:
      res = btor_fun_sort (table, sort->fun.domain, sort->fun.codomain);
      break;

    case BTOR_TUPLE_SORT:
      res = btor_tuple_sort (
          table, sort->tuple.elements, sort->tuple.num_elements);
      break;

    default: break;
  }
  assert (res);
  /* NOTE: 'res' must be already in 'table' */
  assert (res->refs > 1);
  res->refs--;
  return res;
}

static void
clone_sorts_unique_table (BtorMemMgr *mm,
                          BtorSortUniqueTable *table,
                          BtorSortUniqueTable *res)
{
  assert (mm);
  assert (table);
  assert (res);

  int i, j;
  BtorSort *sort, *csort;
  BtorSortPtrStack sorts, csorts, elements;

  BTOR_INIT_STACK (sorts);
  BTOR_INIT_STACK (csorts);
  BTOR_INIT_STACK (elements);

  BTOR_CNEWN (mm, res->chains, table->size);
  res->id           = 1;
  res->size         = table->size;
  res->num_elements = 0;
  res->mm           = mm;

  btor_sorts_list_sort (mm, table, &sorts);

  for (i = 0; i < BTOR_COUNT_STACK (sorts); i++)
  {
    sort = BTOR_PEEK_STACK (sorts, i);

    switch (sort->kind)
    {
      case BTOR_BOOL_SORT: csort = btor_bool_sort (res); break;

      case BTOR_BITVEC_SORT:
        csort = btor_bitvec_sort (res, sort->bitvec.len);
        break;

      case BTOR_LST_SORT:
        csort = btor_lst_sort (res,
                               find_sort (res, sort->lst.head),
                               find_sort (res, sort->lst.tail));
        break;

      case BTOR_ARRAY_SORT:
        csort = btor_array_sort (res,
                                 find_sort (res, sort->array.index),
                                 find_sort (res, sort->array.element));
        break;

      case BTOR_FUN_SORT:
        csort = btor_fun_sort (res,
                               find_sort (res, sort->fun.domain),
                               find_sort (res, sort->fun.codomain));
        break;

      case BTOR_TUPLE_SORT:
        BTOR_RESET_STACK (elements);
        for (j = 0; j < sort->tuple.num_elements; j++)
          BTOR_PUSH_STACK (
              mm, elements, find_sort (res, sort->tuple.elements[j]));
        csort =
            btor_tuple_sort (res, elements.start, BTOR_COUNT_STACK (elements));
        break;

      default: csort = 0; break;
    }
    assert (csort);
    assert (csort->refs == 1);
    assert (csort->kind == sort->kind);
    csort->id = sort->id;
  }

  /* update sort references (must be the same as in table) */
  btor_sorts_list_sort (mm, res, &csorts);
  assert (BTOR_COUNT_STACK (sorts) == BTOR_COUNT_STACK (csorts));
  for (i = 0; i < BTOR_COUNT_STACK (csorts); i++)
  {
    sort  = BTOR_PEEK_STACK (sorts, i);
    csort = BTOR_PEEK_STACK (csorts, i);
    assert (csort->id == sort->id);
    assert (csort->ext_refs == 0);
    csort->refs     = sort->refs;
    csort->ext_refs = sort->ext_refs;
  }
  res->id = table->id;
  assert (res->num_elements == table->num_elements);
  BTOR_RELEASE_STACK (mm, sorts);
  BTOR_RELEASE_STACK (mm, csorts);
  BTOR_RELEASE_STACK (mm, elements);
}

static BtorNode *
clone_exp (Btor *clone,
           BtorNode *exp,
           BtorNodePtrPtrStack *parents,
           BtorNodePtrPtrStack *nodes,
           BtorPtrHashTablePtrPtrStack *rhos,
           BtorPtrHashTablePtrPtrStack *sapps,
           BtorNodeMap *exp_map,
           BtorAIGMap *aig_map)
{
  assert (clone);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (parents);
  assert (nodes);
  assert (sapps);
  assert (exp_map);

  int i, len;
  BtorNode *res;
  BtorMemMgr *mm;

  mm = clone->mm;

  res = btor_malloc (mm, exp->bytes);
  memcpy (res, exp, exp->bytes);
  if (!aig_map)
  {
    res->tseitin      = 0;
    res->lazy_tseitin = 0;
  }

  /* ----------------- BTOR_BV_VAR_NODE_STRUCT (all nodes) ----------------> */
  if (exp->bits)
  {
    len = strlen (exp->bits);
    BTOR_NEWN (mm, res->bits, len + 1);
    for (i = 0; i < len; i++) res->bits[i] = exp->bits[i];
    res->bits[len] = '\0';
  }

  /* Note: no need to cache aig vectors here (exp->av is unique to exp). */
  if (!BTOR_IS_FUN_NODE (exp) && exp->av)
    res->av = btor_clone_aigvec (exp->av, clone->avmgr, aig_map);
  else
  {
    BTOR_PUSH_STACK_IF (res->rho, mm, *rhos, &res->rho);
    BTOR_PUSH_STACK_IF (exp->rho, mm, *rhos, &exp->rho);
  }

  BTOR_PUSH_STACK_IF (exp->next, mm, *nodes, &res->next);

  /* Note: parent node used during BFS only, pointer is not reset after bfs,
   *	   do not clone do avoid access to invalid nodes */
  res->parent = 0;

  BTOR_PUSH_STACK_IF (exp->simplified, mm, *nodes, &res->simplified);
  res->btor = clone;
  BTOR_PUSH_STACK_IF (exp->first_parent, mm, *parents, &res->first_parent);
  BTOR_PUSH_STACK_IF (exp->last_parent, mm, *parents, &res->last_parent);
  /* <---------------------------------------------------------------------- */

  /* ------------ BTOR_BV_ADDITIONAL_VAR_NODE_STRUCT (all nodes) ----------> */
  if (!BTOR_IS_BV_CONST_NODE (exp))
  {
    if (BTOR_IS_BV_VAR_NODE (exp) || BTOR_IS_PARAM_NODE (exp)
        || BTOR_IS_PROXY_NODE (exp) || BTOR_IS_UF_NODE (exp))
    {
      res->symbol = btor_strdup (mm, exp->symbol);
    }

    if (!BTOR_IS_BV_VAR_NODE (exp) && !BTOR_IS_PARAM_NODE (exp))
    {
      if (exp->arity)
      {
        for (i = 0; i < exp->arity; i++)
        {
          res->e[i] = btor_mapped_node (exp_map, exp->e[i]);
          assert (exp->e[i] != res->e[i]);
          assert (res->e[i]);
        }
      }
      else
      {
        if (BTOR_IS_ARRAY_EQ_NODE (exp) && exp->vreads)
        {
          assert (btor_mapped_node (exp_map, exp->vreads->exp1));
          assert (btor_mapped_node (exp_map, exp->vreads->exp2));
          res->vreads =
              new_exp_pair (clone,
                            btor_mapped_node (exp_map, exp->vreads->exp1),
                            btor_mapped_node (exp_map, exp->vreads->exp2));
        }
      }

      for (i = 0; i < exp->arity; i++)
      {
        BTOR_PUSH_STACK_IF (
            exp->prev_parent[i], mm, *parents, &res->prev_parent[i]);
        BTOR_PUSH_STACK_IF (
            exp->next_parent[i], mm, *parents, &res->next_parent[i]);
      }
    }
  }
  /* <----------------------------------------------------------------------
   */

#if 0
  /* ---------------- BTOR_ARRAY_VAR_NODE_STRUCT (all nodes) --------------> */
  if (BTOR_IS_FUN_NODE (exp) || BTOR_IS_ARRAY_EQ_NODE (exp))
    {
      BTOR_PUSH_STACK_IF (exp->first_aeq_acond_parent,
                          mm, *parents, &res->first_aeq_acond_parent);
      BTOR_PUSH_STACK_IF (exp->last_aeq_acond_parent,
                          mm, *parents, &res->last_aeq_acond_parent);

      /* ----------- BTOR_ARRAY_ADDITIONAL_NODE_STRUCT (all nodes) -------> */
      if (!BTOR_IS_ARRAY_VAR_NODE (exp))
        {
          for (i = 0; i < exp->arity; i++)
            {
              BTOR_PUSH_STACK_IF (exp->prev_aeq_acond_parent[i],
                  mm, *parents, &res->prev_aeq_acond_parent[i]);
              BTOR_PUSH_STACK_IF (exp->next_aeq_acond_parent[i],
                  mm, *parents, &res->next_aeq_acond_parent[i]);
            }
        }
      /* <------------------------------------------------------------------ */
    }
  /* <---------------------------------------------------------------------- */
#endif

  if (BTOR_IS_PARAM_NODE (exp))
  {
    BTOR_PUSH_STACK_IF (((BtorParamNode *) exp)->lambda_exp,
                        mm,
                        *nodes,
                        (BtorNode **) &((BtorParamNode *) res)->lambda_exp);
    BTOR_PUSH_STACK_IF (((BtorParamNode *) exp)->assigned_exp,
                        mm,
                        *nodes,
                        (BtorNode **) &((BtorParamNode *) res)->assigned_exp);
  }

  if (BTOR_IS_LAMBDA_NODE (exp))
  {
    if (((BtorLambdaNode *) exp)->synth_apps)
    {
      BTOR_PUSH_STACK (mm, *sapps, &((BtorLambdaNode *) res)->synth_apps);
      BTOR_PUSH_STACK (mm, *sapps, &((BtorLambdaNode *) exp)->synth_apps);
    }
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) exp)->head,
                        mm,
                        *nodes,
                        (BtorNode **) &((BtorLambdaNode *) res)->head);
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) exp)->body,
                        mm,
                        *nodes,
                        &((BtorLambdaNode *) res)->body);
  }

  if (BTOR_IS_UF_NODE (exp))
  {
    ((BtorUFNode *) res)->num_params = ((BtorUFNode *) exp)->num_params;
    ((BtorUFNode *) res)->sort =
        find_sort (&clone->sorts_unique_table, ((BtorUFNode *) exp)->sort);
    assert (((BtorUFNode *) res)->sort->id == ((BtorUFNode *) exp)->sort->id);
    assert (((BtorUFNode *) res)->sort->refs
            == ((BtorUFNode *) exp)->sort->refs);
  }

  res = BTOR_IS_INVERTED_NODE (exp) ? BTOR_INVERT_NODE (res) : res;
  btor_map_node (exp_map, exp, res);

  return res;
}

static void
clone_node_ptr_stack (BtorMemMgr *mm,
                      BtorNodePtrStack *stack,
                      BtorNodePtrStack *res,
                      BtorNodeMap *exp_map)
{
  assert (stack);
  assert (res);
  assert (exp_map);

  int i;
  BtorNode *cloned_exp;

  BTOR_INIT_STACK (*res);
  assert (BTOR_SIZE_STACK (*stack) || !BTOR_COUNT_STACK (*stack));
  if (BTOR_SIZE_STACK (*stack))
  {
    BTOR_NEWN (mm, res->start, BTOR_SIZE_STACK (*stack));
    res->top = res->start;
    res->end = res->start + BTOR_SIZE_STACK (*stack);

    for (i = 0; i < BTOR_COUNT_STACK (*stack); i++)
    {
      assert ((*stack).start[i]);
      cloned_exp = btor_mapped_node (exp_map, (*stack).start[i]);
      assert (cloned_exp);
      BTOR_PUSH_STACK (mm, *res, cloned_exp);
    }
  }
  assert (BTOR_COUNT_STACK (*stack) == BTOR_COUNT_STACK (*res));
  assert (BTOR_SIZE_STACK (*stack) == BTOR_SIZE_STACK (*res));
}

static void *
mapped_node (const void *map, const void *key)
{
  assert (map);
  assert (key);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  exp        = (BtorNode *) key;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_mapped_node (exp_map, exp);
  assert (cloned_exp);
  return cloned_exp;
}

static void
data_as_node_ptr (BtorMemMgr *mm,
                  const void *map,
                  const void *data_ptr,
                  BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (data_ptr);
  assert (data);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  (void) mm;
  exp        = (BtorNode *) data_ptr;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_mapped_node (exp_map, exp);
  assert (cloned_exp);
  data->asPtr = cloned_exp;
}

static void
data_as_int_ptr (BtorMemMgr *mm,
                 const void *map,
                 const void *data_ptr,
                 BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (data_ptr);
  assert (data);

  (void) mm;
  (void) map;
  data->asInt = (int) (long) data_ptr;
}

static void
data_as_bv_ptr (BtorMemMgr *mm,
                const void *map,
                const void *data_ptr,
                BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (data_ptr);
  assert (data);

  BtorNodeMap *exp_map;

  (void) mm;
  exp_map     = (BtorNodeMap *) map;
  data->asPtr = btor_copy_bv (exp_map->btor, (BitVector *) data_ptr);
}

static void
data_as_bv_htable_ptr (BtorMemMgr *mm,
                       const void *map,
                       const void *data_ptr,
                       BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (data_ptr);
  assert (data);

  BtorPtrHashTable *t;
  BtorHashTableIterator it;
  BtorNodeMap *exp_map;
  BitVectorTuple *key;
  BitVector *value;

  exp_map = (BtorNodeMap *) map;

  t = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv_tuple, (BtorCmpPtr) btor_compare_bv_tuple);

  init_hash_table_iterator (&it, (BtorPtrHashTable *) data_ptr);
  while (has_next_hash_table_iterator (&it))
  {
    value = btor_copy_bv (exp_map->btor, (BitVector *) it.bucket->data.asPtr);
    key   = btor_copy_bv_tuple (
        exp_map->btor, (BitVectorTuple *) next_hash_table_iterator (&it));

    btor_insert_in_ptr_hash_table (t, key)->data.asPtr = value;
  }

  data->asPtr = t;
}

static void
data_as_htable_ptr (BtorMemMgr *mm,
                    const void *map,
                    const void *data_ptr,
                    BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (data_ptr);
  assert (data);

  BtorPtrHashTable *table;
  BtorNodeMap *exp_map;

  table   = (BtorPtrHashTable *) data_ptr;
  exp_map = (BtorNodeMap *) map;

  data->asPtr =
      btor_clone_ptr_hash_table (mm, table, mapped_node, 0, exp_map, 0);
}

static void
clone_nodes_id_table (Btor *clone,
                      BtorNodePtrStack *id_table,
                      BtorNodePtrStack *res,
                      BtorNodeMap *exp_map,
                      BtorAIGMap *aig_map)
{
  assert (id_table);
  assert (res);
  assert (exp_map);

  int i, tag;
  BtorNode **tmp;
  BtorMemMgr *mm;
  BtorNodePtrPtrStack parents, nodes;
  BtorPtrHashTablePtrPtrStack sapps, rhos;
  BtorPtrHashTable **htable, **chtable;

  mm = clone->mm;

  BTOR_INIT_STACK (parents);
  BTOR_INIT_STACK (nodes);
  BTOR_INIT_STACK (sapps);
  BTOR_INIT_STACK (rhos);

  BTOR_INIT_STACK (*res);
  assert (BTOR_SIZE_STACK (*id_table) || !BTOR_COUNT_STACK (*id_table));

  if (BTOR_SIZE_STACK (*id_table))
  {
    BTOR_NEWN (mm, res->start, BTOR_SIZE_STACK (*id_table));
    res->top      = res->start + BTOR_COUNT_STACK (*id_table);
    res->end      = res->start + BTOR_SIZE_STACK (*id_table);
    res->start[0] = 0;

    /* first element (id = 0) is empty */
    for (i = 1; i < BTOR_COUNT_STACK (*id_table); i++)
    {
      res->start[i] = id_table->start[i] ? clone_exp (clone,
                                                      id_table->start[i],
                                                      &parents,
                                                      &nodes,
                                                      &rhos,
                                                      &sapps,
                                                      exp_map,
                                                      aig_map)
                                         : id_table->start[i];
      assert (!id_table->start[i] || res->start[i]->id == i);
    }
  }
  assert (BTOR_COUNT_STACK (*res) == BTOR_COUNT_STACK (*id_table));
  assert (BTOR_SIZE_STACK (*res) == BTOR_SIZE_STACK (*id_table));

  /* update children, parent, lambda and next pointers of expressions */
  while (!BTOR_EMPTY_STACK (nodes))
  {
    tmp = BTOR_POP_STACK (nodes);
    assert (*tmp);
    *tmp = btor_mapped_node (exp_map, *tmp);
    assert (*tmp);
  }

  while (!BTOR_EMPTY_STACK (parents))
  {
    tmp = BTOR_POP_STACK (parents);
    assert (*tmp);
    tag  = BTOR_GET_TAG_NODE (*tmp);
    *tmp = btor_mapped_node (exp_map, BTOR_REAL_ADDR_NODE (*tmp));
    assert (*tmp);
    *tmp = BTOR_TAG_NODE (*tmp, tag);
  }

  /* clone rhos tables */
  while (!BTOR_EMPTY_STACK (rhos))
  {
    htable   = BTOR_POP_STACK (rhos);
    chtable  = BTOR_POP_STACK (rhos);
    *chtable = btor_clone_ptr_hash_table (
        mm, *htable, mapped_node, data_as_node_ptr, exp_map, exp_map);
  }

  /* clone synth_apps of lambda nodes */
  while (!BTOR_EMPTY_STACK (sapps))
  {
    htable  = BTOR_POP_STACK (sapps);
    chtable = BTOR_POP_STACK (sapps);
    if (aig_map)
    {
      *chtable =
          btor_clone_ptr_hash_table (mm, *htable, mapped_node, 0, exp_map, 0);
    }
    else
    {
      BtorNode *cur;
      BtorHashTableIterator it;
      init_node_hash_table_iterator (&it, *htable);
      while (has_next_node_hash_table_iterator (&it))
      {
        cur = next_node_hash_table_iterator (&it);
        btor_release_exp (clone, BTOR_PEEK_STACK (*res, cur->id));
      }
      *chtable = 0;
    }
  }

  BTOR_RELEASE_STACK (mm, parents);
  BTOR_RELEASE_STACK (mm, nodes);
  BTOR_RELEASE_STACK (mm, rhos);
  BTOR_RELEASE_STACK (mm, sapps);
}

static void
clone_nodes_unique_table (BtorMemMgr *mm,
                          BtorNodeUniqueTable *table,
                          BtorNodeUniqueTable *res,
                          BtorNodeMap *exp_map)
{
  assert (mm);
  assert (table);
  assert (res);
  assert (exp_map);

  int i;

  BTOR_CNEWN (mm, res->chains, table->size);
  res->size         = table->size;
  res->num_elements = table->num_elements;

  for (i = 0; i < table->size; i++)
  {
    if (!table->chains[i]) continue;
    res->chains[i] = btor_mapped_node (exp_map, table->chains[i]);
    assert (res->chains[i]);
  }
}

#define MEM_PTR_HASH_TABLE(table)                                             \
  ((table) ? sizeof (*(table)) + (table)->size * sizeof (BtorPtrHashBucket *) \
                 + (table)->count * sizeof (BtorPtrHashBucket)                \
           : 0)

#define CHKCLONE_MEM_PTR_HASH_TABLE(table)         \
  do                                               \
  {                                                \
    assert (MEM_PTR_HASH_TABLE (btor->table)       \
            == MEM_PTR_HASH_TABLE (clone->table)); \
  } while (0)

#define CLONE_PTR_HASH_TABLE(table)                                           \
  do                                                                          \
  {                                                                           \
    clone->table =                                                            \
        btor_clone_ptr_hash_table (mm, btor->table, mapped_node, 0, emap, 0); \
    CHKCLONE_MEM_PTR_HASH_TABLE (table);                                      \
  } while (0)

#define CLONE_PTR_HASH_TABLE_ASPTR(table, data_ptr_func)          \
  do                                                              \
  {                                                               \
    BTORLOG_TIMESTAMP (delta);                                    \
    clone->table = btor_clone_ptr_hash_table (                    \
        mm, btor->table, mapped_node, data_ptr_func, emap, emap); \
    BTORLOG ("  clone " #table " table: %.3f s",                  \
             (btor_time_stamp () - delta));                       \
    CHKCLONE_MEM_PTR_HASH_TABLE (table);                          \
  } while (0)

static Btor *
clone_aux_btor (Btor *btor,
                BtorNodeMap **exp_map,
                BtorAIGMap **aig_map,
                int exp_layer_only)
{
  assert (btor);

  Btor *clone;
  BtorNodeMap *emap = 0;
  BtorAIGMap *amap  = 0;
  BtorMemMgr *mm;
  double start, delta;
  int len;
  char *prefix, *clone_prefix;
#ifndef NDEBUG
  int i;
  size_t allocated, amap_size = 0, amap_count = 0, emap_size, emap_count;
  BtorNode *cur;
  BtorAIGMgr *amgr;
  BtorPtrHashBucket *b, *cb;
  BtorBVAssignment *bvass;
  BtorArrayAssignment *arrass;
  BtorHashTableIterator it;
  BtorSortPtrStack sorts;
  BtorSort *sort;
  char **ind, **val;
  amgr = exp_layer_only ? 0 : btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
#endif

  BTORLOG ("start cloning btor %p ...", btor);
  start = btor_time_stamp ();

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, clone);
  memcpy (clone, btor, sizeof (Btor));
  clone->mm = mm;

  if (exp_layer_only)
  {
    /* reset */
    clone->btor_sat_btor_called = 0;
    clone->valid_assignments    = 0;
    btor_reset_time_btor (clone);
    btor_reset_stats_btor (clone);
  }

  assert ((allocated = sizeof (Btor)) == clone->mm->allocated);

  BTOR_INIT_STACK (clone->stats.lemmas_size);
  if (BTOR_SIZE_STACK (btor->stats.lemmas_size) > 0)
  {
    BTOR_CNEWN (mm,
                clone->stats.lemmas_size.start,
                BTOR_SIZE_STACK (btor->stats.lemmas_size));
    clone->stats.lemmas_size.end = clone->stats.lemmas_size.start
                                   + BTOR_SIZE_STACK (btor->stats.lemmas_size);
    clone->stats.lemmas_size.top = clone->stats.lemmas_size.start
                                   + BTOR_COUNT_STACK (btor->stats.lemmas_size);
    memcpy (clone->stats.lemmas_size.start,
            btor->stats.lemmas_size.start,
            BTOR_SIZE_STACK (btor->stats.lemmas_size) * sizeof (int));
  }
  assert (BTOR_SIZE_STACK (btor->stats.lemmas_size)
          == BTOR_SIZE_STACK (clone->stats.lemmas_size));
  assert (BTOR_COUNT_STACK (btor->stats.lemmas_size)
          == BTOR_COUNT_STACK (clone->stats.lemmas_size));
  assert (
      (allocated += BTOR_SIZE_STACK (btor->stats.lemmas_size) * sizeof (int))
      == clone->mm->allocated);

  if (exp_layer_only)
  {
    clone->bv_assignments = btor_new_bv_assignment_list (mm);
    assert ((allocated += sizeof (BtorBVAssignmentList))
            == clone->mm->allocated);
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    clone->bv_assignments =
        btor_clone_bv_assignment_list (clone->mm, btor->bv_assignments);
    BTORLOG ("  clone BV assignments: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
    for (bvass = btor->bv_assignments->first; bvass; bvass = bvass->next)
      allocated += sizeof (BtorBVAssignment)
                   + strlen (btor_get_bv_assignment_str (bvass));
    assert ((allocated += sizeof (BtorBVAssignmentList))
            == clone->mm->allocated);
#endif
  }

  if (exp_layer_only)
  {
    clone->array_assignments = btor_new_array_assignment_list (mm);
    assert ((allocated += sizeof (BtorArrayAssignmentList))
            == clone->mm->allocated);
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    clone->array_assignments =
        btor_clone_array_assignment_list (clone->mm, btor->array_assignments);
    BTORLOG ("  clone array assignments: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
    for (arrass = btor->array_assignments->first; arrass; arrass = arrass->next)
    {
      allocated +=
          sizeof (BtorArrayAssignment) + 2 * arrass->size * sizeof (char *);
      btor_get_array_assignment_indices_values (
          arrass, &ind, &val, arrass->size);
      for (i = 0; i < arrass->size; i++)
        allocated += strlen (ind[i]) + strlen (val[i]);
    }
    assert ((allocated += sizeof (BtorArrayAssignmentList))
            == clone->mm->allocated);
#endif
  }

  if (exp_layer_only)
  {
    clone->avmgr = btor_new_aigvec_mgr (mm);
    assert ((allocated += sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr)
                          + sizeof (BtorSATMgr)
                          + sizeof (BtorAIG *)) /* BtorAIGUniqueTable chains */
            == clone->mm->allocated);
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    clone->avmgr = btor_clone_aigvec_mgr (mm, btor->avmgr);
    BTORLOG ("  clone AIG mgr: %.3f s", (btor_time_stamp () - delta));
    assert ((allocated +=
             sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr) + sizeof (BtorSATMgr)
             + (amgr->smgr->solver ? sizeof (BtorLGL) : 0)
             + (amgr->smgr->optstr ? strlen (amgr->smgr->optstr) + 1 : 0))
            == clone->mm->allocated);

    amap = btor_new_aig_map (clone,
                             btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                             btor_get_aig_mgr_aigvec_mgr (clone->avmgr));
    assert ((allocated += sizeof (*amap) + sizeof (*(amap->table)))
            == clone->mm->allocated);

    BTORLOG_TIMESTAMP (delta);
    btor_clone_aigs (btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                     btor_get_aig_mgr_aigvec_mgr (clone->avmgr),
                     amap);
    BTORLOG ("  clone AIGs: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
    assert ((allocated += amap->table->size * sizeof (BtorPtrHashBucket *)
                          + amap->table->count * sizeof (BtorPtrHashBucket)
                          + amap->table->count * sizeof (BtorAIG)
                          + amgr->table.size * sizeof (BtorAIG *)
                          + BTOR_SIZE_STACK (amgr->id2aig) * sizeof (BtorAIG *))
            == clone->mm->allocated);
    amap_size  = amap->table->size;
    amap_count = amap->table->count;
#endif
  }

  BTORLOG_TIMESTAMP (delta);
  clone_sorts_unique_table (
      mm, &btor->sorts_unique_table, &clone->sorts_unique_table);
  BTORLOG ("  clone sorts unique table: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  allocated += btor->sorts_unique_table.size * sizeof (BtorSort *)
               + btor->sorts_unique_table.num_elements * sizeof (BtorSort);
  BTOR_INIT_STACK (sorts);
  btor_sorts_list_sort (btor->mm, &btor->sorts_unique_table, &sorts);
  for (i = 0; i < BTOR_COUNT_STACK (sorts); i++)
  {
    sort = BTOR_PEEK_STACK (sorts, i);
    if (sort->kind != BTOR_TUPLE_SORT) continue;
    allocated += sort->tuple.num_elements * sizeof (BtorSort *);
  }
  BTOR_RELEASE_STACK (btor->mm, sorts);
  assert (allocated == clone->mm->allocated);
#endif

  emap = btor_new_node_map (clone);
  assert ((allocated += sizeof (*emap) + sizeof (*(emap)->table))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone_nodes_id_table (
      clone, &btor->nodes_id_table, &clone->nodes_id_table, emap, amap);
  BTORLOG ("  clone nodes id table: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  int vread_bytes = 0;
  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    if (exp_layer_only && cur->vread && cur->refs == 1)
    {
      vread_bytes += cur->bytes;
      continue;
    }
    allocated += cur->bytes;
    if (cur->bits) allocated += strlen (cur->bits) + 1;
    if (!BTOR_IS_FUN_NODE (cur) && cur->av)
    {
      if (!exp_layer_only)
        allocated += sizeof (*(cur->av)) + cur->len * sizeof (BtorAIG *);
    }
    else if (cur->rho)
      allocated += MEM_PTR_HASH_TABLE (cur->rho);
    if (!BTOR_IS_BV_CONST_NODE (cur)
        && (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_PARAM_NODE (cur)
            || BTOR_IS_PROXY_NODE (cur) || BTOR_IS_UF_NODE (cur)))
      allocated += cur->symbol ? strlen (cur->symbol) + 1 : 0;
    if (BTOR_IS_ARRAY_EQ_NODE (cur) && cur->vreads)
      allocated += sizeof (BtorNodePair);
    if (!exp_layer_only && BTOR_IS_LAMBDA_NODE (cur)
        && ((BtorLambdaNode *) cur)->synth_apps)
      allocated += MEM_PTR_HASH_TABLE (((BtorLambdaNode *) cur)->synth_apps);
  }
  allocated -= vread_bytes;
  if (amap)
  {
    if (amap->table->size - amap_size)
      allocated +=
          (amap->table->size - amap_size) * sizeof (BtorPtrHashBucket *);
    if (amap->table->count - amap_count)
      allocated += (amap->table->count - amap_count)
                   * (sizeof (BtorPtrHashBucket) + sizeof (BtorAIG));
  }
  allocated += emap->table->size * sizeof (BtorPtrHashBucket *)
               + emap->table->count * sizeof (BtorPtrHashBucket)
               + BTOR_SIZE_STACK (btor->nodes_id_table) * sizeof (BtorNode *);
  assert (allocated == clone->mm->allocated);
  emap_size  = emap->table->size;
  emap_count = emap->table->count;
#endif

  clone->true_exp = btor_mapped_node (emap, btor->true_exp);
  assert (clone->true_exp);
  assert (emap->table->count == emap_count);
  /* btor_mapped_node might cause hash table enlargement if size == count */
  assert ((allocated += (emap->table->size - emap_size) * sizeof (BtorNode *))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone_nodes_unique_table (
      mm, &btor->nodes_unique_table, &clone->nodes_unique_table, emap);
  BTORLOG ("  clone nodes unique table: %.3f s", (btor_time_stamp () - delta));
  assert ((allocated += btor->nodes_unique_table.size * sizeof (BtorNode *))
          == clone->mm->allocated);

  CLONE_PTR_HASH_TABLE (bv_vars);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->bv_vars))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (ufs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->ufs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (lambdas);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->lambdas))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (substitutions, data_as_node_ptr);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->substitutions))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (lod_cache);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->lod_cache))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (varsubst_constraints, data_as_node_ptr);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->varsubst_constraints))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (embedded_constraints);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->embedded_constraints))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (unsynthesized_constraints);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->unsynthesized_constraints))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (synthesized_constraints);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->synthesized_constraints))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (assumptions);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->assumptions))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (var_rhs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->var_rhs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (array_rhs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->array_rhs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (bv_model, data_as_bv_ptr);
#ifndef NDEBUG
  if (btor->bv_model)
  {
    for (b = btor->bv_model->first, cb = clone->bv_model->first; b;
         b = b->next, cb = cb->next)
    {
      assert (btor_size_bv ((BitVector *) b->data.asPtr)
              == btor_size_bv ((BitVector *) cb->data.asPtr));
      allocated += btor_size_bv ((BitVector *) cb->data.asPtr);
    }
  }
#endif
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->bv_model))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (array_model, data_as_bv_htable_ptr);
#ifndef NDEBUG
  if (btor->array_model)
  {
    for (b = btor->array_model->first, cb = clone->array_model->first; b;
         b = b->next, cb = cb->next)
    {
      assert (MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) b->data.asPtr)
              == MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cb->data.asPtr));
      allocated += MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cb->data.asPtr);

      init_hash_table_iterator (&it, ((BtorPtrHashTable *) cb->data.asPtr));
      while (has_next_hash_table_iterator (&it))
      {
        allocated += btor_size_bv ((BitVector *) it.bucket->data.asPtr);
        allocated += btor_size_bv_tuple (
            (BitVectorTuple *) next_hash_table_iterator (&it));
      }
    }
  }
#endif
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->array_model))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone_node_ptr_stack (
      mm, &btor->functions_with_model, &clone->functions_with_model, emap);
  BTORLOG ("  clone functions_with_model: %.3f s", btor_time_stamp () - delta);
  assert ((allocated +=
           BTOR_SIZE_STACK (btor->functions_with_model) * sizeof (BtorNode *))
          == clone->mm->allocated);

  CLONE_PTR_HASH_TABLE_ASPTR (cache, data_as_node_ptr);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->cache))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone->parameterized = btor_clone_ptr_hash_table (
      mm, btor->parameterized, mapped_node, data_as_htable_ptr, emap, emap);
  BTORLOG ("  clone parameterized table: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  CHKCLONE_MEM_PTR_HASH_TABLE (parameterized);
  allocated += MEM_PTR_HASH_TABLE (btor->parameterized);
  for (b = btor->parameterized->first, cb = clone->parameterized->first; b;
       b = b->next, cb = cb->next)
  {
    assert (MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) b->data.asPtr)
            == MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cb->data.asPtr));
    allocated += MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) b->data.asPtr);
  }
  assert (allocated == clone->mm->allocated);
#endif

  if (btor->score)
  {
    clone->score = btor_clone_ptr_hash_table (
        mm, btor->score, mapped_node, data_as_htable_ptr, emap, emap);
    BTORLOG ("  clone score table: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
    CHKCLONE_MEM_PTR_HASH_TABLE (score);
    allocated += MEM_PTR_HASH_TABLE (btor->score);
    for (b = btor->score->first, cb = clone->score->first; b;
         b = b->next, cb = cb->next)
    {
      assert (MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) b->data.asPtr)
              == MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cb->data.asPtr));
      allocated += MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) b->data.asPtr);
    }
    assert (allocated == clone->mm->allocated);
#endif
  }

  if (btor->score_depth)
  {
    CLONE_PTR_HASH_TABLE_ASPTR (score_depth, data_as_int_ptr);
    assert ((allocated += MEM_PTR_HASH_TABLE (btor->score_depth))
            == clone->mm->allocated);
  }

  if (exp_layer_only)
  {
    BtorNode *exp;
    BtorNodePtrStack stack;
    BtorHashTableIterator it;

    BTOR_INIT_STACK (stack);
    init_node_hash_table_iterator (&it, clone->synthesized_constraints);
    while (has_next_node_hash_table_iterator (&it))
    {
      exp = next_node_hash_table_iterator (&it);
      BTOR_REAL_ADDR_NODE (exp)->constraint = 0;
      BTOR_PUSH_STACK (btor->mm, stack, exp);
    }
    btor_delete_ptr_hash_table (clone->synthesized_constraints);
    clone->synthesized_constraints =
        btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    while (!BTOR_EMPTY_STACK (stack))
    {
      exp = BTOR_POP_STACK (stack);
      assert (!BTOR_REAL_ADDR_NODE (exp)->constraint);
      if (!btor_find_in_ptr_hash_table (clone->synthesized_constraints, exp))
        btor_insert_in_ptr_hash_table (clone->unsynthesized_constraints, exp);
    }
    assert (clone->unsynthesized_constraints->count
            || clone->embedded_constraints->count);
    BTOR_RELEASE_STACK (btor->mm, stack);
  }

  clone->clone          = NULL;
  clone->apitrace       = NULL;
  clone->close_apitrace = 0;

  clone_prefix = "clone ";
  len          = btor->msg_prefix ? strlen (btor->msg_prefix) : 0;
  len += strlen (clone_prefix) + 3;
  BTOR_NEWN (clone->mm, prefix, len + 1);
  sprintf (prefix,
           "[%s] %s",
           clone_prefix,
           btor->msg_prefix ? btor->msg_prefix : "");
  btor_set_msg_prefix_btor (clone, prefix);
  BTOR_DELETEN (clone->mm, prefix, len + 1);

  if (aig_map)
    *aig_map = amap;
  else
  {
    if (!exp_layer_only) btor_delete_aig_map (amap);
  }

  if (exp_map)
    *exp_map = emap;
  else
    btor_delete_node_map (emap);

  btor->time.cloning += btor_time_stamp () - start;
  BTORLOG ("cloning total: %.3f s", btor->time.cloning);

  return clone;
}

Btor *
btor_clone_btor (Btor *btor)
{
  assert (btor);
  return clone_aux_btor (btor, 0, 0, 0);
}

Btor *
btor_clone_exp_layer (Btor *btor, BtorNodeMap **exp_map, BtorAIGMap **aig_map)
{
  assert (btor);
  return clone_aux_btor (btor, exp_map, aig_map, 1);
}

BtorNode *
btor_recursively_rebuild_exp_clone (Btor *btor,
                                    Btor *clone,
                                    BtorNode *exp,
                                    BtorNodeMap *exp_map)
{
  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  assert (exp_map);

  int i, rwl;
  BtorNode *real_exp, *cur, *cur_clone, *e[3];
  BtorNodePtrStack work_stack, unmark_stack;
#ifndef NDEBUG
  BtorNodeMap *key_map = btor_new_node_map (btor);
#endif

  // FIXME lemmas are currently built with rwl1 (in parent)
  rwl = clone->options.rewrite_level.val;
  if (clone->options.rewrite_level.val > 0)
    btor_set_opt (clone, "rewrite_level", 1);
  //

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_PUSH_STACK (btor->mm, work_stack, real_exp);
  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));

    if (btor_mapped_node (exp_map, cur)) continue;

    if (cur->clone_mark == 2) continue;

    if (cur->clone_mark == 0)
    {
      cur->clone_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);
      BTOR_PUSH_STACK (btor->mm, work_stack, cur);
      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, work_stack, cur->e[i]);
    }
    else
    {
      assert (cur->clone_mark == 1);
      assert (!btor_mapped_node (exp_map, cur));
      assert (!BTOR_IS_PROXY_NODE (cur));
      for (i = 0; i < cur->arity; i++)
      {
        e[i] = btor_mapped_node (exp_map, cur->e[i]);
        assert (e[i]);
      }
      switch (cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          cur_clone = btor_const_exp (clone, cur->bits);
          break;
        case BTOR_BV_VAR_NODE:
          cur_clone = btor_var_exp (clone, cur->len, cur->symbol);
          break;
        case BTOR_PARAM_NODE:
          cur_clone = btor_param_exp (clone, cur->len, cur->symbol);
          break;
        case BTOR_UF_NODE:
          cur_clone = btor_uf_exp (clone,
                                   find_sort (&clone->sorts_unique_table,
                                              ((BtorUFNode *) cur)->sort),
                                   cur->symbol);
          break;
        case BTOR_SLICE_NODE:
          cur_clone = btor_slice_exp (clone, e[0], cur->upper, cur->lower);
          break;
        case BTOR_AND_NODE: cur_clone = btor_and_exp (clone, e[0], e[1]); break;
        case BTOR_BEQ_NODE:
        case BTOR_FEQ_NODE: cur_clone = btor_eq_exp (clone, e[0], e[1]); break;
        case BTOR_ADD_NODE: cur_clone = btor_add_exp (clone, e[0], e[1]); break;
        case BTOR_MUL_NODE: cur_clone = btor_mul_exp (clone, e[0], e[1]); break;
        case BTOR_ULT_NODE: cur_clone = btor_ult_exp (clone, e[0], e[1]); break;
        case BTOR_SLL_NODE: cur_clone = btor_sll_exp (clone, e[0], e[1]); break;
        case BTOR_SRL_NODE: cur_clone = btor_srl_exp (clone, e[0], e[1]); break;
        case BTOR_UDIV_NODE:
          cur_clone = btor_udiv_exp (clone, e[0], e[1]);
          break;
        case BTOR_UREM_NODE:
          cur_clone = btor_urem_exp (clone, e[0], e[1]);
          break;
        case BTOR_CONCAT_NODE:
          cur_clone = btor_concat_exp (clone, e[0], e[1]);
          break;
        case BTOR_LAMBDA_NODE:
          assert (!btor_param_cur_assignment (e[0]));
          BTOR_PARAM_SET_LAMBDA_NODE (e[0], 0);
          cur_clone = btor_lambda_exp (clone, e[0], e[1]);
          break;
        case BTOR_APPLY_NODE:
          // FIXME use btor_apply_exp as soon as applies are
          // generated with rewriting (currently without)
          // cur_clone = btor_apply_exp (clone, e[0], e[1]);
          cur_clone = btor_apply_exp_node (clone, e[0], e[1]);
          break;
        case BTOR_ARGS_NODE:
          cur_clone = btor_args_exp (clone, cur->arity, e);
          break;
        default:
          assert (BTOR_IS_BV_COND_NODE (cur));
          cur_clone = btor_cond_exp (clone, e[0], e[1], e[2]);
      }
      btor_map_node (exp_map, cur, cur_clone);
#ifndef NDEBUG
      assert (!btor_mapped_node (key_map, cur_clone));
      assert (cur->kind == cur_clone->kind);
      btor_map_node (key_map, cur_clone, cur);
#endif
      btor_release_exp (clone, cur_clone);
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->clone_mark = 0;

  BTOR_RELEASE_STACK (btor->mm, work_stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);

  // FIXME lemmas are currently built with rwl1 (in parent)
  btor_set_opt (clone, "rewrite_level", rwl);
  //
#ifndef NDEBUG
  btor_delete_node_map (key_map);
#endif
  return btor_copy_exp (clone, btor_mapped_node (exp_map, exp));
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Aina Niemetz.
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
#include "btormsg.h"
#include "btorsat.h"
#include "btorsort.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (BtorNodePtrStackPtr, BtorNodePtrStack *);
BTOR_DECLARE_STACK (BtorPtrHashTablePtrPtr, BtorPtrHashTable **);

static void
clone_sorts_unique_table (BtorMemMgr *mm,
                          BtorSortUniqueTable *table,
                          BtorSortUniqueTable *res)
{
  assert (mm);
  assert (table);
  assert (res);

  int i, j;
  BtorSort *sort, *csort, *tmp;
  BtorSortPtrStack elements;

  BTOR_INIT_STACK (elements);

  BTOR_CNEWN (mm, res->chains, table->size);
  res->size         = table->size;
  res->num_elements = 0;
  res->mm           = mm;
  BTOR_INIT_STACK (res->id2sort);

  for (i = 0; i < BTOR_COUNT_STACK (table->id2sort); i++)
  {
    sort = BTOR_PEEK_STACK (table->id2sort, i);

    if (!sort)
    {
      BTOR_PUSH_STACK (res->mm, res->id2sort, 0);
      continue;
    }

    switch (sort->kind)
    {
      case BTOR_BOOL_SORT: csort = btor_bool_sort (res); break;

      case BTOR_BITVEC_SORT:
        csort = btor_bitvec_sort (res, sort->bitvec.len);
        break;

      case BTOR_LST_SORT:
        csort =
            btor_lst_sort (res,
                           BTOR_PEEK_STACK (res->id2sort, sort->lst.head->id),
                           BTOR_PEEK_STACK (res->id2sort, sort->lst.tail->id));
        break;

      case BTOR_ARRAY_SORT:
        csort = btor_array_sort (
            res,
            BTOR_PEEK_STACK (res->id2sort, sort->array.index->id),
            BTOR_PEEK_STACK (res->id2sort, sort->array.element->id));
        break;

      case BTOR_FUN_SORT:
        tmp = BTOR_PEEK_STACK (res->id2sort, sort->fun.domain->id);
        assert (tmp);
        if (sort->fun.arity > 1)
        {
          assert (sort->fun.domain->kind == BTOR_TUPLE_SORT);
          assert (tmp->kind == BTOR_TUPLE_SORT);
          assert (sort->fun.arity == tmp->tuple.num_elements);
          csort = btor_fun_sort (
              res,
              tmp->tuple.elements,
              sort->fun.arity,
              BTOR_PEEK_STACK (res->id2sort, sort->fun.codomain->id));
        }
        else
        {
          assert (sort->fun.domain->kind != BTOR_TUPLE_SORT
                  && sort->fun.domain->kind != BTOR_LST_SORT);
          csort = btor_fun_sort (
              res,
              &tmp,
              1,
              BTOR_PEEK_STACK (res->id2sort, sort->fun.codomain->id));
        }
        break;

      case BTOR_TUPLE_SORT:
        BTOR_RESET_STACK (elements);
        for (j = 0; j < sort->tuple.num_elements; j++)
          BTOR_PUSH_STACK (
              mm,
              elements,
              BTOR_PEEK_STACK (res->id2sort, sort->tuple.elements[j]->id));
        csort =
            btor_tuple_sort (res, elements.start, BTOR_COUNT_STACK (elements));
        break;

      default: csort = 0; break;
    }
    assert (csort);
    assert (csort->refs == 1);
    assert (csort->id == sort->id);
    assert (csort->kind == sort->kind);
    assert (csort->table != sort->table);
  }

  /* update sort references (must be the same as in table) */
  assert (BTOR_COUNT_STACK (table->id2sort) == BTOR_COUNT_STACK (res->id2sort));
  for (i = 0; i < BTOR_COUNT_STACK (res->id2sort); i++)
  {
    sort  = BTOR_PEEK_STACK (table->id2sort, i);
    csort = BTOR_PEEK_STACK (res->id2sort, i);
    if (!sort)
    {
      assert (!csort);
      continue;
    }
    assert (csort->id == sort->id);
    assert (csort->parents == sort->parents);
    assert (csort->ext_refs == 0);
    assert (sort->refs == csort->refs - 1 + sort->refs - sort->parents);
    csort->refs     = sort->refs;
    csort->ext_refs = sort->ext_refs;
  }
  assert (res->num_elements == table->num_elements);
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
  BtorParamNode *param;
  BtorLambdaNode *lambda;
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

  if (exp->invbits)
  {
    len = strlen (exp->invbits);
    BTOR_NEWN (mm, res->invbits, len + 1);
    for (i = 0; i < len; i++) res->invbits[i] = exp->invbits[i];
    res->invbits[len] = '\0';
  }

  /* Note: no need to cache aig vectors here (exp->av is unique to exp). */
  if (!BTOR_IS_FUN_NODE (exp) && exp->av)
    res->av = btor_clone_aigvec (exp->av, clone->avmgr, aig_map);
  else
  {
    BTOR_PUSH_STACK_IF (res->rho, mm, *rhos, &res->rho);
    BTOR_PUSH_STACK_IF (exp->rho, mm, *rhos, &exp->rho);
  }

  assert (!exp->next || !BTOR_IS_INVALID_NODE (exp->next));
  BTOR_PUSH_STACK_IF (exp->next, mm, *nodes, &res->next);

  /* Note: parent node used during BFS only, pointer is not reset after bfs,
   *	   do not clone to avoid access to invalid nodes */
  res->parent = 0;

  assert (!exp->simplified
          || !BTOR_IS_INVALID_NODE (BTOR_REAL_ADDR_NODE (exp->simplified)));
  BTOR_PUSH_STACK_IF (exp->simplified, mm, *nodes, &res->simplified);

  res->btor = clone;

  assert (!exp->first_parent
          || !BTOR_IS_INVALID_NODE (BTOR_REAL_ADDR_NODE (exp->first_parent)));
  assert (!exp->last_parent
          || !BTOR_IS_INVALID_NODE (BTOR_REAL_ADDR_NODE (exp->last_parent)));

  BTOR_PUSH_STACK_IF (exp->first_parent, mm, *parents, &res->first_parent);
  BTOR_PUSH_STACK_IF (exp->last_parent, mm, *parents, &res->last_parent);
  /* <---------------------------------------------------------------------- */

  /* ------------ BTOR_BV_ADDITIONAL_VAR_NODE_STRUCT (all nodes) ----------> */
  if (!BTOR_IS_BV_CONST_NODE (exp))
  {
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
        if (BTOR_IS_FEQ_NODE (exp) && exp->vreads)
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
        assert (!exp->prev_parent[i]
                || !BTOR_IS_INVALID_NODE (
                       BTOR_REAL_ADDR_NODE (exp->prev_parent[i])));
        assert (!exp->next_parent[i]
                || !BTOR_IS_INVALID_NODE (
                       BTOR_REAL_ADDR_NODE (exp->next_parent[i])));

        BTOR_PUSH_STACK_IF (
            exp->prev_parent[i], mm, *parents, &res->prev_parent[i]);
        BTOR_PUSH_STACK_IF (
            exp->next_parent[i], mm, *parents, &res->next_parent[i]);
      }
    }
  }
  /* <---------------------------------------------------------------------- */

  if (BTOR_IS_PARAM_NODE (exp))
  {
    param = (BtorParamNode *) exp;
    assert (!param->lambda_exp
            || !BTOR_IS_INVALID_NODE (BTOR_REAL_ADDR_NODE (param->lambda_exp)));
    assert (
        !param->assigned_exp
        || !BTOR_IS_INVALID_NODE (BTOR_REAL_ADDR_NODE (param->assigned_exp)));

    BTOR_PUSH_STACK_IF (param->lambda_exp,
                        mm,
                        *nodes,
                        (BtorNode **) &((BtorParamNode *) res)->lambda_exp);
    BTOR_PUSH_STACK_IF (param->assigned_exp,
                        mm,
                        *nodes,
                        (BtorNode **) &((BtorParamNode *) res)->assigned_exp);
  }

  if (BTOR_IS_LAMBDA_NODE (exp))
  {
    lambda = (BtorLambdaNode *) exp;
    if (lambda->synth_apps)
    {
      BTOR_PUSH_STACK (mm, *sapps, &((BtorLambdaNode *) res)->synth_apps);
      BTOR_PUSH_STACK (mm, *sapps, &((BtorLambdaNode *) exp)->synth_apps);
    }

    assert (!lambda->head || !BTOR_IS_INVALID_NODE (lambda->head));
    assert (!lambda->body
            || !BTOR_IS_INVALID_NODE (BTOR_REAL_ADDR_NODE (lambda->body)));

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
    ((BtorUFNode *) res)->sort       = BTOR_PEEK_STACK (
        clone->sorts_unique_table.id2sort, ((BtorUFNode *) exp)->sort->id);
    assert (((BtorUFNode *) res)->sort->id == ((BtorUFNode *) exp)->sort->id);
    assert (((BtorUFNode *) res)->sort->refs
            == ((BtorUFNode *) exp)->sort->refs);
  }

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
mapped_node (BtorMemMgr *mm, const void *map, const void *key)
{
  assert (map);
  assert (key);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  (void) mm;
  exp        = (BtorNode *) key;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_mapped_node (exp_map, exp);
  assert (cloned_exp);
  return cloned_exp;
}

static void *
clone_str_key (BtorMemMgr *mm, const void *map, const void *key)
{
  assert (mm);
  assert (key);

  (void) map;

  return btor_strdup (mm, (char *) key);
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
data_as_str_ptr (BtorMemMgr *mm,
                 const void *str_table,
                 const void *data_ptr,
                 BtorPtrHashData *data)
{
  assert (mm);
  assert (str_table);
  assert (data_ptr);
  assert (data);

  char *str;

  (void) mm;
  str = (char *) data_ptr;
  assert (btor_find_in_ptr_hash_table ((BtorPtrHashTable *) str_table, str));

  data->asStr =
      (char *) btor_find_in_ptr_hash_table ((BtorPtrHashTable *) str_table, str)
          ->key;
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

  Btor *btor;

  (void) mm;
  btor        = ((BtorNodeMap *) map)->btor;
  data->asPtr = btor_copy_bv (btor, (BitVector *) data_ptr);
}

static void *
copy_bv_tuple (BtorMemMgr *mm, const void *map, const void *t)
{
  Btor *btor;
  (void) mm;
  btor = ((BtorNodeMap *) map)->btor;
  return btor_copy_bv_tuple (btor, (BitVectorTuple *) t);
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

  BtorPtrHashTable *table;
  table       = (BtorPtrHashTable *) data_ptr;
  data->asPtr = btor_clone_ptr_hash_table (
      mm, table, copy_bv_tuple, data_as_bv_ptr, map, map);
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
  assert (exp_layer_only
          || btor_has_clone_support_sat_mgr (btor_get_sat_mgr_btor (btor)));

  Btor *clone;
  BtorNodeMap *emap = 0;
  BtorAIGMap *amap  = 0;
  BtorMemMgr *mm;
  double start, delta;
  int len;
  char *prefix, *clone_prefix;
#ifndef NDEBUG
  int i, h;
  size_t allocated, amap_size = 0, amap_count = 0;
  BtorNode *cur;
  BtorAIGMgr *amgr;
  BtorBVAssignment *bvass;
  BtorArrayAssignment *arrass;
  BtorHashTableIterator it, cit, ncit;
  BtorSort *sort;
  char **ind, **val;
  amgr = exp_layer_only ? 0 : btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  BtorPtrHashData *data, *cdata;
#endif

  BTORLOG ("start cloning btor %p ...", btor);
  start = btor_time_stamp ();

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, clone);
  memcpy (clone, btor, sizeof (Btor));
  clone->mm = mm;

  /* always auto cleanup external references (dangling, not held from extern) */
  clone->options.auto_cleanup.val = 1;

  if (exp_layer_only)
  {
    /* reset */
    clone->btor_sat_btor_called = 0;
    clone->valid_assignments    = 0;
    btor_reset_time_btor (clone);
    btor_reset_stats_btor (clone);
  }

  assert ((allocated = sizeof (Btor)) == clone->mm->allocated);

  clone->msg = btor_new_btor_msg (clone->mm, &clone->options.verbosity.val);
  assert ((allocated += sizeof (BtorMsg)) == clone->mm->allocated);

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
    clone->avmgr = btor_new_aigvec_mgr (mm, clone->msg);
    assert ((allocated += sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr)
                          + sizeof (BtorSATMgr)
                          + sizeof (BtorAIG *)) /* BtorAIGUniqueTable chains */
            == clone->mm->allocated);
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    clone->avmgr = btor_clone_aigvec_mgr (mm, clone->msg, btor->avmgr);
    BTORLOG ("  clone AIG mgr: %.3f s", (btor_time_stamp () - delta));
    assert ((allocated +=
             sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr) + sizeof (BtorSATMgr)
             + (amgr->smgr->solver ? sizeof (BtorLGL) : 0)
             + (amgr->smgr->optstr ? strlen (amgr->smgr->optstr) + 1 : 0))
            == clone->mm->allocated);

    amap = btor_new_aig_map (clone,
                             btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                             btor_get_aig_mgr_aigvec_mgr (clone->avmgr));
    assert ((allocated += sizeof (*amap) + MEM_PTR_HASH_TABLE (amap->table))
            == clone->mm->allocated);

    BTORLOG_TIMESTAMP (delta);
    btor_clone_aigs (btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                     btor_get_aig_mgr_aigvec_mgr (clone->avmgr),
                     amap);
    BTORLOG ("  clone AIGs: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
    /* Note: hash table is initialized with size 1 */
    assert ((allocated += (amap->table->size - 1) * sizeof (BtorPtrHashBucket *)
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
               + btor->sorts_unique_table.num_elements * sizeof (BtorSort)
               + BTOR_SIZE_STACK (btor->sorts_unique_table.id2sort)
                     * sizeof (BtorSort *);
  for (i = 0; i < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort); i++)
  {
    sort = BTOR_PEEK_STACK (btor->sorts_unique_table.id2sort, i);
    if (!sort || sort->kind != BTOR_TUPLE_SORT) continue;
    allocated += sort->tuple.num_elements * sizeof (BtorSort *);
  }
  assert (allocated == clone->mm->allocated);
#endif

  emap = btor_new_node_map (clone);
  assert ((allocated += sizeof (*emap) + MEM_PTR_HASH_TABLE (emap->table))
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
    if (cur->invbits) allocated += strlen (cur->invbits) + 1;
    if (!BTOR_IS_FUN_NODE (cur) && cur->av)
    {
      if (!exp_layer_only)
        allocated += sizeof (*(cur->av)) + cur->len * sizeof (BtorAIG *);
    }
    else if (cur->rho)
      allocated += MEM_PTR_HASH_TABLE (cur->rho);
    if (BTOR_IS_FEQ_NODE (cur) && cur->vreads)
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
  /* Note: hash table is initialized with size 1 */
  allocated += (emap->table->size - 1) * sizeof (BtorPtrHashBucket *)
               + emap->table->count * sizeof (BtorPtrHashBucket)
               + BTOR_SIZE_STACK (btor->nodes_id_table) * sizeof (BtorNode *);
  assert (allocated == clone->mm->allocated);
#endif

  clone->true_exp = btor_mapped_node (emap, btor->true_exp);
  assert (clone->true_exp);

  BTORLOG_TIMESTAMP (delta);
  clone_nodes_unique_table (
      mm, &btor->nodes_unique_table, &clone->nodes_unique_table, emap);
  BTORLOG ("  clone nodes unique table: %.3f s", (btor_time_stamp () - delta));
  assert ((allocated += btor->nodes_unique_table.size * sizeof (BtorNode *))
          == clone->mm->allocated);

  clone->symbols =
      btor_clone_ptr_hash_table (mm, btor->symbols, clone_str_key, 0, 0, 0);
#ifndef NDEBUG
  int str_bytes = 0;
  init_hash_table_iterator (&it, btor->symbols);
  while (has_next_hash_table_iterator (&it))
    str_bytes +=
        (strlen ((char *) next_hash_table_iterator (&it)) + 1) * sizeof (char);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->symbols) + str_bytes)
          == clone->mm->allocated);
#endif
  clone->node2symbol = btor_clone_ptr_hash_table (mm,
                                                  btor->node2symbol,
                                                  mapped_node,
                                                  data_as_str_ptr,
                                                  emap,
                                                  clone->symbols);
#ifndef NDEBUG
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->node2symbol))
          == clone->mm->allocated);
#endif

  CLONE_PTR_HASH_TABLE (inputs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->inputs))
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
  CLONE_PTR_HASH_TABLE (fun_rhs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->fun_rhs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (bv_model, data_as_bv_ptr);
#ifndef NDEBUG
  if (btor->bv_model)
  {
    init_hash_table_iterator (&it, btor->bv_model);
    init_hash_table_iterator (&cit, clone->bv_model);
    while (has_next_node_hash_table_iterator (&it))
    {
      data  = next_data_hash_table_iterator (&it);
      cdata = next_data_hash_table_iterator (&cit);
      assert (btor_size_bv ((BitVector *) data->asPtr)
              == btor_size_bv ((BitVector *) cdata->asPtr));
      allocated += btor_size_bv ((BitVector *) cdata->asPtr);
    }
  }
#endif
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->bv_model))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (fun_model, data_as_bv_htable_ptr);
#ifndef NDEBUG
  if (btor->fun_model)
  {
    init_hash_table_iterator (&it, btor->fun_model);
    init_hash_table_iterator (&cit, clone->fun_model);
    while (has_next_hash_table_iterator (&it))
    {
      data  = next_data_hash_table_iterator (&it);
      cdata = next_data_hash_table_iterator (&cit);
      assert (MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) data->asPtr)
              == MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cdata->asPtr));
      allocated += MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) data->asPtr);

      init_hash_table_iterator (&ncit, ((BtorPtrHashTable *) data->asPtr));
      while (has_next_hash_table_iterator (&ncit))
      {
        allocated += btor_size_bv ((BitVector *) ncit.bucket->data.asPtr);
        allocated += btor_size_bv_tuple (
            (BitVectorTuple *) next_hash_table_iterator (&ncit));
      }
    }
  }
#endif
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->fun_model))
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
  init_node_hash_table_iterator (&it, btor->parameterized);
  init_node_hash_table_iterator (&cit, clone->parameterized);
  while (has_next_node_hash_table_iterator (&it))
  {
    assert (
        MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) it.bucket->data.asPtr)
        == MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cit.bucket->data.asPtr));
    allocated +=
        MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cit.bucket->data.asPtr);
    (void) next_node_hash_table_iterator (&it);
    (void) next_node_hash_table_iterator (&cit);
  }
  assert (allocated == clone->mm->allocated);
#endif

  if (btor->score)
  {
#ifndef NDEBUG
    h = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC);
#endif
    if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
    {
      clone->score = btor_clone_ptr_hash_table (
          mm, btor->score, mapped_node, data_as_htable_ptr, emap, emap);
      BTORLOG ("  clone score table: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
      CHKCLONE_MEM_PTR_HASH_TABLE (score);
      allocated += MEM_PTR_HASH_TABLE (btor->score);
      init_node_hash_table_iterator (&it, btor->score);
      init_node_hash_table_iterator (&cit, clone->score);
      while (has_next_node_hash_table_iterator (&it))
      {
        assert (MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) it.bucket->data.asPtr)
                == MEM_PTR_HASH_TABLE (
                       (BtorPtrHashTable *) cit.bucket->data.asPtr));
        allocated +=
            MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) it.bucket->data.asPtr);
        (void) next_node_hash_table_iterator (&it);
        (void) next_node_hash_table_iterator (&cit);
      }
      assert (allocated == clone->mm->allocated);
    }
    else
    {
      assert (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
      CLONE_PTR_HASH_TABLE_ASPTR (score, data_as_int_ptr);
      assert ((allocated += MEM_PTR_HASH_TABLE (btor->score))
              == clone->mm->allocated);
    }
#endif
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
    BTOR_RELEASE_STACK (btor->mm, stack);
  }

  clone->clone          = NULL;
  clone->close_apitrace = 0;

  clone_prefix = "clone";
  len          = btor->msg->prefix ? strlen (btor->msg->prefix) : 0;
  len += strlen (clone_prefix) + 3;
  BTOR_NEWN (clone->mm, prefix, len + 1);
  sprintf (prefix,
           "[%s] %s",
           clone_prefix,
           btor->msg->prefix ? btor->msg->prefix : "");
  btor_set_msg_prefix_btor (clone, prefix);
  BTOR_DELETEN (clone->mm, prefix, len + 1);

  if (aig_map)
    *aig_map = amap;
  else if (!exp_layer_only)
    btor_delete_aig_map (amap);

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
  char *symbol;
  BtorNode *real_exp, *cur, *cur_clone, *e[3];
  BtorNodePtrStack work_stack, unmark_stack;
#ifndef NDEBUG
  BtorNodeMap *key_map = btor_new_node_map (btor);
#endif

  // FIXME lemmas are currently built with rwl1 (in parent)
  rwl = clone->options.rewrite_level.val;
  if (clone->options.rewrite_level.val > 0)
    btor_set_opt (clone, BTOR_OPT_REWRITE_LEVEL, 1);
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
          symbol =
              btor_find_in_ptr_hash_table (btor->node2symbol, cur)->data.asStr;
          cur_clone = btor_var_exp (clone, cur->len, symbol);
          break;
        case BTOR_PARAM_NODE:
          symbol =
              btor_find_in_ptr_hash_table (btor->node2symbol, cur)->data.asStr;
          cur_clone = btor_param_exp (clone, cur->len, symbol);
          break;
        case BTOR_UF_NODE:
          symbol =
              btor_find_in_ptr_hash_table (btor->node2symbol, cur)->data.asStr;
          cur_clone =
              btor_uf_exp (clone,
                           BTOR_PEEK_STACK (clone->sorts_unique_table.id2sort,
                                            ((BtorUFNode *) cur)->sort->id),
                           symbol);
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
  btor_set_opt (clone, BTOR_OPT_REWRITE_LEVEL, rwl);
  //
#ifndef NDEBUG
  btor_delete_node_map (key_map);
#endif
  return btor_copy_exp (clone, btor_mapped_node (exp_map, exp));
}

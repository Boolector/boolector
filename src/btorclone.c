/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2014-2018 Mathias Preiner.
 *  Copyright (C) 2014-2015 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbeta.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btormsg.h"
#include "btorrwcache.h"
#include "btorsat.h"
#include "btorslvaigprop.h"
#include "btorslvfun.h"
#include "btorslvprop.h"
#include "btorslvsls.h"
#include "btorsort.h"
#include "sat/btorlgl.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btornodemap.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (BtorNodePtrStackPtr, BtorNodePtrStack *);
BTOR_DECLARE_STACK (BtorPtrHashTablePtrPtr, BtorPtrHashTable **);

/*------------------------------------------------------------------------*/

void *
btor_clone_key_as_node (BtorMemMgr *mm, const void *map, const void *key)
{
  assert (map);
  assert (key);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  (void) mm;
  exp        = (BtorNode *) key;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_nodemap_mapped (exp_map, exp);
  assert (cloned_exp);
  return cloned_exp;
}

void *
btor_clone_key_as_str (BtorMemMgr *mm, const void *map, const void *key)
{
  assert (mm);
  assert (key);

  (void) map;

  return btor_mem_strdup (mm, (char *) key);
}

void *
btor_clone_key_as_static_str (BtorMemMgr *mm, const void *map, const void *key)
{
  (void) mm;
  (void) map;
  return (void *) key;
}

void *
btor_clone_key_as_bv_tuple (BtorMemMgr *mm, const void *map, const void *t)
{
  assert (mm);
  assert (t);
  (void) map;
  return btor_bv_copy_tuple (mm, (BtorBitVectorTuple *) t);
}

void *
btor_clone_key_as_rw_cache_tuple (BtorMemMgr *mm,
                                  const void *map,
                                  const void *t)
{
  assert (mm);
  assert (t);
  (void) map;

  BtorRwCacheTuple *res;
  BTOR_CNEW (mm, res);
  memcpy (res, t, sizeof (BtorRwCacheTuple));
  return res;
}

void
btor_clone_data_as_node_ptr (BtorMemMgr *mm,
                             const void *map,
                             BtorHashTableData *data,
                             BtorHashTableData *cloned_data)
{
  assert (map);
  assert (data);
  assert (cloned_data);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  (void) mm;
  exp        = (BtorNode *) data->as_ptr;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_nodemap_mapped (exp_map, exp);
  assert (cloned_exp);
  cloned_data->as_ptr = cloned_exp;
}

void
btor_clone_data_as_str_ptr (BtorMemMgr *mm,
                            const void *str_table,
                            BtorHashTableData *data,
                            BtorHashTableData *cloned_data)
{
  assert (str_table);
  assert (data);
  assert (cloned_data);

  char *str;

  (void) mm;
  str = data->as_str;
  assert (btor_hashptr_table_get ((BtorPtrHashTable *) str_table, str));

  cloned_data->as_str =
      (char *) btor_hashptr_table_get ((BtorPtrHashTable *) str_table, str)
          ->key;
}

void
btor_clone_data_as_int (BtorMemMgr *mm,
                        const void *map,
                        BtorHashTableData *data,
                        BtorHashTableData *cloned_data)
{
  assert (data);
  assert (cloned_data);

  (void) mm;
  (void) map;
  cloned_data->as_int = data->as_int;
}

void
btor_clone_data_as_dbl (BtorMemMgr *mm,
                        const void *map,
                        BtorHashTableData *data,
                        BtorHashTableData *cloned_data)
{
  assert (data);
  assert (cloned_data);

  (void) mm;
  (void) map;

  cloned_data->as_dbl = data->as_dbl;
}

void
btor_clone_data_as_bv_ptr (BtorMemMgr *mm,
                           const void *map,
                           BtorHashTableData *data,
                           BtorHashTableData *cloned_data)
{
  assert (mm);
  assert (data);
  assert (cloned_data);

  (void) map;
  cloned_data->as_ptr = btor_bv_copy (mm, (BtorBitVector *) data->as_ptr);
}

void
btor_clone_data_as_ptr_htable (BtorMemMgr *mm,
                               const void *map,
                               BtorHashTableData *data,
                               BtorHashTableData *cloned_data)
{
  assert (mm);
  assert (map);
  assert (data);
  assert (cloned_data);

  BtorPtrHashTable *table;
  BtorNodeMap *exp_map;

  table   = (BtorPtrHashTable *) data->as_ptr;
  exp_map = (BtorNodeMap *) map;

  cloned_data->as_ptr = btor_hashptr_table_clone (
      mm, table, btor_clone_key_as_node, 0, exp_map, 0);
}

void
btor_clone_data_as_int_htable (BtorMemMgr *mm,
                               const void *map,
                               BtorHashTableData *data,
                               BtorHashTableData *cloned_data)
{
  (void) map;
  assert (mm);
  assert (map);
  assert (data);
  assert (cloned_data);

  BtorIntHashTable *table, *res;

  table = (BtorIntHashTable *) data->as_ptr;

  res = btor_hashint_table_new (mm);

  BTOR_DELETEN (mm, res->keys, res->size);
  BTOR_DELETEN (mm, res->hop_info, res->size);

  res->size  = table->size;
  res->count = table->count;
  BTOR_CNEWN (mm, res->keys, res->size);
  BTOR_CNEWN (mm, res->hop_info, res->size);
  if (table->data) BTOR_CNEWN (mm, res->data, res->size);

  memcpy (res->keys, table->keys, table->size);
  memcpy (res->hop_info, table->hop_info, table->size);
  if (table->data) memcpy (res->data, table->data, table->size);

  cloned_data->as_ptr = res;
}

void
btor_clone_data_as_bv_ptr_htable (BtorMemMgr *mm,
                                  const void *map,
                                  BtorHashTableData *data,
                                  BtorHashTableData *cloned_data)
{
  assert (mm);
  assert (data);
  assert (cloned_data);

  BtorPtrHashTable *table;
  table               = (BtorPtrHashTable *) data->as_ptr;
  cloned_data->as_ptr = btor_hashptr_table_clone (mm,
                                                  table,
                                                  btor_clone_key_as_bv_tuple,
                                                  btor_clone_data_as_bv_ptr,
                                                  map,
                                                  map);
}

/*------------------------------------------------------------------------*/

static void
clone_sorts_unique_table (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

  uint32_t i, j;
  BtorSort *sort, *csort;
  BtorSortId cid;
  BtorSortIdStack elements;
  BtorSortUniqueTable *table, *res;
  BtorMemMgr *mm;

  mm    = clone->mm;
  table = &btor->sorts_unique_table;
  res   = &clone->sorts_unique_table;

  BTOR_INIT_STACK (mm, elements);

  BTOR_CNEWN (mm, res->chains, table->size);
  res->size         = table->size;
  res->num_elements = 0;
  res->mm           = mm;
  BTOR_INIT_STACK (mm, res->id2sort);

  for (i = 0; i < BTOR_COUNT_STACK (table->id2sort); i++)
  {
    sort = BTOR_PEEK_STACK (table->id2sort, i);

    if (!sort)
    {
      BTOR_PUSH_STACK (res->id2sort, 0);
      continue;
    }

    switch (sort->kind)
    {
#if 0
	  case BTOR_BOOL_SORT:
	    cid = btor_sort_bool (clone);
	    break;
#endif
      case BTOR_BITVEC_SORT:
        cid = btor_sort_bv (clone, sort->bitvec.width);
        break;
#if 0
	  case BTOR_LST_SORT:
	    cid = btor_sort_lst (clone, sort->lst.head->id, sort->lst.tail->id);
	    break;

	  case BTOR_ARRAY_SORT:
	    cid = btor_sort_array (clone, sort->array.index->id,
				   sort->array.element->id);
	    break;
#endif
      case BTOR_FUN_SORT:
        assert (BTOR_PEEK_STACK (res->id2sort, sort->fun.domain->id));
        cid =
            btor_sort_fun (clone, sort->fun.domain->id, sort->fun.codomain->id);
        break;

      case BTOR_TUPLE_SORT:
        BTOR_RESET_STACK (elements);
        for (j = 0; j < sort->tuple.num_elements; j++)
          BTOR_PUSH_STACK (elements, sort->tuple.elements[j]->id);
        cid = btor_sort_tuple (
            clone, elements.start, BTOR_COUNT_STACK (elements));
        break;

      default: cid = 0; break;
    }
    assert (cid);
    csort = BTOR_PEEK_STACK (res->id2sort, cid);
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
  BTOR_RELEASE_STACK (elements);
}

#if 0
static void
clone_sorts_unique_table (BtorMemMgr * mm,
			  BtorSortUniqueTable * table,
			  BtorSortUniqueTable * res)
{
  assert (mm);
  assert (table);
  assert (res);

  uint32_t i, j;
  BtorSort *sort, *csort, *tmp;
  BtorSortPtrStack elements;
  
  BTOR_INIT_STACK (elements);

  BTOR_CNEWN (mm, res->chains, table->size);
  res->size = table->size;
  res->num_elements = 0;
  res->mm = mm;
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
	  case BTOR_BOOL_SORT:
	    csort = btor_sort_bool (res);
	    break;

	  case BTOR_BITVEC_SORT:
	    csort = btor_sort_bv (res, sort->bitvec.len);
	    break;

	  case BTOR_LST_SORT:
	    csort = btor_sort_lst (res,
			BTOR_PEEK_STACK (res->id2sort, sort->lst.head->id),
			BTOR_PEEK_STACK (res->id2sort, sort->lst.tail->id));
	    break;

	  case BTOR_ARRAY_SORT:
	    csort = btor_sort_array (res,
			BTOR_PEEK_STACK (res->id2sort, sort->array.index->id),
			BTOR_PEEK_STACK (res->id2sort,
					 sort->array.element->id));
	    break;

	  case BTOR_FUN_SORT:
	    tmp = BTOR_PEEK_STACK (res->id2sort, sort->fun.domain->id);
	    assert (tmp);
	    if (sort->fun.arity > 1)
	      {
		assert (sort->fun.domain->kind == BTOR_TUPLE_SORT);
		assert (tmp->kind == BTOR_TUPLE_SORT);
		assert (sort->fun.arity == tmp->tuple.num_elements);
		csort = btor_sort_fun (res, tmp->tuple.elements,
			    sort->fun.arity,
			    BTOR_PEEK_STACK (res->id2sort,
					     sort->fun.codomain->id));
	      }
	    else
	      {
		assert (sort->fun.domain->kind != BTOR_TUPLE_SORT
			&& sort->fun.domain->kind != BTOR_LST_SORT);
		csort = btor_sort_fun (res, &tmp, 1,
			    BTOR_PEEK_STACK (res->id2sort,
					     sort->fun.codomain->id));
	      }
	    break;

	  case BTOR_TUPLE_SORT:
	    BTOR_RESET_STACK (elements);
	    for (j = 0; j < sort->tuple.num_elements; j++)
	      BTOR_PUSH_STACK (mm, elements,
			       BTOR_PEEK_STACK (res->id2sort,
						sort->tuple.elements[j]->id));
	    csort = btor_sort_tuple (res, elements.start,
				     BTOR_COUNT_STACK (elements));
	    break;

	  default:
	    csort = 0;
	    break;
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
      sort = BTOR_PEEK_STACK (table->id2sort, i);
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
      csort->refs = sort->refs;
      csort->ext_refs = sort->ext_refs;
    }
  assert (res->num_elements == table->num_elements);
  BTOR_RELEASE_STACK (mm, elements);
}
#endif

static BtorNode *
clone_exp (Btor *clone,
           BtorNode *exp,
           BtorNodePtrPtrStack *parents,
           BtorNodePtrPtrStack *nodes,
           BtorNodePtrStack *rhos,
           BtorNodePtrStack *static_rhos,
           BtorNodeMap *exp_map,
           bool exp_layer_only)
{
  assert (clone);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (parents);
  assert (nodes);
  assert (exp_map);

  uint32_t i;
  BtorBitVector *bits;
  BtorNode *res;
  BtorParamNode *param;
  BtorMemMgr *mm;

  mm = clone->mm;

  res = btor_mem_malloc (mm, exp->bytes);
  memcpy (res, exp, exp->bytes);

  /* ------------------- BTOR_VAR_NODE_STRUCT (all nodes) -----------------> */
  if (btor_node_is_bv_const (exp))
  {
    bits = btor_bv_copy (mm, btor_node_bv_const_get_bits (exp));
    btor_node_bv_const_set_bits (res, bits);
    bits = btor_bv_copy (mm, btor_node_bv_const_get_invbits (exp));
    btor_node_bv_const_set_invbits (res, bits);
  }

  /* Note: no need to cache aig vectors here (exp->av is unique to exp). */
  if (btor_node_is_fun (exp))
  {
    if (exp_layer_only)
      res->rho = 0;
    else if (exp->rho)
    {
      BTOR_PUSH_STACK (*rhos, res);
      BTOR_PUSH_STACK (*rhos, exp);
    }
  }
  else if (exp->av)
    res->av = exp_layer_only ? 0 : btor_aigvec_clone (exp->av, clone->avmgr);

  assert (!exp->next || !btor_node_is_invalid (exp->next));
  BTOR_PUSH_STACK_IF (exp->next, *nodes, &res->next);

  assert (!exp->simplified || !btor_node_is_invalid (exp->simplified));
  BTOR_PUSH_STACK_IF (exp->simplified, *nodes, &res->simplified);

  res->btor = clone;

  assert (!exp->first_parent || !btor_node_is_invalid (exp->first_parent));
  assert (!exp->last_parent || !btor_node_is_invalid (exp->last_parent));

  BTOR_PUSH_STACK_IF (exp->first_parent, *parents, &res->first_parent);
  BTOR_PUSH_STACK_IF (exp->last_parent, *parents, &res->last_parent);
  /* <---------------------------------------------------------------------- */

  /* ------------ BTOR_BV_ADDITIONAL_VAR_NODE_STRUCT (all nodes) ----------> */
  if (!btor_node_is_bv_const (exp))
  {
    if (!btor_node_is_bv_var (exp) && !btor_node_is_param (exp))
    {
      if (exp->arity)
      {
        for (i = 0; i < exp->arity; i++)
        {
          res->e[i] = btor_nodemap_mapped (exp_map, exp->e[i]);
          assert (exp->e[i] != res->e[i]);
          assert (res->e[i]);
        }
      }

      for (i = 0; i < exp->arity; i++)
      {
        assert (!exp->prev_parent[i]
                || !btor_node_is_invalid (exp->prev_parent[i]));
        assert (!exp->next_parent[i]
                || !btor_node_is_invalid (exp->next_parent[i]));

        BTOR_PUSH_STACK_IF (
            exp->prev_parent[i], *parents, &res->prev_parent[i]);
        BTOR_PUSH_STACK_IF (
            exp->next_parent[i], *parents, &res->next_parent[i]);
      }
    }
  }
  /* <---------------------------------------------------------------------- */

  if (btor_node_is_param (exp))
  {
    param = (BtorParamNode *) exp;
    assert (!btor_node_param_is_bound (exp)
            || !btor_node_is_invalid (btor_node_param_get_binder (exp)));
    assert (!param->assigned_exp
            || !btor_node_is_invalid (param->assigned_exp));

    BTOR_PUSH_STACK_IF (
        param->binder, *nodes, (BtorNode **) &((BtorParamNode *) res)->binder);
    BTOR_PUSH_STACK_IF (param->assigned_exp,
                        *nodes,
                        (BtorNode **) &((BtorParamNode *) res)->assigned_exp);
  }

  if (btor_node_is_binder (exp))
  {
    if (btor_node_is_lambda (exp) && btor_node_lambda_get_static_rho (exp))
    {
      BTOR_PUSH_STACK (*static_rhos, res);
      BTOR_PUSH_STACK (*static_rhos, exp);
    }
    assert (!btor_node_binder_get_body (exp)
            || !btor_node_is_invalid (btor_node_binder_get_body (exp)));
    BTOR_PUSH_STACK_IF (btor_node_binder_get_body (exp),
                        *nodes,
                        &((BtorBinderNode *) res)->body);
  }

  btor_nodemap_map (exp_map, exp, res);

  return res;
}

void
btor_clone_node_ptr_stack (BtorMemMgr *mm,
                           BtorNodePtrStack *stack,
                           BtorNodePtrStack *res,
                           BtorNodeMap *exp_map,
                           bool is_zero_terminated)
{
  assert (stack);
  assert (res);
  assert (exp_map);

  uint32_t i, n;
  BtorNode *cloned_exp;
  bool has_zero_terminated;

  BTOR_INIT_STACK (mm, *res);
  assert (BTOR_SIZE_STACK (*stack) || !BTOR_COUNT_STACK (*stack));
  if (BTOR_SIZE_STACK (*stack))
  {
    BTOR_NEWN (mm, res->start, BTOR_SIZE_STACK (*stack));
    res->top = res->start;
    res->end = res->start + BTOR_SIZE_STACK (*stack);

    n                   = BTOR_COUNT_STACK (*stack);
    has_zero_terminated = n && !BTOR_PEEK_STACK (*stack, n - 1);
    if (is_zero_terminated && has_zero_terminated) n -= 1;

    for (i = 0; i < n; i++)
    {
      assert ((*stack).start[i]);
      cloned_exp = btor_nodemap_mapped (exp_map, (*stack).start[i]);
      assert (cloned_exp);
      BTOR_PUSH_STACK (*res, cloned_exp);
    }

    if (is_zero_terminated && has_zero_terminated) BTOR_PUSH_STACK (*res, 0);
  }
  assert (BTOR_COUNT_STACK (*stack) == BTOR_COUNT_STACK (*res));
  assert (BTOR_SIZE_STACK (*stack) == BTOR_SIZE_STACK (*res));
}

static void
clone_nodes_id_table (Btor *btor,
                      Btor *clone,
                      BtorNodePtrStack *res,
                      BtorNodeMap *exp_map,
                      bool exp_layer_only,
                      BtorNodePtrStack *rhos)
{
  assert (btor);
  assert (clone);
  assert (res);
  assert (exp_map);

  size_t i;
  int32_t tag;
  BtorNode **tmp, *exp, *cloned_exp;
  BtorMemMgr *mm;
  BtorNodePtrStack *id_table;
  BtorNodePtrPtrStack parents, nodes;
  BtorPtrHashTable *t;
  BtorNodePtrStack static_rhos;

  mm       = clone->mm;
  id_table = &btor->nodes_id_table;

  BTOR_INIT_STACK (mm, parents);
  BTOR_INIT_STACK (mm, nodes);
  BTOR_INIT_STACK (mm, static_rhos);

  BTOR_INIT_STACK (mm, *res);
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
      exp           = id_table->start[i];
      res->start[i] = exp ? clone_exp (clone,
                                       exp,
                                       &parents,
                                       &nodes,
                                       rhos,
                                       &static_rhos,
                                       exp_map,
                                       exp_layer_only)
                          : 0;
      assert (!exp || res->start[i]->id > 0);
      assert (!exp || (size_t) res->start[i]->id == i);
    }
  }
  assert (BTOR_COUNT_STACK (*res) == BTOR_COUNT_STACK (*id_table));
  assert (BTOR_SIZE_STACK (*res) == BTOR_SIZE_STACK (*id_table));

  /* update children, parent, lambda and next pointers of expressions */
  while (!BTOR_EMPTY_STACK (nodes))
  {
    tmp = BTOR_POP_STACK (nodes);
    assert (*tmp);
    *tmp = btor_nodemap_mapped (exp_map, *tmp);
    assert (*tmp);
  }

  while (!BTOR_EMPTY_STACK (parents))
  {
    tmp = BTOR_POP_STACK (parents);
    assert (*tmp);
    tag  = btor_node_get_tag (*tmp);
    *tmp = btor_nodemap_mapped (exp_map, btor_node_real_addr (*tmp));
    assert (*tmp);
    *tmp = btor_node_set_tag (*tmp, tag);
  }

  /* clone static_rho tables */
  while (!BTOR_EMPTY_STACK (static_rhos))
  {
    exp        = BTOR_POP_STACK (static_rhos);
    cloned_exp = BTOR_POP_STACK (static_rhos);
    assert (btor_node_is_lambda (exp));
    assert (btor_node_is_lambda (cloned_exp));
    t = btor_node_lambda_get_static_rho (exp);
    assert (t);
    btor_node_lambda_set_static_rho (
        cloned_exp,
        btor_hashptr_table_clone (mm,
                                  t,
                                  btor_clone_key_as_node,
                                  btor_clone_data_as_node_ptr,
                                  exp_map,
                                  exp_map));
  }

  BTOR_RELEASE_STACK (parents);
  BTOR_RELEASE_STACK (nodes);
  BTOR_RELEASE_STACK (static_rhos);
}

static void
clone_nodes_unique_table (Btor *btor, Btor *clone, BtorNodeMap *exp_map)
{
  assert (btor);
  assert (clone);
  assert (exp_map);

  uint32_t i;
  BtorNodeUniqueTable *table, *res;
  BtorMemMgr *mm;

  mm    = clone->mm;
  table = &btor->nodes_unique_table;
  res   = &clone->nodes_unique_table;

  BTOR_CNEWN (mm, res->chains, table->size);
  res->size         = table->size;
  res->num_elements = table->num_elements;

  for (i = 0; i < table->size; i++)
  {
    if (!table->chains[i]) continue;
    res->chains[i] = btor_nodemap_mapped (exp_map, table->chains[i]);
    assert (res->chains[i]);
  }
}

#define MEM_INT_HASH_TABLE(table)                                 \
  ((table) ? sizeof (*(table)) + (table)->size * sizeof (int32_t) \
                 + (table)->size * sizeof (uint8_t)               \
           : 0)

#define MEM_INT_HASH_MAP(table)                               \
  ((table) ? MEM_INT_HASH_TABLE (table)                       \
                 + (table)->size * sizeof (BtorHashTableData) \
           : 0)

#define MEM_PTR_HASH_TABLE(table)                                             \
  ((table) ? sizeof (*(table)) + (table)->size * sizeof (BtorPtrHashBucket *) \
                 + (table)->count * sizeof (BtorPtrHashBucket)                \
           : 0)

#define CHKCLONE_MEM_INT_HASH_TABLE(table, clone)                      \
  do                                                                   \
  {                                                                    \
    assert (MEM_INT_HASH_TABLE (table) == MEM_INT_HASH_TABLE (clone)); \
  } while (0)

#define CHKCLONE_MEM_INT_HASH_MAP(table, clone)                    \
  do                                                               \
  {                                                                \
    assert (MEM_INT_HASH_MAP (table) == MEM_INT_HASH_MAP (clone)); \
  } while (0)

#define CHKCLONE_MEM_PTR_HASH_TABLE(table, clone)                      \
  do                                                                   \
  {                                                                    \
    assert (MEM_PTR_HASH_TABLE (table) == MEM_PTR_HASH_TABLE (clone)); \
  } while (0)

#define CLONE_PTR_HASH_TABLE(table)                           \
  do                                                          \
  {                                                           \
    clone->table = btor_hashptr_table_clone (                 \
        mm, btor->table, btor_clone_key_as_node, 0, emap, 0); \
    CHKCLONE_MEM_PTR_HASH_TABLE (btor->table, clone->table);  \
  } while (0)

#define CLONE_PTR_HASH_TABLE_DATA(table, data_func)                      \
  do                                                                     \
  {                                                                      \
    BTORLOG_TIMESTAMP (delta);                                           \
    clone->table = btor_hashptr_table_clone (                            \
        mm, btor->table, btor_clone_key_as_node, data_func, emap, emap); \
    BTORLOG (1,                                                          \
             "  clone " #table " table: %.3f s",                         \
             (btor_util_time_stamp () - delta));                         \
    CHKCLONE_MEM_PTR_HASH_TABLE (btor->table, clone->table);             \
  } while (0)

#if 0
#define CLONE_INT_HASH_MAP_DATA(table, data_func)                          \
  do                                                                       \
  {                                                                        \
    BTORLOG_TIMESTAMP (delta);                                             \
    clone->table = btor_hashint_map_clone (mm, btor->table, data_func, 0); \
    BTORLOG (1,                                                            \
             "  clone " #table " table: %.3f s",                           \
             (btor_util_time_stamp () - delta));                           \
    CHKCLONE_MEM_INT_HASH_MAP (btor->table, clone->table);                 \
  } while (0)
#endif

#define MEM_BITVEC(bv) \
  ((bv) ? sizeof (*(bv)) + bv->len * sizeof (BTOR_BV_TYPE) : 0)

static Btor *
clone_aux_btor (Btor *btor,
                BtorNodeMap **exp_map,
                bool exp_layer_only,
                bool clone_slv)
{
  assert (btor);
  assert (exp_layer_only
          || btor_sat_mgr_has_clone_support (btor_get_sat_mgr (btor)));
  Btor *clone;
  BtorNodeMap *emap = 0;
  BtorMemMgr *mm;
  double start, delta;
  uint32_t i, len;
  char *prefix, *clone_prefix;
  BtorNode *exp, *cloned_exp;
  BtorPtrHashTableIterator pit;
  BtorNodePtrStack rhos;
#ifndef NDEBUG
  uint32_t h;
  size_t allocated;
  BtorNode *cur;
  BtorAIGMgr *amgr;
  BtorBVAss *bvass;
  BtorFunAss *funass;
  BtorPtrHashTableIterator cpit, ncpit;
  BtorIntHashTableIterator iit, ciit;
  BtorSort *sort;
  char **ind, **val;
  amgr = exp_layer_only ? 0 : btor_get_aig_mgr (btor);
  BtorHashTableData *data, *cdata;
  BtorOption o;
#endif

  BTORLOG (1, "start cloning btor %p ...", btor);
  start = btor_util_time_stamp ();
  btor->stats.clone_calls += 1;

  mm = btor_mem_mgr_new ();
  BTOR_CNEW (mm, clone);
#ifndef NDEBUG
  allocated = sizeof (Btor);
#endif
  memcpy (clone, btor, sizeof (Btor));
  clone->mm = mm;
  BTOR_CLR (&clone->cbs);
  btor_opt_clone_opts (btor, clone);
#ifndef NDEBUG
  allocated += BTOR_OPT_NUM_OPTS * sizeof (BtorOpt);
  for (o = btor_opt_first (btor); btor_opt_is_valid (btor, o);
       o = btor_opt_next (btor, o))
  {
    if (btor->options[o].valstr)
      allocated += strlen (btor->options[o].valstr) + 1;
    if (btor->options[o].options)
      allocated += MEM_PTR_HASH_TABLE (clone->options[o].options)
                   + clone->options[o].options->count * sizeof (BtorOptHelp);
  }
  allocated += MEM_PTR_HASH_TABLE (clone->str2opt);
#endif
  assert (allocated == clone->mm->allocated);

  /* always auto cleanup internal and external references (may be dangling
   * otherise) */
  btor_opt_set (clone, BTOR_OPT_AUTO_CLEANUP, 1);
  btor_opt_set (clone, BTOR_OPT_AUTO_CLEANUP_INTERNAL, 1);

  if (exp_layer_only)
  {
    /* reset */
    clone->btor_sat_btor_called = 0;
    clone->last_sat_result      = 0;
    btor_reset_time (clone);
#ifndef NDEBUG
    /* we need to explicitely reset the pointer to the table, since
     * it is the memcpy-ied pointer of btor->stats.rw_rules_applied */
    clone->stats.rw_rules_applied = 0;
#endif
    btor_reset_stats (clone);
#ifndef NDEBUG
    allocated += MEM_PTR_HASH_TABLE (clone->stats.rw_rules_applied);
    assert (allocated == clone->mm->allocated);
#endif
  }

  clone->msg = btor_msg_new (clone);
  assert ((allocated += sizeof (BtorMsg)) == clone->mm->allocated);

  /* set msg prefix for clone */
  clone_prefix = "clone";
  len          = btor->msg->prefix ? strlen (btor->msg->prefix) : 0;
  len += strlen (clone_prefix) + 1;
#ifndef NDEBUG
  allocated += len + 1;
#endif
  BTOR_NEWN (clone->mm, prefix, len + 1);
  sprintf (prefix, "%s>%s", btor->msg->prefix, clone_prefix);
  btor_set_msg_prefix (clone, prefix);
  BTOR_DELETEN (clone->mm, prefix, len + 1);

  if (exp_layer_only)
  {
    clone->bv_assignments = btor_ass_new_bv_list (mm);
    assert ((allocated += sizeof (BtorBVAssList)) == clone->mm->allocated);
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    clone->bv_assignments =
        btor_ass_clone_bv_list (clone->mm, btor->bv_assignments);
    BTORLOG (
        1, "  clone BV assignments: %.3f s", (btor_util_time_stamp () - delta));
#ifndef NDEBUG
    for (bvass = btor->bv_assignments->first; bvass; bvass = bvass->next)
      allocated +=
          sizeof (BtorBVAss) + strlen (btor_ass_get_bv_str (bvass)) + 1;
    assert ((allocated += sizeof (BtorBVAssList)) == clone->mm->allocated);
#endif
  }

  if (exp_layer_only)
  {
    clone->fun_assignments = btor_ass_new_fun_list (mm);
    assert ((allocated += sizeof (BtorFunAssList)) == clone->mm->allocated);
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    clone->fun_assignments =
        btor_ass_clone_fun_list (clone->mm, btor->fun_assignments);
    BTORLOG (1,
             "  clone array assignments: %.3f s",
             (btor_util_time_stamp () - delta));
#ifndef NDEBUG
    for (funass = btor->fun_assignments->first; funass; funass = funass->next)
    {
      allocated += sizeof (BtorFunAss) + 2 * funass->size * sizeof (char *);
      btor_ass_get_fun_indices_values (funass, &ind, &val, funass->size);
      for (i = 0; i < funass->size; i++)
        allocated += strlen (ind[i]) + 1 + strlen (val[i]) + 1;
    }
    assert ((allocated += sizeof (BtorFunAssList)) == clone->mm->allocated);
#endif
  }

  if (btor->avmgr)
  {
    if (exp_layer_only)
    {
      clone->avmgr = btor_aigvec_mgr_new (clone);
      assert ((allocated += sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr)
                            + sizeof (BtorSATMgr)
                            /* true and false AIGs */
                            + 2 * sizeof (BtorAIG *)
                            + sizeof (int32_t)) /* unique table chains */
              == clone->mm->allocated);
    }
    else
    {
      BTORLOG_TIMESTAMP (delta);
      clone->avmgr = btor_aigvec_mgr_clone (clone, btor->avmgr);
      BTORLOG (1, "  clone AIG mgr: %.3f s", (btor_util_time_stamp () - delta));
      assert (
          (allocated +=
           sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr) + sizeof (BtorSATMgr)
#ifdef BTOR_USE_LINGELING
           + (amgr->smgr->solver ? sizeof (BtorLGL) : 0)
#endif
           /* memory of AIG nodes */
           + (amgr->cur_num_aigs + amgr->cur_num_aig_vars) * sizeof (BtorAIG)
           /* children for AND AIGs */
           + amgr->cur_num_aigs * sizeof (int32_t) * 2
           /* unique table chain */
           + amgr->table.size * sizeof (int32_t)
           + BTOR_SIZE_STACK (amgr->id2aig) * sizeof (BtorAIG *)
           + BTOR_SIZE_STACK (amgr->cnfid2aig) * sizeof (int32_t))
          == clone->mm->allocated);
    }
  }

  BTORLOG_TIMESTAMP (delta);
  clone_sorts_unique_table (btor, clone);
  BTORLOG (1,
           "  clone sorts unique table: %.3f s",
           (btor_util_time_stamp () - delta));
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

  emap = btor_nodemap_new (clone);
  assert ((allocated += sizeof (*emap) + MEM_PTR_HASH_TABLE (emap->table))
          == clone->mm->allocated);

  BTOR_INIT_STACK (btor->mm, rhos);
  BTORLOG_TIMESTAMP (delta);
  clone_nodes_id_table (
      btor, clone, &clone->nodes_id_table, emap, exp_layer_only, &rhos);
  BTORLOG (
      1, "  clone nodes id table: %.3f s", (btor_util_time_stamp () - delta));
#ifndef NDEBUG
  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    allocated += cur->bytes;
    if (btor_node_is_bv_const (cur))
    {
      allocated += MEM_BITVEC (btor_node_bv_const_get_bits (cur));
      allocated += MEM_BITVEC (btor_node_bv_const_get_invbits (cur));
    }
    if (!exp_layer_only)
    {
      if (!btor_node_is_fun (cur) && cur->av)
        allocated += sizeof (*(cur->av)) + cur->av->width * sizeof (BtorAIG *);
    }
    if (btor_node_is_lambda (cur) && btor_node_lambda_get_static_rho (cur))
      allocated += MEM_PTR_HASH_TABLE (btor_node_lambda_get_static_rho (cur));
  }
  /* Note: hash table is initialized with size 1 */
  allocated += (emap->table->size - 1) * sizeof (BtorPtrHashBucket *)
               + emap->table->count * sizeof (BtorPtrHashBucket)
               + BTOR_SIZE_STACK (btor->nodes_id_table) * sizeof (BtorNode *);
  assert (allocated == clone->mm->allocated);
#endif

  clone->true_exp = btor_nodemap_mapped (emap, btor->true_exp);
  assert (clone->true_exp);

  BTORLOG_TIMESTAMP (delta);
  clone_nodes_unique_table (btor, clone, emap);
  BTORLOG (1,
           "  clone nodes unique table: %.3f s",
           (btor_util_time_stamp () - delta));
  assert ((allocated += btor->nodes_unique_table.size * sizeof (BtorNode *))
          == clone->mm->allocated);

  clone->symbols = btor_hashptr_table_clone (mm,
                                             btor->symbols,
                                             btor_clone_key_as_str,
                                             btor_clone_data_as_node_ptr,
                                             0,
                                             emap);
#ifndef NDEBUG
  uint32_t str_bytes = 0;
  btor_iter_hashptr_init (&pit, btor->symbols);
  while (btor_iter_hashptr_has_next (&pit))
    str_bytes +=
        (strlen ((char *) btor_iter_hashptr_next (&pit)) + 1) * sizeof (char);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->symbols) + str_bytes)
          == clone->mm->allocated);
#endif
  clone->node2symbol = btor_hashptr_table_clone (mm,
                                                 btor->node2symbol,
                                                 btor_clone_key_as_node,
                                                 btor_clone_data_as_str_ptr,
                                                 emap,
                                                 clone->symbols);
#ifndef NDEBUG
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->node2symbol))
          == clone->mm->allocated);
#endif

  CLONE_PTR_HASH_TABLE_DATA (inputs, btor_clone_data_as_int);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->inputs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (bv_vars);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->bv_vars))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (ufs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->ufs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA (lambdas, btor_clone_data_as_int);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->lambdas))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA (quantifiers, btor_clone_data_as_int);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->quantifiers))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (exists_vars);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->exists_vars))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (forall_vars);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->forall_vars))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA (feqs, btor_clone_data_as_int);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->feqs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA (substitutions, btor_clone_data_as_node_ptr);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->substitutions))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA (varsubst_constraints, btor_clone_data_as_node_ptr);
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
  btor_clone_node_ptr_stack (
      mm, &btor->failed_assumptions, &clone->failed_assumptions, emap, true);
  assert ((allocated +=
           BTOR_SIZE_STACK (btor->failed_assumptions) * sizeof (BtorNode *))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (var_rhs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->var_rhs))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (fun_rhs);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->fun_rhs))
          == clone->mm->allocated);

  clone->assertions_cache =
      btor_hashint_table_clone (clone->mm, btor->assertions_cache);
  assert ((allocated += MEM_INT_HASH_TABLE (btor->assertions_cache))
          == clone->mm->allocated);

  btor_clone_node_ptr_stack (
      mm, &btor->assertions, &clone->assertions, emap, false);
  assert (
      (allocated += BTOR_SIZE_STACK (btor->assertions) * sizeof (BtorNode *))
      == clone->mm->allocated);

  BTOR_INIT_STACK (clone->mm, clone->assertions_trail);
  for (i = 0; i < BTOR_COUNT_STACK (btor->assertions_trail); i++)
    BTOR_PUSH_STACK (clone->assertions_trail,
                     BTOR_PEEK_STACK (btor->assertions_trail, i));
  BTOR_ADJUST_STACK (btor->assertions_trail, clone->assertions_trail);
  assert ((allocated +=
           BTOR_SIZE_STACK (btor->assertions_trail) * sizeof (uint32_t))
          == clone->mm->allocated);

  if (btor->bv_model)
  {
    clone->bv_model = btor_model_clone_bv (clone, btor->bv_model, false);
#ifndef NDEBUG
    btor_iter_hashint_init (&iit, btor->bv_model);
    btor_iter_hashint_init (&ciit, clone->bv_model);
    while (btor_iter_hashint_has_next (&iit))
    {
      data  = btor_iter_hashint_next_data (&iit);
      cdata = btor_iter_hashint_next_data (&ciit);
      assert (btor_bv_size ((BtorBitVector *) data->as_ptr)
              == btor_bv_size ((BtorBitVector *) cdata->as_ptr));
      allocated += btor_bv_size ((BtorBitVector *) cdata->as_ptr);
    }
#endif
  }
  assert ((allocated += MEM_INT_HASH_MAP (btor->bv_model))
          == clone->mm->allocated);
#ifndef NDEBUG
  if (!exp_layer_only && btor->stats.rw_rules_applied)
  {
    clone->stats.rw_rules_applied =
        btor_hashptr_table_clone (mm,
                                  btor->stats.rw_rules_applied,
                                  btor_clone_key_as_static_str,
                                  btor_clone_data_as_int,
                                  0,
                                  0);
    assert ((allocated += MEM_PTR_HASH_TABLE (btor->stats.rw_rules_applied))
            == clone->mm->allocated);
  }
#endif
  if (btor->fun_model)
  {
    clone->fun_model = btor_model_clone_fun (clone, btor->fun_model, false);
#ifndef NDEBUG
    btor_iter_hashint_init (&iit, btor->fun_model);
    btor_iter_hashint_init (&ciit, clone->fun_model);
    while (btor_iter_hashint_has_next (&iit))
    {
      data  = btor_iter_hashint_next_data (&iit);
      cdata = btor_iter_hashint_next_data (&ciit);
      assert (MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) data->as_ptr)
              == MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) cdata->as_ptr));
      allocated += MEM_PTR_HASH_TABLE ((BtorPtrHashTable *) data->as_ptr);
      btor_iter_hashptr_init (&ncpit, ((BtorPtrHashTable *) data->as_ptr));
      while (btor_iter_hashptr_has_next (&ncpit))
      {
        allocated += btor_bv_size ((BtorBitVector *) ncpit.bucket->data.as_ptr);
        allocated += btor_bv_size_tuple (
            (BtorBitVectorTuple *) btor_iter_hashptr_next (&ncpit));
      }
    }
#endif
  }
  assert ((allocated += MEM_INT_HASH_MAP (btor->fun_model))
          == clone->mm->allocated);

  /* NOTE: we need bv_model for cloning rhos */
  while (!BTOR_EMPTY_STACK (rhos))
  {
    exp        = BTOR_POP_STACK (rhos);
    cloned_exp = BTOR_POP_STACK (rhos);
    assert (btor_node_is_fun (exp));
    assert (btor_node_is_fun (cloned_exp));
    assert (exp->rho);
    cloned_exp->rho = btor_hashptr_table_clone (mm,
                                                exp->rho,
                                                btor_clone_key_as_node,
                                                btor_clone_data_as_node_ptr,
                                                emap,
                                                emap);
#ifndef NDEBUG
    allocated += MEM_PTR_HASH_TABLE (cloned_exp->rho);
#endif
  }
  BTOR_RELEASE_STACK (rhos);
  assert (allocated == clone->mm->allocated);

  if (exp_layer_only)
  {
    BTOR_INIT_STACK (mm, clone->functions_with_model);
    /* we need to decrement the reference count of the cloned expressions
     * that were pushed onto the functions_with_model stack. */
    for (i = 0; i < BTOR_COUNT_STACK (btor->functions_with_model); i++)
      btor_node_release (
          clone,
          btor_nodemap_mapped (
              emap, BTOR_PEEK_STACK (btor->functions_with_model, i)));
  }
  else
  {
    BTORLOG_TIMESTAMP (delta);
    btor_clone_node_ptr_stack (mm,
                               &btor->functions_with_model,
                               &clone->functions_with_model,
                               emap,
                               false);
    BTORLOG (1,
             "  clone functions_with_model: %.3f s",
             btor_util_time_stamp () - delta);
    assert ((allocated +=
             BTOR_SIZE_STACK (btor->functions_with_model) * sizeof (BtorNode *))
            == clone->mm->allocated);
  }

  BTORLOG_TIMESTAMP (delta);
  btor_clone_node_ptr_stack (mm, &btor->outputs, &clone->outputs, emap, false);
  BTORLOG (1, "  clone outputs: %.3f s", btor_util_time_stamp () - delta);
  assert ((allocated += BTOR_SIZE_STACK (btor->outputs) * sizeof (BtorNode *))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone->parameterized =
      btor_hashptr_table_clone (mm,
                                btor->parameterized,
                                btor_clone_key_as_node,
                                btor_clone_data_as_int_htable,
                                emap,
                                emap);
  BTORLOG (1,
           "  clone parameterized table: %.3f s",
           (btor_util_time_stamp () - delta));
#ifndef NDEBUG
  CHKCLONE_MEM_PTR_HASH_TABLE (btor->parameterized, clone->parameterized);
  allocated += MEM_PTR_HASH_TABLE (btor->parameterized);
  btor_iter_hashptr_init (&pit, btor->parameterized);
  btor_iter_hashptr_init (&cpit, clone->parameterized);
  while (btor_iter_hashptr_has_next (&pit))
  {
    assert (btor_hashint_table_size (pit.bucket->data.as_ptr)
            == btor_hashint_table_size (cpit.bucket->data.as_ptr));
    allocated += btor_hashint_table_size (cpit.bucket->data.as_ptr);
    (void) btor_iter_hashptr_next (&pit);
    (void) btor_iter_hashptr_next (&cpit);
  }
  assert (allocated == clone->mm->allocated);
#endif
  BTOR_NEW (mm, clone->rw_cache);
  clone->rw_cache->btor  = clone;
  clone->rw_cache->cache = btor_hashptr_table_clone (
      mm, btor->rw_cache->cache, btor_clone_key_as_rw_cache_tuple, 0, 0, 0);
#ifndef NDEBUG
  CHKCLONE_MEM_PTR_HASH_TABLE (btor->rw_cache->cache, clone->rw_cache->cache);
  allocated += sizeof (*btor->rw_cache);
  allocated += btor->rw_cache->cache->count * sizeof (BtorRwCacheTuple);
  allocated += MEM_PTR_HASH_TABLE (btor->rw_cache->cache);
#endif

  /* move synthesized constraints to unsynthesized if we only clone the exp
   * layer */
  if (exp_layer_only)
  {
#ifndef NDEBUG
    allocated -= MEM_PTR_HASH_TABLE (clone->synthesized_constraints);
    allocated -= MEM_PTR_HASH_TABLE (clone->unsynthesized_constraints);
#endif
    btor_iter_hashptr_init (&pit, clone->synthesized_constraints);
    while (btor_iter_hashptr_has_next (&pit))
    {
      exp = btor_iter_hashptr_next (&pit);
      btor_hashptr_table_add (clone->unsynthesized_constraints, exp);
    }
    btor_hashptr_table_delete (clone->synthesized_constraints);
    clone->synthesized_constraints =
        btor_hashptr_table_new (mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
#ifndef NDEBUG
    allocated += MEM_PTR_HASH_TABLE (clone->synthesized_constraints);
    allocated += MEM_PTR_HASH_TABLE (clone->unsynthesized_constraints);
    assert (allocated == clone->mm->allocated);
#endif
  }

  if (clone_slv && btor->slv)
    clone->slv = btor->slv->api.clone (clone, btor->slv, emap);
  else
    clone->slv = 0;
  assert (!clone_slv || (btor->slv && clone->slv)
          || (!btor->slv && !clone->slv));
#ifndef NDEBUG
  if (clone->slv)
  {
    if (clone->slv->kind == BTOR_FUN_SOLVER_KIND)
    {
      BtorFunSolver *slv  = BTOR_FUN_SOLVER (btor);
      BtorFunSolver *cslv = BTOR_FUN_SOLVER (clone);

      allocated += sizeof (BtorFunSolver);

      allocated += MEM_PTR_HASH_TABLE (slv->lemmas);
      allocated += BTOR_SIZE_STACK (slv->cur_lemmas) * sizeof (BtorNode *);

      if (slv->score)
      {
        h = btor_opt_get (btor, BTOR_OPT_FUN_JUST_HEURISTIC);
        if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
        {
          CHKCLONE_MEM_PTR_HASH_TABLE (slv->score, cslv->score);
          allocated += MEM_PTR_HASH_TABLE (slv->score);

          btor_iter_hashptr_init (&pit, slv->score);
          btor_iter_hashptr_init (&cpit, cslv->score);
          while (btor_iter_hashptr_has_next (&pit))
          {
            assert (MEM_PTR_HASH_TABLE (
                        (BtorPtrHashTable *) pit.bucket->data.as_ptr)
                    == MEM_PTR_HASH_TABLE (
                           (BtorPtrHashTable *) cpit.bucket->data.as_ptr));
            allocated += MEM_PTR_HASH_TABLE (
                (BtorPtrHashTable *) pit.bucket->data.as_ptr);
            (void) btor_iter_hashptr_next (&pit);
            (void) btor_iter_hashptr_next (&cpit);
          }
        }
        else
        {
          assert (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
          allocated += MEM_PTR_HASH_TABLE (slv->score);
        }
      }

      assert (BTOR_SIZE_STACK (slv->stats.lemmas_size)
              == BTOR_SIZE_STACK (cslv->stats.lemmas_size));
      assert (BTOR_COUNT_STACK (slv->stats.lemmas_size)
              == BTOR_COUNT_STACK (cslv->stats.lemmas_size));
      allocated += BTOR_SIZE_STACK (slv->stats.lemmas_size) * sizeof (uint32_t);
    }
    else if (clone->slv->kind == BTOR_SLS_SOLVER_KIND)
    {
      BtorSLSMove *m;
      BtorSLSSolver *slv  = BTOR_SLS_SOLVER (btor);
      BtorSLSSolver *cslv = BTOR_SLS_SOLVER (clone);

      CHKCLONE_MEM_INT_HASH_MAP (slv->roots, cslv->roots);
      CHKCLONE_MEM_INT_HASH_MAP (slv->score, cslv->score);
      CHKCLONE_MEM_INT_HASH_MAP (slv->weights, cslv->weights);

      allocated += sizeof (BtorSLSSolver) + MEM_INT_HASH_MAP (cslv->roots)
                   + MEM_INT_HASH_MAP (cslv->score)
                   + MEM_INT_HASH_MAP (cslv->weights);

      if (slv->weights)
        allocated += slv->weights->count * sizeof (BtorSLSConstrData);

      assert (BTOR_SIZE_STACK (slv->moves) == BTOR_SIZE_STACK (cslv->moves));
      assert (BTOR_COUNT_STACK (slv->moves) == BTOR_COUNT_STACK (cslv->moves));

      allocated += BTOR_SIZE_STACK (cslv->moves) * sizeof (BtorSLSMove *)
                   + BTOR_COUNT_STACK (cslv->moves) * sizeof (BtorSLSMove);

      for (i = 0; i < BTOR_COUNT_STACK (cslv->moves); i++)
      {
        assert (BTOR_PEEK_STACK (cslv->moves, i));
        m = BTOR_PEEK_STACK (cslv->moves, i);
        assert (MEM_PTR_HASH_TABLE (m->cans)
                == MEM_PTR_HASH_TABLE (BTOR_PEEK_STACK (cslv->moves, i)->cans));
        allocated += MEM_PTR_HASH_TABLE (m->cans);
        btor_iter_hashint_init (&iit, m->cans);
        while (btor_iter_hashint_has_next (&iit))
          allocated +=
              btor_bv_size (btor_iter_hashint_next_data (&iit)->as_ptr);
      }

      if (cslv->max_cans)
      {
        assert (slv->max_cans);
        assert (slv->max_cans->count == cslv->max_cans->count);
        allocated += MEM_PTR_HASH_TABLE (cslv->max_cans);
        btor_iter_hashint_init (&iit, cslv->max_cans);
        while (btor_iter_hashint_has_next (&iit))
          allocated +=
              btor_bv_size (btor_iter_hashint_next_data (&iit)->as_ptr);
      }
    }
    else if (clone->slv->kind == BTOR_PROP_SOLVER_KIND)
    {
      BtorPropSolver *slv  = BTOR_PROP_SOLVER (btor);
      BtorPropSolver *cslv = BTOR_PROP_SOLVER (clone);

      CHKCLONE_MEM_INT_HASH_MAP (slv->roots, cslv->roots);
      CHKCLONE_MEM_INT_HASH_MAP (slv->score, cslv->score);

      allocated += sizeof (BtorPropSolver) + MEM_PTR_HASH_TABLE (cslv->roots)
                   + MEM_PTR_HASH_TABLE (cslv->score);
    }
    else if (clone->slv->kind == BTOR_AIGPROP_SOLVER_KIND)
    {
      BtorAIGPropSolver *slv  = BTOR_AIGPROP_SOLVER (btor);
      BtorAIGPropSolver *cslv = BTOR_AIGPROP_SOLVER (clone);

      if (slv->aprop)
      {
        assert (cslv->aprop);
        CHKCLONE_MEM_PTR_HASH_TABLE (slv->aprop->roots, cslv->aprop->roots);
        CHKCLONE_MEM_PTR_HASH_TABLE (slv->aprop->score, cslv->aprop->score);
        CHKCLONE_MEM_PTR_HASH_TABLE (slv->aprop->model, cslv->aprop->model);
        allocated += sizeof (AIGProp) + MEM_PTR_HASH_TABLE (cslv->aprop->roots)
                     + MEM_PTR_HASH_TABLE (cslv->aprop->score)
                     + MEM_PTR_HASH_TABLE (cslv->aprop->model);
      }

      allocated += sizeof (BtorAIGPropSolver);
    }

    assert (allocated == clone->mm->allocated);
  }
#endif

  clone->parse_error_msg = NULL;
#ifndef NDEBUG
  clone->clone = NULL;
#endif
  clone->close_apitrace = 0;

  if (exp_map)
    *exp_map = emap;
  else
    btor_nodemap_delete (emap);

#ifndef NDEBUG
  /* flag sanity checks */
  btor_iter_hashptr_init (&pit, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&pit, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&pit, btor->embedded_constraints);
  while (btor_iter_hashptr_has_next (&pit))
  {
    exp = btor_iter_hashptr_next (&pit);
    assert (btor_node_real_addr (exp)->constraint);
  }
#endif

  btor->time.cloning += btor_util_time_stamp () - start;
  BTORLOG (1, "cloning total: %.3f s", btor->time.cloning);
  return clone;
}

Btor *
btor_clone_btor (Btor *btor)
{
  assert (btor);
  return clone_aux_btor (
      btor, 0, !btor_sat_mgr_has_clone_support (btor_get_sat_mgr (btor)), true);
}

Btor *
btor_clone_exp_layer (Btor *btor, BtorNodeMap **exp_map)
{
  assert (btor);
  return clone_aux_btor (btor, exp_map, true, true);
}

Btor *
btor_clone_formula (Btor *btor)
{
  assert (btor);
  return clone_aux_btor (btor, 0, true, false);
}

BtorSortId
btor_clone_recursively_rebuild_sort (Btor *btor, Btor *clone, BtorSortId sort)
{
  uint32_t i;
  BtorSort *s;
  BtorSortId r, s0, s1;
  BtorSortPtrStack sort_stack;
  BtorIntHashTable *map;
  BtorHashTableData *d;
  BtorMemMgr *mm;
  BtorSortIdStack sort_ids;

  mm  = btor->mm;
  map = btor_hashint_map_new (mm);

  s = btor_sort_get_by_id (btor, sort);

  BTOR_INIT_STACK (mm, sort_ids);
  BTOR_INIT_STACK (mm, sort_stack);
  BTOR_PUSH_STACK (sort_stack, s);
  while (!BTOR_EMPTY_STACK (sort_stack))
  {
    s = BTOR_POP_STACK (sort_stack);
    d = btor_hashint_map_get (map, s->id);
    if (!d)
    {
      btor_hashint_map_add (map, s->id);

      BTOR_PUSH_STACK (sort_stack, s);
      switch (s->kind)
      {
        case BTOR_ARRAY_SORT:
          BTOR_PUSH_STACK (sort_stack, s->array.element);
          BTOR_PUSH_STACK (sort_stack, s->array.index);
          break;
        case BTOR_LST_SORT:
          BTOR_PUSH_STACK (sort_stack, s->lst.head);
          BTOR_PUSH_STACK (sort_stack, s->lst.tail);
          break;
        case BTOR_FUN_SORT:
          BTOR_PUSH_STACK (sort_stack, s->fun.domain);
          BTOR_PUSH_STACK (sort_stack, s->fun.codomain);
          break;
        case BTOR_TUPLE_SORT:
          for (i = 0; i < s->tuple.num_elements; i++)
            BTOR_PUSH_STACK (sort_stack, s->tuple.elements[i]);
          break;
        default:
          assert (s->kind == BTOR_BOOL_SORT || s->kind == BTOR_BITVEC_SORT);
      }
    }
    else if (!d->as_int)
    {
      switch (s->kind)
      {
        case BTOR_ARRAY_SORT:
          s0 = btor_hashint_map_get (map, s->array.index->id)->as_int;
          s1 = btor_hashint_map_get (map, s->array.element->id)->as_int;
          r  = btor_sort_array (clone, s0, s1);
          break;
#if 0
	      case BTOR_LST_SORT:
		s0 = btor_hashint_map_get (map, s->lst.head->id)->as_int;
		s1 = btor_hashint_map_get (map, s->lst.tail->id)->as_int;
		r = btor_lst_sort (clone, s0, s1);
		break;
#endif
        case BTOR_FUN_SORT:
          s0 = btor_hashint_map_get (map, s->fun.domain->id)->as_int;
          s1 = btor_hashint_map_get (map, s->fun.codomain->id)->as_int;
          r  = btor_sort_fun (clone, s0, s1);
          break;
        case BTOR_TUPLE_SORT:
          for (i = 0; i < s->tuple.num_elements; i++)
          {
            s0 = btor_hashint_map_get (map, s->tuple.elements[i]->id)->as_int;
            BTOR_PUSH_STACK (sort_ids, s0);
          }
          r = btor_sort_tuple (clone, sort_ids.start, s->tuple.num_elements);
          BTOR_RESET_STACK (sort_ids);
          break;
        case BTOR_BOOL_SORT: r = btor_sort_bool (clone); break;
        default:
          assert (s->kind == BTOR_BITVEC_SORT);
          r = btor_sort_bv (clone, s->bitvec.width);
      }
      assert (r);
      d->as_int = r;
    }
  }
  d = btor_hashint_map_get (map, sort);
  assert (d);
  assert (d->as_int);
  r = btor_sort_copy (clone, d->as_int);

  for (i = 0; i < map->size; i++)
  {
    if (!map->keys[i]) continue;
    s0 = map->data[i].as_int;
    btor_sort_release (clone, s0);
  }
  btor_hashint_map_delete (map);
  BTOR_RELEASE_STACK (sort_ids);
  BTOR_RELEASE_STACK (sort_stack);
  return r;
}

BtorNode *
btor_clone_recursively_rebuild_exp (Btor *btor,
                                    Btor *clone,
                                    BtorNode *exp,
                                    BtorNodeMap *exp_map,
                                    uint32_t rewrite_level)
{
  assert (btor);
  assert (exp);
  assert (btor_node_real_addr (exp)->btor == btor);
  assert (exp_map);

  uint32_t i, rwl;
  char *symbol;
  BtorNode *real_exp, *cur, *cur_clone, *e[3];
  BtorNodePtrStack work_stack;
  BtorIntHashTable *mark;
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  BtorSortId sort;

  mm   = btor->mm;
  mark = btor_hashint_table_new (mm);

  /* in some cases we may want to rebuild the expressions with a certain
   * rewrite level */
  rwl = btor_opt_get (clone, BTOR_OPT_REWRITE_LEVEL);
  if (rwl > 0) btor_opt_set (clone, BTOR_OPT_REWRITE_LEVEL, rewrite_level);

  BTOR_INIT_STACK (mm, work_stack);

  real_exp = btor_node_real_addr (exp);
  BTOR_PUSH_STACK (work_stack, real_exp);
  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (work_stack));

    if (btor_nodemap_mapped (exp_map, cur)) continue;

    if (!btor_hashint_table_contains (mark, cur->id))
    {
      btor_hashint_table_add (mark, cur->id);
      BTOR_PUSH_STACK (work_stack, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (work_stack, cur->e[i]);
    }
    else
    {
      assert (!btor_nodemap_mapped (exp_map, cur));
      assert (!btor_node_is_proxy (cur));
      for (i = 0; i < cur->arity; i++)
      {
        e[i] = btor_nodemap_mapped (exp_map, cur->e[i]);
        assert (e[i]);
      }
      switch (cur->kind)
      {
        case BTOR_CONST_NODE:
          cur_clone = btor_exp_bv_const (clone, btor_node_bv_const_get_bits (cur));
          break;
        case BTOR_VAR_NODE:
          b      = btor_hashptr_table_get (btor->node2symbol, cur);
          symbol = b ? b->data.as_str : 0;
          if (symbol && (b = btor_hashptr_table_get (clone->symbols, symbol)))
          {
            cur_clone = btor_node_copy (clone, b->data.as_ptr);
            assert (cur_clone->sort_id == cur->sort_id);
            assert (cur_clone->kind == cur->kind);
          }
          else
          {
            sort = btor_sort_bv (clone, btor_node_bv_get_width (btor, cur));
            cur_clone = btor_exp_var (clone, sort, symbol);
            btor_sort_release (clone, sort);
          }
          break;
        case BTOR_PARAM_NODE:
          b      = btor_hashptr_table_get (btor->node2symbol, cur);
          symbol = b ? b->data.as_str : 0;
          if (symbol && (b = btor_hashptr_table_get (clone->symbols, symbol)))
          {
            cur_clone = btor_node_copy (clone, b->data.as_ptr);
            assert (cur_clone->sort_id == cur->sort_id);
            assert (cur_clone->kind == cur->kind);
          }
          else
          {
            sort = btor_sort_bv (clone, btor_node_bv_get_width (btor, cur));
            cur_clone = btor_exp_param (clone, sort, symbol);
            btor_sort_release (clone, sort);
          }
          break;
        case BTOR_UF_NODE:
          b      = btor_hashptr_table_get (btor->node2symbol, cur);
          symbol = b ? b->data.as_str : 0;
          if (symbol && (b = btor_hashptr_table_get (clone->symbols, symbol)))
          {
            cur_clone = btor_node_copy (clone, b->data.as_ptr);
            assert (cur_clone->sort_id == cur->sort_id);
            assert (cur_clone->kind == cur->kind);
          }
          else
          {
            sort =
                btor_clone_recursively_rebuild_sort (btor, clone, cur->sort_id);
            cur_clone = btor_exp_uf (clone, sort, symbol);
            btor_sort_release (clone, sort);
          }
          break;
        case BTOR_BV_SLICE_NODE:
          cur_clone = btor_exp_bv_slice (clone,
                                         e[0],
                                         btor_node_bv_slice_get_upper (cur),
                                         btor_node_bv_slice_get_lower (cur));
          break;
        case BTOR_BV_AND_NODE:
          cur_clone = btor_exp_bv_and (clone, e[0], e[1]);
          break;
        case BTOR_BV_EQ_NODE:
        case BTOR_FUN_EQ_NODE:
          cur_clone = btor_exp_eq (clone, e[0], e[1]);
          break;
        case BTOR_BV_ADD_NODE:
          cur_clone = btor_exp_bv_add (clone, e[0], e[1]);
          break;
        case BTOR_BV_MUL_NODE:
          cur_clone = btor_exp_bv_mul (clone, e[0], e[1]);
          break;
        case BTOR_BV_ULT_NODE:
          cur_clone = btor_exp_bv_ult (clone, e[0], e[1]);
          break;
        case BTOR_BV_SLL_NODE:
          cur_clone = btor_exp_bv_sll (clone, e[0], e[1]);
          break;
        case BTOR_BV_SRL_NODE:
          cur_clone = btor_exp_bv_srl (clone, e[0], e[1]);
          break;
        case BTOR_BV_UDIV_NODE:
          cur_clone = btor_exp_bv_udiv (clone, e[0], e[1]);
          break;
        case BTOR_BV_UREM_NODE:
          cur_clone = btor_exp_bv_urem (clone, e[0], e[1]);
          break;
        case BTOR_BV_CONCAT_NODE:
          cur_clone = btor_exp_bv_concat (clone, e[0], e[1]);
          break;
        case BTOR_LAMBDA_NODE:
          assert (!btor_node_param_get_assigned_exp (e[0]));
          btor_node_param_set_binder (e[0], 0);
          cur_clone = btor_exp_lambda (clone, e[0], e[1]);
          break;
        case BTOR_APPLY_NODE:
          // FIXME use btor_exp_apply as soon as applies are
          // generated with rewriting (currently without)
          // cur_clone = btor_exp_apply (clone, e[0], e[1]);
          cur_clone = btor_node_create_apply (clone, e[0], e[1]);
          break;
        case BTOR_ARGS_NODE:
          cur_clone = btor_exp_args (clone, e, cur->arity);
          break;
        case BTOR_EXISTS_NODE:
          cur_clone = btor_exp_exists (clone, e[0], e[1]);
          break;
        case BTOR_FORALL_NODE:
          cur_clone = btor_exp_forall (clone, e[0], e[1]);
          break;
        default:
          assert (btor_node_is_bv_cond (cur));
          cur_clone = btor_exp_cond (clone, e[0], e[1], e[2]);
      }
      btor_nodemap_map (exp_map, cur, cur_clone);
      btor_node_release (clone, cur_clone);
    }
  }

  BTOR_RELEASE_STACK (work_stack);
  btor_hashint_table_delete (mark);

  /* reset rewrite_level to original value */
  btor_opt_set (clone, BTOR_OPT_REWRITE_LEVEL, rwl);
  return btor_node_copy (clone, btor_nodemap_mapped (exp_map, exp));
}

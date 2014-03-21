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
#include "btorcore.h"
#include "btorhash.h"
#include "btorlog.h"
#include "btormap.h"
#include "btorsat.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (BtorNodePtrStackPtr, BtorNodePtrStack *);
BTOR_DECLARE_STACK (BtorPtrHashTablePtrPtr, BtorPtrHashTable **);

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
  assert (aig_map);

  int i, len;
  BtorNode *res;
  BtorMemMgr *mm;

  mm = clone->mm;

  res = btor_malloc (mm, exp->bytes);
  memcpy (res, exp, exp->bytes);

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
    if (BTOR_IS_BV_VAR_NODE (exp) || BTOR_IS_ARRAY_VAR_NODE (exp)
        || BTOR_IS_PARAM_NODE (exp) || BTOR_IS_PROXY_NODE (exp))
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
                  const void *key,
                  BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (key);
  assert (data);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  (void) mm;
  exp        = (BtorNode *) key;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_mapped_node (exp_map, exp);
  assert (cloned_exp);
  data->asPtr = cloned_exp;
}

static void
data_as_htable_ptr (BtorMemMgr *mm,
                    const void *map,
                    const void *key,
                    BtorPtrHashData *data)
{
  assert (mm);
  assert (map);
  assert (key);
  assert (data);

  BtorPtrHashTable *table;
  BtorNodeMap *exp_map;

  table   = (BtorPtrHashTable *) key;
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
  assert (aig_map);

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
    *chtable =
        btor_clone_ptr_hash_table (mm, *htable, mapped_node, 0, exp_map, 0);
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

#define CLONE_PTR_HASH_TABLE(table)                   \
  do                                                  \
  {                                                   \
    clone->table = btor_clone_ptr_hash_table (        \
        mm, btor->table, mapped_node, 0, exp_map, 0); \
    CHKCLONE_MEM_PTR_HASH_TABLE (table);              \
  } while (0)

#define CLONE_PTR_HASH_TABLE_ASPTR(table)                                  \
  do                                                                       \
  {                                                                        \
    BTORLOG_TIMESTAMP (delta);                                             \
    clone->table = btor_clone_ptr_hash_table (                             \
        mm, btor->table, mapped_node, data_as_node_ptr, exp_map, exp_map); \
    BTORLOG ("  clone " #table " table: %.3f s",                           \
             (btor_time_stamp () - delta));                                \
    CHKCLONE_MEM_PTR_HASH_TABLE (table);                                   \
  } while (0)

Btor *
btor_clone_btor (Btor *btor)
{
  assert (btor);

  Btor *clone;
  BtorNodeMap *exp_map;
  BtorAIGMap *aig_map;
  BtorMemMgr *mm;
  double start, delta;
#ifndef NDEBUG
  int i;
  size_t allocated, amap_size, amap_count, emap_size, emap_count;
  BtorNode *cur;
  BtorAIGMgr *amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  BtorPtrHashBucket *b, *cb;
  BtorBVAssignment *bvass;
  BtorArrayAssignment *arrass;
  char **ind, **val;
#endif

  BTORLOG ("start cloning btor %p ...", btor);
  start = btor_time_stamp ();

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, clone);
  memcpy (clone, btor, sizeof (Btor));
  clone->mm = mm;
  assert ((allocated = sizeof (Btor)) == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone->bv_assignments =
      btor_clone_bv_assignment_list (clone->mm, btor->bv_assignments);
  BTORLOG ("  clone BV assignments: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  for (bvass = btor->bv_assignments->first; bvass; bvass = bvass->next)
    allocated +=
        sizeof (BtorBVAssignment) + strlen (btor_get_bv_assignment_str (bvass));
  assert ((allocated += sizeof (BtorBVAssignmentList)) == clone->mm->allocated);
#endif

  BTORLOG_TIMESTAMP (delta);
  clone->array_assignments =
      btor_clone_array_assignment_list (clone->mm, btor->array_assignments);
  BTORLOG ("  clone array assignments: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  for (arrass = btor->array_assignments->first; arrass; arrass = arrass->next)
  {
    allocated +=
        sizeof (BtorArrayAssignment) + 2 * arrass->size * sizeof (char *);
    btor_get_array_assignment_indices_values (arrass, &ind, &val, arrass->size);
    for (i = 0; i < arrass->size; i++)
      allocated += strlen (ind[i]) + strlen (val[i]);
  }
  assert ((allocated += sizeof (BtorArrayAssignmentList))
          == clone->mm->allocated);
#endif

  BTORLOG_TIMESTAMP (delta);
  clone->avmgr = btor_clone_aigvec_mgr (mm, btor->avmgr);
  BTORLOG ("  clone AIG mgr: %.3f s", (btor_time_stamp () - delta));
  assert ((allocated +=
           sizeof (BtorAIGVecMgr) + sizeof (BtorAIGMgr) + sizeof (BtorSATMgr)
           + (amgr->smgr->solver ? sizeof (BtorLGL) : 0)
           + (amgr->smgr->optstr ? strlen (amgr->smgr->optstr) + 1 : 0))
          == clone->mm->allocated);

  aig_map = btor_new_aig_map (clone,
                              btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                              btor_get_aig_mgr_aigvec_mgr (clone->avmgr));
  assert ((allocated += sizeof (*aig_map) + sizeof (*(aig_map->table)))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  btor_clone_aigs (btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                   btor_get_aig_mgr_aigvec_mgr (clone->avmgr),
                   aig_map);
  BTORLOG ("  clone AIGs: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  assert ((allocated += aig_map->table->size * sizeof (BtorPtrHashBucket *)
                        + aig_map->table->count * sizeof (BtorPtrHashBucket)
                        + aig_map->table->count * sizeof (BtorAIG)
                        + amgr->table.size * sizeof (BtorAIG *)
                        + BTOR_SIZE_STACK (amgr->id2aig) * sizeof (BtorAIG *))
          == clone->mm->allocated);
  amap_size  = aig_map->table->size;
  amap_count = aig_map->table->count;
#endif

  exp_map = btor_new_node_map (clone);
  assert ((allocated += sizeof (*exp_map) + sizeof (*(exp_map)->table))
          == clone->mm->allocated);
  BTORLOG_TIMESTAMP (delta);
  clone_nodes_id_table (
      clone, &btor->nodes_id_table, &clone->nodes_id_table, exp_map, aig_map);
  BTORLOG ("  clone nodes id table: %.3f s", (btor_time_stamp () - delta));
#ifndef NDEBUG
  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    allocated += cur->bytes;
    if (cur->bits) allocated += strlen (cur->bits) + 1;
    if (!BTOR_IS_FUN_NODE (cur) && cur->av)
      allocated += sizeof (*(cur->av)) + cur->len * sizeof (BtorAIG *);
    else if (cur->rho)
      allocated += MEM_PTR_HASH_TABLE (cur->rho);
    if (!BTOR_IS_BV_CONST_NODE (cur)
        && (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur)
            || BTOR_IS_PARAM_NODE (cur) || BTOR_IS_PROXY_NODE (cur)))
      allocated += cur->symbol ? strlen (cur->symbol) + 1 : 0;
    if (BTOR_IS_ARRAY_EQ_NODE (cur) && cur->vreads)
      allocated += sizeof (BtorNodePair);
    if (BTOR_IS_LAMBDA_NODE (cur) && ((BtorLambdaNode *) cur)->synth_apps)
      allocated += MEM_PTR_HASH_TABLE (((BtorLambdaNode *) cur)->synth_apps);
  }
  if (aig_map->table->size - amap_size)
    allocated +=
        (aig_map->table->size - amap_size) * sizeof (BtorPtrHashBucket *);
  if (aig_map->table->count - amap_count)
    allocated += (aig_map->table->count - amap_count)
                 * (sizeof (BtorPtrHashBucket) + sizeof (BtorAIG));
  allocated += exp_map->table->size * sizeof (BtorPtrHashBucket *)
               + exp_map->table->count * sizeof (BtorPtrHashBucket)
               + BTOR_SIZE_STACK (btor->nodes_id_table) * sizeof (BtorNode *);
  assert (allocated == clone->mm->allocated);
  emap_size  = exp_map->table->size;
  emap_count = exp_map->table->count;
#endif

  clone->true_exp = btor_mapped_node (exp_map, btor->true_exp);
  assert (clone->true_exp);
  assert (exp_map->table->count == emap_count);
  /* btor_mapped_node might cause hash table enlargement if size == count */
  assert (
      (allocated += (exp_map->table->size - emap_size) * sizeof (BtorNode *))
      == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone_nodes_unique_table (
      mm, &btor->nodes_unique_table, &clone->nodes_unique_table, exp_map);
  BTORLOG ("  clone nodes unique table: %.3f s", (btor_time_stamp () - delta));
  assert ((allocated += btor->nodes_unique_table.size * sizeof (BtorNode *))
          == clone->mm->allocated);

  // TODO sorts_unique_table (currently unused)

  CLONE_PTR_HASH_TABLE (bv_vars);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->bv_vars))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (array_vars);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->array_vars))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (lambdas);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->lambdas))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (substitutions);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->substitutions))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (lod_cache);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->lod_cache))
          == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (varsubst_constraints);
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

  BTORLOG_TIMESTAMP (delta);
  clone_node_ptr_stack (
      mm, &btor->arrays_with_model, &clone->arrays_with_model, exp_map);
  BTORLOG ("  clone arrays_with_model: %.3f s", (btor_time_stamp () - delta));
  assert ((allocated +=
           BTOR_SIZE_STACK (btor->arrays_with_model) * sizeof (BtorNode *))
          == clone->mm->allocated);

  CLONE_PTR_HASH_TABLE_ASPTR (cache);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->cache))
          == clone->mm->allocated);

  BTORLOG_TIMESTAMP (delta);
  clone->parameterized = btor_clone_ptr_hash_table (mm,
                                                    btor->parameterized,
                                                    mapped_node,
                                                    data_as_htable_ptr,
                                                    exp_map,
                                                    exp_map);
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
  clone->clone         = NULL;
  clone->apitrace      = NULL;
  clone->closeapitrace = 0;

  assert (!btor->clone /* not a shadow clone */
          || (clone->mm->allocated
              == btor->mm->allocated + sizeof (BtorNodeMap)
                     + MEM_PTR_HASH_TABLE (exp_map->table) + sizeof (BtorAIGMap)
                     + MEM_PTR_HASH_TABLE (aig_map->table)));

  btor_delete_node_map (exp_map);
  btor_delete_aig_map (aig_map);

  assert (!btor->clone || btor->mm->allocated == clone->mm->allocated);
  assert (!btor->clone || btor->mm->sat_allocated == clone->mm->sat_allocated);

  btor->time.cloning += btor_time_stamp () - start;
  return clone;
}

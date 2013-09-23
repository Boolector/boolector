/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraig.h"
#include "btoraigvec.h"
#include "btorexp.h"
#include "btorhash.h"
#include "btormap.h"
#include "btorstack.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (NodePtrStackPtr, BtorNodePtrStack *);
BTOR_DECLARE_STACK (PtrHashTablePtrPtr, BtorPtrHashTable **);

//// TODO DEBUG
// int strings = 0;
// int bits = 0;
// int bytes = 0;
// int exppairs = 0;
////
BtorNode *
clone_exp (Btor *clone,
           BtorNode *exp,
           BtorNodePtrPtrStack *parents,
           BtorNodePtrPtrStack *nodes,
           BtorNodePtrStackPtrStack *aexps,
           BtorPtrHashTablePtrPtrStack *sreads,
           BtorNodeMap *exp_map,
           BtorAIGMap *aig_map)
{
  assert (clone);
  assert (exp);
  assert (parents);
  assert (nodes);
  assert (aexps);
  assert (sreads);
  assert (exp_map);
  assert (aig_map);

  int i, len;
  BtorNode *res, *real_exp;
  BtorMemMgr *mm;

  mm = clone->mm;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (!BTOR_IS_PROXY_NODE (real_exp));

  res = btor_malloc (mm, real_exp->bytes);
  memcpy (res, real_exp, real_exp->bytes);
  // bytes += real_exp->bytes;  // TODO DEBUG

  ////// BTOR_BV_VAR_NODE_STRUCT (all nodes)
  if (real_exp->bits)
  {
    len = strlen (real_exp->bits);
    BTOR_NEWN (mm, res->bits, len + 1);
    // bits += len + 1; // TODO DEBUG
    for (i = 0; i < len; i++) res->bits[i] = real_exp->bits[i];
    res->bits[len] = '\0';
  }

  /* Note: no need to cache aig vectors here (exp->av is unique to exp). */
  if (!BTOR_IS_ARRAY_NODE (real_exp) && real_exp->av)
    res->av = btor_clone_aigvec (real_exp->av, clone->avmgr, aig_map);
  /* else: no need to clone rho (valid only during consistency checking). */

  BTOR_PUSH_STACK_IF (real_exp->next, mm, *nodes, &res->next);
  BTOR_PUSH_STACK_IF (real_exp->parent, mm, *parents, &res->parent);
  assert (!real_exp->simplified);
  res->btor = clone;
  BTOR_PUSH_STACK_IF (real_exp->first_parent, mm, *parents, &res->first_parent);
  BTOR_PUSH_STACK_IF (real_exp->last_parent, mm, *parents, &res->last_parent);
  //////

  ///// symbol
  if (!BTOR_IS_BV_CONST_NODE (real_exp))
  {
    if (BTOR_IS_BV_VAR_NODE (real_exp) || BTOR_IS_ARRAY_VAR_NODE (real_exp)
        || BTOR_IS_PARAM_NODE (real_exp) || BTOR_IS_PROXY_NODE (real_exp))
    {
      res->symbol = btor_strdup (mm, real_exp->symbol);
      // strings += strlen (res->symbol) + 1; // TODO DEBUG
    }

    ///// BTOR_BV_ADDITIONAL_NODE_STRUCT
    if (!BTOR_IS_BV_VAR_NODE (real_exp) && !BTOR_IS_PARAM_NODE (real_exp))
    {
      if (real_exp->arity)
      {
        for (i = 0; i < real_exp->arity; i++)
        {
          res->e[i] = btor_mapped_node (exp_map, real_exp->e[i]);
          assert (res->e[i]);
        }
      }
      else
      {
        if (BTOR_IS_ARRAY_EQ_NODE (real_exp) && real_exp->vreads)
        {
          // exppairs += 1; // TODO DEBUG
          assert (btor_mapped_node (exp_map, real_exp->vreads->exp1));
          assert (btor_mapped_node (exp_map, real_exp->vreads->exp2));
          res->vreads =
              new_exp_pair (clone,
                            btor_mapped_node (exp_map, real_exp->vreads->exp1),
                            btor_mapped_node (exp_map, real_exp->vreads->exp2));
        }
      }

      for (i = 0; i < real_exp->arity; i++)
      {
        BTOR_PUSH_STACK_IF (
            real_exp->prev_parent[i], mm, *parents, &res->prev_parent[i]);
        BTOR_PUSH_STACK_IF (
            real_exp->next_parent[i], mm, *parents, &res->next_parent[i]);
      }
    }
    //////
  }
  //////

  ////// BTOR_ARRAY_VAR_NODE_STRUCT
  if (BTOR_IS_ARRAY_NODE (real_exp) || BTOR_IS_ARRAY_EQ_NODE (real_exp))
  {
    BTOR_PUSH_STACK_IF (real_exp->first_aeq_acond_parent,
                        mm,
                        *parents,
                        &res->first_aeq_acond_parent);
    BTOR_PUSH_STACK_IF (real_exp->last_aeq_acond_parent,
                        mm,
                        *parents,
                        &res->last_aeq_acond_parent);

    ////// BTOR_ARRAY_ADDITIONAL_NODE_STRUCT
    if (!BTOR_IS_ARRAY_VAR_NODE (real_exp))
    {
      for (i = 0; i < real_exp->arity; i++)
      {
        BTOR_PUSH_STACK_IF (real_exp->prev_aeq_acond_parent[i],
                            mm,
                            *parents,
                            &res->prev_aeq_acond_parent[i]);
        BTOR_PUSH_STACK_IF (real_exp->next_aeq_acond_parent[i],
                            mm,
                            *parents,
                            &res->next_aeq_acond_parent[i]);
      }
    }
    //////
  }
  //////

  if (BTOR_IS_PARAM_NODE (real_exp))
  {
    BTOR_PUSH_STACK_IF (((BtorParamNode *) real_exp)->lambda_exp,
                        mm,
                        *nodes,
                        &((BtorParamNode *) res)->lambda_exp);
    BTOR_PUSH_STACK (mm, *aexps, &((BtorParamNode *) res)->assigned_exp);
    BTOR_PUSH_STACK (mm, *aexps, &((BtorParamNode *) real_exp)->assigned_exp);
  }

  if (BTOR_IS_LAMBDA_NODE (real_exp))
  {
    if (((BtorLambdaNode *) real_exp)->synth_reads)
    {
      BTOR_PUSH_STACK (mm, *sreads, &((BtorLambdaNode *) res)->synth_reads);
      BTOR_PUSH_STACK (
          mm, *sreads, &((BtorLambdaNode *) real_exp)->synth_reads);
    }
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) real_exp)->nested,
                        mm,
                        *nodes,
                        &((BtorLambdaNode *) res)->nested);
  }

  res = BTOR_IS_INVERTED_NODE (exp) ? BTOR_INVERT_NODE (res) : res;
  btor_map_node (clone, exp_map, exp, res);

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

  for (i = 0; i < BTOR_COUNT_STACK (*stack); i++)
  {
    assert ((*stack).start[i]);
    cloned_exp = btor_mapped_node (exp_map, (*stack).start[i]);
    assert (cloned_exp);
    BTOR_PUSH_STACK (mm, *res, cloned_exp);
  }
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
data_as_node_ptr (const void *map, const void *key, BtorPtrHashData *data)
{
  assert (map);
  assert (key);
  assert (data);

  BtorNode *exp, *cloned_exp;
  BtorNodeMap *exp_map;

  exp        = (BtorNode *) key;
  exp_map    = (BtorNodeMap *) map;
  cloned_exp = btor_mapped_node (exp_map, exp);
  assert (cloned_exp);
  data->asPtr = cloned_exp;
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

  int i, n, tag;
  BtorNode **tmp;
  BtorMemMgr *mm;
  BtorNodePtrPtrStack parents, nodes;
  BtorNodePtrStackPtrStack aexps;
  BtorNodePtrStack *aexp, *caexp;
  BtorPtrHashTablePtrPtrStack sreads;
  BtorPtrHashTable **sread, **csread;

  mm = clone->mm;

  BTOR_INIT_STACK (parents);
  BTOR_INIT_STACK (nodes);
  BTOR_INIT_STACK (aexps);
  BTOR_INIT_STACK (sreads);
  BTOR_INIT_STACK (*res);
  BTOR_PUSH_STACK (mm, *res, 0);

  n = BTOR_COUNT_STACK (*id_table);
  /* first element (id = 0) is empty */
  //// TODO debug
  // int nbytes = 0;
  ////
  for (i = 1; i < n; i++)
  {
    // if (id_table->start[i])
    //  nbytes += id_table->start[i]->bytes; // TODO DEBUG
    BTOR_PUSH_STACK (mm,
                     *res,
                     id_table->start[i] ? clone_exp (clone,
                                                     id_table->start[i],
                                                     &parents,
                                                     &nodes,
                                                     &aexps,
                                                     &sreads,
                                                     exp_map,
                                                     aig_map)
                                        : id_table->start[i]);
    assert (!id_table->start[i] || res->start[i]->id == i);
  }
  assert (BTOR_COUNT_STACK (*res) == BTOR_COUNT_STACK (*id_table));
  assert (BTOR_SIZE_STACK (*res) == BTOR_SIZE_STACK (*id_table));
  // printf (">>>> bytes: %d\n", nbytes); // TODO DEBUG
  // printf (">>>> bytes: %d\n", bytes); // TODO DEBUG
  // printf (">>>> bits: %d\n", bits); // TODO DEBUG
  // printf (">>>> strings: %d\n", strings); // TODO DEBUG
  // printf (">>>> exppairs: %d\n", exppairs); // TODO DEBUG
  // printf (">>>> id table count: %lu\n", BTOR_COUNT_STACK (*id_table));
  // printf (">>>> id table size: %lu\n", BTOR_SIZE_STACK (*id_table));
  // printf (">>>> exp_map count: %d\n", exp_map->table->count);
  // printf (">>>> exp_map size: %d\n", exp_map->table->size);
  // printf (">>>> aig_map count: %d\n", aig_map->table->count);
  // printf (">>>> aig_map size: %d\n", aig_map->table->size);

  // printf ("///**** after id table push %lu\n", clone->mm->allocated);

  /* update children, parent, lambda and next pointers of expressions */
  // printf (">>>> nodes stack count: %lu\n", BTOR_COUNT_STACK (nodes));
  // printf (">>>> nodes stack size: %lu\n", BTOR_SIZE_STACK (nodes));
  while (!BTOR_EMPTY_STACK (nodes))
  {
    tmp = BTOR_POP_STACK (nodes);
    assert (*tmp);
    *tmp = btor_mapped_node (exp_map, *tmp);
    assert (*tmp);
  }
  // printf (">>>> parents stack count: %lu\n", BTOR_COUNT_STACK (parents));
  // printf (">>>> parents stack size: %lu\n", BTOR_SIZE_STACK (parents));
  while (!BTOR_EMPTY_STACK (parents))
  {
    tmp = BTOR_POP_STACK (parents);
    assert (*tmp);
    tag  = BTOR_GET_TAG_NODE (*tmp);
    *tmp = btor_mapped_node (exp_map, BTOR_REAL_ADDR_NODE (*tmp));
    assert (*tmp);
    *tmp = BTOR_TAG_NODE (*tmp, tag);
  }

  /* clone assigned_exp of param nodes */
  // int naexps = 0;  // TODO DEBUG
  while (!BTOR_EMPTY_STACK (aexps))
  {
    // naexps += 1; // TODO DEBUG
    aexp  = BTOR_POP_STACK (aexps);
    caexp = BTOR_POP_STACK (aexps);
    clone_node_ptr_stack (mm, aexp, caexp, exp_map);
  }
  // printf (">>>> no of aexps: %d\n", naexps); // TODO DEBUG

  /* clone synth_reads of lambda nodes */
  // int nsreads = 0;// TODO DEBUG
  while (!BTOR_EMPTY_STACK (sreads))
  {
    // nsreads += 1; // TODO DEBUG
    sread  = BTOR_POP_STACK (sreads);
    csread = BTOR_POP_STACK (sreads);
    *csread =
        btor_clone_ptr_hash_table (mm, *sread, mapped_node, 0, exp_map, 0);
  }
  // printf (">>>> no of synth reads: %d\n", nsreads); // TODO DEBUG

  BTOR_RELEASE_STACK (mm, parents);
  BTOR_RELEASE_STACK (mm, nodes);
  BTOR_RELEASE_STACK (mm, aexps);
  BTOR_RELEASE_STACK (mm, sreads);
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

  // printf (">>>> unique table size: %u\n", table->size); // TODO debug
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

#define MEM_PTR_HASH_TABLE(table)                                       \
  (table ? sizeof (*table) + table->size * sizeof (BtorPtrHashBucket *) \
               + table->count * sizeof (BtorPtrHashBucket)              \
         : 0)

//#define CHKCLONE_MEM_PTR_HASH_TABLE(table) \
//  do { \
//    printf ("-- count btor %u clone %u\n", btor->table ? btor->table->count : 0,  clone->table ? clone->table->count : 0); \
//    printf ("-- size btor %u clone %u\n", btor->table ? btor->table->size : 0,  clone->table ? clone->table->size : 0); \
//    printf ("-- mem btor %lu clone %lu\n", MEM_PTR_HASH_TABLE (btor->table),  MEM_PTR_HASH_TABLE (clone->table)); \
//    assert (MEM_PTR_HASH_TABLE (btor->table) \
//	    == MEM_PTR_HASH_TABLE (clone->table)); \
//  } while (0)
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
    clone->table = btor_clone_ptr_hash_table (                             \
        mm, btor->table, mapped_node, data_as_node_ptr, exp_map, exp_map); \
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

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, clone);
  clone->mm = mm;

  exp_map = btor_new_node_map (clone);
  aig_map = btor_new_aig_map (clone);

  memcpy (&clone->bv_lambda_id,
          &btor->bv_lambda_id,
          (char *) &btor->lod_cache - (char *) &btor->bv_lambda_id);
  memcpy (&clone->stats,
          &btor->stats,
          (char *) btor + sizeof (*btor) - (char *) &btor->stats);

  // printf ("///**** after memcpy %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  clone->avmgr = btor_clone_aigvec_mgr (btor->avmgr, mm, aig_map);

  // printf ("///**** after avmgr%lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  clone_nodes_id_table (
      clone, &btor->nodes_id_table, &clone->nodes_id_table, exp_map, aig_map);
  // printf ("///**** after id table%lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  clone->true_exp = btor_mapped_node (exp_map, btor->true_exp);
  // printf ("///**** after true exp %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  clone_nodes_unique_table (
      mm, &btor->nodes_unique_table, &clone->nodes_unique_table, exp_map);
  // printf ("///**** after unique table %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  // TODO sorts_unique_table (currently unused)

  CLONE_PTR_HASH_TABLE (bv_vars);
  // printf ("///**** after bv_vars %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (array_vars);
  // printf ("///**** after array_vars %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (lambdas);
  // printf ("///**** after lambdas_vars %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (substitutions);
  // printf ("///**** after substitutions %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (lod_cache);
  // printf ("///**** after lod_cache %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_ASPTR (varsubst_constraints);
  // printf ("///**** after varsubst_constraints %lu %lu\n",
  // btor->mm->allocated, clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (embedded_constraints);
  // printf ("///**** after embedded_constraints %lu %lu\n",
  // btor->mm->allocated, clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (unsynthesized_constraints);
  // printf ("///**** after unsynthesized_constraints %lu %lu\n",
  // btor->mm->allocated, clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (synthesized_constraints);
  // printf ("///**** after synthesized_constraints %lu %lu\n",
  // btor->mm->allocated, clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (assumptions);
  // printf ("///**** after assumptions %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (var_rhs);
  // printf ("///**** after var_rhs %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);
  CLONE_PTR_HASH_TABLE (array_rhs);
  // printf ("///**** after array_rhs %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  clone_node_ptr_stack (
      mm, &btor->arrays_with_model, &clone->arrays_with_model, exp_map);
  // printf ("///**** after arrays_with_model %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  CLONE_PTR_HASH_TABLE_ASPTR (cache);
  // printf ("///**** after cache %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  clone->clone         = NULL;
  clone->apitrace      = NULL;
  clone->closeapitrace = 0;

  assert (clone->mm->allocated
          == btor->mm->allocated + sizeof (BtorNodeMap)
                 + MEM_PTR_HASH_TABLE (exp_map->table) + sizeof (BtorAIGMap)
                 + MEM_PTR_HASH_TABLE (aig_map->table));

  // printf ("///--- %lu\n", sizeof(BtorNodeMap) + MEM_PTR_HASH_TABLE
  // (exp_map->table) + sizeof(BtorAIGMap) + MEM_PTR_HASH_TABLE
  // (aig_map->table));  printf ("///**** %lu %lu\n", btor->mm->allocated,
  // clone->mm->allocated);

  btor_delete_node_map (exp_map);
  btor_delete_aig_map (aig_map);

  // printf ("///++++ %lu %lu\n", btor->mm->allocated, clone->mm->allocated);
  assert (btor->mm->allocated == clone->mm->allocated);
  assert (btor->mm->sat_allocated == clone->mm->sat_allocated);
  assert (btor->mm->sat_maxallocated == clone->mm->sat_maxallocated);

  return clone;
}

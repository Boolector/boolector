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
#include "btorsat.h"
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
// int av = 0;
// int rho = 0;
////
BtorNode *
clone_exp (Btor *clone,
           BtorNode *exp,
           BtorNodePtrPtrStack *parents,
           BtorNodePtrPtrStack *nodes,
           BtorPtrHashTablePtrPtrStack *rhos,
           BtorNodePtrStackPtrStack *aexps,
           BtorPtrHashTablePtrPtrStack *sapps,
           BtorNodeMap *exp_map,
           BtorAIGMap *aig_map)
{
  assert (clone);
  assert (exp);
  assert (parents);
  assert (nodes);
  assert (aexps);
  assert (sapps);
  assert (exp_map);
  assert (aig_map);

  int i, len;
  BtorNode *res, *real_exp;
  BtorMemMgr *mm;

  mm = clone->mm;

  // TODO shouldn't this already be the case, always??
  real_exp = BTOR_REAL_ADDR_NODE (exp);

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
  {
    // av += 1; // TODO DEBUG
    res->av = btor_clone_aigvec (real_exp->av, clone->avmgr, aig_map);
  }
  else
  {
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) res)->rho,
                        mm,
                        *rhos,
                        &((BtorLambdaNode *) res)->rho);
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) real_exp)->rho,
                        mm,
                        *rhos,
                        &((BtorLambdaNode *) real_exp)->rho);
  }

  BTOR_PUSH_STACK_IF (real_exp->next, mm, *nodes, &res->next);

  /* Note: parent node used during BFS only, pointer is not reset after bfs,
   *	   do not clone do avoid access to invalid nodes */
  res->parent = 0;

  BTOR_PUSH_STACK_IF (real_exp->simplified, mm, *nodes, &res->simplified);
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
          assert (real_exp->e[i] != res->e[i]);
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
                        (BtorNode **) &((BtorParamNode *) res)->lambda_exp);
    BTOR_PUSH_STACK (mm, *aexps, &((BtorParamNode *) res)->assigned_exp);
    BTOR_PUSH_STACK (mm, *aexps, &((BtorParamNode *) real_exp)->assigned_exp);
  }

  if (BTOR_IS_LAMBDA_NODE (real_exp))
  {
    if (((BtorLambdaNode *) real_exp)->synth_apps)
    {
      BTOR_PUSH_STACK (mm, *sapps, &((BtorLambdaNode *) res)->synth_apps);
      BTOR_PUSH_STACK (mm, *sapps, &((BtorLambdaNode *) real_exp)->synth_apps);
    }
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) real_exp)->nested,
                        mm,
                        *nodes,
                        (BtorNode **) &((BtorLambdaNode *) res)->nested);
    BTOR_PUSH_STACK_IF (((BtorLambdaNode *) real_exp)->body,
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
  BtorNodePtrStackPtrStack aexps;
  BtorNodePtrStack *aexp, *caexp;
  BtorPtrHashTablePtrPtrStack sapps, rhos;
  BtorPtrHashTable **htable, **chtable;

  mm = clone->mm;

  BTOR_INIT_STACK (parents);
  BTOR_INIT_STACK (nodes);
  BTOR_INIT_STACK (aexps);
  BTOR_INIT_STACK (sapps);
  BTOR_INIT_STACK (rhos);

  BTOR_INIT_STACK (*res);
  assert (BTOR_SIZE_STACK (*id_table) || !BTOR_COUNT_STACK (*id_table));
  if (BTOR_SIZE_STACK (*id_table))
  {
    BTOR_NEWN (mm, res->start, BTOR_SIZE_STACK (*id_table));
    res->top = res->start;
    res->end = res->start + BTOR_SIZE_STACK (*id_table);
    BTOR_PUSH_STACK (mm, *res, 0);

    /* first element (id = 0) is empty */
    //// TODO debug
    // int nbytes = 0;
    ////
    for (i = 1; i < BTOR_COUNT_STACK (*id_table); i++)
    {
      // if (id_table->start[i])
      //  {
      //    nbytes += id_table->start[i]->bytes; // TODO DEBUG
      //    if (id_table->start[i]->bits)
      //      nbytes += strlen (id_table->start[i]->bits) + 1;
      //    if (id_table->start[i]->av)
      //      nbytes += sizeof (*(id_table->start[i]->av))
      //      	  + id_table->start[i]->len * sizeof (BtorAIG *);
      //    if (!BTOR_IS_BV_CONST_NODE (id_table->start[i])
      //        && (BTOR_IS_BV_VAR_NODE (id_table->start[i])
      //            || BTOR_IS_ARRAY_VAR_NODE (id_table->start[i])
      //            || BTOR_IS_PARAM_NODE (id_table->start[i])
      //            || BTOR_IS_PROXY_NODE (id_table->start[i])))
      //      nbytes += id_table->start[i]
      //		    ? strlen (id_table->start[i]->symbol) + 1 : 0;
      //    if (BTOR_IS_ARRAY_EQ_NODE (id_table->start[i])
      //        && id_table->start[i]->vreads)
      //      nbytes += sizeof (BtorNodePair);
      //    if (BTOR_IS_PARAM_NODE (id_table->start[i]))
      //      nbytes += BTOR_SIZE_STACK (((BtorParamNode *)
      //      id_table->start[i])->assigned_exp) * sizeof (BtorNode *);
      //    if (BTOR_IS_LAMBDA_NODE (id_table->start[i])
      //        && ((BtorLambdaNode *) id_table->start[i])->synth_apps)
      //      nbytes += sizeof (*(((BtorLambdaNode *)
      //      id_table->start[i])->synth_apps))
      //             + ((BtorLambdaNode *) id_table->start[i])->synth_apps->size
      //             * sizeof (BtorPtrHashBucket *)
      //             + ((BtorLambdaNode *)
      //             id_table->start[i])->synth_apps->count * sizeof
      //             (BtorPtrHashBucket);
      //  }
      //
      BTOR_PUSH_STACK (mm,
                       *res,
                       id_table->start[i] ? clone_exp (clone,
                                                       id_table->start[i],
                                                       &parents,
                                                       &nodes,
                                                       &rhos,
                                                       &aexps,
                                                       &sapps,
                                                       exp_map,
                                                       aig_map)
                                          : id_table->start[i]);
      assert (!id_table->start[i] || res->start[i]->id == i);
    }
    // printf (">>>> bytes: %d\n", nbytes); // TODO DEBUG
  }
  assert (BTOR_COUNT_STACK (*res) == BTOR_COUNT_STACK (*id_table));
  assert (BTOR_SIZE_STACK (*res) == BTOR_SIZE_STACK (*id_table));
  // printf (">>>> bytes: %d\n", bytes); // TODO DEBUG
  // printf (">>>> bits: %d\n", bits); // TODO DEBUG
  // printf (">>>> strings: %d\n", strings); // TODO DEBUG
  // printf (">>>> exppairs: %d\n", exppairs); // TODO DEBUG
  // printf (">>>> rho: %d\n", rho); // TODO DEBUG
  // printf (">>>> av: %d\n", av); // TODO DEBUG
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

  /* clone rhos tables */
  while (!BTOR_EMPTY_STACK (rhos))
  {
    htable   = BTOR_POP_STACK (rhos);
    chtable  = BTOR_POP_STACK (rhos);
    *chtable = btor_clone_ptr_hash_table (
        mm, *htable, mapped_node, data_as_node_ptr, exp_map, exp_map);
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

  /* clone synth_apps of lambda nodes */
  // int nsapps = 0;// TODO DEBUG
  while (!BTOR_EMPTY_STACK (sapps))
  {
    // nsapps += 1; // TODO DEBUG
    htable  = BTOR_POP_STACK (sapps);
    chtable = BTOR_POP_STACK (sapps);
    *chtable =
        btor_clone_ptr_hash_table (mm, *htable, mapped_node, 0, exp_map, 0);
  }
  // printf (">>>> no of synth reads: %d\n", nsapps); // TODO DEBUG

  BTOR_RELEASE_STACK (mm, parents);
  BTOR_RELEASE_STACK (mm, nodes);
  BTOR_RELEASE_STACK (mm, rhos);
  BTOR_RELEASE_STACK (mm, aexps);
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

#define MEM_PTR_HASH_TABLE(table)                                             \
  ((table) ? sizeof (*(table)) + (table)->size * sizeof (BtorPtrHashBucket *) \
                 + (table)->count * sizeof (BtorPtrHashBucket)                \
           : 0)

//#define CHKCLONE_MEM_PTR_HASH_TABLE(table) \
//assert (allocated == clone->mm->allocated);
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
  BtorPtrHashBucket *b, *cb;
#ifndef NDEBUG
  int i;
  size_t allocated, amap_size, amap_count;
  BtorNode *cur;
  BtorAIGMgr *amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
#endif

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, clone);
  clone->mm = mm;

  memcpy (&clone->bv_lambda_id,
          &btor->bv_lambda_id,
          (char *) &btor->lod_cache - (char *) &btor->bv_lambda_id);
  memcpy (&clone->stats,
          &btor->stats,
          (char *) btor + sizeof (*btor) - (char *) &btor->stats);
  assert ((allocated = sizeof (Btor)) == clone->mm->allocated);

  clone->avmgr = btor_clone_aigvec_mgr (mm, btor->avmgr);
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

  btor_clone_aigs (btor_get_aig_mgr_aigvec_mgr (btor->avmgr),
                   btor_get_aig_mgr_aigvec_mgr (clone->avmgr),
                   aig_map);
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
  clone_nodes_id_table (
      clone, &btor->nodes_id_table, &clone->nodes_id_table, exp_map, aig_map);
#ifndef NDEBUG
  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;
    allocated += cur->bytes;
    if (cur->bits) allocated += strlen (cur->bits) + 1;
    if (!BTOR_IS_ARRAY_NODE (cur) && cur->av)
      allocated += sizeof (*(cur->av)) + cur->len * sizeof (BtorAIG *);
    else if (cur->rho)
      allocated += MEM_PTR_HASH_TABLE (cur->rho);
    if (!BTOR_IS_BV_CONST_NODE (cur)
        && (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur)
            || BTOR_IS_PARAM_NODE (cur) || BTOR_IS_PROXY_NODE (cur)))
      allocated += cur->symbol ? strlen (cur->symbol) + 1 : 0;
    if (BTOR_IS_ARRAY_EQ_NODE (cur) && cur->vreads)
      allocated += sizeof (BtorNodePair);
    if (BTOR_IS_PARAM_NODE (cur))
      allocated += BTOR_SIZE_STACK (((BtorParamNode *) cur)->assigned_exp)
                   * sizeof (BtorNode *);
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
#endif

  clone->true_exp = btor_mapped_node (exp_map, btor->true_exp);

  clone_nodes_unique_table (
      mm, &btor->nodes_unique_table, &clone->nodes_unique_table, exp_map);
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

  clone_node_ptr_stack (
      mm, &btor->arrays_with_model, &clone->arrays_with_model, exp_map);
  assert ((allocated +=
           BTOR_SIZE_STACK (btor->arrays_with_model) * sizeof (BtorNode *))
          == clone->mm->allocated);

  CLONE_PTR_HASH_TABLE_ASPTR (cache);
  assert ((allocated += MEM_PTR_HASH_TABLE (btor->cache))
          == clone->mm->allocated);

  clone->parameterized = btor_clone_ptr_hash_table (mm,
                                                    btor->parameterized,
                                                    mapped_node,
                                                    data_as_htable_ptr,
                                                    exp_map,
                                                    exp_map);
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

  assert (clone->mm->allocated
          == btor->mm->allocated + sizeof (BtorNodeMap)
                 + MEM_PTR_HASH_TABLE (exp_map->table) + sizeof (BtorAIGMap)
                 + MEM_PTR_HASH_TABLE (aig_map->table));

  btor_delete_node_map (exp_map);
  btor_delete_aig_map (aig_map);

  assert (btor->mm->allocated == clone->mm->allocated);
  assert (btor->mm->sat_allocated == clone->mm->sat_allocated);

  return clone;
}

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormap.h"
#include "btoriter.h"

/*------------------------------------------------------------------------*/

BtorNodeMap *
btor_new_node_map (Btor *btor)
{
  BtorNodeMap *res;

  assert (btor);

  BTOR_NEW (btor->mm, res);
  res->btor     = btor;
  res->table    = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  res->simplify = 0;

  return res;
}

void
btor_delete_node_map (BtorNodeMap *map)
{
  assert (map);

  BtorHashTableIterator it;
  BtorNode *cur;

  init_node_hash_table_iterator (&it, map->table);
  while (has_next_node_hash_table_iterator (&it))
  {
    btor_release_exp (
        BTOR_REAL_ADDR_NODE ((BtorNode *) it.bucket->data.asPtr)->btor,
        it.bucket->data.asPtr);
    cur = next_node_hash_table_iterator (&it);
    btor_release_exp (BTOR_REAL_ADDR_NODE (cur)->btor, cur);
  }
  btor_delete_ptr_hash_table (map->table);
  BTOR_DELETE (map->btor->mm, map);
}

BtorNode *
btor_mapped_node (BtorNodeMap *map, BtorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorNode *real_node;
  BtorNode *res;

  if (map->simplify)
    node = btor_simplify_exp (BTOR_REAL_ADDR_NODE (node)->btor, node);

  real_node = BTOR_REAL_ADDR_NODE (node);
  bucket    = btor_find_in_ptr_hash_table (map->table, real_node);
  if (!bucket) return 0;
  assert (bucket->key == real_node);
  res = bucket->data.asPtr;
  if (BTOR_IS_INVERTED_NODE (node)) res = BTOR_INVERT_NODE (res);
  return res;
}

int
btor_count_map (BtorNodeMap *map)
{
  assert (map);
  return map->table->count;
}

void
btor_map_node (BtorNodeMap *map, BtorNode *src, BtorNode *dst)
{
  BtorPtrHashBucket *bucket;

  assert (map);
  assert (src);
  assert (dst);

  if (map->simplify)
  {
    src = btor_simplify_exp (BTOR_REAL_ADDR_NODE (src)->btor, src);
    dst = btor_simplify_exp (BTOR_REAL_ADDR_NODE (dst)->btor, dst);
  }

  if (BTOR_IS_INVERTED_NODE (src))
  {
    src = BTOR_INVERT_NODE (src);
    dst = BTOR_INVERT_NODE (dst);
  }
  assert (!btor_find_in_ptr_hash_table (map->table, src));
  bucket = btor_insert_in_ptr_hash_table (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_exp (BTOR_REAL_ADDR_NODE (src)->btor, src);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = btor_copy_exp (BTOR_REAL_ADDR_NODE (dst)->btor, dst);
}

/*------------------------------------------------------------------------*/

static BtorNode *
btor_map_node_internal (Btor *btor, BtorNodeMap *map, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *m[3], *src, *dst, *real_exp;
  int i;

  m[0] = m[1] = m[2] = 0;

  for (i = 0; i < exp->arity; i++)
  {
    src  = exp->e[i];
    dst  = btor_mapped_node (map, src);
    m[i] = dst ? dst : src;
    assert (BTOR_REAL_ADDR_NODE (m[i])->btor == btor);
  }

  assert (exp->kind != BTOR_PROXY_NODE);

  switch (exp->kind)
  {
    case BTOR_BV_CONST_NODE:

      real_exp = BTOR_REAL_ADDR_NODE (exp);
      if (real_exp->btor != btor)
      {
        BtorNode *res = btor_const_exp (btor, exp->bits);
        if (real_exp != exp) res = BTOR_INVERT_NODE (res);
        return res;
      }

      // ELSE FALL THROUGH!!!

    case BTOR_BV_VAR_NODE:
    case BTOR_UF_NODE: return btor_copy_exp (btor, exp);
    case BTOR_SLICE_NODE:
      return btor_slice_exp (btor, m[0], exp->upper, exp->lower);
    case BTOR_AND_NODE: return btor_and_exp (btor, m[0], m[1]);
    case BTOR_BEQ_NODE:
    case BTOR_FEQ_NODE: return btor_eq_exp (btor, m[0], m[1]);
    case BTOR_ADD_NODE: return btor_add_exp (btor, m[0], m[1]);
    case BTOR_MUL_NODE: return btor_mul_exp (btor, m[0], m[1]);
    case BTOR_ULT_NODE: return btor_ult_exp (btor, m[0], m[1]);
    case BTOR_SLL_NODE: return btor_sll_exp (btor, m[0], m[1]);
    case BTOR_SRL_NODE: return btor_srl_exp (btor, m[0], m[1]);
    case BTOR_UDIV_NODE: return btor_udiv_exp (btor, m[0], m[1]);
    case BTOR_UREM_NODE: return btor_urem_exp (btor, m[0], m[1]);
    case BTOR_CONCAT_NODE: return btor_concat_exp (btor, m[0], m[1]);
    case BTOR_LAMBDA_NODE: return btor_lambda_exp (btor, m[0], m[1]);
    default:
      assert (BTOR_IS_BV_COND_NODE (exp));
      return btor_cond_exp (btor, m[0], m[1], m[2]);
  }
}

BtorNode *
btor_non_recursive_extended_substitute_node (Btor *btor,
                                             BtorNodeMap *map,
                                             void *state,
                                             BtorNodeMapper mapper,
                                             BtorNodeReleaser release,
                                             BtorNode *root)
{
  BtorNodePtrStack working_stack, marked_stack;
  BtorNode *res, *node, *mapped;
  BtorMemMgr *mm;
  int i;

  if (map->simplify)
    root = btor_simplify_exp (BTOR_REAL_ADDR_NODE (root)->btor, root);

  mm = btor->mm;

  BTOR_INIT_STACK (working_stack);
  BTOR_INIT_STACK (marked_stack);
  BTOR_PUSH_STACK (mm, working_stack, root);

  while (!BTOR_EMPTY_STACK (working_stack))
  {
    node = BTOR_POP_STACK (working_stack);
    node = BTOR_REAL_ADDR_NODE (node);
    assert (node->kind != BTOR_PROXY_NODE);
    if (btor_mapped_node (map, node)) continue;
    if (node->mark == 2) continue;
    mapped = mapper (btor, state, node);
    if (mapped)
    {
      btor_map_node (map, node, mapped);
      release (btor, mapped);
    }
    else if (!node->mark)
    {
      node->mark = 1;
      BTOR_PUSH_STACK (mm, working_stack, node);
      BTOR_PUSH_STACK (mm, marked_stack, node);
      for (i = node->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, working_stack, node->e[i]);
    }
    else
    {
      mapped = btor_map_node_internal (btor, map, node);
      btor_map_node (map, node, mapped);
      btor_release_exp (btor, mapped);
      assert (node->mark == 1);
      node->mark = 2;
    }
  }
  BTOR_RELEASE_STACK (mm, working_stack);
  while (!BTOR_EMPTY_STACK (marked_stack))
  {
    node = BTOR_POP_STACK (marked_stack);
    assert (node->mark == 2);
    node->mark = 0;
  }
  BTOR_RELEASE_STACK (mm, marked_stack);
  res = btor_mapped_node (map, root);
  assert (res);
  return res;
}

static BtorNode *
btor_never_map_mapper (Btor *btor, void *state, BtorNode *node)
{
  (void) btor;
  (void) state;
  (void) node;
  return 0;
}

BtorNode *
btor_non_recursive_substitute_node (Btor *btor,
                                    BtorNodeMap *map,
                                    BtorNode *root)
{
  return btor_non_recursive_extended_substitute_node (
      btor, map, 0, btor_never_map_mapper, 0, root);
}

/*------------------------------------------------------------------------*/

BoolectorNodeMap *
boolector_new_node_map (Btor *btor)
{
  BtorNodeMap *map;
  map           = btor_new_node_map (btor);
  map->simplify = 1;
  return (BoolectorNodeMap *) map;
}

void
boolector_delete_node_map (BoolectorNodeMap *map)
{
  btor_delete_node_map ((BtorNodeMap *) map);
}

int
boolector_count_map (BoolectorNodeMap *map)
{
  return btor_count_map ((BtorNodeMap *) map);
}

BoolectorNode *
boolector_mapped_node (BoolectorNodeMap *map, BoolectorNode *node)
{
  BtorNode *exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BtorNode *res = btor_mapped_node ((BtorNodeMap *) map, exp);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

void
boolector_map_node (BoolectorNodeMap *map,
                    BoolectorNode *src,
                    BoolectorNode *dst)
{
  btor_map_node ((BtorNodeMap *) map,
                 BTOR_IMPORT_BOOLECTOR_NODE (src),
                 BTOR_IMPORT_BOOLECTOR_NODE (dst));
}

BoolectorNode *
boolector_non_recursive_extended_substitute_node (Btor *btor,
                                                  BoolectorNodeMap *map,
                                                  void *state,
                                                  BoolectorNodeMapper mapper,
                                                  BoolectorNodeReleaser release,
                                                  BoolectorNode *root)
{
  return BTOR_EXPORT_BOOLECTOR_NODE (
      btor_non_recursive_extended_substitute_node (
          btor,
          (BtorNodeMap *) map,
          state,
          (BtorNodeMapper) mapper,
          (BtorNodeReleaser) release,
          BTOR_IMPORT_BOOLECTOR_NODE (root)));
}

BoolectorNode *
boolector_non_recursive_substitute_node (Btor *btor,
                                         BoolectorNodeMap *map,
                                         BoolectorNode *root)
{
  return BTOR_EXPORT_BOOLECTOR_NODE (btor_non_recursive_substitute_node (
      btor, (BtorNodeMap *) map, BTOR_IMPORT_BOOLECTOR_NODE (root)));
}

/*------------------------------------------------------------------------*/

BtorAIGMap *
btor_new_aig_map (Btor *btor, BtorAIGMgr *amgr_src, BtorAIGMgr *amgr_dst)
{
  assert (btor);
  assert (amgr_src);
  assert (amgr_dst);

  BtorAIGMap *res;

  BTOR_NEW (btor->mm, res);
  res->btor     = btor;
  res->amgr_src = amgr_src;
  res->amgr_dst = amgr_dst;
  res->table    = btor_new_ptr_hash_table (btor->mm, 0, 0);
  return res;
}

BtorAIG *
btor_mapped_aig (BtorAIGMap *map, BtorAIG *aig)
{
  assert (map);
  assert (aig);

  BtorPtrHashBucket *bucket;
  BtorAIG *real_aig, *res;

  real_aig = BTOR_REAL_ADDR_AIG (aig);
  bucket   = btor_find_in_ptr_hash_table (map->table, real_aig);
  if (!bucket) return 0;
  assert (bucket->key == real_aig);
  res = bucket->data.asPtr;
  if (BTOR_IS_INVERTED_AIG (aig)) res = BTOR_INVERT_AIG (res);
  return res;
}

void
btor_map_aig (BtorAIGMap *map, BtorAIG *src, BtorAIG *dst)
{
  assert (map);
  assert (src);
  assert (dst);

  BtorPtrHashBucket *bucket;

  if (BTOR_IS_INVERTED_AIG (src))
  {
    assert (BTOR_IS_INVERTED_AIG (dst));
    src = BTOR_INVERT_AIG (src);
    dst = BTOR_INVERT_AIG (dst);
  }
  assert (!btor_find_in_ptr_hash_table (map->table, src));
  bucket = btor_insert_in_ptr_hash_table (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_aig (map->amgr_src, src);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = btor_copy_aig (map->amgr_dst, dst);
}

void
btor_delete_aig_map (BtorAIGMap *map)
{
  assert (map);

  Btor *btor;
  BtorHashTableIterator it;

  btor = map->btor;

  init_hash_table_iterator (&it, map->table);
  while (has_next_hash_table_iterator (&it))
  {
    btor_release_aig (map->amgr_dst, it.bucket->data.asPtr);
    btor_release_aig (map->amgr_src, next_hash_table_iterator (&it));
  }
  btor_delete_ptr_hash_table (map->table);
  BTOR_DELETE (btor->mm, map);
}

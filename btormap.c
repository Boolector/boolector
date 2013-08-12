/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormap.h"

/*------------------------------------------------------------------------*/

BtorNodeMap *
btor_new_node_map (Btor *btor)
{
  assert (btor);
  return btor_new_ptr_hash_table (btor->mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
}

void
btor_delete_node_map (Btor *btor, BtorNodeMap *map)
{
  BtorPtrHashBucket *bucket;
  assert (btor);
  assert (map);
  for (bucket = map->first; bucket; bucket = bucket->next)
  {
    btor_release_exp (btor, bucket->key);
    btor_release_exp (btor, bucket->data.asPtr);
  }
  btor_delete_ptr_hash_table (map);
}

BtorNode *
btor_mapped_node (BtorNodeMap *map, BtorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorNode *realnode = BTOR_REAL_ADDR_NODE (node);
  BtorNode *res;
  bucket = btor_find_in_ptr_hash_table (map, realnode);
  if (!bucket) return 0;
  assert (bucket->key == realnode);
  res = bucket->data.asPtr;
  if (BTOR_IS_INVERTED_NODE (node)) res = BTOR_INVERT_NODE (res);
  return res;
}

void
btor_map_node (Btor *btor, BtorNodeMap *map, BtorNode *src, BtorNode *dst)
{
  BtorPtrHashBucket *bucket;
  assert (btor);
  assert (map);
  assert (src);
  assert (dst);
  if (BTOR_IS_INVERTED_NODE (src))
  {
    src = BTOR_INVERT_NODE (src);
    dst = BTOR_INVERT_NODE (dst);
  }
  assert (!btor_find_in_ptr_hash_table (map, src));
  bucket = btor_insert_in_ptr_hash_table (map, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_exp (btor, src);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = btor_copy_exp (btor, dst);
}

/*------------------------------------------------------------------------*/

static BtorNode *
map_node (Btor *btor, BtorNodeMap *map, BtorNode *exp)
{
  BtorNode *m[3], *src, *dst, *real_exp;
  int i;

  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  for (i = 0; i < exp->arity; i++)
  {
    src  = exp->e[i];
    dst  = btor_mapped_node (map, src);
    m[i] = dst ? dst : src;
    assert (BTOR_REAL_ADDR_NODE (m[i])->btor == btor);
  }

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

    case BTOR_PROXY_NODE:
    case BTOR_BV_VAR_NODE:
    case BTOR_ARRAY_VAR_NODE: return btor_copy_exp (btor, exp);
    case BTOR_SLICE_NODE:
      return btor_slice_exp (btor, m[0], exp->upper, exp->lower);
    case BTOR_AND_NODE: return btor_and_exp (btor, m[0], m[1]);
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: return btor_eq_exp (btor, m[0], m[1]);
    case BTOR_ADD_NODE: return btor_add_exp (btor, m[0], m[1]);
    case BTOR_MUL_NODE: return btor_mul_exp (btor, m[0], m[1]);
    case BTOR_ULT_NODE: return btor_ult_exp (btor, m[0], m[1]);
    case BTOR_SLL_NODE: return btor_sll_exp (btor, m[0], m[1]);
    case BTOR_SRL_NODE: return btor_srl_exp (btor, m[0], m[1]);
    case BTOR_UDIV_NODE: return btor_udiv_exp (btor, m[0], m[1]);
    case BTOR_UREM_NODE: return btor_urem_exp (btor, m[0], m[1]);
    case BTOR_CONCAT_NODE: return btor_concat_exp (btor, m[0], m[1]);
    case BTOR_READ_NODE: return btor_read_exp (btor, m[0], m[1]);
    case BTOR_WRITE_NODE: return btor_write_exp (btor, m[0], m[1], m[2]);
    case BTOR_LAMBDA_NODE: return btor_lambda_exp (btor, m[0], m[1]);
    default:
      assert (BTOR_IS_ARRAY_OR_BV_COND_NODE (exp));
      return btor_cond_exp (btor, m[0], m[1], m[2]);
  }
}

BtorNode *
btor_non_recursive_extended_substitute_node (Btor *btor,
                                             BtorNodeMap *map,
                                             void *state,
                                             BtorNodeMapper mapper,
                                             BtorNode *root)
{
  BtorNodePtrStack working_stack, marked_stack;
  BtorNode *res, *node, *mapped;
  BtorMemMgr *mm = btor->mm;
  int i;
  BTOR_INIT_STACK (working_stack);
  BTOR_INIT_STACK (marked_stack);
  BTOR_PUSH_STACK (mm, working_stack, root);
  while (!BTOR_EMPTY_STACK (working_stack))
  {
    node = BTOR_POP_STACK (working_stack);
    node = BTOR_REAL_ADDR_NODE (node);
    if (btor_mapped_node (map, node)) continue;
    if (node->mark == 2) continue;
    mapped = mapper (btor, state, node);
    if (mapped)
    {
      btor_map_node (btor, map, node, mapped);
      btor_release_exp (btor, mapped);
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
      mapped = map_node (btor, map, node);
      btor_map_node (btor, map, node, mapped);
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
      btor, map, 0, btor_never_map_mapper, root);
}

/*------------------------------------------------------------------------*/

BtorAIGMap *
btor_new_aig_map (Btor *btor)
{
  assert (btor);
  return btor_new_ptr_hash_table (btor->mm, 0, 0);
}

BtorAIG *
btor_mapped_aig (BtorAIGMap *map, BtorAIG *aig)
{
  assert (map);
  assert (aig);

  BtorPtrHashBucket *bucket;
  BtorAIG *res;

  bucket = btor_find_in_ptr_hash_table (map, aig);
  if (!bucket) return 0;
  assert (bucket->key == aig);
  res = bucket->data.asPtr;
  if (BTOR_IS_INVERTED_AIG (aig)) res = BTOR_INVERT_AIG (res);
  return res;
}

void
btor_map_aig (Btor *btor, BtorAIGMap *map, BtorAIG *src, BtorAIG *dst)
{
  assert (btor);
  assert (map);
  assert (src);
  assert (dst);

  BtorPtrHashBucket *bucket;
  BtorAIGMgr *amgr;

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  if (BTOR_IS_INVERTED_AIG (src))
  {
    src = BTOR_INVERT_AIG (src);
    dst = BTOR_INVERT_AIG (dst);
  }
  assert (!btor_find_in_ptr_hash_table (map, src));
  bucket = btor_insert_in_ptr_hash_table (map, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_aig (amgr, src);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = btor_copy_aig (amgr, dst);
}
void
btor_delete_aig_map (Btor *btor, BtorNodeMap *map)
{
  assert (btor);
  assert (map);

  BtorPtrHashBucket *bucket;
  BtorAIGMgr *amgr;

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  for (bucket = map->first; bucket; bucket = bucket->next)
  {
    btor_release_aig (amgr, bucket->key);
    btor_release_aig (amgr, bucket->data.asPtr);
  }
  btor_delete_ptr_hash_table (map);
}

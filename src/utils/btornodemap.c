/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btornodemap.h"
#include "btorcore.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"

/*------------------------------------------------------------------------*/

BtorNodeMap *
btor_new_node_map (Btor *btor)
{
  BtorNodeMap *res;

  assert (btor);

  BTOR_NEW (btor->mm, res);
  res->btor  = btor;
  res->table = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  return res;
}

void
btor_delete_node_map (BtorNodeMap *map)
{
  assert (map);

  BtorPtrHashTableIterator it;
  BtorNode *cur;

  btor_init_node_ptr_hash_table_iterator (&it, map->table);
  while (btor_has_next_node_ptr_hash_table_iterator (&it))
  {
    btor_release_exp (
        BTOR_REAL_ADDR_NODE ((BtorNode *) it.bucket->data.as_ptr)->btor,
        it.bucket->data.as_ptr);
    cur = btor_next_node_ptr_hash_table_iterator (&it);
    btor_release_exp (BTOR_REAL_ADDR_NODE (cur)->btor, cur);
  }
  btor_delete_ptr_hash_table (map->table);
  BTOR_DELETE (map->btor->mm, map);
}

BtorNode *
btor_mapped_node (BtorNodeMap *map, const BtorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorNode *real_node;
  BtorNode *res;

  real_node = BTOR_REAL_ADDR_NODE (node);
  bucket    = btor_get_ptr_hash_table (map->table, real_node);
  if (!bucket) return 0;
  assert (bucket->key == real_node);
  res = bucket->data.as_ptr;
  if (BTOR_IS_INVERTED_NODE (node)) res = BTOR_INVERT_NODE (res);
  return res;
}

int
btor_count_map (const BtorNodeMap *map)
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

  if (BTOR_IS_INVERTED_NODE (src))
  {
    src = BTOR_INVERT_NODE (src);
    dst = BTOR_INVERT_NODE (dst);
  }
  assert (!btor_get_ptr_hash_table (map->table, src));
  bucket = btor_add_ptr_hash_table (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_exp (BTOR_REAL_ADDR_NODE (src)->btor, src);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = btor_copy_exp (BTOR_REAL_ADDR_NODE (dst)->btor, dst);
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

      // FIXME real_exp = exp weil BTOR_IS_REGULAR_NODE (exp)
      real_exp = BTOR_REAL_ADDR_NODE (exp);
      if (real_exp->btor != btor)
      {
        BtorNode *res = btor_const_exp (btor, btor_const_get_bits (exp));
        if (real_exp != exp) res = BTOR_INVERT_NODE (res);
        return res;
      }

      // ELSE FALL THROUGH!!!

    case BTOR_BV_VAR_NODE:
    case BTOR_UF_NODE: return btor_copy_exp (btor, exp);
    case BTOR_SLICE_NODE:
      return btor_slice_exp (
          btor, m[0], btor_slice_get_upper (exp), btor_slice_get_lower (exp));
    case BTOR_AND_NODE: return btor_and_exp (btor, m[0], m[1]);
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE: return btor_eq_exp (btor, m[0], m[1]);
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
      assert (btor_is_bv_cond_node (exp));
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
  BtorNodePtrStack working_stack;
  BtorNode *res, *node, *mapped;
  BtorMemMgr *mm;
  int i;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm   = btor->mm;
  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (working_stack);
  BTOR_PUSH_STACK (mm, working_stack, root);

  while (!BTOR_EMPTY_STACK (working_stack))
  {
    node = BTOR_POP_STACK (working_stack);
    node = BTOR_REAL_ADDR_NODE (node);
    assert (node->kind != BTOR_PROXY_NODE);
    if (btor_mapped_node (map, node)) continue;
    d = btor_get_int_hash_map (mark, node->id);
    if (d && d->as_int == 1) continue;
    mapped = mapper (btor, state, node);
    if (mapped)
    {
      btor_map_node (map, node, mapped);
      release (btor, mapped);
    }
    else if (!d)
    {
      btor_add_int_hash_map (mark, node->id);
      BTOR_PUSH_STACK (mm, working_stack, node);
      for (i = node->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, working_stack, node->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;
      mapped    = btor_map_node_internal (btor, map, node);
      btor_map_node (map, node, mapped);
      btor_release_exp (btor, mapped);
    }
  }
  BTOR_RELEASE_STACK (mm, working_stack);
  btor_delete_int_hash_map (mark);
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

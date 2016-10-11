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

/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btornodemap.h"
#include "btorcore.h"
#include "utils/btorhashint.h"

/*------------------------------------------------------------------------*/

BtorNodeMap *
btor_nodemap_new (Btor *btor)
{
  BtorNodeMap *res;

  assert (btor);

  BTOR_NEW (btor->mm, res);
  res->btor  = btor;
  res->table = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  return res;
}

void
btor_nodemap_delete (BtorNodeMap *map)
{
  assert (map);

  BtorPtrHashTableIterator it;
  BtorNode *cur;

  btor_iter_hashptr_init (&it, map->table);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_release_exp (
        BTOR_REAL_ADDR_NODE ((BtorNode *) it.bucket->data.as_ptr)->btor,
        it.bucket->data.as_ptr);
    cur = btor_iter_hashptr_next (&it);
    btor_release_exp (BTOR_REAL_ADDR_NODE (cur)->btor, cur);
  }
  btor_hashptr_table_delete (map->table);
  BTOR_DELETE (map->btor->mm, map);
}

BtorNode *
btor_nodemap_mapped (BtorNodeMap *map, const BtorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorNode *real_node;
  BtorNode *res;

  real_node = BTOR_REAL_ADDR_NODE (node);
  bucket    = btor_hashptr_table_get (map->table, real_node);
  if (!bucket) return 0;
  assert (bucket->key == real_node);
  res = bucket->data.as_ptr;
  if (BTOR_IS_INVERTED_NODE (node)) res = BTOR_INVERT_NODE (res);
  return res;
}

void
btor_nodemap_map (BtorNodeMap *map, BtorNode *src, BtorNode *dst)
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
  assert (!btor_hashptr_table_get (map->table, src));
  bucket = btor_hashptr_table_add (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_exp (BTOR_REAL_ADDR_NODE (src)->btor, src);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = btor_copy_exp (BTOR_REAL_ADDR_NODE (dst)->btor, dst);
}

/*------------------------------------------------------------------------*/
/* iterators    						          */
/*------------------------------------------------------------------------*/

void
btor_iter_nodemap_init (BtorNodeMapIterator *it, const BtorNodeMap *map)
{
  assert (map);
  btor_iter_hashptr_init (&it->it, map->table);
}

void
btor_iter_nodemap_init_reversed (BtorNodeMapIterator *it,
                                 const BtorNodeMap *map)
{
  assert (map);
  btor_iter_hashptr_init_reversed (&it->it, map->table);
}

bool
btor_iter_nodemap_has_next (const BtorNodeMapIterator *it)
{
  return btor_iter_hashptr_has_next (&it->it);
}

void
btor_iter_nodemap_queue (BtorNodeMapIterator *it, const BtorNodeMap *map)
{
  assert (map);
  btor_iter_hashptr_queue (&it->it, map->table);
}

BtorNode *
btor_iter_nodemap_next (BtorNodeMapIterator *it)
{
  return btor_iter_hashptr_next (&it->it);
}

BtorHashTableData *
btor_iter_nodemap_next_data (BtorNodeMapIterator *it)
{
  return btor_iter_hashptr_next_data (&it->it);
}

/*------------------------------------------------------------------------*/

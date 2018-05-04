/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
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
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);
  return res;
}

void
btor_nodemap_delete (BtorNodeMap *map)
{
  assert (map);

  BtorPtrHashTableIterator it;
  BtorNode *src;
  BtorNode *dst;

  btor_iter_hashptr_init (&it, map->table);
  while (btor_iter_hashptr_has_next (&it))
  {
    dst = (BtorNode *) it.bucket->data.as_ptr;
    btor_node_release (btor_node_real_addr (dst)->btor, dst);
    src = btor_iter_hashptr_next (&it);
    btor_node_release (btor_node_real_addr (src)->btor, src);
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

  real_node = btor_node_real_addr (node);
  bucket    = btor_hashptr_table_get (map->table, real_node);
  if (!bucket) return 0;
  assert (bucket->key == real_node);
  res = bucket->data.as_ptr;
  if (btor_node_is_inverted (node)) res = btor_node_invert (res);
  return res;
}

void
btor_nodemap_map (BtorNodeMap *map, BtorNode *src, BtorNode *dst)
{
  BtorPtrHashBucket *bucket;

  assert (map);
  assert (src);
  assert (dst);

  if (btor_node_is_inverted (src))
  {
    src = btor_node_invert (src);
    dst = btor_node_invert (dst);
  }
  assert (!btor_hashptr_table_get (map->table, src));
  bucket = btor_hashptr_table_add (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_node_copy (btor_node_real_addr (src)->btor, src);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = btor_node_copy (btor_node_real_addr (dst)->btor, dst);
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

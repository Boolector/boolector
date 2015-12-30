/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btoraigmap.h"
#include "btorcore.h"
#include "utils/btoriter.h"

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
  bucket   = btor_get_ptr_hash_table (map->table, real_aig);
  if (!bucket) return 0;
  assert (bucket->key == real_aig);
  res = bucket->data.as_ptr;
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
  assert (!btor_get_ptr_hash_table (map->table, src));
  bucket = btor_add_ptr_hash_table (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_aig (map->amgr_src, src);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = btor_copy_aig (map->amgr_dst, dst);
}

void
btor_delete_aig_map (BtorAIGMap *map)
{
  assert (map);

  Btor *btor;
  BtorHashTableIterator it;

  btor = map->btor;

  btor_init_hash_table_iterator (&it, map->table);
  while (btor_has_next_hash_table_iterator (&it))
  {
    btor_release_aig (map->amgr_dst, it.bucket->data.as_ptr);
    btor_release_aig (map->amgr_src, btor_next_hash_table_iterator (&it));
  }
  btor_delete_ptr_hash_table (map->table);
  BTOR_DELETE (btor->mm, map);
}

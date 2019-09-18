/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btoraigmap.h"
#include "btorcore.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/

BtorAIGMap *
btor_aigmap_new (Btor *btor, BtorAIGMgr *amgr_src, BtorAIGMgr *amgr_dst)
{
  assert (btor);
  assert (amgr_src);
  assert (amgr_dst);

  BtorAIGMap *res;

  BTOR_NEW (btor->mm, res);
  res->btor     = btor;
  res->amgr_src = amgr_src;
  res->amgr_dst = amgr_dst;
  res->table    = btor_hashptr_table_new (btor->mm, 0, 0);
  return res;
}

BtorAIG *
btor_aigmap_mapped (BtorAIGMap *map, BtorAIG *aig)
{
  assert (map);
  assert (aig);

  BtorPtrHashBucket *bucket;
  BtorAIG *real_aig, *res;

  real_aig = btor_aig_real_addr (aig);
  bucket   = btor_hashptr_table_get (map->table, real_aig);
  if (!bucket) return 0;
  assert (bucket->key == real_aig);
  res = bucket->data.as_ptr;
  if (btor_aig_is_inverted (aig)) res = btor_aig_invert (res);
  return res;
}

void
btor_aigmap_map (BtorAIGMap *map, BtorAIG *src, BtorAIG *dst)
{
  assert (map);
  assert (src);
  assert (dst);

  BtorPtrHashBucket *bucket;

  if (btor_aig_is_inverted (src))
  {
    assert (btor_aig_is_inverted (dst));
    src = btor_aig_invert (src);
    dst = btor_aig_invert (dst);
  }
  assert (!btor_hashptr_table_get (map->table, src));
  bucket = btor_hashptr_table_add (map->table, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_aig_copy (map->amgr_src, src);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = btor_aig_copy (map->amgr_dst, dst);
}

void
btor_aigmap_delete (BtorAIGMap *map)
{
  assert (map);

  Btor *btor;
  BtorPtrHashTableIterator it;

  btor = map->btor;

  btor_iter_hashptr_init (&it, map->table);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_aig_release (map->amgr_dst, it.bucket->data.as_ptr);
    btor_aig_release (map->amgr_src, btor_iter_hashptr_next (&it));
  }
  btor_hashptr_table_delete (map->table);
  BTOR_DELETE (btor->mm, map);
}

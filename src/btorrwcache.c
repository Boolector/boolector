/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorrwcache.h"
#include "btorcore.h"

static uint32_t hash_primes[] = {
    333444569u, 76891121u, 456790003u, 2654435761u};

int32_t
compare_rw_cache_tuple (const BtorRwCacheTuple *t0, const BtorRwCacheTuple *t1)
{
  assert (t0);
  assert (t1);

  if (t0->kind == t1->kind && t0->n[0] == t1->n[0] && t0->n[1] == t1->n[1]
      && t0->n[2] == t1->n[2])
  {
    return 0;
  }
  return 1;
}

uint32_t
hash_rw_cache_tuple (const BtorRwCacheTuple *t)
{
  uint32_t hash;
  hash = hash_primes[0] * (uint32_t) t->kind;
  hash += hash_primes[1] * (uint32_t) t->n[0];
  hash += hash_primes[2] * (uint32_t) t->n[1];
  hash += hash_primes[3] * (uint32_t) t->n[2];
  return hash;
}

static bool
is_valid_node (Btor *btor, int32_t id)
{
  BtorNode *n = btor_node_get_by_id (btor, id);
  if (!n || btor_node_is_proxy (n))
  {
    return false;
  }
  return true;
}

int32_t
btor_rw_cache_get (BtorRwCache *rwc,
                   BtorNodeKind kind,
                   int32_t nid0,
                   int32_t nid1,
                   int32_t nid2)
{
#ifndef NDEBUG
  assert (!nid0 || is_valid_node (rwc->btor, nid0));
  /* For slice nodes nid1 and nid2 correspond to the upper/lower indices. */
  if (kind != BTOR_BV_SLICE_NODE)
  {
    assert (!nid1 || is_valid_node (rwc->btor, nid1));
    assert (!nid2 || is_valid_node (rwc->btor, nid2));
  }
#endif

  BtorRwCacheTuple t   = {.kind = kind, .n = {nid0, nid1, nid2}};
  BtorPtrHashBucket *b = btor_hashptr_table_get (rwc->cache, &t);
  if (b)
  {
    BtorRwCacheTuple *cached = b->key;
    return cached->result;
  }
  return 0;
}

void
btor_rw_cache_add (BtorRwCache *rwc,
                   BtorNodeKind kind,
                   int32_t nid0,
                   int32_t nid1,
                   int32_t nid2,
                   int32_t result)
{
  assert (result);

#ifndef NDEBUG
  assert (is_valid_node (rwc->btor, result));
  assert (!nid0 || is_valid_node (rwc->btor, nid0));
  /* For slice nodes nid1 and nid2 correspond to the upper/lower indices. */
  if (kind != BTOR_BV_SLICE_NODE)
  {
    assert (!nid1 || is_valid_node (rwc->btor, nid1));
    assert (!nid2 || is_valid_node (rwc->btor, nid2));
  }
#endif

  /* The bruttomesso benchmark family produces extremely many distinct slice
   * nodes that let's the cache grow to several GB in some cases. For now, we
   * will disable caching of slice nodes until we find a better solution.
   * Note: Calling btor_rw_cache_gc(...) does not help here. */
  if (kind == BTOR_BV_SLICE_NODE)
  {
    return;
  }

  int32_t cached_result_id;
  if ((cached_result_id = btor_rw_cache_get (rwc, kind, nid0, nid1, nid2)))
  {
    /* This can only happen if the node corresponding to cached_result_id does
     * not exist anymore (= deallocated). */
    if (cached_result_id != result)
    {
      assert (btor_node_get_by_id (rwc->btor, cached_result_id) == 0);
      BtorRwCacheTuple t   = {.kind = kind, .n = {nid0, nid1, nid2}};
      BtorPtrHashBucket *b = btor_hashptr_table_get (rwc->cache, &t);
      assert (b);
      BtorRwCacheTuple *cached = b->key;
      cached->result           = result;  // Update the result
      rwc->num_update++;
    }
    return;
  }

  BtorRwCacheTuple *t;
  BTOR_CNEW (rwc->btor->mm, t);
  t->kind   = kind;
  t->n[0]   = nid0;
  t->n[1]   = nid1;
  t->n[2]   = nid2;
  t->result = result;
  rwc->num_add++;

  btor_hashptr_table_add (rwc->cache, t);

  if (rwc->num_add % 100000 == 0)
  {
    btor_rw_cache_gc (rwc);
  }
}

void
btor_rw_cache_init (BtorRwCache *rwc, Btor *btor)
{
  assert (rwc);
  rwc->btor       = btor;
  rwc->cache      = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) hash_rw_cache_tuple,
                                       (BtorCmpPtr) compare_rw_cache_tuple);
  rwc->num_add    = 0;
  rwc->num_get    = 0;
  rwc->num_update = 0;
  rwc->num_remove = 0;
}

void
btor_rw_cache_delete (BtorRwCache *rwc)
{
  assert (rwc);

  BtorPtrHashTableIterator it;
  BtorRwCacheTuple *t;

  btor_iter_hashptr_init (&it, rwc->cache);
  while (btor_iter_hashptr_has_next (&it))
  {
    t = btor_iter_hashptr_next (&it);
    BTOR_DELETE (rwc->btor->mm, t);
  }
  btor_hashptr_table_delete (rwc->cache);
}

void
btor_rw_cache_reset (BtorRwCache *rwc)
{
  assert (rwc);
  assert (rwc->btor->mm);
  assert (rwc->cache);

  Btor *btor = rwc->btor;
  btor_rw_cache_delete (rwc);
  btor_rw_cache_init (rwc, btor);
}

void
btor_rw_cache_gc (BtorRwCache *rwc)
{
  assert (rwc->btor->mm);
  assert (rwc->cache);

  bool remove;
  BtorPtrHashTableIterator it;
  BtorRwCacheTuple *t;
  BtorNodeKind kind;

  Btor *btor            = rwc->btor;
  BtorPtrHashTable *old = rwc->cache;

  rwc->cache = btor_hashptr_table_new (btor->mm, old->hash, old->cmp);

  /* We remove all cache entries that store invalid children node ids. An
   * invalid node is either a node that does not exist anymore (deallocated) or
   * if the node id belongs to a proxy node. Proxy nodes are never used to
   * query the cache and are therefore useless cache entries. */
  btor_iter_hashptr_init (&it, old);
  while (btor_iter_hashptr_has_next (&it))
  {
    t = btor_iter_hashptr_next (&it);
    kind = t->kind;

    remove = !is_valid_node (btor, t->n[0]);

    if (!remove && kind != BTOR_BV_SLICE_NODE)
    {
      if (t->n[1])
      {
        remove = remove || !is_valid_node (btor, t->n[1]);
      }
      if (!remove && t->n[2])
      {
        remove = remove || !is_valid_node (btor, t->n[2]);
      }

      remove = remove || !btor_node_get_by_id (btor, t->result);
    }

    if (remove)
    {
      BTOR_DELETE (btor->mm, t);
      rwc->num_remove++;
    }
    else
    {
      btor_hashptr_table_add (rwc->cache, t);
    }
  }
  btor_hashptr_table_delete (old);
}

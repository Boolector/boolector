/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORRWCACHE_H_INCLUDED
#define BTORRWCACHE_H_INCLUDED

#include "btornode.h"
#include "utils/btorhashptr.h"

/* Cache entry that stores the result of rewriting a node with kind 'kind' and
 * it's children 'n'.
 * Note: In the case of BTOR_SLICE_NODE n[1] and n[2] are the upper and lower
 * indices. */
struct BtorRwCacheTuple
{
  BtorNodeKind kind;
  int32_t n[3];
  int32_t result;
};

typedef struct BtorRwCacheTuple BtorRwCacheTuple;

/* Stores all cache entries and some statistics. Note that the statistics are
 * not reset if btor_rw_cache_reset() or btor_rw_cache_gc() is called. */
struct BtorRwCache
{
  Btor *btor;
  BtorPtrHashTable *cache;  /* Hash table of BtorRwCacheTuple. */
  uint64_t num_add;         /* Number of cached rewrite rules. */
  uint64_t num_get;         /* Number of cache checks. */
  uint64_t num_update;      /* Number of updated cache entries. */
  uint64_t num_remove;      /* Number of removed cache entries (GC). */
};

typedef struct BtorRwCache BtorRwCache;

/* Add a new entry to the rewrite cache. */
void btor_rw_cache_add (BtorRwCache *cache,
                        BtorNodeKind kind,
                        int32_t nid0,
                        int32_t nid1,
                        int32_t nid2,
                        int32_t result_nid);

/* Check if we already cached a rewritten node. */
int32_t btor_rw_cache_get (BtorRwCache *cache,
                           BtorNodeKind kind,
                           int32_t nid0,
                           int32_t nid1,
                           int32_t nid2);

/* Initialize the rewrite cache. */
void btor_rw_cache_init (BtorRwCache *cache, Btor *mm);

/* Delete the rewrite cache. */
void btor_rw_cache_delete (BtorRwCache *cache);

/* Reset the rewrite cache. */
void btor_rw_cache_reset (BtorRwCache *cache);

/* Remove all cache entries that contain invalid nodes (= deallocated) or
 * proxies as children. */
void btor_rw_cache_gc (BtorRwCache *cache);

#endif

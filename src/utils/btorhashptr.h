/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_PTR_HASH_H_INCLUDED
#define BTOR_PTR_HASH_H_INCLUDED

#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include "utils/btorhash.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"

/*------------------------------------------------------------------------*/

typedef struct BtorPtrHashTable BtorPtrHashTable;
typedef struct BtorPtrHashBucket BtorPtrHashBucket;

typedef void *(*BtorCloneKeyPtr) (BtorMemMgr *mm,
                                  const void *map,
                                  const void *key);
typedef void (*BtorCloneDataPtr) (BtorMemMgr *mm,
                                  const void *map,
                                  BtorHashTableData *data,
                                  BtorHashTableData *cloned_data);

struct BtorPtrHashBucket
{
  /* public:
   */
  void *key;

  BtorHashTableData data;

  BtorPtrHashBucket *next; /* chronologically */
  BtorPtrHashBucket *prev; /* chronologically */

  /* private:
   */
  BtorPtrHashBucket *chain; /* collision chain */
};

struct BtorPtrHashTable
{
  BtorMemMgr *mm;

  uint32_t size;
  uint32_t count;
  BtorPtrHashBucket **table;

  BtorHashPtr hash;
  BtorCmpPtr cmp;

  BtorPtrHashBucket *first; /* chronologically */
  BtorPtrHashBucket *last;  /* chronologically */
};

/*------------------------------------------------------------------------*/

BtorPtrHashTable *btor_hashptr_table_new (BtorMemMgr *,
                                          BtorHashPtr,
                                          BtorCmpPtr);

/* Clone hash table. 'ckey' is a function mapping key to cloned key,
 * 'cdata' is a function mapping data to cloned data (note: as_ptr vs.
 * as_int!). 'key_map' represents a map mapping key to cloned key values.
 * 'data_map' represents a map mapping data to cloned data values. */
BtorPtrHashTable *btor_hashptr_table_clone (BtorMemMgr *mm,
                                            BtorPtrHashTable *table,
                                            BtorCloneKeyPtr ckey,
                                            BtorCloneDataPtr cdata,
                                            const void *key_map,
                                            const void *data_map);

void btor_hashptr_table_delete (BtorPtrHashTable *p2iht);

BtorPtrHashBucket *btor_hashptr_table_get (BtorPtrHashTable *p2iht, void *key);

BtorPtrHashBucket *btor_hashptr_table_add (BtorPtrHashTable *p2iht, void *key);

/* Remove from hash table the bucket with the key.  The key has to be an
 * element of the hash table.  If 'stored_data_ptr' is non zero, then data
 * to which the given key was mapped is copied to this location.   The same
 * applies to 'stored_key_ptr'.  If you traverse/iterate a hash table
 * through the chronological chains, then you can remove elements while
 * traversing the hash table.
 */
void btor_hashptr_table_remove (BtorPtrHashTable *,
                                void *key,
                                void **stored_key_ptr,
                                BtorHashTableData *stored_data_ptr);

uint32_t btor_hash_str (const void *str);

#define btor_compare_str ((BtorCmpPtr) strcmp)

/*------------------------------------------------------------------------*/
/* iterators     		                                          */
/*------------------------------------------------------------------------*/

#define BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE 8

typedef struct BtorPtrHashTableIterator
{
  BtorPtrHashBucket *bucket;
  void *cur;
  bool reversed;
  uint8_t num_queued;
  uint8_t pos;
  const BtorPtrHashTable *stack[BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE];
} BtorPtrHashTableIterator;

void btor_iter_hashptr_init (BtorPtrHashTableIterator *it,
                             const BtorPtrHashTable *t);
void btor_iter_hashptr_init_reversed (BtorPtrHashTableIterator *it,
                                      const BtorPtrHashTable *t);
void btor_iter_hashptr_queue (BtorPtrHashTableIterator *it,
                              const BtorPtrHashTable *t);
bool btor_iter_hashptr_has_next (const BtorPtrHashTableIterator *it);
void *btor_iter_hashptr_next (BtorPtrHashTableIterator *it);
BtorHashTableData *btor_iter_hashptr_next_data (BtorPtrHashTableIterator *it);

/*------------------------------------------------------------------------*/
#endif

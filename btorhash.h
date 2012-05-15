/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_HASH_H_INCLUDED
#define BTOR_HASH_H_INCLUDED

#include <string.h>
#include "btormem.h"

#include <assert.h>

/*------------------------------------------------------------------------*/

typedef struct BtorPtrHashTable BtorPtrHashTable;
typedef struct BtorPtrHashBucket BtorPtrHashBucket;

typedef unsigned (*BtorHashPtr) (const void *key);
typedef int (*BtorCmpPtr) (const void *a, const void *b);

typedef union BtorPtrHashData BtorPtrHashData;

union BtorPtrHashData
{
  int asInt;
  void *asPtr;
  char *asStr;
};

struct BtorPtrHashBucket
{
  /* public:
   */
  void *key;

  BtorPtrHashData data;

  BtorPtrHashBucket *next; /* chronologically */
  BtorPtrHashBucket *prev; /* chronologically */

  /* private:
   */
  BtorPtrHashBucket *chain; /* collision chain */
};

struct BtorPtrHashTable
{
  BtorMemMgr *mem;

  unsigned size;
  unsigned count;
  BtorPtrHashBucket **table;

  BtorHashPtr hash;
  BtorCmpPtr cmp;

  BtorPtrHashBucket *first; /* chronologically */
  BtorPtrHashBucket *last;  /* chronologically */
};

/*------------------------------------------------------------------------*/

BtorPtrHashTable *btor_new_ptr_hash_table (BtorMemMgr *,
                                           BtorHashPtr,
                                           BtorCmpPtr);

void btor_delete_ptr_hash_table (BtorPtrHashTable *);

BtorPtrHashBucket *btor_find_in_ptr_hash_table (BtorPtrHashTable *, void *);

BtorPtrHashBucket *btor_insert_in_ptr_hash_table (BtorPtrHashTable *, void *);

/* Remove from hash table the bucke with the key.  The key has to be an
 * element of the hash table.  If 'stored_data_ptr' is non zero, then data
 * to which the given key was mapped is copied to this location.   The same
 * applies to 'stored_key_ptr'.  If you traverse/iterate a hash table
 * through the chronological chains, then you can remove elements while
 * traversing the hash table.
 */
void btor_remove_from_ptr_hash_table (BtorPtrHashTable *,
                                      void *key,
                                      void **stored_key_ptr,
                                      BtorPtrHashData *stored_data_ptr);

unsigned btor_hashstr (const void *str);

#define btor_cmpstr ((BtorCmpPtr) strcmp)

#endif

#ifndef BTOR_HASH_H_INCLUDED
#define BTOR_HASH_H_INCLUDED

#include <string.h>
#include "btormem.h"

#include <assert.h>

typedef struct BtorPtrToIntHashTable BtorPtrToIntHashTable;
typedef struct BtorPtrToIntHashBucket BtorPtrToIntHashBucket;

typedef unsigned (*BtorHashPtr) (void *key);
typedef int (*BtorCmpPtr) (void *a, void *b);

struct BtorPtrToIntHashBucket
{
  /* public:
   */
  void *key;
  int data;

  BtorPtrToIntHashBucket *next; /* chronologically */

  /* private:
   */
  BtorPtrToIntHashBucket *chain; /* collision chain */
};

struct BtorPtrToIntHashTable
{
  BtorMemMgr *mem;

  unsigned size;
  unsigned count;
  BtorPtrToIntHashBucket **table;

  BtorHashPtr hash;
  BtorCmpPtr cmp;

  BtorPtrToIntHashBucket *first; /* chronologically */
  BtorPtrToIntHashBucket *last;  /* chronologically */
};

BtorPtrToIntHashTable *btor_new_ptr_to_int_hash_table (BtorMemMgr *,
                                                       BtorHashPtr,
                                                       BtorCmpPtr);

void btor_delete_ptr_to_int_hash_table (BtorPtrToIntHashTable *);

BtorPtrToIntHashBucket *btor_find_in_ptr_to_int_hash_table (
    BtorPtrToIntHashTable *, void *);

BtorPtrToIntHashBucket *btor_insert_in_ptr_to_int_hash_table (
    BtorPtrToIntHashTable *, void *key, int data);

unsigned btor_hashstr (void *str);

#define btor_cmpstr ((BtorCmpPtr) strcmp)

#endif

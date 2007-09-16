#ifndef BTOR_HASH_H_INCLUDED
#define BTOR_HASH_H_INCLUDED

#include <string.h>
#include "btormem.h"

#include <assert.h>

typedef struct BtorPtrHashTable BtorPtrHashTable;
typedef struct BtorPtrHashBucket BtorPtrHashBucket;

typedef unsigned (*BtorHashPtr) (void *key);
typedef int (*BtorCmpPtr) (void *a, void *b);

struct BtorPtrHashBucket
{
  /* public:
   */
  void *key;

  union
  {
    int asInt;
    void *asPtr;
    char *asStr;
  } data;

  BtorPtrHashBucket *next; /* chronologically */

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

BtorPtrHashTable *btor_new_ptr_hash_table (BtorMemMgr *,
                                           BtorHashPtr,
                                           BtorCmpPtr);

void btor_delete_ptr_hash_table (BtorPtrHashTable *);

BtorPtrHashBucket *btor_find_in_ptr_hash_table (BtorPtrHashTable *, void *);

BtorPtrHashBucket *btor_insert_in_ptr_hash_table (BtorPtrHashTable *,
                                                  void *key);

unsigned btor_hashstr (void *str);

#define btor_cmpstr ((BtorCmpPtr) strcmp)

#endif

#ifndef BTOR_HASH_H_INCLUDED
#define BTOR_HASH_H_INCLUDED

#include <assert.h>
#include "btormem.h"

typedef struct BtorPtrToIntHashTable BtorPtrToIntHashTable;
typedef struct BtorPtrToIntHashBucket BtorPtrToIntHashBucket;

typedef unsigned (*BtorHashPtr) (void *state, void *key);
typedef int (*BtorCmpPtr) (void *state, void *a, void *b);

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

  void *state;
  BtorHashPtr hash;
  BtorCmpPtr cmp;

  BtorPtrToIntHashBucket *first; /* chronologically */
  BtorPtrToIntHashBucket *last;  /* chronologically */
};

BtorPtrToIntHashTable *btor_new_ptr_to_int_hash_table (BtorMemMgr *,
                                                       void *state,
                                                       BtorHashPtr,
                                                       BtorCmpPtr);

void btor_delete_ptr_to_int_hash_tabale (BtorPtrToIntHashTable *);

BtorPtrToIntHashBucket *btor_find_in_ptr_to_int_hash_table (
    BtorPtrToIntHashTable *, void *);

BtorPtrToIntHashBucket *btor_insert_in_ptr_to_int_hash_table (
    BtorPtrToIntHashTable *, void *key, int data);

unsigned btor_hashstr (void *state_dummy, void *str);
int btor_cmpstr (void *state_dummy, void *a, void *b);

#endif

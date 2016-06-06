/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_PTR2_HASH_H_INCLUDED
#define BTOR_PTR2_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "utils/btorhashptr.h"
#include "utils/btormem.h"

union BtorPtrHashTable2Data
{
  int32_t as_int;
  void *as_ptr;
  char *as_str;
};

typedef union BtorPtrHashTable2Data BtorPtrHashTable2Data;

struct BtorPtrHashTable2
{
  BtorMemMgr *mm;
  size_t count;
  size_t size;
  void **keys;
  uint8_t *hop_info; /* displacement information */
  BtorPtrHashTable2Data *data;
  size_t *next;
  size_t *prev;

  size_t first;
  size_t last;

  BtorHashPtr hash;
  BtorCmpPtr cmp;
};

typedef struct BtorPtrHashTable2 BtorPtrHashTable2;

/* Create new int32_t hash table. */
BtorPtrHashTable2 *btor_new_ptr_hash_table2 (BtorMemMgr *,
                                             BtorHashPtr,
                                             BtorCmpPtr);

/* Free int32_t hash table. */
void btor_delete_ptr_hash_table2 (BtorPtrHashTable2 *);

/* Returns the size of the BtorPtrHashTable2 in Byte. */
size_t btor_size_ptr_hash_table2 (BtorPtrHashTable2 *);

/* Add 'key' to the hash table and return the position at which 'key' is
 * stored in the keys array. */
size_t btor_add_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* Check whether 'key' is in the hash table. */
bool btor_contains_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* Remove 'key' from the hash table and return the position at which 'key'
 * was stored in the keys array. */
size_t btor_remove_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* Returns the position at which 'key' is stored in the keys array. It returns
 * 'size' of the hash table if 'key' could not be found. */
// TODO (ma): remove
size_t btor_get_pos_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* map functions */

BtorPtrHashTable2 *btor_new_ptr_hash_map2 (BtorMemMgr *,
                                           BtorHashPtr,
                                           BtorCmpPtr);

bool btor_contains_ptr_hash_map2 (BtorPtrHashTable2 *, void *key);

void btor_remove_ptr_hash_map2 (BtorPtrHashTable2 *,
                                void *key,
                                BtorPtrHashTable2Data *stored_data);

BtorPtrHashTable2Data *btor_add_ptr_hash_map2 (BtorPtrHashTable2 *, void *key);
BtorPtrHashTable2Data *btor_get_ptr_hash_map2 (BtorPtrHashTable2 *, void *key);

void btor_delete_ptr_hash_map2 (BtorPtrHashTable2 *);

#endif

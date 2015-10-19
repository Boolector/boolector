/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_INT_HASH_H_INCLUDED
#define BTOR_INT_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "utils/btormem.h"

struct BtorIntHashTable
{
  BtorMemMgr *mm;
  size_t count;
  size_t size;
  int32_t *keys;
  uint8_t *hop_info; /* displacement information */
};

typedef struct BtorIntHashTable BtorIntHashTable;

/* Create new int32_t hash table. */
BtorIntHashTable *btor_new_int_hash_table (BtorMemMgr *);

/* Free int32_t hash table. */
void btor_free_int_hash_table (BtorIntHashTable *);

/* Returns the size of the BtorIntHashTable in Byte. */
size_t btor_size_int_hash_table (BtorIntHashTable *);

/* Add 'key' to the hash table and return the position at which 'key' is
 * stored in the keys array. */
size_t btor_add_int_hash_table (BtorIntHashTable *, int32_t key);

/* Check whether 'key' is in the hash table. */
bool btor_contains_int_hash_table (BtorIntHashTable *, int32_t key);

/* Remove 'key' from the hash table and return the position at which 'key'
 * was stored in the keys array. */
size_t btor_remove_int_hash_table (BtorIntHashTable *, int32_t key);

/* Returns the position at which 'key' is stored in the keys array. It returns
 * 'size' of the hash table if 'key' could not be found. */
size_t btor_get_pos_int_hash_table (BtorIntHashTable *, int32_t key);
#endif

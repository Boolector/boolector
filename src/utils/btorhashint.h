/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_INT_HASH_H_INCLUDED
#define BTOR_INT_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "utils/btorhash.h"
#include "utils/btormem.h"

/*------------------------------------------------------------------------*/

struct BtorIntHashTable
{
  BtorMemMgr *mm;
  size_t count;
  size_t size;
  int32_t *keys;
  uint8_t *hop_info; /* displacement information */
  BtorHashTableData *data;
};

typedef struct BtorIntHashTable BtorIntHashTable;

/*------------------------------------------------------------------------*/
/* hash table                                                             */
/*------------------------------------------------------------------------*/

/* Create new int32_t hash table. */
BtorIntHashTable *btor_hashint_table_new (BtorMemMgr *);

/* Free int32_t hash table. */
void btor_hashint_table_delete (BtorIntHashTable *);

/* Returns the size of the BtorIntHashTable in Byte. */
size_t btor_hashint_table_size (BtorIntHashTable *);

/* Add 'key' to the hash table and return the position at which 'key' is
 * stored in the keys array. */
size_t btor_hashint_table_add (BtorIntHashTable *, int32_t key);

/* Check whether 'key' is in the hash table. */
bool btor_hashint_table_contains (BtorIntHashTable *, int32_t key);

/* Remove 'key' from the hash table and return the position at which 'key'
 * was stored in the keys array. */
size_t btor_hashint_table_remove (BtorIntHashTable *, int32_t key);

/* Returns the position at which 'key' is stored in the keys array. It returns
 * 'size' of the hash table if 'key' could not be found. */
// TODO (ma): remove
size_t btor_hashint_table_get_pos (BtorIntHashTable *, int32_t key);

BtorIntHashTable *btor_hashint_table_clone (BtorMemMgr *mm,
                                            BtorIntHashTable *table);

/*------------------------------------------------------------------------*/
/* hash map                                                               */
/*------------------------------------------------------------------------*/

BtorIntHashTable *btor_hashint_map_new (BtorMemMgr *);

bool btor_hashint_map_contains (BtorIntHashTable *, int32_t key);

void btor_hashint_map_remove (BtorIntHashTable *,
                              int32_t key,
                              BtorHashTableData *stored_data);

BtorHashTableData *btor_hashint_map_add (BtorIntHashTable *, int32_t key);
BtorHashTableData *btor_hashint_map_get (BtorIntHashTable *, int32_t key);

void btor_hashint_map_delete (BtorIntHashTable *);

BtorIntHashTable *btor_hashint_map_clone (BtorMemMgr *mm,
                                          BtorIntHashTable *table,
                                          BtorCloneHashTableData cdata,
                                          const void *data_map);

/*------------------------------------------------------------------------*/
/* iterators                                                              */
/*------------------------------------------------------------------------*/

typedef struct BtorIntHashTableIterator
{
  size_t cur_pos;
  const BtorIntHashTable *t;
} BtorIntHashTableIterator;

void btor_iter_hashint_init (BtorIntHashTableIterator *it,
                             const BtorIntHashTable *t);

bool btor_iter_hashint_has_next (const BtorIntHashTableIterator *it);

int32_t btor_iter_hashint_next (BtorIntHashTableIterator *it);

BtorHashTableData *btor_iter_hashint_next_data (BtorIntHashTableIterator *it);

/*------------------------------------------------------------------------*/

#endif

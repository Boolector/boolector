/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorhashptr.h"

static uint32_t
btor_hash_ptr (const void *p)
{
  return 1183477 * (uint32_t) (uintptr_t) p;
}

static int32_t
btor_compare_ptr (const void *p, const void *q)
{
  return ((uintptr_t) p) != ((uintptr_t) q);
}

static void
btor_enlarge_ptr_hash_table (BtorPtrHashTable *p2iht)
{
  BtorPtrHashBucket *p, *chain, **old_table, **new_table;
  uint32_t old_size, new_size, i, h;
  BtorHashPtr hash;

  old_size  = p2iht->size;
  old_table = p2iht->table;

  new_size = old_size ? 2 * old_size : 1;
  BTOR_CNEWN (p2iht->mm, new_table, new_size);

  hash = p2iht->hash;

  for (i = 0; i < old_size; i++)
    for (p = old_table[i]; p; p = chain)
    {
      chain = p->chain;
      h     = hash (p->key);
      h &= new_size - 1;
      p->chain     = new_table[h];
      new_table[h] = p;
    }

  BTOR_DELETEN (p2iht->mm, old_table, old_size);

  p2iht->size  = new_size;
  p2iht->table = new_table;
}

BtorPtrHashTable *
btor_hashptr_table_new (BtorMemMgr *mm, BtorHashPtr hash, BtorCmpPtr cmp)
{
  BtorPtrHashTable *res;

  BTOR_NEW (mm, res);
  BTOR_CLR (res);

  res->mm   = mm;
  res->hash = hash ? hash : btor_hash_ptr;
  res->cmp  = cmp ? cmp : btor_compare_ptr;

  btor_enlarge_ptr_hash_table (res);

  return res;
}

BtorPtrHashTable *
btor_hashptr_table_clone (BtorMemMgr *mm,
                          BtorPtrHashTable *table,
                          BtorCloneKeyPtr ckey,
                          BtorCloneDataPtr cdata,
                          const void *key_map,
                          const void *data_map)
{
  assert (mm);
  assert (ckey);

  BtorPtrHashTable *res;
  BtorPtrHashTableIterator it;
  BtorPtrHashBucket *b, *cloned_b;
  void *key, *cloned_key;

  if (!table) return NULL;

  res = btor_hashptr_table_new (mm, table->hash, table->cmp);
  while (res->size < table->size) btor_enlarge_ptr_hash_table (res);
  assert (res->size == table->size);

  btor_iter_hashptr_init (&it, table);
  while (btor_iter_hashptr_has_next (&it))
  {
    b          = it.bucket;
    key        = btor_iter_hashptr_next (&it);
    cloned_key = ckey (mm, key_map, key);
    assert (cloned_key);
    cloned_b = btor_hashptr_table_add (res, cloned_key);
    if (!cdata)
      assert (b->data.as_ptr == 0);
    else
      cdata (mm, data_map, &b->data, &cloned_b->data);
  }

  assert (table->count == res->count);

  return res;
}

void
btor_hashptr_table_delete (BtorPtrHashTable *p2iht)
{
  BtorPtrHashBucket *p, *next;

  for (p = p2iht->first; p; p = next)
  {
    next = p->next;
    BTOR_DELETE (p2iht->mm, p);
  }

  BTOR_DELETEN (p2iht->mm, p2iht->table, p2iht->size);
  BTOR_DELETE (p2iht->mm, p2iht);
}

BtorPtrHashBucket *
btor_hashptr_table_get (BtorPtrHashTable *p2iht, void *key)
{
  BtorPtrHashBucket *res, **p, *b;
  uint32_t i, h;

  assert (p2iht->size > 0);

  res = 0;
  h   = p2iht->hash (key);
  h &= p2iht->size - 1;

  for (i = 0, p = p2iht->table + h; i < p2iht->count; i++, p = &b->chain)
  {
    if (!(b = *p)) break;
    if (!p2iht->cmp (b->key, key))
    {
      res = b;
      break;
    }
  }

  return res;
}

static BtorPtrHashBucket **
btor_findpos_in_ptr_hash_table_pos (BtorPtrHashTable *p2iht, void *key)
{
  BtorPtrHashBucket **p, *b;
  uint32_t h;

  if (p2iht->count == p2iht->size) btor_enlarge_ptr_hash_table (p2iht);

  assert (p2iht->size > 0);

  h = p2iht->hash (key);
  h &= p2iht->size - 1;

  for (p = p2iht->table + h; (b = *p) && p2iht->cmp (b->key, key);
       p = &b->chain)
    ;

  return p;
}

BtorPtrHashBucket *
btor_hashptr_table_add (BtorPtrHashTable *p2iht, void *key)
{
  BtorPtrHashBucket **p, *res;
  p = btor_findpos_in_ptr_hash_table_pos (p2iht, key);
  assert (!*p);
  BTOR_CNEW (p2iht->mm, res);
  res->key = key;
  *p       = res;
  p2iht->count++;

  res->prev = p2iht->last;

  if (p2iht->first)
    p2iht->last->next = res;
  else
    p2iht->first = res;

  p2iht->last = res;

  return res;
}

static uint32_t btor_hash_primes[] = {111130391, 22237357, 33355519, 444476887};

#define BTOR_HASH_PRIMES ((sizeof btor_hash_primes) / sizeof *btor_hash_primes)

uint32_t
btor_hash_str (const void *str)
{
  const char *p = (const char *) str;
  uint32_t res, i;
  char ch;

  i   = 0;
  res = 0;

  while ((ch = *p++))
  {
    res += btor_hash_primes[i++] * (uint32_t) ch;
    if (i == BTOR_HASH_PRIMES) i = 0;
  }

  return res;
}

void
btor_hashptr_table_remove (BtorPtrHashTable *table,
                           void *key,
                           void **stored_key_ptr,
                           BtorHashTableData *stored_data_ptr)
{
  BtorPtrHashBucket **p, *bucket;

  p      = btor_findpos_in_ptr_hash_table_pos (table, key);
  bucket = *p;

  assert (bucket);
  *p = bucket->chain;

  if (bucket->prev)
    bucket->prev->next = bucket->next;
  else
    table->first = bucket->next;

  if (bucket->next)
    bucket->next->prev = bucket->prev;
  else
    table->last = bucket->prev;

  assert (table->count > 0);
  table->count--;

  if (stored_key_ptr) *stored_key_ptr = bucket->key;

  if (stored_data_ptr) *stored_data_ptr = bucket->data;

  BTOR_DELETE (table->mm, bucket);
}

/*------------------------------------------------------------------------*/
/* iterators     		                                          */
/*------------------------------------------------------------------------*/

void
btor_iter_hashptr_init (BtorPtrHashTableIterator *it, const BtorPtrHashTable *t)
{
  assert (it);
  assert (t);

  it->bucket                  = t->first;
  it->cur                     = it->bucket ? it->bucket->key : 0;
  it->reversed                = false;
  it->num_queued              = 0;
  it->pos                     = 0;
  it->stack[it->num_queued++] = t;
}

void
btor_iter_hashptr_init_reversed (BtorPtrHashTableIterator *it,
                                 const BtorPtrHashTable *t)
{
  assert (it);
  assert (t);

  it->bucket                  = t->last;
  it->cur                     = it->bucket ? it->bucket->key : 0;
  it->reversed                = true;
  it->num_queued              = 0;
  it->pos                     = 0;
  it->stack[it->num_queued++] = t;
}

void
btor_iter_hashptr_queue (BtorPtrHashTableIterator *it,
                         const BtorPtrHashTable *t)
{
  assert (it);
  assert (t);
  assert (it->num_queued < BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE);

  /* if initial table is empty, initialize with queued table */
  if (!it->bucket)
  {
    it->bucket = it->reversed ? t->last : t->first;
    it->cur    = it->bucket ? it->bucket->key : 0;
    it->pos += 1;
  }
  it->stack[it->num_queued++] = t;
}

bool
btor_iter_hashptr_has_next (const BtorPtrHashTableIterator *it)
{
  assert (it);
  return it->cur != 0;
}

void *
btor_iter_hashptr_next (BtorPtrHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);

  void *res;
  res = it->cur;
  if (it->bucket)
    it->bucket = it->reversed ? it->bucket->prev : it->bucket->next;

  while (!it->bucket)
  {
    it->pos += 1;
    if (it->pos >= it->num_queued) break;
    it->bucket =
        it->reversed ? it->stack[it->pos]->last : it->stack[it->pos]->first;
  }

  it->cur = it->bucket ? it->bucket->key : 0;
  return res;
}

BtorHashTableData *
btor_iter_hashptr_next_data (BtorPtrHashTableIterator *it)
{
  assert (it);
  assert (it->bucket);
  assert (it->cur);

  void *res;

  res = &it->bucket->data;
  btor_iter_hashptr_next (it);
  return res;
}

/*------------------------------------------------------------------------*/

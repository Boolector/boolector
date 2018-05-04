/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorhashint.h"
#include <assert.h>

/*------------------------------------------------------------------------*/

#define HOP_RANGE 32
#define ADD_RANGE 8 * HOP_RANGE

/*------------------------------------------------------------------------*/

static inline uint32_t
hash (uint32_t h)
{
  return h;
  return h * 2654435761;
}

static inline size_t
pow2size (size_t size)
{
  return size;  // - HOP_RANGE;
}

static inline size_t
initsize (size_t size)
{
  return size;  // + HOP_RANGE;
}

#if 0
#ifndef NDEBUG
#include <stdio.h>
static void
print_int_hash_table (BtorIntHashTable * t)
{
  size_t i;

  printf ("keys: ");
  for (i = 0; i < t->size; i++)
    {
      if (i % HOP_RANGE == 0)
	printf ("|");
      printf ("%d[%d]", t->keys[i], t->hop_info[i]);
      if (i < t->size - 1)
	printf (".");
    }
  printf ("|\n");
}
#endif
#endif

#if 0
static void
print_density (BtorIntHashTable *t, int32_t key)
{
  size_t j, insert_pos = hash (key) & (pow2size (t->size) - 1);
  for (j = 0; j < t->size; j++)
    if (j % 20 == 0)
      printf ("|");
    else
      printf (" ");
  printf ("\n");
  for (j = 0; j < t->size; j++)
    if (j == insert_pos)
      printf ("%c", t->keys[j] ? 'O' : 'F');
    else
      printf ("%c", t->keys[j] ? 'x' : '.'); 
  printf ("\n");
}
#endif

/*
 * try to add 'key' to 't'.
 * if adding 'key' succeeds 'key' is stored in 't->keys' and the function
 * returns the position of 'key' in 't->keys'.
 * if adding 'key' does not succeed, the function return 't->size'.
 */
static size_t
add (BtorIntHashTable *t, int32_t key)
{
  bool found, moved;
  size_t i, j, size, pos, move_pos, rem_move_dist;
  uint32_t h;
  uint8_t move_hop_info, *hop_info;
  int32_t *keys;
  BtorHashTableData *data;

  keys     = t->keys;
  hop_info = t->hop_info;
  size     = t->size;
  data     = t->data;
  h        = hash (key);
  i        = h & (pow2size (size) - 1);

  /* search a free position within the ADD_RANGE window */
  found = false;
  for (j = 0, pos = i + j; j < ADD_RANGE && pos < size; j++, pos = i + j)
  {
    if (!keys[pos])
    {
      found = true;
      break;
    }
    /* already in hash table */
    else if (keys[pos] == key)
    {
      assert (pos < i + HOP_RANGE);
      return pos;
    }
  }

  /* no suitable index found for moving key, needs resizing */
  if (!found) return size;

  found = false;
  moved = true;
  do
  {
    assert (!keys[pos]);
    if (pos - i < HOP_RANGE)
    {
      found = true;
      break;
    }

    /* needs resizing */
    if (!moved) return size;

    /* 'pos' contains a free index */
    move_pos = pos - (HOP_RANGE - 1);
    moved    = false;
    for (j = HOP_RANGE - 1; j > 0; j--)
    {
      move_hop_info = hop_info[move_pos];
      rem_move_dist = HOP_RANGE - 1 - move_hop_info;

      /* not suitable for moving as remaining move distance 'rem_move_dist'
       * is smaller than the required move distance 'j' */
      if (rem_move_dist < j)
      {
        move_pos++;
        continue;
      }

      /* move key to free position 'pos' */
      keys[pos]     = keys[move_pos];
      hop_info[pos] = move_hop_info + j; /* update hop info */
      assert (hop_info[pos] < HOP_RANGE);
      keys[move_pos]     = 0;
      hop_info[move_pos] = 0;
      if (data)
      {
        data[pos] = data[move_pos];
        memset (&data[move_pos], 0, sizeof (*data));
        data[move_pos].as_ptr = 0;
      }
      pos   = move_pos;
      moved = true;
      break;
    }
  } while (true);

  assert (found);
  keys[pos]     = key;
  hop_info[pos] = pos - i; /* store number of hops */
  assert (hop_info[pos] < HOP_RANGE);
  t->count += 1;
  return pos;
}

static void
resize (BtorIntHashTable *t)
{
#ifndef NDEBUG
  size_t old_count;
#endif
  size_t i, new_pos, old_size, new_size;
  int32_t key, *old_keys;
  uint8_t *old_hop_info;
  BtorHashTableData *old_data;

  old_size     = t->size;
  old_keys     = t->keys;
  old_hop_info = t->hop_info;
  old_data     = t->data;
#ifndef NDEBUG
  old_count = t->count;
#endif
  assert (old_size > 0);
  new_size = initsize ((pow2size (old_size)) * 2);
  BTOR_CNEWN (t->mm, t->keys, new_size);
  BTOR_CNEWN (t->mm, t->hop_info, new_size);
  if (old_data) BTOR_CNEWN (t->mm, t->data, new_size);
  t->count = 0;
  t->size  = new_size;

  for (i = 0; i < old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    new_pos = add (t, key);
    if (old_data) t->data[new_pos] = old_data[i];
    /* after resizing it should always be possible to find a new position */
    assert (new_pos < new_size);
  }

  BTOR_DELETEN (t->mm, old_keys, old_size);
  BTOR_DELETEN (t->mm, old_hop_info, old_size);
  if (old_data) BTOR_DELETEN (t->mm, old_data, old_size);
  assert (old_count == t->count);
}

/*------------------------------------------------------------------------*/

BtorIntHashTable *
btor_hashint_table_new (BtorMemMgr *mm)
{
  BtorIntHashTable *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->size = initsize (HOP_RANGE);
  BTOR_CNEWN (mm, res->keys, res->size);
  BTOR_CNEWN (mm, res->hop_info, res->size);
  return res;
}

void
btor_hashint_table_delete (BtorIntHashTable *t)
{
  assert (!t->data);
  BTOR_DELETEN (t->mm, t->keys, t->size);
  BTOR_DELETEN (t->mm, t->hop_info, t->size);
  BTOR_DELETE (t->mm, t);
}

size_t
btor_hashint_table_size (BtorIntHashTable *t)
{
  return sizeof (BtorIntHashTable)
         + t->size * (sizeof (*t->keys) + sizeof (*t->hop_info));
}

size_t
btor_hashint_table_add (BtorIntHashTable *t, int32_t key)
{
  assert (key);

  size_t pos;

  //  print_density (t, key);
  pos = add (t, key);
  /* 'add(...)' returns 't->size' if 'key' could not be added to 't'. hence,
   * we need to resize 't'. */
  while (pos == t->size)  // TODO: loop may be obsolete
  {
    resize (t);
    pos = add (t, key);
  }
  return pos;
}

bool
btor_hashint_table_contains (BtorIntHashTable *t, int32_t key)
{
  return btor_hashint_table_get_pos (t, key) != t->size;
}

size_t
btor_hashint_table_remove (BtorIntHashTable *t, int32_t key)
{
  size_t pos;

  pos = btor_hashint_table_get_pos (t, key);

  if (pos == t->size) return pos;

  assert (t->keys[pos] == key);
  t->keys[pos]     = 0;
  t->hop_info[pos] = 0;
  t->count -= 1;
  return pos;
}

size_t
btor_hashint_table_get_pos (BtorIntHashTable *t, int32_t key)
{
  size_t i, size, end;
  uint32_t h;
  int32_t *keys;

  keys = t->keys;
  size = t->size;
  h    = hash (key);
  i    = h & (pow2size (size) - 1);
  end  = i + HOP_RANGE;
  //  assert (end < size);
  if (end > size) end = size;

  for (; i < end; i++)
  {
    if (keys[i] == key) return i;
  }
  return size;
}

BtorIntHashTable *
btor_hashint_table_clone (BtorMemMgr *mm, BtorIntHashTable *table)
{
  assert (mm);

  BtorIntHashTable *res;

  if (!table) return NULL;

  res = btor_hashint_table_new (mm);
  while (res->size < table->size) resize (res);
  assert (res->size == table->size);
  memcpy (res->keys, table->keys, table->size * sizeof (*table->keys));
  memcpy (
      res->hop_info, table->hop_info, table->size * sizeof (*table->hop_info));
  res->count = table->count;
  return res;
}

/* map functions */

BtorIntHashTable *
btor_hashint_map_new (BtorMemMgr *mm)
{
  BtorIntHashTable *res;

  res = btor_hashint_table_new (mm);
  BTOR_CNEWN (mm, res->data, res->size);
  return res;
}

bool
btor_hashint_map_contains (BtorIntHashTable *t, int32_t key)
{
  assert (t->data);
  return btor_hashint_table_contains (t, key);
}

void
btor_hashint_map_remove (BtorIntHashTable *t,
                         int32_t key,
                         BtorHashTableData *stored_data)
{
  assert (t->data);
  assert (btor_hashint_map_contains (t, key));

  size_t pos;

  pos = btor_hashint_table_remove (t, key);

  if (stored_data) *stored_data = t->data[pos];
  memset (&t->data[pos], 0, sizeof (BtorHashTableData));
}

BtorHashTableData *
btor_hashint_map_add (BtorIntHashTable *t, int32_t key)
{
  assert (t->data);

  size_t pos;
  pos = btor_hashint_table_add (t, key);
  return &t->data[pos];
}

BtorHashTableData *
btor_hashint_map_get (BtorIntHashTable *t, int32_t key)
{
  assert (t->data);

  size_t pos;

  pos = btor_hashint_table_get_pos (t, key);
  if (pos == t->size) return 0;
  return &t->data[pos];
}

void
btor_hashint_map_delete (BtorIntHashTable *t)
{
  assert (t->data);

  BTOR_DELETEN (t->mm, t->data, t->size);
  t->data = 0;
  btor_hashint_table_delete (t);
}

BtorIntHashTable *
btor_hashint_map_clone (BtorMemMgr *mm,
                        BtorIntHashTable *table,
                        BtorCloneHashTableData cdata,
                        const void *data_map)
{
  assert (mm);

  size_t i;
  BtorIntHashTable *res;

  if (!table) return NULL;

  res = btor_hashint_table_clone (mm, table);
  BTOR_CNEWN (mm, res->data, res->size);
  if (cdata)
  {
    for (i = 0; i < res->size; i++)
    {
      if (!table->keys[i]) continue;
      cdata (mm, data_map, &table->data[i], &res->data[i]);
    }
  }
  else /* as_ptr does not have to be cloned */
    memcpy (res->data, table->data, table->size * sizeof (*table->data));

  assert (table->count == res->count);

  return res;
}

/*------------------------------------------------------------------------*/
/* iterators     		                                          */
/*------------------------------------------------------------------------*/

void
btor_iter_hashint_init (BtorIntHashTableIterator *it, const BtorIntHashTable *t)
{
  assert (it);
  assert (t);

  it->cur_pos = 0;
  it->t       = t;
  while (it->cur_pos < it->t->size && !it->t->keys[it->cur_pos])
    it->cur_pos += 1;
}

bool
btor_iter_hashint_has_next (const BtorIntHashTableIterator *it)
{
  assert (it);
  return it->cur_pos < it->t->size;
}

int32_t
btor_iter_hashint_next (BtorIntHashTableIterator *it)
{
  assert (it);

  int32_t res;

  res = it->t->keys[it->cur_pos++];
  while (it->cur_pos < it->t->size && !it->t->keys[it->cur_pos])
    it->cur_pos += 1;
  return res;
}

BtorHashTableData *
btor_iter_hashint_next_data (BtorIntHashTableIterator *it)
{
  assert (it);
  assert (it->t->data);

  BtorHashTableData *res;

  res = &it->t->data[it->cur_pos++];
  while (it->cur_pos < it->t->size && !it->t->keys[it->cur_pos])
    it->cur_pos += 1;
  return res;
}

/*------------------------------------------------------------------------*/

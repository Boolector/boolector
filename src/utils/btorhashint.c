/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorhashint.h"
#include <assert.h>

#define HOP_RANGE 32
#define ADD_RANGE 8 * HOP_RANGE

static inline uint32_t
hash (uint32_t h)
{
  return h;
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
  size_t i, j, size, pos, move_pos, rem_move_dist, real_size;
  uint32_t h;
  uint8_t move_hop_info, *hop_info;
  int32_t *keys;
  BtorHashTableData *data;

  keys      = t->keys;
  hop_info  = t->hop_info;
  size      = t->size;
  data      = t->data;
  h         = hash (key);
  i         = h & (size - 1);
  real_size = size + HOP_RANGE;

  /* search a free position within the ADD_RANGE window */
  found = false;
  for (j = 0, pos = i + j; j < ADD_RANGE && pos < real_size; j++, pos = i + j)
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
  if (!found) return real_size;

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
    if (!moved) return real_size;

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
      keys[pos]          = keys[move_pos];
      hop_info[pos]      = move_hop_info + j; /* update hop info */
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
  t->count += 1;
  return pos;
}

static void
resize (BtorIntHashTable *t)
{
#ifndef NDEBUG
  size_t old_count;
#endif
  size_t i, new_pos, old_size, new_size, real_old_size, real_new_size;
  int32_t key, *old_keys;
  uint8_t *old_hop_info;
  BtorHashTableData *old_data;

  old_size      = t->size;
  real_old_size = old_size + HOP_RANGE;
  old_keys      = t->keys;
  old_hop_info  = t->hop_info;
  old_data      = t->data;
#ifndef NDEBUG
  old_count = t->count;
#endif
  assert (old_size > 0);
  new_size      = old_size * 2;
  real_new_size = new_size + HOP_RANGE;
  BTOR_CNEWN (t->mm, t->keys, real_new_size);
  BTOR_CNEWN (t->mm, t->hop_info, real_new_size);
  if (old_data) BTOR_CNEWN (t->mm, t->data, real_new_size);
  t->count = 0;
  t->size  = new_size;

  for (i = 0; i < real_old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    new_pos = add (t, key);
    if (old_data) t->data[new_pos] = old_data[i];
    /* after resizing it should always be possible to find a new position */
    assert (new_pos < real_new_size);
  }

  BTOR_DELETEN (t->mm, old_keys, real_old_size);
  BTOR_DELETEN (t->mm, old_hop_info, real_old_size);
  if (old_data) BTOR_DELETEN (t->mm, old_data, real_old_size);
  assert (old_count == t->count);
}

BtorIntHashTable *
btor_new_int_hash_table (BtorMemMgr *mm)
{
  size_t real_size;
  BtorIntHashTable *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->size = HOP_RANGE;
  real_size = HOP_RANGE + HOP_RANGE;
  BTOR_CNEWN (mm, res->keys, real_size);
  BTOR_CNEWN (mm, res->hop_info, real_size);
  return res;
}

void
btor_delete_int_hash_table (BtorIntHashTable *t)
{
  assert (!t->data);
  size_t real_size;

  real_size = t->size + HOP_RANGE;
  BTOR_DELETEN (t->mm, t->keys, real_size);
  BTOR_DELETEN (t->mm, t->hop_info, real_size);
  BTOR_DELETE (t->mm, t);
}

size_t
btor_size_int_hash_table (BtorIntHashTable *t)
{
  size_t real_size;
  real_size = t->size + HOP_RANGE;
  return sizeof (BtorIntHashTable)
         + real_size * (sizeof (*t->keys) + sizeof (*t->hop_info));
}

size_t
btor_add_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  assert (key);

  size_t pos, real_size;

  real_size = t->size + HOP_RANGE;
  pos       = add (t, key);
  /* 'add(...)' returns 't->size' if 'key' could not be added to 't'. hence,
   * we need to resize 't'. */
  while (pos == real_size)  // TODO: loop may be obsolete
  {
    resize (t);
    pos = add (t, key);
    assert (pos != t->size + HOP_RANGE);
  }
  return pos;
}

bool
btor_contains_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  return btor_get_pos_int_hash_table (t, key) != t->size + HOP_RANGE;
}

size_t
btor_remove_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  size_t pos, real_size;

  real_size = t->size + HOP_RANGE;
  pos       = btor_get_pos_int_hash_table (t, key);

  if (pos == real_size) return pos;

  assert (t->keys[pos] == key);
  t->keys[pos]     = 0;
  t->hop_info[pos] = 0;
  t->count -= 1;
  return pos;
}

size_t
btor_get_pos_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  size_t i, size, end, real_size;
  uint32_t h;
  int32_t *keys;

  keys      = t->keys;
  size      = t->size;
  h         = hash (key);
  i         = h & (size - 1);
  end       = i + HOP_RANGE;
  real_size = size + HOP_RANGE;
  assert (end < real_size);
  if (end > real_size) end = real_size;

  for (; i < end; i++)
  {
    if (keys[i] == key) return i;
  }
  return real_size;
}

BtorIntHashTable *
btor_clone_int_hash_table (BtorMemMgr *mm, BtorIntHashTable *table)
{
  assert (mm);

  size_t real_size;
  BtorIntHashTable *res;

  if (!table) return NULL;

  real_size = table->size + HOP_RANGE;
  res       = btor_new_int_hash_table (mm);
  while (res->size < table->size) resize (res);
  assert (res->size == table->size);
  memcpy (res->keys, table->keys, real_size * sizeof (*table->keys));
  memcpy (
      res->hop_info, table->hop_info, real_size * sizeof (*table->hop_info));
  res->count = table->count;
  return res;
}

/* map functions */

BtorIntHashTable *
btor_new_int_hash_map (BtorMemMgr *mm)
{
  BtorIntHashTable *res;
  size_t real_size;

  res       = btor_new_int_hash_table (mm);
  real_size = res->size + HOP_RANGE;
  BTOR_CNEWN (mm, res->data, real_size);
  return res;
}

bool
btor_contains_int_hash_map (BtorIntHashTable *t, int32_t key)
{
  assert (t->data);
  return btor_contains_int_hash_table (t, key);
}

void
btor_remove_int_hash_map (BtorIntHashTable *t,
                          int32_t key,
                          BtorHashTableData *stored_data)
{
  assert (t->data);
  assert (btor_contains_int_hash_map (t, key));

  size_t pos;

  pos = btor_remove_int_hash_table (t, key);

  if (stored_data) *stored_data = t->data[pos];
  memset (&t->data[pos], 0, sizeof (BtorHashTableData));
}

BtorHashTableData *
btor_add_int_hash_map (BtorIntHashTable *t, int32_t key)
{
  assert (t->data);

  size_t pos;
  pos = btor_add_int_hash_table (t, key);
  return &t->data[pos];
}

BtorHashTableData *
btor_get_int_hash_map (BtorIntHashTable *t, int32_t key)
{
  assert (t->data);

  size_t pos, real_size;

  real_size = t->size + HOP_RANGE;
  pos       = btor_get_pos_int_hash_table (t, key);
  if (pos == real_size) return 0;
  return &t->data[pos];
}

void
btor_delete_int_hash_map (BtorIntHashTable *t)
{
  assert (t->data);

  size_t real_size;

  real_size = t->size + HOP_RANGE;
  BTOR_DELETEN (t->mm, t->data, real_size);
  t->data = 0;
  btor_delete_int_hash_table (t);
}

BtorIntHashTable *
btor_clone_int_hash_map (BtorMemMgr *mm,
                         BtorIntHashTable *table,
                         BtorCloneHashTableData cdata,
                         const void *data_map)
{
  assert (mm);

  size_t i, real_size;
  BtorIntHashTable *res;

  if (!table) return NULL;

  res       = btor_clone_int_hash_table (mm, table);
  real_size = res->size + HOP_RANGE;
  BTOR_CNEWN (mm, res->data, real_size);
  if (cdata)
  {
    for (i = 0; i < real_size; i++)
    {
      if (!table->keys[i]) continue;
      cdata (mm, data_map, &table->data[i], &res->data[i]);
    }
  }
  else /* as_ptr does not have to be cloned */
    memcpy (res->data, table->data, real_size * sizeof (*table->data));

  assert (table->count == res->count);

  return res;
}

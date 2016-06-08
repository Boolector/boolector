/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorhashptr2.h"
#include <assert.h>

#define HOP_RANGE 32
#define ADD_RANGE 8 * HOP_RANGE

static uint32_t
hash_ptr (const void *p)
{
  return (size_t) p >> 3;
}

static int32_t
cmp_ptr (const void *p, const void *q)
{
  return p != q;
}

#if 0
#ifndef NDEBUG
#include <stdio.h>
static void
print_ptr_hash_table2 (BtorPtrHashTable2 * t)
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
add (BtorPtrHashTable2 *t, void *key)
{
  bool found, moved;
  size_t i, j, size, pos, move_pos, rem_move_dist, *next, *prev, real_size;
  uint32_t h;
  uint8_t move_hop_info, *hop_info;
  void **keys;
  BtorHashTableData *data;

  keys      = t->keys;
  hop_info  = t->hop_info;
  size      = t->size;
  data      = t->data;
  next      = t->next;
  prev      = t->prev;
  h         = t->hash (key);
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
    else if (t->cmp (keys[pos], key) == 0)
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

      if (move_pos == t->first)
        t->first = pos;
      else
      {
        assert (next[prev[move_pos]] == move_pos);
        next[prev[move_pos]] = pos;
      }
      if (move_pos == t->last)
        t->last = pos;
      else
      {
        assert (prev[next[move_pos]] == move_pos);
        prev[next[move_pos]] = pos;
      }
      next[pos]      = next[move_pos];
      prev[pos]      = prev[move_pos];
      next[move_pos] = prev[move_pos] = 0;

      if (data)
      {
        data[pos] = data[move_pos];
        memset (&data[move_pos], 0, sizeof (*data));
      }
      pos   = move_pos;
      moved = true;
      break;
    }
  } while (true);

  assert (found);
  keys[pos]     = key;
  hop_info[pos] = pos - i; /* store number of hops */
  assert (prev[pos] == 0);
  if (t->count > 0)
  {
    next[t->last] = pos;
    prev[pos]     = t->last;
  }
  else
    t->first = pos;
  assert (next[pos] == 0);
  t->last = pos;
  t->count += 1;
  return pos;
}

static void
resize (BtorPtrHashTable2 *t)
{
#ifndef NDEBUG
  size_t old_count;
#endif
  size_t i, new_pos, old_size, new_size, *old_next, *old_prev, first, last;
  size_t *new_mapping, real_old_size, real_new_size;
  void *key, **old_keys;
  uint8_t *old_hop_info;
  BtorHashTableData *old_data;

  old_size      = t->size;
  old_keys      = t->keys;
  old_hop_info  = t->hop_info;
  old_data      = t->data;
  old_next      = t->next;
  old_prev      = t->prev;
  first         = t->first;
  last          = t->last;
  real_old_size = old_size + HOP_RANGE;
#ifndef NDEBUG
  old_count = t->count;
#endif
  assert (old_size > 0);
  new_size      = old_size * 2;
  real_new_size = new_size + HOP_RANGE;
  BTOR_CNEWN (t->mm, t->keys, real_new_size);
  BTOR_CNEWN (t->mm, t->hop_info, real_new_size);
  BTOR_CNEWN (t->mm, t->next, real_new_size);
  BTOR_CNEWN (t->mm, t->prev, real_new_size);
  BTOR_CNEWN (t->mm, new_mapping, real_old_size);
  if (old_data) BTOR_CNEWN (t->mm, t->data, new_size);
  t->count = 0;
  t->size  = new_size;

  //  printf ("resize load: %.2f %u %u\n", (float) old_count / real_old_size,
  //  old_count, real_old_size);
  for (i = 0; i < real_old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    new_pos        = add (t, key);
    new_mapping[i] = new_pos;
    if (old_data) t->data[new_pos] = old_data[i];
    /* after resizing it should always be possible to find a new
     * position */
    assert (new_pos < real_new_size);
  }

  /* restore old chronological order */
  for (i = 0; i < real_old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    t->next[new_mapping[i]] = new_mapping[old_next[i]];
    t->prev[new_mapping[i]] = new_mapping[old_prev[i]];
  }
  t->first = new_mapping[first];
  t->last  = new_mapping[last];

  BTOR_DELETEN (t->mm, old_keys, real_old_size);
  BTOR_DELETEN (t->mm, old_hop_info, real_old_size);
  BTOR_DELETEN (t->mm, old_next, real_old_size);
  BTOR_DELETEN (t->mm, old_prev, real_old_size);
  BTOR_DELETEN (t->mm, new_mapping, real_old_size);
  if (old_data) BTOR_DELETEN (t->mm, old_data, real_old_size);
  assert (old_count == t->count);
#ifndef NDEBUG
  size_t pos, cnt = 0;
  if (t->count > 0)
  {
    pos = t->first;
    while (true)
    {
      cnt += 1;
      if (pos == t->last) break;
      pos = t->next[pos];
    }
  }
  assert (cnt == t->count);
#endif
}

BtorPtrHashTable2 *
btor_new_ptr_hash_table2 (BtorMemMgr *mm,
                          BtorHashPtr hash_func,
                          BtorCmpPtr cmp_func)
{
  size_t real_size;
  BtorPtrHashTable2 *res;

  real_size = HOP_RANGE + HOP_RANGE;
  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->size = HOP_RANGE;
  BTOR_CNEWN (mm, res->keys, real_size);
  BTOR_CNEWN (mm, res->hop_info, real_size);
  BTOR_CNEWN (mm, res->next, real_size);
  BTOR_CNEWN (mm, res->prev, real_size);
  res->hash = hash_func ? hash_func : hash_ptr;
  res->cmp  = cmp_func ? cmp_func : cmp_ptr;
  return res;
}

void
btor_delete_ptr_hash_table2 (BtorPtrHashTable2 *t)
{
  assert (!t->data);

  size_t real_size;

  real_size = t->size + HOP_RANGE;
  BTOR_DELETEN (t->mm, t->keys, real_size);
  BTOR_DELETEN (t->mm, t->hop_info, real_size);
  BTOR_DELETEN (t->mm, t->next, real_size);
  BTOR_DELETEN (t->mm, t->prev, real_size);
  BTOR_DELETE (t->mm, t);
}

size_t
btor_size_ptr_hash_table2 (BtorPtrHashTable2 *t)
{
  size_t real_size;
  real_size = t->size + HOP_RANGE;
  return sizeof (BtorPtrHashTable2)
         + real_size
               * (sizeof (*t->keys) + sizeof (*t->hop_info) + sizeof (*t->next)
                  + sizeof (*t->prev));
}

size_t
btor_add_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
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
btor_contains_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
{
  size_t real_size;
  real_size = t->size + HOP_RANGE;
  return btor_get_pos_ptr_hash_table2 (t, key) != real_size;
}

size_t
btor_remove_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
{
  size_t pos, prev, next, real_size;

  real_size = t->size + HOP_RANGE;

  pos = btor_get_pos_ptr_hash_table2 (t, key);

  if (pos == real_size) return pos;

  assert (t->cmp (t->keys[pos], key) == 0);
  t->keys[pos]     = 0;
  t->hop_info[pos] = 0;
  next             = t->next[pos];
  prev             = t->prev[pos];
  t->next[prev]    = next;
  t->prev[next]    = prev;
  if (t->count > 1)
  {
    if (pos == t->first) t->first = next;
    if (pos == t->last) t->last = prev;
  }
  else
  {
    t->first = 0;
    t->last  = 0;
  }
  t->next[pos] = 0;
  t->prev[pos] = 0;
  t->count -= 1;
  return pos;
}

size_t
btor_get_pos_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
{
  size_t i, size, end, real_size;
  uint32_t h;
  void **keys;

  keys      = t->keys;
  size      = t->size;
  real_size = size + HOP_RANGE;
  h         = t->hash (key);
  i         = h & (size - 1);
  end       = i + HOP_RANGE;
  assert (end < real_size);
  if (end > real_size) end = real_size;

  for (; i < end; i++)
  {
    if (!keys[i]) continue;
    if (t->cmp (keys[i], key) == 0) return i;
  }
  return real_size;
}

BtorPtrHashTable2 *
btor_clone_ptr_hash_table2 (BtorMemMgr *mm,
                            BtorPtrHashTable2 *table,
                            BtorCloneKeyPtr2 ckey,
                            const void *key_map)
{
  assert (mm);
  assert (table);

  size_t i, real_size;
  void *key;
  BtorPtrHashTable2 *res;

  if (!table) return NULL;

  real_size = table->size + HOP_RANGE;
  res       = btor_new_ptr_hash_table2 (mm, table->hash, table->cmp);
  while (res->size < table->size) resize (res);
  assert (res->size == table->size);
  if (ckey)
  {
    for (i = 0; i < real_size; i++)
    {
      key = table->keys[i];
      if (!key) continue;
      res->keys[i] = ckey (mm, key_map, key);
    }
  }
  /* if clone function for keys is not given, just copy the keys */
  else
    memcpy (res->keys, table->keys, real_size * sizeof (*table->keys));
  memcpy (
      res->hop_info, table->hop_info, real_size * sizeof (*table->hop_info));
  memcpy (res->next, table->next, real_size * sizeof (*table->next));
  memcpy (res->prev, table->prev, real_size * sizeof (*table->prev));
  res->first = table->first;
  res->last  = table->last;
  res->count = table->count;
  return res;
}

/* map functions */

BtorPtrHashTable2 *
btor_new_ptr_hash_map2 (BtorMemMgr *mm,
                        BtorHashPtr hash_func,
                        BtorCmpPtr cmp_func)
{
  BtorPtrHashTable2 *res;
  size_t real_size;

  res       = btor_new_ptr_hash_table2 (mm, hash_func, cmp_func);
  real_size = res->size + HOP_RANGE;
  BTOR_CNEWN (mm, res->data, real_size);
  return res;
}

bool
btor_contains_ptr_hash_map2 (BtorPtrHashTable2 *t, void *key)
{
  assert (t->data);
  return btor_contains_ptr_hash_table2 (t, key);
}

void
btor_remove_ptr_hash_map2 (BtorPtrHashTable2 *t,
                           void *key,
                           BtorHashTableData *stored_data)
{
  assert (t->data);
  assert (btor_contains_ptr_hash_map2 (t, key));

  size_t pos;

  pos = btor_remove_ptr_hash_table2 (t, key);

  if (stored_data) *stored_data = t->data[pos];
  memset (&t->data[pos], 0, sizeof (BtorHashTableData));
}

BtorHashTableData *
btor_add_ptr_hash_map2 (BtorPtrHashTable2 *t, void *key)
{
  assert (t->data);

  size_t pos;
  pos = btor_add_ptr_hash_table2 (t, key);
  return &t->data[pos];
}

BtorHashTableData *
btor_get_ptr_hash_map2 (BtorPtrHashTable2 *t, void *key)
{
  assert (t->data);

  size_t pos, real_size;
  real_size = t->size + HOP_RANGE;
  pos       = btor_get_pos_ptr_hash_table2 (t, key);
  if (pos == real_size) return 0;
  return &t->data[pos];
}

void
btor_delete_ptr_hash_map2 (BtorPtrHashTable2 *t)
{
  assert (t->data);
  size_t real_size;

  real_size = t->size + HOP_RANGE;
  BTOR_DELETEN (t->mm, t->data, real_size);
  t->data = 0;
  btor_delete_ptr_hash_table2 (t);
}

size_t
btor_size_ptr_hash_map2 (BtorPtrHashTable2 *t)
{
  assert (t);

  size_t res, real_size;
  real_size = t->size + HOP_RANGE;
  res       = btor_size_ptr_hash_table2 (t);
  res += real_size * sizeof (*t->data);
  return res;
}

BtorPtrHashTable2 *
btor_clone_ptr_hash_map2 (BtorMemMgr *mm,
                          BtorPtrHashTable2 *table,
                          BtorCloneKeyPtr2 ckey,
                          BtorCloneHashTableData cdata,
                          const void *key_map,
                          const void *data_map)
{
  assert (mm);
  assert (table);
  assert (table->data);

  size_t i, real_size;
  BtorPtrHashTable2 *res;

  res       = btor_clone_ptr_hash_table2 (mm, table, ckey, key_map);
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
  /* 'cdata' is not given, copy data */
  else
    memcpy (res->data, table->data, real_size * sizeof (*table->data));

  return res;
}

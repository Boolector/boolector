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

static inline size_t
pow2size (size_t size)
{
  return size - HOP_RANGE;
}

static inline size_t
initsize (size_t size)
{
  return size + HOP_RANGE;
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
  size_t i, j, size, pos, move_pos, rem_move_dist, *next, *prev;
  uint32_t h;
  uint8_t move_hop_info, *hop_info;
  void **keys;
  BtorHashTableData *data;

  keys     = t->keys;
  hop_info = t->hop_info;
  size     = t->size;
  data     = t->data;
  next     = t->next;
  prev     = t->prev;
  h        = t->hash (key);
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
    else if (t->cmp (keys[pos], key) == 0)
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

      /* update chronological order */
      assert (move_pos != t->first || move_pos != t->last);
      if (move_pos == t->first)
      {
        t->first = pos;
        assert (prev[next[move_pos]] == move_pos);
        prev[next[move_pos]] = pos;
      }
      else if (move_pos == t->last)
      {
        t->last = pos;
        assert (next[prev[move_pos]] == move_pos);
        next[prev[move_pos]] = pos;
      }
      else
      {
        assert (prev[next[move_pos]] == move_pos);
        assert (next[prev[move_pos]] == move_pos);
        prev[next[move_pos]] = pos;
        next[prev[move_pos]] = pos;
      }
      next[pos] = next[move_pos];
      prev[pos] = prev[move_pos];

      /* reset moved data at old position */
      keys[move_pos]     = 0;
      hop_info[move_pos] = 0;
      next[move_pos]     = 0;
      prev[move_pos]     = 0;
      if (data)
      {
        data[pos] = data[move_pos];
        memset (&data[move_pos], 0, sizeof (*data));
      }

      /* move next position */
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
#ifndef NDEBUG
  if (pos == t->first)
  {
    assert (t->prev[pos] == 0);
    assert (t->first == t->last || t->prev[t->next[pos]] == pos);
  }
  else if (pos == t->last)
  {
    assert (t->next[pos] == 0);
    assert (t->next[t->prev[pos]] == pos);
  }
  else
  {
    assert (t->prev[t->next[pos]] == pos);
    assert (t->next[t->prev[pos]] == pos);
  }
#endif
  return pos;
}

static void
resize (BtorPtrHashTable2 *t)
{
#ifndef NDEBUG
  size_t old_count;
#endif
  size_t i, new_pos, old_size, new_size, *old_next, *old_prev, first, last;
  size_t *new_mapping;
  void *key, **old_keys;
  uint8_t *old_hop_info;
  BtorHashTableData *old_data;

  old_size     = t->size;
  old_keys     = t->keys;
  old_hop_info = t->hop_info;
  old_data     = t->data;
  old_next     = t->next;
  old_prev     = t->prev;
  first        = t->first;
  last         = t->last;
#ifndef NDEBUG
  old_count = t->count;
#endif
  // printf ("resize load: %.2f %u %u\n", (float) t->count / old_size, t->count,
  // old_size);

  assert (old_size > 0);
  new_size = initsize (pow2size (old_size) * 2);
  BTOR_CNEWN (t->mm, t->keys, new_size);
  BTOR_CNEWN (t->mm, t->hop_info, new_size);
  BTOR_CNEWN (t->mm, t->next, new_size);
  BTOR_CNEWN (t->mm, t->prev, new_size);
  BTOR_CNEWN (t->mm, new_mapping, old_size);
  if (old_data) BTOR_CNEWN (t->mm, t->data, new_size);
  t->count = 0;
  t->size  = new_size;
  t->first = t->last = 0;

#if 0
  i = first;
  while (true)
    {
      key = old_keys[i];
      assert (key);
      new_pos = add (t, key);
      /* after resizing it should always be possible to find a new position */
      assert (new_pos < new_size);
      if (old_data)
	t->data[new_pos] = old_data[i];
      if (i == last)
	break;
      i = old_next[i];
    }
  assert (old_count == t->count);
#else
  for (i = 0; i < old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    new_pos = add (t, key);
    if (old_data) t->data[new_pos] = old_data[i];
    /* after resizing it should always be possible to find a new position */
    assert (new_pos < new_size);
  }
  assert (old_count == t->count);

  for (i = 0; i < old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    new_pos        = btor_get_pos_ptr_hash_table2 (t, key);
    new_mapping[i] = new_pos;
  }

  /* restore old chronological order */
  for (i = 0; i < old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    t->next[new_mapping[i]] = new_mapping[old_next[i]];
    t->prev[new_mapping[i]] = new_mapping[old_prev[i]];
  }
  t->first          = new_mapping[first];
  t->prev[t->first] = 0;
  t->last           = new_mapping[last];
  t->next[t->last]  = 0;
#endif

#ifndef NDEBUG
  size_t pos0, pos1, cnt = 0;
  for (i = 0; i < new_size; i++)
  {
    if (!t->keys[i]) continue;
    if (i == t->first)
    {
      assert (t->count > 1);
      assert (t->prev[i] == 0);
      assert (t->prev[t->next[i]] == i);
    }
    else if (i == t->last)
    {
      assert (t->next[i] == 0);
      assert (t->next[t->prev[i]] == i);
    }
    else
    {
      assert (t->prev[t->next[i]] == i);
      assert (t->next[t->prev[i]] == i);
    }
  }
  if (t->count > 0)
  {
    pos0 = t->first;
    pos1 = first;
    while (true)
    {
      assert (t->keys[pos0] == old_keys[pos1]);
      cnt += 1;
      if (pos0 == t->last) break;
      pos0 = t->next[pos0];
      //	  assert (t->prev[t->next[pos0]] == pos0);
      //	  assert (t->next[t->prev[pos0]] == pos0);
      pos1 = old_next[pos1];
    }
  }
  assert (cnt == t->count);
#endif

  BTOR_DELETEN (t->mm, old_keys, old_size);
  BTOR_DELETEN (t->mm, old_hop_info, old_size);
  BTOR_DELETEN (t->mm, old_next, old_size);
  BTOR_DELETEN (t->mm, old_prev, old_size);
  BTOR_DELETEN (t->mm, new_mapping, old_size);
  if (old_data) BTOR_DELETEN (t->mm, old_data, old_size);
}

BtorPtrHashTable2 *
btor_new_ptr_hash_table2 (BtorMemMgr *mm,
                          BtorHashPtr hash_func,
                          BtorCmpPtr cmp_func)
{
  BtorPtrHashTable2 *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->size = initsize (HOP_RANGE);
  BTOR_CNEWN (mm, res->keys, res->size);
  BTOR_CNEWN (mm, res->hop_info, res->size);
  BTOR_CNEWN (mm, res->next, res->size);
  BTOR_CNEWN (mm, res->prev, res->size);
  res->hash = hash_func ? hash_func : hash_ptr;
  res->cmp  = cmp_func ? cmp_func : cmp_ptr;
  return res;
}

void
btor_delete_ptr_hash_table2 (BtorPtrHashTable2 *t)
{
  assert (!t->data);

  BTOR_DELETEN (t->mm, t->keys, t->size);
  BTOR_DELETEN (t->mm, t->hop_info, t->size);
  BTOR_DELETEN (t->mm, t->next, t->size);
  BTOR_DELETEN (t->mm, t->prev, t->size);
  BTOR_DELETE (t->mm, t);
}

size_t
btor_size_ptr_hash_table2 (BtorPtrHashTable2 *t)
{
  return sizeof (BtorPtrHashTable2)
         + t->size
               * (sizeof (*t->keys) + sizeof (*t->hop_info) + sizeof (*t->next)
                  + sizeof (*t->prev));
}

size_t
btor_add_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
{
  assert (key);

  size_t pos;

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
btor_contains_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
{
  return btor_get_pos_ptr_hash_table2 (t, key) != t->size;
}

size_t
btor_remove_ptr_hash_table2 (BtorPtrHashTable2 *t, void *key)
{
  size_t pos, prev, next;

  pos = btor_get_pos_ptr_hash_table2 (t, key);

  if (pos == t->size) return pos;

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
  size_t i, size, end;
  uint32_t h;
  void **keys;

  keys = t->keys;
  size = t->size;
  h    = t->hash (key);
  i    = h & (pow2size (size) - 1);
  end  = i + HOP_RANGE;
  assert (end < size);
  if (end > size) end = size;

  for (; i < end; i++)
  {
    if (!keys[i]) continue;
    if (t->cmp (keys[i], key) == 0) return i;
  }
  return size;
}

BtorPtrHashTable2 *
btor_clone_ptr_hash_table2 (BtorMemMgr *mm,
                            BtorPtrHashTable2 *table,
                            BtorCloneKeyPtr2 ckey,
                            const void *key_map)
{
  assert (mm);
  assert (table);

  size_t i;
  void *key;
  BtorPtrHashTable2 *res;

  if (!table) return NULL;

  res = btor_new_ptr_hash_table2 (mm, table->hash, table->cmp);
  while (res->size < table->size) resize (res);
  assert (res->size == table->size);
  if (ckey)
  {
    for (i = 0; i < res->size; i++)
    {
      key = table->keys[i];
      if (!key) continue;
      res->keys[i] = ckey (mm, key_map, key);
    }
  }
  /* if clone function for keys is not given, just copy the keys */
  else
    memcpy (res->keys, table->keys, table->size * sizeof (*table->keys));
  memcpy (
      res->hop_info, table->hop_info, table->size * sizeof (*table->hop_info));
  memcpy (res->next, table->next, table->size * sizeof (*table->next));
  memcpy (res->prev, table->prev, table->size * sizeof (*table->prev));
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

  res = btor_new_ptr_hash_table2 (mm, hash_func, cmp_func);
  BTOR_CNEWN (mm, res->data, res->size);
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

  size_t pos;
  pos = btor_get_pos_ptr_hash_table2 (t, key);
  if (pos == t->size) return 0;
  return &t->data[pos];
}

void
btor_delete_ptr_hash_map2 (BtorPtrHashTable2 *t)
{
  assert (t->data);

  BTOR_DELETEN (t->mm, t->data, t->size);
  t->data = 0;
  btor_delete_ptr_hash_table2 (t);
}

size_t
btor_size_ptr_hash_map2 (BtorPtrHashTable2 *t)
{
  assert (t);

  size_t res;
  res = btor_size_ptr_hash_table2 (t);
  res += t->size * sizeof (*t->data);
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

  size_t i;
  BtorPtrHashTable2 *res;

  res = btor_clone_ptr_hash_table2 (mm, table, ckey, key_map);
  BTOR_CNEWN (mm, res->data, res->size);

  if (cdata)
  {
    for (i = 0; i < table->size; i++)
    {
      if (!table->keys[i]) continue;
      cdata (mm, data_map, &table->data[i], &res->data[i]);
    }
  }
  /* 'cdata' is not given, copy data */
  else
    memcpy (res->data, table->data, table->size * sizeof (*table->data));

  return res;
}

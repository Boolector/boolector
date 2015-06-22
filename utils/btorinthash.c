/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorinthash.h"
#include <assert.h>

#define HOP_RANGE 32
#define ADD_RANGE 8 * HOP_RANGE

static inline uint32_t
hash (uint32_t h)
{
  return h;
  //  return h; // * 1183477;
  //  h ^= h >> 16;
  //  h *= 0x85ebca6b;
  //  h ^= h >> 13;
  //  h *= 0xc2b2ae35;
  //  h ^= h >> 16;
  //  return h;
  //  uint32_t c2=0x27d4eb2d; // a prime or an odd constant
  //  h = (h ^ 61) ^ (h >> 16);
  //  h = h + (h << 3);
  //  h = h ^ (h >> 4);
  //  h = h * c2;
  //  h = h ^ (h >> 15);
  //  return h;

  //  h = ((h >> 16) ^ h) * 0x45d9f3b;
  //  h = ((h >> 16) ^ h) * 0x45d9f3b;
  //  h = ((h >> 16) ^ h);
  //  return h;

  h += ~(h << 15);
  h ^= (h >> 10);
  h += (h << 3);
  h ^= (h >> 6);
  h += ~(h << 11);
  h ^= (h >> 16);
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
  size_t i, j, size, pos, move_pos, rem_move_dist;
  uint32_t h;
  uint8_t move_hop_info, *hop_info;
  int32_t *keys;

  keys     = t->keys;
  hop_info = t->hop_info;
  size     = t->size;
  h        = hash (key);
  i        = h & (size - 1);

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
      keys[pos]          = keys[move_pos];
      hop_info[pos]      = move_hop_info + j; /* update hop info */
      keys[move_pos]     = 0;
      hop_info[move_pos] = 0;
      pos                = move_pos;
      moved              = true;
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
  size_t new_pos, old_count;
#endif
  size_t i, old_size, new_size;
  int32_t key, *old_keys;
  uint8_t *old_hop_info;

  old_size     = t->size;
  old_keys     = t->keys;
  old_hop_info = t->hop_info;
#ifndef NDEBUG
  old_count = t->count;
#endif
  assert (old_size > 0);
  new_size = old_size * 2;
  BTOR_CNEWN (t->mm, t->keys, new_size);
  BTOR_CNEWN (t->mm, t->hop_info, new_size);
  t->count = 0;
  t->size  = new_size;

  for (i = 0; i < old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
#ifndef NDEBUG
    new_pos =
#endif
        add (t, key);
    /* after resizing it should alwys be possible to find a new position */
    assert (new_pos < new_size);
  }

  BTOR_DELETEN (t->mm, old_keys, old_size);
  BTOR_DELETEN (t->mm, old_hop_info, old_size);
  assert (old_count == t->count);
}

BtorIntHashTable *
btor_new_int_hash_table (BtorMemMgr *mm)
{
  BtorIntHashTable *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->size = HOP_RANGE;
  BTOR_CNEWN (mm, res->keys, res->size);
  BTOR_CNEWN (mm, res->hop_info, res->size);
  return res;
}

void
btor_free_int_hash_table (BtorIntHashTable *t)
{
  BTOR_DELETEN (t->mm, t->keys, t->size);
  BTOR_DELETEN (t->mm, t->hop_info, t->size);
  BTOR_DELETE (t->mm, t);
}

size_t
btor_size_int_hash_table (BtorIntHashTable *t)
{
  return sizeof (BtorIntHashTable)
         + t->size * (sizeof (*t->keys) + sizeof (*t->hop_info));
}

size_t
btor_add_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  assert (key);

  size_t pos;

  pos = add (t, key);
  /* 'add(...)' returns 't->size' if 'key' could not be added to 't'. hence,
   * we need to resize 't'. */
  while (pos == t->size)
  {
    resize (t);
    pos = add (t, key);
  }
  return pos;
}

bool
btor_contains_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  return btor_get_pos_int_hash_table (t, key) != t->size;
}

size_t
btor_remove_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  size_t pos;

  pos = btor_get_pos_int_hash_table (t, key);

  if (pos == t->size) return pos;

  assert (t->keys[pos] == key);
  t->keys[pos]     = 0;
  t->hop_info[pos] = 0;
  return pos;
}

size_t
btor_get_pos_int_hash_table (BtorIntHashTable *t, int32_t key)
{
  size_t i, j, size, pos;
  uint32_t h;
  int32_t *keys;

  keys = t->keys;
  size = t->size;
  h    = hash (key);
  i    = h & (size - 1);

  for (j = 0, pos = i + j; j < HOP_RANGE && pos < size; j++, pos = i + j)
  {
    if (keys[pos] == key) return pos;
  }
  return size;
}

#include "btorhash.h"

static unsigned
btor_hash_ptr (void *state, void *p)
{
  (void) state;
  return 1183477 * (unsigned) (unsigned long) p;
}

static int
btor_cmp_ptr (void *state, void *p, void *q)
{
  (void) state;
  return ((long) p) - ((long) q);
}

BtorPtrToIntHashTable *
btor_new_ptr_to_int_hash_table (BtorMemMgr *mem,
                                void *state,
                                BtorHashPtr hash,
                                BtorCmpPtr cmp)
{
  BtorPtrToIntHashTable *res;

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->mem   = mem;
  res->state = state;

  res->hash = hash ? hash : btor_hash_ptr;
  res->cmp  = cmp ? cmp : btor_cmp_ptr;

  return res;
}

void
btor_delete_ptr_to_int_hash_tabale (BtorPtrToIntHashTable *p2iht)
{
  BtorPtrToIntHashBucket *p, *next;

  for (p = p2iht->first; p; p = next)
  {
    next = p->next;
    BTOR_DELETE (p2iht->mem, p);
  }

  BTOR_DELETEN (p2iht->mem, p2iht->table, p2iht->size);
  BTOR_DELETE (p2iht->mem, p2iht);
}

static void
btor_enlarge_ptr_to_int_hash_table (BtorPtrToIntHashTable *p2iht)
{
  BtorPtrToIntHashBucket *p, *chain, **old_table, **new_table;
  unsigned old_size, new_size, i, h;
  BtorHashPtr hash;
  void *state;

  old_size  = p2iht->size;
  old_table = p2iht->table;

  new_size = old_size ? 2 * old_size : 1;
  BTOR_CNEWN (p2iht->mem, new_table, new_size);

  state = p2iht->state;
  hash  = p2iht->hash;

  for (i = 0; i < old_size; i++)
    for (p = old_table[i]; p; p = chain)
    {
      chain = p->chain;
      h     = hash (state, p->key);
      h &= new_size - 1;
      p->chain     = new_table[h];
      new_table[h] = p;
    }

  BTOR_DELETEN (p2iht->mem, old_table, old_size);

  p2iht->size  = new_size;
  p2iht->table = new_table;
}

static BtorPtrToIntHashBucket **
btor_findpos_in_ptr_to_int_hash_table_pos (BtorPtrToIntHashTable *p2iht,
                                           void *key)
{
  BtorPtrToIntHashBucket **p, *b;
  unsigned h;

  if (p2iht->count == p2iht->size) btor_enlarge_ptr_to_int_hash_table (p2iht);

  assert (p2iht->size > 0);

  h = p2iht->hash (p2iht->state, key);
  h &= p2iht->size - 1;

  for (p = p2iht->table + h; (b = *p) && p2iht->cmp (p2iht->state, b->key, key);
       p = &b->chain)
    ;

  return p;
}

BtorPtrToIntHashBucket *
btor_find_in_ptr_to_int_hash_table (BtorPtrToIntHashTable *p2iht, void *key)
{
  return *btor_findpos_in_ptr_to_int_hash_table_pos (p2iht, key);
}

BtorPtrToIntHashBucket *
btor_insert_in_ptr_to_int_hash_table (BtorPtrToIntHashTable *p2iht,
                                      void *key,
                                      int data)
{
  BtorPtrToIntHashBucket **p, *res;
  p = btor_findpos_in_ptr_to_int_hash_table_pos (p2iht, key);
  assert (!*p);
  BTOR_CNEW (p2iht->mem, res);
  res->key  = key;
  res->data = data;
  *p        = res;
  p2iht->count++;
  if (p2iht->first)
    p2iht->last->next = res;
  else
    p2iht->first = res;
  p2iht->last = res;
  return res;
}

static unsigned primes[] = {1183477, 1183541, 1183579, 1183277, 1183279};
#define PRIMES ((sizeof primes) / sizeof *primes)

unsigned
btor_hashstr (void *state_dummy, void *str)
{
  const char *p = (const char *) str;
  unsigned res, i;
  char ch;

  (void) state_dummy;

  i   = 0;
  res = 0;

  while ((ch = *p++))
  {
    res += primes[i++] * (unsigned) ch;
    if (i == PRIMES) i = 0;
  }

  return res;
}

int
btor_cmpstr (void *state_dummy, void *a, void *b)
{
  (void) state_dummy;
  return strcmp ((const char *) a, (const char *) b);
}

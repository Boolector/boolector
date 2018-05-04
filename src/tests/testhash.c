/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testhash.h"
#include "testrunner.h"
#include "utils/btorhashptr.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

static BtorMemMgr *mem;

void
init_hash_tests (void)
{
  mem = btor_mem_mgr_new ();
}

static void
test_new_delete_hash (void)
{
  size_t allocated     = mem->allocated;
  BtorPtrHashTable *ht = btor_hashptr_table_new (mem, 0, 0);
  btor_hashptr_table_delete (ht);
  assert (allocated == mem->allocated);
}

static void
test_hash_str2i (void)
{
  BtorPtrHashTable *ht = btor_hashptr_table_new (mem, 0, 0);

  btor_hashptr_table_add (ht, "one")->data.as_int = 1;
  assert (btor_hashptr_table_get (ht, "one"));
  assert (btor_hashptr_table_get (ht, "one")->data.as_int == 1);

  btor_hashptr_table_add (ht, "two")->data.as_int = 2;
  assert (btor_hashptr_table_get (ht, "two"));
  assert (btor_hashptr_table_get (ht, "two")->data.as_int == 2);

  btor_hashptr_table_add (ht, "three")->data.as_int = 3;
  assert (btor_hashptr_table_get (ht, "three"));
  assert (btor_hashptr_table_get (ht, "three")->data.as_int == 3);

  btor_hashptr_table_delete (ht);
}

static void
test_traverse_hash_str2i (void)
{
  BtorPtrHashTable *ht;
  BtorPtrHashBucket *p;
  char buffer[20];
  int32_t i;

  ht = btor_hashptr_table_new (mem, btor_hash_str, btor_compare_str);

  for (i = 0; i < 40; i++)
  {
    sprintf (buffer, "%d", i);
    p              = btor_hashptr_table_add (ht, buffer);
    p->data.as_int = i;
    p->key         = btor_mem_strdup (mem, buffer);
  }

  for (i = 0; i < 40; i++)
  {
    sprintf (buffer, "%d", i);
    assert (btor_hashptr_table_get (ht, buffer));
    assert (btor_hashptr_table_get (ht, buffer)->data.as_int == i);
  }

  for (p = ht->first; p; p = p->next)
  {
    fprintf (g_logfile, "%s %d\n", (const char *) p->key, p->data.as_int);
    btor_mem_freestr (mem, p->key);
  }

  btor_hashptr_table_delete (ht);
}

static void
test_hash_str2str (void)
{
  BtorPtrHashTable *ht;
  BtorPtrHashBucket *p;
  BtorHashTableData data;
  char buffer[20];
  void *key;
  int32_t i;

  ht = btor_hashptr_table_new (mem, btor_hash_str, btor_compare_str);

  for (i = 0; i < 10; i++)
  {
    sprintf (buffer, "%d", i);
    p      = btor_hashptr_table_add (ht, buffer);
    p->key = btor_mem_strdup (mem, buffer);
    sprintf (buffer, "%d", 10 - i);
    p->data.as_str = btor_mem_strdup (mem, buffer);
  }

  for (i = 0; i < 10; i++)
  {
    sprintf (buffer, "%d", i);
    p = btor_hashptr_table_get (ht, buffer);
    assert (p);
    assert (i == atoi (p->key));
    assert (10 - i == atoi (p->data.as_str));
  }

  for (i = 0; i < 10; i += 2)
  {
    sprintf (buffer, "%d", i);
    btor_hashptr_table_remove (ht, buffer, &key, &data);
    btor_mem_freestr (mem, data.as_str);
    btor_mem_freestr (mem, key);
  }

  for (p = ht->first; p; p = p->next)
  {
    fprintf (g_logfile, "%s -> %s\n", (char *) p->key, p->data.as_str);
    btor_mem_freestr (mem, p->key);
    btor_mem_freestr (mem, p->data.as_str);
  }

  btor_hashptr_table_delete (ht);
}

void
run_hash_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_hash);
  BTOR_RUN_TEST (hash_str2i);
  BTOR_RUN_TEST_CHECK_LOG (traverse_hash_str2i);
  BTOR_RUN_TEST_CHECK_LOG (hash_str2str);
}

void
finish_hash_tests (void)
{
  btor_mem_mgr_delete (mem);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testinthash.h"
#include "testrunner.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

static BtorMemMgr *mem;
static BtorIntHashTable *h;

void
init_int_hash_table_tests (void)
{
  mem = btor_mem_mgr_new ();
}

static void
init_int_hash_table_test (void)
{
  assert (!h);
  h = btor_hashint_table_new (mem);
}

static void
finish_int_hash_table_test (void)
{
  assert (h);
  btor_hashint_table_delete (h);
  h = 0;
}

#if 0
static void
test_add_int_hash_table (void)
{
  double start;
  int32_t i, num_items = 5000000, val;

  init_int_hash_table_test ();
  srand (129);

  printf ("\n");
  start = btor_util_time_stamp ();
  for (i = num_items; i > 0; i--)
    {
      val = rand() % 2123541 + 1;
//      val = i * 7;
      if (!btor_hashint_table_contains (h, val))
	btor_hashint_table_add (h, val);
    }
  printf ("%.3f add\n", btor_util_time_stamp () - start);

  srand (129);
  start = btor_util_time_stamp ();
  for (i = num_items; i > 0; i--)
    {
//      val = i * 7;
//      val = rand();
      val = rand() % 2123541 + 1;
      assert (btor_hashint_table_contains (h, val));
    }
  printf ("%.3f contains\n", btor_util_time_stamp () - start);

  printf ("size: %.3f MB (%.2f %% full)\n",
	  (double) btor_hashint_table_size (h) / 1024 / 1024,
	  (double) h->count / h->size * 100);

  srand (129);
  start = btor_util_time_stamp ();
  for (i = num_items; i > 0; i--)
    {
//      val = i * 7;
//      val = rand();
      val = rand() % 2123541 + 1;
      btor_hashint_table_remove (h, val);
    }
  printf ("%.3f remove\n", btor_util_time_stamp () - start);

  srand (129);
  BtorPtrHashTable *ht;
  ht = btor_hashptr_table_new (mem, 0, 0);
  start = btor_util_time_stamp ();
  for (i = num_items; i > 0; i--)
    {
//      val = i * 7;
//      val = rand();
      val = rand() % 2123541 + 1;
      if (!btor_hashptr_table_get (ht, (void *) (size_t) val))
	btor_hashptr_table_add (ht, (void *) (size_t) val);
    }
  printf ("%.3f insert\n", btor_util_time_stamp () - start);

  srand (129);
  start = btor_util_time_stamp ();
  for (i = num_items; i > 0; i--)
    {
//      val = i * 7;
//      val = rand();
      val = rand() % 2123541 + 1;
      assert (btor_hashptr_table_get (ht, (void *) (size_t) val));
    }
  printf ("%.3f find\n", btor_util_time_stamp () - start);

  int32_t num_free = 0;
  for (i = 0; i < ht->size; i++)
    {
      if (!ht->table[i])
	num_free++;
    }
  printf ("size: %.3f MB (%.2f %% full)\n",
	  (double) (sizeof (BtorPtrHashTable) +
	  ht->size * sizeof (*ht->table) +
	  ht->count * sizeof (BtorPtrHashBucket)) / 1024 / 1024,
	  (double) ht->count / (ht->size + num_free) * 100); 

  srand (129);
  start = btor_util_time_stamp ();
  for (i = num_items; i > 0; i--)
    {
//      val = i * 7;
//      val = rand();
      val = rand() % 2123541 + 1;
      if (btor_hashptr_table_get (ht, (void *) (size_t) val))
      btor_hashptr_table_remove (ht, (void *) (size_t) val, 0, 0);
    }
  printf ("%.3f remove\n", btor_util_time_stamp () - start);

  num_free = 0;
  for (i = 0; i < ht->size; i++)
    {
      if (!ht->table[i])
	num_free++;
    }
  printf ("size: %.3f MB (%.2f %% full)\n",
	  (double) (sizeof (BtorPtrHashTable) +
	  ht->size * sizeof (*ht->table) +
	  ht->count * sizeof (BtorPtrHashBucket)) / 1024 / 1024,
	  (double) ht->count / (ht->size + num_free) * 100); 


  btor_hashptr_table_delete (ht);
  finish_int_hash_table_test ();
}
#endif

static void
test_new_delete_int_hash_table (void)
{
  size_t allocated     = mem->allocated;
  BtorIntHashTable *ht = btor_hashint_table_new (mem);
  btor_hashint_table_delete (ht);
  assert (allocated == mem->allocated);
}

static void
test_add_int_hash_table (void)
{
  init_int_hash_table_test ();

  size_t i;
  int32_t items[] = {
      123,       -1,     17,      5,       32,       64,      -1023,    101231,
      10,        11,     12,      13,      14,       -25,     43,       57,
      75,        51,     86,      -210,    1349,     1084,    -5860,    -1948,
      19548,     45802,  489501,  5810,    -85901,   4885,    28040,    -54801,
      185018,    -43019, 5801,    50185,   18501,    -60154,  105,      195,
      192,       1941,   -148702, -182491, 109581,   -51883,  12840918, -189203,
      -19128348, 129481, 184022,  875092,  19824192, 4913823, 0};

  for (i = 0; items[i] != 0; i++)
  {
    btor_hashint_table_add (h, items[i]);
    assert (btor_hashint_table_get_pos (h, items[i]) < h->size);
  }

  for (i = 0; items[i] != 0; i++)
    assert (btor_hashint_table_contains (h, items[i]));

  for (i = 0; items[i] != 0; i++)
  {
    btor_hashint_table_remove (h, items[i]);
    assert (!btor_hashint_table_contains (h, items[i]));
    assert (btor_hashint_table_get_pos (h, items[i]) == h->size);
  }

  finish_int_hash_table_test ();
}

void
run_int_hash_table_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_int_hash_table);
  BTOR_RUN_TEST (add_int_hash_table);
}

void
finish_int_hash_table_tests (void)
{
  btor_mem_mgr_delete (mem);
}

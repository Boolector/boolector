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

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

static BtorMemMgr *mem;
static BtorIntHashTable *h;

void
init_int_hash_map_tests (void)
{
  mem = btor_mem_mgr_new ();
}

static void
init_int_hash_map_test (void)
{
  assert (!h);
  h = btor_hashint_map_new (mem);
}

static void
finish_int_hash_map_test (void)
{
  assert (h);
  btor_hashint_map_delete (h);
  h = 0;
}

static void
test_new_delete_int_hash_map (void)
{
  size_t allocated     = mem->allocated;
  BtorIntHashTable *ht = btor_hashint_map_new (mem);
  btor_hashint_map_delete (ht);
  assert (allocated == mem->allocated);
}

static void
test_add_int_hash_map (void)
{
  init_int_hash_map_test ();

  size_t i;
  BtorHashTableData d;
  int32_t items[] = {
      123,       -1,     17,      5,       32,       64,      -1023,    101231,
      10,        11,     12,      13,      14,       -25,     43,       57,
      75,        51,     86,      -210,    1349,     1084,    -5860,    -1948,
      19548,     45802,  489501,  5810,    -85901,   4885,    28040,    -54801,
      185018,    -43019, 5801,    50185,   18501,    -60154,  105,      195,
      192,       1941,   -148702, -182491, 109581,   -51883,  12840918, -189203,
      -19128348, 129481, 184022,  875092,  19824192, 4913823, 0};
  int32_t data[] = {
      123,       -1,     17,      5,       32,       64,      -1023,    101231,
      10,        11,     12,      13,      14,       -25,     43,       57,
      75,        51,     86,      -210,    1349,     1084,    -5860,    -1948,
      19548,     45802,  489501,  5810,    -85901,   4885,    28040,    -54801,
      185018,    -43019, 5801,    50185,   18501,    -60154,  105,      195,
      192,       1941,   -148702, -182491, 109581,   -51883,  12840918, -189203,
      -19128348, 129481, 184022,  875092,  19824192, 4913823, 0};

  for (i = 0; items[i] != 0; i++)
    btor_hashint_map_add (h, items[i])->as_int = data[i];

  for (i = 0; items[i] != 0; i++)
    assert (btor_hashint_map_contains (h, items[i]));

  for (i = 0; items[i] != 0; i++)
  {
    btor_hashint_map_remove (h, items[i], &d);
    assert (d.as_int == data[i]);
    assert (!btor_hashint_map_contains (h, items[i]));
  }

  finish_int_hash_map_test ();
}

void
run_int_hash_map_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_int_hash_map);
  BTOR_RUN_TEST (add_int_hash_map);
}

void
finish_int_hash_map_tests (void)
{
  btor_mem_mgr_delete (mem);
}

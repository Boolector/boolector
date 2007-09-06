#include "testhash.h"
#include "btorhash.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static BtorMemMgr *mem;

void
init_hash_tests (void)
{
  mem = btor_new_mem_mgr ();
}

static void
test_new_delete_hash (void)
{
  size_t allocated          = mem->allocated;
  BtorPtrToIntHashTable *ht = btor_new_ptr_to_int_hash_table (mem, 0, 0, 0);
  btor_delete_ptr_to_int_hash_tabale (ht);
  assert (allocated == mem->allocated);
}

static void
test_hash_str2i (void)
{
  BtorPtrToIntHashTable *ht = btor_new_ptr_to_int_hash_table (mem, 0, 0, 0);

  btor_insert_in_ptr_to_int_hash_table (ht, "one", 1);
  assert (btor_find_in_ptr_to_int_hash_table (ht, "one"));
  assert (btor_find_in_ptr_to_int_hash_table (ht, "one")->data == 1);

  btor_insert_in_ptr_to_int_hash_table (ht, "two", 2);
  assert (btor_find_in_ptr_to_int_hash_table (ht, "two"));
  assert (btor_find_in_ptr_to_int_hash_table (ht, "two")->data == 2);

  btor_insert_in_ptr_to_int_hash_table (ht, "three", 3);
  assert (btor_find_in_ptr_to_int_hash_table (ht, "three"));
  assert (btor_find_in_ptr_to_int_hash_table (ht, "three")->data == 3);

  btor_delete_ptr_to_int_hash_tabale (ht);
}

static void
test_traverse_hash_str2i (void)
{
  BtorPtrToIntHashTable *ht;
  BtorPtrToIntHashBucket *p;
  char buffer[20];
  FILE *file;
  int i;

  ht = btor_new_ptr_to_int_hash_table (mem, 0, btor_hashstr, btor_cmpstr);

  for (i = 0; i < 40; i++)
  {
    sprintf (buffer, "%d", i);
    p      = btor_insert_in_ptr_to_int_hash_table (ht, buffer, i);
    p->key = btor_strdup (mem, buffer);
  }

  for (i = 0; i < 40; i++)
  {
    sprintf (buffer, "%d", i);
    assert (btor_find_in_ptr_to_int_hash_table (ht, buffer));
    assert (btor_find_in_ptr_to_int_hash_table (ht, buffer)->data == i);
  }

  file = fopen ("log/traverse_hash_str2i.log", "w");
  for (p = ht->first; p; p = p->next)
  {
    fprintf (file, "%s %d\n", (const char *) p->key, p->data);
    btor_freestr (mem, p->key);
  }
  fclose (file);

  btor_delete_ptr_to_int_hash_tabale (ht);
}

void
run_hash_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_hash);
  BTOR_RUN_TEST (hash_str2i);
  BTOR_RUN_TEST_CHECK_LOG (traverse_hash_str2i);
}

void
finish_hash_tests (void)
{
  btor_delete_mem_mgr (mem);
}

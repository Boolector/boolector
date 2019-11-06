/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/btorhashptr.h"
}

#include <stdlib.h>

class TestHash : public TestMm
{
};

TEST_F (TestHash, new_delete)
{
  size_t allocated     = d_mm->allocated;
  BtorPtrHashTable *ht = btor_hashptr_table_new (d_mm, 0, 0);
  btor_hashptr_table_delete (ht);
  ASSERT_EQ (allocated, d_mm->allocated);
}

TEST_F (TestHash, str2i)
{
  BtorPtrHashTable *ht = btor_hashptr_table_new (d_mm, 0, 0);

  btor_hashptr_table_add (ht, (void *) "one")->data.as_int = 1;
  ASSERT_NE (btor_hashptr_table_get (ht, (void *) "one"), nullptr);
  ASSERT_EQ (btor_hashptr_table_get (ht, (void *) "one")->data.as_int, 1);

  btor_hashptr_table_add (ht, (void *) "two")->data.as_int = 2;
  ASSERT_NE (btor_hashptr_table_get (ht, (void *) "two"), nullptr);
  ASSERT_EQ (btor_hashptr_table_get (ht, (void *) "two")->data.as_int, 2);

  btor_hashptr_table_add (ht, (void *) "three")->data.as_int = 3;
  ASSERT_NE (btor_hashptr_table_get (ht, (void *) "three"), nullptr);
  ASSERT_EQ (btor_hashptr_table_get (ht, (void *) "three")->data.as_int, 3);

  btor_hashptr_table_delete (ht);
}

TEST_F (TestHash, traverse_str2i)
{
  open_log_file ("traverse_hash_str2i");

  BtorPtrHashTable *ht;
  BtorPtrHashBucket *p;
  char buffer[20];
  int32_t i;

  ht = btor_hashptr_table_new (d_mm, btor_hash_str, btor_compare_str);

  for (i = 0; i < 40; i++)
  {
    sprintf (buffer, "%d", i);
    p              = btor_hashptr_table_add (ht, buffer);
    p->data.as_int = i;
    p->key         = btor_mem_strdup (d_mm, buffer);
  }

  for (i = 0; i < 40; i++)
  {
    sprintf (buffer, "%d", i);
    ASSERT_NE (btor_hashptr_table_get (ht, buffer), nullptr);
    ASSERT_EQ (btor_hashptr_table_get (ht, buffer)->data.as_int, i);
  }

  for (p = ht->first; p; p = p->next)
  {
    fprintf (d_log_file, "%s %d\n", (char *) p->key, p->data.as_int);
    btor_mem_freestr (d_mm, (char *) p->key);
  }

  btor_hashptr_table_delete (ht);
}

TEST_F (TestHash, str2str)
{
  open_log_file ("hash_str2str");

  BtorPtrHashTable *ht;
  BtorPtrHashBucket *p;
  BtorHashTableData data;
  char buffer[20];
  void *key;
  int32_t i;

  ht = btor_hashptr_table_new (d_mm, btor_hash_str, btor_compare_str);

  for (i = 0; i < 10; i++)
  {
    sprintf (buffer, "%d", i);
    p      = btor_hashptr_table_add (ht, buffer);
    p->key = btor_mem_strdup (d_mm, buffer);
    sprintf (buffer, "%d", 10 - i);
    p->data.as_str = btor_mem_strdup (d_mm, buffer);
  }

  for (i = 0; i < 10; i++)
  {
    sprintf (buffer, "%d", i);
    p = btor_hashptr_table_get (ht, buffer);
    ASSERT_NE (p, nullptr);
    ASSERT_EQ (i, atoi ((char *) p->key));
    ASSERT_EQ (10 - i, atoi (p->data.as_str));
  }

  for (i = 0; i < 10; i += 2)
  {
    sprintf (buffer, "%d", i);
    btor_hashptr_table_remove (ht, buffer, &key, &data);
    btor_mem_freestr (d_mm, data.as_str);
    btor_mem_freestr (d_mm, (char *) key);
  }

  for (p = ht->first; p; p = p->next)
  {
    fprintf (d_log_file, "%s -> %s\n", (char *) p->key, p->data.as_str);
    btor_mem_freestr (d_mm, (char *) p->key);
    btor_mem_freestr (d_mm, p->data.as_str);
  }

  btor_hashptr_table_delete (ht);
}

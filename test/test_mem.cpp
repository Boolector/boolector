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
#include "utils/btormem.h"
}

class TestMem : public TestMm
{
 protected:
};

TEST_F (TestMem, new_delete_mem_mgr) {}

TEST_F (TestMem, malloc)
{
  int32_t *test = NULL;
  test          = (int32_t *) btor_mem_malloc (d_mm, sizeof (int32_t));
  ASSERT_NE (test, nullptr);
  *test = 3;
  btor_mem_free (d_mm, test, sizeof (int32_t));
}

TEST_F (TestMem, realloc)
{
  int32_t *test = NULL;
  test          = (int32_t *) btor_mem_malloc (d_mm, sizeof (int32_t));
  ASSERT_NE (test, nullptr);
  test[0] = 3;
  test    = (int32_t *) btor_mem_realloc (
      d_mm, test, sizeof (int32_t), sizeof (int32_t) * 2);
  ASSERT_EQ (test[0], 3);
  test[1] = 5;
  ASSERT_EQ (test[0], 3);
  ASSERT_EQ (test[1], 5);
  btor_mem_free (d_mm, test, sizeof (int32_t) * 2);
}

TEST_F (TestMem, calloc)
{
  int32_t *test = NULL;
  test          = (int32_t *) btor_mem_calloc (d_mm, sizeof (int32_t), 4);
  ASSERT_NE (test, nullptr);
  ASSERT_EQ (test[0], 0);
  ASSERT_EQ (test[1], 0);
  ASSERT_EQ (test[2], 0);
  ASSERT_EQ (test[3], 0);
  btor_mem_free (d_mm, test, sizeof (int32_t) * 4);
}

TEST_F (TestMem, strdup)
{
  char *test = btor_mem_strdup (d_mm, "test");
  ASSERT_EQ (strcmp (test, "test"), 0);
  btor_mem_freestr (d_mm, test);
}

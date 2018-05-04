/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmem.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <string.h>

void
init_mem_tests (void)
{
}

static void
test_new_delete_mem_mgr (void)
{
  BtorMemMgr *mm = btor_mem_mgr_new ();
  btor_mem_mgr_delete (mm);
}

static void
test_malloc_mem (void)
{
  int32_t *test  = NULL;
  BtorMemMgr *mm = btor_mem_mgr_new ();
  test           = (int32_t *) btor_mem_malloc (mm, sizeof (int32_t));
  assert (test != NULL);
  *test = 3;
  btor_mem_free (mm, test, sizeof (int32_t));
  btor_mem_mgr_delete (mm);
}

static void
test_realloc_mem (void)
{
  int32_t *test  = NULL;
  BtorMemMgr *mm = btor_mem_mgr_new ();
  test           = (int32_t *) btor_mem_malloc (mm, sizeof (int32_t));
  assert (test != NULL);
  test[0] = 3;
  test    = (int32_t *) btor_mem_realloc (
      mm, test, sizeof (int32_t), sizeof (int32_t) * 2);
  assert (test[0] == 3);
  test[1] = 5;
  assert (test[0] == 3);
  assert (test[1] == 5);
  btor_mem_free (mm, test, sizeof (int32_t) * 2);
  btor_mem_mgr_delete (mm);
}

static void
test_calloc_mem (void)
{
  int32_t *test  = NULL;
  BtorMemMgr *mm = btor_mem_mgr_new ();
  test           = (int32_t *) btor_mem_calloc (mm, sizeof (int32_t), 4);
  assert (test != NULL);
  assert (test[0] == 0);
  assert (test[1] == 0);
  assert (test[2] == 0);
  assert (test[3] == 0);
  btor_mem_free (mm, test, sizeof (int32_t) * 4);
  btor_mem_mgr_delete (mm);
}

static void
test_strdup_mem (void)
{
  BtorMemMgr *mm = btor_mem_mgr_new ();
  char *test     = btor_mem_strdup (mm, "test");
  assert (strcmp (test, "test") == 0);
  btor_mem_freestr (mm, test);
  btor_mem_mgr_delete (mm);
}

void
run_mem_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_mem_mgr);
  BTOR_RUN_TEST (malloc_mem);
  BTOR_RUN_TEST (realloc_mem);
  BTOR_RUN_TEST (calloc_mem);
  BTOR_RUN_TEST (strdup_mem);
}

void
finish_mem_tests (void)
{
}

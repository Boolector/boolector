/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  All rights reserved.
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
  BtorMemMgr *mm = btor_new_mem_mgr ();
  btor_delete_mem_mgr (mm);
}

static void
test_malloc_mem (void)
{
  int *test      = NULL;
  BtorMemMgr *mm = btor_new_mem_mgr ();
  test           = (int *) btor_malloc (mm, sizeof (int));
  assert (test != NULL);
  *test = 3;
  btor_free (mm, test, sizeof (int));
  btor_delete_mem_mgr (mm);
}

static void
test_realloc_mem (void)
{
  int *test      = NULL;
  BtorMemMgr *mm = btor_new_mem_mgr ();
  test           = (int *) btor_malloc (mm, sizeof (int));
  assert (test != NULL);
  test[0] = 3;
  test    = (int *) btor_realloc (mm, test, sizeof (int), sizeof (int) * 2);
  assert (test[0] == 3);
  test[1] = 5;
  assert (test[0] == 3);
  assert (test[1] == 5);
  btor_free (mm, test, sizeof (int) * 2);
  btor_delete_mem_mgr (mm);
}

static void
test_calloc_mem (void)
{
  int *test      = NULL;
  BtorMemMgr *mm = btor_new_mem_mgr ();
  test           = (int *) btor_calloc (mm, sizeof (int), 4);
  assert (test != NULL);
  assert (test[0] == 0);
  assert (test[1] == 0);
  assert (test[2] == 0);
  assert (test[3] == 0);
  btor_free (mm, test, sizeof (int) * 4);
  btor_delete_mem_mgr (mm);
}

static void
test_strdup_mem (void)
{
  BtorMemMgr *mm = btor_new_mem_mgr ();
  char *test     = btor_strdup (mm, "test");
  assert (strcmp (test, "test") == 0);
  btor_freestr (mm, test);
  btor_delete_mem_mgr (mm);
}

void
run_mem_tests (int argc, char **argv)
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

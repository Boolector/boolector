/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmodelgen.h"

#include "testrunner.h"
#include "utils/btorstack.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static BtorMemMgr *g_mm = NULL;

void
init_modelgen_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

static void
modelgen_test (const char *fname, int32_t rwl)
{
  assert (rwl >= 0);
  assert (rwl <= 3);

  char *btor_fname, *log_fname;
  size_t len, len_btor_fname, len_btor, len_log_fname, len_log;
#ifndef BTOR_WINDOWS_BUILD
  char *syscall_string;
  size_t len_syscall_string;
  int32_t ret_val;
#endif
  char *s_btor, *s_log;
  BtorCharPtrStack args;

  BTOR_INIT_STACK (g_mm, args);
  BTOR_PUSH_STACK (args, (char *) fname);

  len = strlen (fname);

  len_btor_fname = len + 6;
  BTOR_NEWN (g_mm, btor_fname, len_btor_fname);
  sprintf (btor_fname, "%s.btor", fname);
  len_btor = strlen (btor_log_dir) + strlen (btor_fname) + 20;
  BTOR_NEWN (g_mm, s_btor, len_btor);
  sprintf (s_btor, "%s%s", btor_log_dir, btor_fname);
  BTOR_PUSH_STACK (args, s_btor);

  len_log_fname = len + 5;
  BTOR_NEWN (g_mm, log_fname, len_log_fname);
  sprintf (log_fname, "%s.log", fname);
  BTOR_PUSH_STACK (args, "-o");
  len_log = strlen (btor_log_dir) + strlen (log_fname) + 20;
  BTOR_NEWN (g_mm, s_log, len_log);
  sprintf (s_log, "%s%s", btor_log_dir, log_fname);
  BTOR_PUSH_STACK (args, s_log);

  BTOR_PUSH_STACK (args, "-rwl=3");
  BTOR_PUSH_STACK (args, "-m");

  run_boolector (BTOR_COUNT_STACK (args), args.start);

#ifndef BTOR_WINDOWS_BUILD
  len_syscall_string = len + 5 + len + 4
                       + strlen ("btorcheckmodel.py   boolector > /dev/null")
                       + strlen (btor_contrib_dir) + strlen (btor_log_dir) * 2
                       + 1 + strlen (btor_bin_dir);
  BTOR_NEWN (g_mm, syscall_string, len_syscall_string);
  sprintf (syscall_string,
           "%sbtorcheckmodel.py %s%s %s%s %sboolector > /dev/null",
           btor_contrib_dir,
           btor_log_dir,
           btor_fname,
           btor_log_dir,
           log_fname,
           btor_bin_dir);
  ret_val = system (syscall_string);
  assert (ret_val == 0);
  BTOR_DELETEN (g_mm, syscall_string, len_syscall_string);
#endif

  BTOR_DELETEN (g_mm, log_fname, len_log_fname);
  BTOR_DELETEN (g_mm, btor_fname, len_btor_fname);
  BTOR_DELETEN (g_mm, s_btor, len_btor);
  BTOR_DELETEN (g_mm, s_log, len_log);
  BTOR_RELEASE_STACK (args);
}

static void
test_modelgen1 ()
{
  modelgen_test ("modelgen1", 1);
}

static void
test_modelgen2 ()
{
  modelgen_test ("modelgen2", 3);
}

static void
test_modelgen3 ()
{
  modelgen_test ("modelgen3", 3);
}

static void
test_modelgen4 ()
{
  modelgen_test ("modelgen4", 3);
}

static void
test_modelgen5 ()
{
  modelgen_test ("modelgen5", 3);
}

static void
test_modelgen6 ()
{
  modelgen_test ("modelgen6", 3);
}

static void
test_modelgen7 ()
{
  modelgen_test ("modelgen7", 3);
}

static void
test_modelgen8 ()
{
  modelgen_test ("modelgen8", 0);
}

static void
test_modelgen9 ()
{
  modelgen_test ("modelgen9", 3);
}

static void
test_modelgen10 ()
{
  modelgen_test ("modelgen10", 3);
}

static void
test_modelgen11 ()
{
  modelgen_test ("modelgen11", 3);
}

static void
test_modelgen12 ()
{
  modelgen_test ("modelgen12", 3);
}

static void
test_modelgen13 ()
{
  modelgen_test ("modelgen13", 3);
}

static void
test_modelgen14 ()
{
  modelgen_test ("modelgen14", 3);
}

static void
test_modelgen15 ()
{
  modelgen_test ("modelgen15", 3);
}

static void
test_modelgen16 ()
{
  modelgen_test ("modelgen16", 1);
}

static void
test_modelgen17 ()
{
  modelgen_test ("modelgen17", 1);
}

static void
test_modelgen18 ()
{
  modelgen_test ("modelgen18", 3);
}

static void
test_modelgen19 ()
{
  modelgen_test ("modelgen19", 2);
}

static void
test_modelgen20 ()
{
  modelgen_test ("modelgen20", 3);
}

static void
test_modelgen21 ()
{
  modelgen_test ("modelgen21", 3);
}

static void
test_modelgen22 ()
{
  modelgen_test ("modelgen22", 3);
}

static void
test_modelgen23 ()
{
  modelgen_test ("modelgen23", 3);
}

static void
test_modelgen24 ()
{
  modelgen_test ("modelgen24", 3);
}

static void
test_modelgen25 ()
{
  modelgen_test ("modelgen25", 3);
}

static void
test_modelgen26 ()
{
  modelgen_test ("modelgen26", 3);
}

static void
test_modelgen27 ()
{
  modelgen_test ("modelgen27", 3);
}

void
run_modelgen_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (modelgen1);
  BTOR_RUN_TEST (modelgen2);
  BTOR_RUN_TEST (modelgen3);
  BTOR_RUN_TEST (modelgen4);
  BTOR_RUN_TEST (modelgen5);
  BTOR_RUN_TEST (modelgen6);
  BTOR_RUN_TEST (modelgen7);
  BTOR_RUN_TEST (modelgen8);
  BTOR_RUN_TEST (modelgen9);
  BTOR_RUN_TEST (modelgen10);
  BTOR_RUN_TEST (modelgen11);
  BTOR_RUN_TEST (modelgen12);
  BTOR_RUN_TEST (modelgen13);
  BTOR_RUN_TEST (modelgen14);
  BTOR_RUN_TEST (modelgen15);
  BTOR_RUN_TEST (modelgen16);
  BTOR_RUN_TEST (modelgen17);
  BTOR_RUN_TEST (modelgen18);
  BTOR_RUN_TEST (modelgen19);
  BTOR_RUN_TEST (modelgen20);
  BTOR_RUN_TEST (modelgen21);
  BTOR_RUN_TEST (modelgen22);
  BTOR_RUN_TEST (modelgen23);
  BTOR_RUN_TEST (modelgen24);
  BTOR_RUN_TEST (modelgen25);
  BTOR_RUN_TEST (modelgen26);
  BTOR_RUN_TEST (modelgen27);
}

void
finish_modelgen_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

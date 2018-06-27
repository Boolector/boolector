/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmodelgensmt2.h"

#include "testrunner.h"
#include "utils/btorstack.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static BtorMemMgr *g_mm;

void
init_modelgensmt2_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

static void
modelgensmt2_test (const char *fname, int32_t rwl)
{
  assert (rwl >= 0);
  assert (rwl <= 3);

  char *smt_fname, *log_fname;
  size_t len, len_smt_fname, len_log_fname, len_smt, len_log;
#ifndef BTOR_WINDOWS_BUILD
  char *syscall_string;
  size_t len_syscall_string;
  int32_t ret_val;
#endif
  char *s_smt, *s_log;
  BtorCharPtrStack args;

  BTOR_INIT_STACK (g_mm, args);
  BTOR_PUSH_STACK (args, (char *) fname);

  len = strlen (fname);

  len_smt_fname = len + 6;
  BTOR_NEWN (g_mm, smt_fname, len_smt_fname);
  sprintf (smt_fname, "%s.smt2", fname);
  len_smt = strlen (btor_log_dir) + strlen (smt_fname) + 20;
  BTOR_NEWN (g_mm, s_smt, len_smt);
  sprintf (s_smt, "%s%s", btor_log_dir, smt_fname);
  BTOR_PUSH_STACK (args, s_smt);

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
  BTOR_PUSH_STACK (args, "--smt2-model");

  run_boolector (BTOR_COUNT_STACK (args), args.start);

#ifndef BTOR_WINDOWS_BUILD
  len_syscall_string =
      len + 5 + len + 4
      + strlen ("btorcheckmodelsmt2.sh   boolector > /dev/null")
      + strlen (btor_contrib_dir) + strlen (btor_log_dir) * 2 + 1
      + strlen (btor_bin_dir);
  BTOR_NEWN (g_mm, syscall_string, len_syscall_string);
  sprintf (syscall_string,
           "%sbtorcheckmodelsmt2.sh %s%s %s%s %sboolector > /dev/null",
           btor_contrib_dir,
           btor_log_dir,
           smt_fname,
           btor_log_dir,
           log_fname,
           btor_bin_dir);

  ret_val = system (syscall_string);
  assert (ret_val == 0);
  BTOR_DELETEN (g_mm, syscall_string, len_syscall_string);
#endif

  BTOR_DELETEN (g_mm, smt_fname, len_smt_fname);
  BTOR_DELETEN (g_mm, s_smt, len_smt);
  BTOR_DELETEN (g_mm, log_fname, len_log_fname);
  BTOR_DELETEN (g_mm, s_log, len_log);
  BTOR_RELEASE_STACK (args);
}

static void
test_modelgensmt21 ()
{
  modelgensmt2_test ("modelgensmt21", 1);
}

static void
test_modelgensmt22 ()
{
  modelgensmt2_test ("modelgensmt22", 3);
}

static void
test_modelgensmt23 ()
{
  modelgensmt2_test ("modelgensmt23", 3);
}

static void
test_modelgensmt24 ()
{
  modelgensmt2_test ("modelgensmt24", 3);
}

static void
test_modelgensmt25 ()
{
  modelgensmt2_test ("modelgensmt25", 3);
}

static void
test_modelgensmt26 ()
{
  modelgensmt2_test ("modelgensmt26", 3);
}

static void
test_modelgensmt27 ()
{
  modelgensmt2_test ("modelgensmt27", 3);
}

static void
test_modelgensmt28 ()
{
  modelgensmt2_test ("modelgensmt28", 0);
}

static void
test_modelgensmt29 ()
{
  modelgensmt2_test ("modelgensmt29", 3);
}

static void
test_modelgensmt210 ()
{
  modelgensmt2_test ("modelgensmt210", 3);
}

static void
test_modelgensmt211 ()
{
  modelgensmt2_test ("modelgensmt211", 3);
}

static void
test_modelgensmt212 ()
{
  modelgensmt2_test ("modelgensmt212", 3);
}

static void
test_modelgensmt213 ()
{
  modelgensmt2_test ("modelgensmt213", 3);
}

static void
test_modelgensmt214 ()
{
  modelgensmt2_test ("modelgensmt214", 3);
}

static void
test_modelgensmt215 ()
{
  modelgensmt2_test ("modelgensmt215", 3);
}

static void
test_modelgensmt216 ()
{
  modelgensmt2_test ("modelgensmt216", 1);
}

static void
test_modelgensmt217 ()
{
  modelgensmt2_test ("modelgensmt217", 1);
}

static void
test_modelgensmt218 ()
{
  modelgensmt2_test ("modelgensmt218", 3);
}

static void
test_modelgensmt219 ()
{
  modelgensmt2_test ("modelgensmt219", 2);
}

static void
test_modelgensmt220 ()
{
  modelgensmt2_test ("modelgensmt220", 3);
}

static void
test_modelgensmt221 ()
{
  modelgensmt2_test ("modelgensmt221", 3);
}

static void
test_modelgensmt222 ()
{
  modelgensmt2_test ("modelgensmt222", 3);
}

static void
test_modelgensmt223 ()
{
  modelgensmt2_test ("modelgensmt223", 3);
}

static void
test_modelgensmt224 ()
{
  modelgensmt2_test ("modelgensmt224", 3);
}

static void
test_modelgensmt225 ()
{
  modelgensmt2_test ("modelgensmt225", 3);
}

static void
test_modelgensmt226 ()
{
  modelgensmt2_test ("modelgensmt226", 3);
}

static void
test_modelgensmt227 ()
{
  modelgensmt2_test ("modelgensmt227", 3);
}

void
run_modelgensmt2_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (modelgensmt21);
  BTOR_RUN_TEST (modelgensmt22);
  BTOR_RUN_TEST (modelgensmt23);
  BTOR_RUN_TEST (modelgensmt24);
  BTOR_RUN_TEST (modelgensmt25);
  BTOR_RUN_TEST (modelgensmt26);
  BTOR_RUN_TEST (modelgensmt27);
  BTOR_RUN_TEST (modelgensmt28);
  BTOR_RUN_TEST (modelgensmt29);
  BTOR_RUN_TEST (modelgensmt210);
  BTOR_RUN_TEST (modelgensmt211);
  BTOR_RUN_TEST (modelgensmt212);
  BTOR_RUN_TEST (modelgensmt213);
  BTOR_RUN_TEST (modelgensmt214);
  BTOR_RUN_TEST (modelgensmt215);
  BTOR_RUN_TEST (modelgensmt216);
  BTOR_RUN_TEST (modelgensmt217);
  BTOR_RUN_TEST (modelgensmt218);
  BTOR_RUN_TEST (modelgensmt219);
  BTOR_RUN_TEST (modelgensmt220);
  BTOR_RUN_TEST (modelgensmt221);
  BTOR_RUN_TEST (modelgensmt222);
  BTOR_RUN_TEST (modelgensmt223);
  BTOR_RUN_TEST (modelgensmt224);
  BTOR_RUN_TEST (modelgensmt225);
  BTOR_RUN_TEST (modelgensmt226);
  BTOR_RUN_TEST (modelgensmt227);
}

void
finish_modelgensmt2_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

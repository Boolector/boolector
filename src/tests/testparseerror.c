/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testparseerror.h"

#include "btormain.h"
#include "testrunner.h"
#include "utils/btorstack.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

char *g_name     = NULL;
int32_t g_smtlib = 1;

static BtorMemMgr *g_mm = NULL;

void
init_parseerror_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

static void
run_smt_parse_error_test (void)
{
  char *fname      = g_name, *smt_fname, *log_fname;
  char *smt_suffix = (g_smtlib == 1) ? "smt" : "smt2";
  char *s_smt, *s_log;
  int32_t len, suff_len, len_smt, len_log, len_smt_fname, len_log_fname;
  BtorCharPtrStack args;

  BTOR_INIT_STACK (g_mm, args);

  if (g_smtlib == 1)
    BTOR_PUSH_STACK (args, "--smt1");
  else
    BTOR_PUSH_STACK (args, "--smt2");

  len      = strlen (fname);
  suff_len = strlen (smt_suffix);

  len_smt_fname = len + suff_len + 2;
  len_log_fname = len + 5;

  BTOR_NEWN (g_mm, smt_fname, len_smt_fname);
  sprintf (smt_fname, "%s.%s", fname, smt_suffix);
  len_smt = strlen (btor_log_dir) + strlen (smt_fname) + 20;
  BTOR_NEWN (g_mm, s_smt, len_smt);
  sprintf (s_smt, "%s%s", btor_log_dir, smt_fname);
  BTOR_PUSH_STACK (args, s_smt);

  BTOR_NEWN (g_mm, log_fname, len_log_fname);
  sprintf (log_fname, "%s.log", fname);
  BTOR_PUSH_STACK (args, "-o");
  len_log = strlen (btor_log_dir) + strlen (log_fname) + 20;
  BTOR_NEWN (g_mm, s_log, len_log);
  sprintf (s_log, "%s%s", btor_log_dir, log_fname);
  BTOR_PUSH_STACK (args, s_log);

  run_boolector (BTOR_COUNT_STACK (args), args.start);

  BTOR_DELETEN (g_mm, smt_fname, len_smt_fname);
  BTOR_DELETEN (g_mm, log_fname, len_log_fname);
  BTOR_DELETEN (g_mm, s_smt, len_smt);
  BTOR_DELETEN (g_mm, s_log, len_log);
  BTOR_RELEASE_STACK (args);
}

static bool
hasprefix (const char *str, const char *prefix)
{
  return !strncmp (str, prefix, strlen (prefix));
}

static bool
hassuffix (const char *str, const char *suffix)
{
  int32_t difflen = strlen (str) - strlen (suffix);
  if (difflen < 0) return 0;
  return !strcmp (str + difflen, suffix);
}

void
run_parseerror_tests (int32_t argc, char **argv)
{
  DIR *dir = opendir (btor_log_dir);
  struct dirent *de;
  char *base = NULL;
  while ((de = readdir (dir)))
  {
    char *name = de->d_name, *dotptr;
    base       = strdup (name);
    if ((dotptr = strchr (base, '.')))
    {
      *dotptr  = 0;
      g_name   = base;
      g_smtlib = 0;
      if (hasprefix (name, "smt1perr") && hassuffix (name, ".smt"))
        g_smtlib = 1;
      else if (hasprefix (name, "smt2perr") && hassuffix (name, ".smt2"))
        g_smtlib = 2;

      if (g_smtlib > 0)
        run_test_case (argc, argv, run_smt_parse_error_test, base, 1);
    }
    free (base);
  }
  closedir (dir);
}

void
finish_parseerror_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

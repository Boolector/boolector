/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testparseerror.h"

#include "btormain.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

char *g_name     = NULL;
int32_t g_smtlib = 1;

void
init_parseerror_tests (void)
{
}

static bool
file_exists (const char *path)
{
  struct stat buf;
  return !stat (path, &buf);
}

static void
run_smt_parse_error_test (void)
{
  char *fname      = g_name, *smt_fname, *log_fname, *log_path;
  char *smt_suffix = (g_smtlib == 1) ? "smt" : "smt2";
  char *smt_opt    = (g_smtlib == 1) ? "--smt1" : "--smt2";
  char *syscall_string;
  int32_t res, len, suff_len;

  len      = strlen (fname);
  suff_len = strlen (smt_suffix);

  smt_fname = (char *) malloc (sizeof (char) * (len + suff_len + 2));
  sprintf (smt_fname, "%s.%s", fname, smt_suffix);

  log_fname = (char *) malloc (sizeof (char) * (len + 5));
  sprintf (log_fname, "%s.log", fname);

  syscall_string = (char *) malloc (
      sizeof (char)
      * (len + suff_len + 1 + len + 4 + strlen ("boolector  ")
         + strlen (btor_bin_dir) + strlen (smt_opt) + strlen (" > ")
         + strlen (btor_log_dir) * 2 + strlen (" 2>&1") + 1));

  sprintf (syscall_string,
           "%sboolector %s %s%s > %s%s 2>&1",
           btor_bin_dir,
           smt_opt,
           btor_log_dir,
           smt_fname,
           btor_log_dir,
           log_fname);

  if ((res = WEXITSTATUS (system (syscall_string))) != 1)
  {
    FILE *file;

    log_path = malloc (len + strlen (btor_log_dir) + 4 + 1);
    sprintf (log_path, "%s%s.log", btor_log_dir, log_fname);
    assert (file_exists (log_path));
    file = fopen (log_path, "a");
    fprintf (
        file, "test_parse_error_%s_test: exit code %d != 1\n", smt_suffix, res);
    fclose (file);
    free (log_path);
  }

  free (log_fname);
  free (smt_fname);
  free (syscall_string);
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
}

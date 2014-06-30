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
#include <unistd.h>

char *g_name = NULL;
int g_smtlib = 1;

void
init_parseerror_tests (void)
{
}

static int
file_exists (const char *path)
{
  struct stat buf;
  return !stat (path, &buf);
}

static void
run_smt_parse_error_test (void)
{
  char *inpath, *logpath;
  char *argv[5];
  char *name       = g_name;
  char *smt_suffix = (g_smtlib == 1) ? "smt" : "smt2";
  char *smt_opt    = (g_smtlib == 1) ? "--smt" : "--smt2";
  int res;
  inpath  = malloc (strlen (name) + 20);
  logpath = malloc (strlen (name) + 20);
  sprintf (inpath, "log/%s.%s", name, smt_suffix);
  assert (file_exists (inpath));
  sprintf (logpath, "log/%s.log", name);
  argv[0] = "test_parse_error_smt_test";
  argv[1] = inpath;
  argv[2] = smt_opt;
  argv[3] = "-o";
  argv[4] = logpath;
  res     = boolector_main (5, argv);
  if (res != 1)
  {
    FILE *file = fopen (logpath, "a");
    fprintf (
        file, "test_parse_error_%s_test: exit code %d != 1\n", smt_suffix, res);
    fclose (file);
  }
  free (inpath);
  free (logpath);
}

static int
hasprefix (const char *str, const char *prefix)
{
  return !strncmp (str, prefix, strlen (prefix));
}

static int
hassuffix (const char *str, const char *suffix)
{
  int difflen = strlen (str) - strlen (suffix);
  if (difflen < 0) return 0;
  return !strcmp (str + difflen, suffix);
}

void
run_parseerror_tests (int argc, char **argv)
{
  DIR *dir = opendir ("log/");
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

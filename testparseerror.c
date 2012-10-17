/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2007-2012 Robert Daniel Brummayer, Armin Biere
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "testparseerror.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

void
init_parseerror_tests (void)
{
}

#if 0
static void
parseerror_test (const char *fname, int btor)
{
  char *btor_fname, *syscall_string, *suffix;
  size_t len, suffix_len;
  int ret_val;

  len = strlen(fname);
  if (btor)
    {
      suffix = ".btor";
      suffix_len = 5;
    }
  else
    {
      suffix = ".smt";
      suffix_len = 4;
    }

  btor_fname = (char * ) malloc (sizeof (char) * (len + suffix_len + 1));
  sprintf (btor_fname, "%s%s", fname, suffix);
  syscall_string = (char *) malloc (sizeof (char) * 
                   (strlen ("boolector log/") + len + 6 +
		    strlen(" > /dev/null") + 1));
	
  sprintf (syscall_string, "boolector log/%s > /dev/null", btor_fname);
  ret_val = system (syscall_string);
  assert (WEXITSTATUS(ret_val) == 1);
  
  free (syscall_string);
  free (btor_fname);
}

static void
test_parseerror1 ()
{
  parseerror_test ("parseerror1", 1);
}

static void
test_parseerror2 ()
{
  parseerror_test ("parseerror2", 0);
}

static void
test_parseerror3 ()
{
  parseerror_test ("parseerror3", 0);
}

static void
test_parseerror4 ()
{
  parseerror_test ("parseerror4", 0);
}

static void
test_parseerror5 ()
{
  parseerror_test ("parseerror5", 0);
}


void
run_parseerror_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (parseerror1);
  BTOR_RUN_TEST (parseerror2);
  BTOR_RUN_TEST (parseerror3);
  BTOR_RUN_TEST (parseerror4);
  BTOR_RUN_TEST (parseerror5);
}

#else

#include "btormain.h"

#include <dirent.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static int
file_exists (const char *path)
{
  struct stat buf;
  return !stat (path, &buf);
}

static void
run_parse_error_smt_test (const char *name)
{
  char *inpath, *logpath;
  char *argv[4];
  int res;
  inpath  = malloc (strlen (name) + 20);
  logpath = malloc (strlen (name) + 20);
  sprintf (inpath, "log/%s.smt", name);
  assert (file_exists (inpath));
  sprintf (logpath, "log/%s.log", name);
  argv[0] = "test_parse_error_smt_test";
  argv[1] = inpath;
  argv[2] = "-o";
  argv[3] = logpath;
  res     = boolector_main (4, argv);
  if (res != 1)
  {
    FILE *file = fopen (logpath, "a");
    fprintf (file, "test_parse_error_smt_test: exit code %d != 1\n", res);
    fclose (file);
  }
  free (inpath);
  free (logpath);
}

static void
run_parse_error_smt2_test (const char *name)
{
  char *inpath, *logpath;
  char *argv[4];
  int res;
  inpath  = malloc (strlen (name) + 20);
  logpath = malloc (strlen (name) + 20);
  sprintf (inpath, "log/%s.smt2", name);
  assert (file_exists (inpath));
  sprintf (logpath, "log/%s.log", name);
  argv[0] = "test_parse_error_smt2_test";
  argv[1] = inpath;
  argv[2] = "-o";
  argv[3] = logpath;
  res     = boolector_main (4, argv);
  if (res != 1)
  {
    FILE *file = fopen (logpath, "a");
    fprintf (file, "test_parse_error_smt2_test: exit code %d != 1\n", res);
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
  char *base;
  while ((de = readdir (dir)))
  {
    char *name = de->d_name, *dotptr;
    base       = strdup (name);
    if (!(dotptr = strchr (base, '.'))) continue;
    *dotptr = 0;
    if (hasprefix (name, "parseerror") && hassuffix (name, ".smt"))
      run_test_case (argc, argv, 0, run_parse_error_smt_test, base, 1);
    else if (hasprefix (name, "perr") && hassuffix (name, ".smt2"))
      run_test_case (argc, argv, 0, run_parse_error_smt2_test, base, 1);
    free (base);
  }
  closedir (dir);
}

#endif

void
finish_parseerror_tests (void)
{
}

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

static void
parseerror_test (const char *fname, int btor)
{
  char *suffix, *opt = NULL, *syscall_string;
  int len_opt = 0, ret_val;

  if (g_rwwrites) opt = "-nrw";

  if (btor)
    suffix = ".btor";
  else
    suffix = ".smt";

  if (opt) len_opt = strlen (opt);

  syscall_string = (char *) malloc (
      sizeof (char)
      * (strlen ("./boolector log/") + strlen (fname) + strlen (suffix)
         + len_opt + strlen (" > /dev/null") + 1));

  if (opt)
    sprintf (syscall_string, "./boolector log/%s %s > /dev/null", fname, opt);
  else
    sprintf (syscall_string, "./boolector log/%s > /dev/null", fname);

  ret_val = system (syscall_string);
  assert (WEXITSTATUS (ret_val) == 1);

  free (syscall_string);
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

void
finish_parseerror_tests (void)
{
}

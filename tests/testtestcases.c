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

#ifdef NDEBUG
#undef NDEBUG
#endif

#include "testtestcases.h"
#include "btormain.h"
#include "btorstack.h"
#include "testrunner.h"

#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>

static BtorCharPtrStack g_args;

static void
test_testcase (void)
{
  (void) boolector_main (BTOR_COUNT_STACK (g_args), g_args.start);
}

void
init_testcases_tests (void)
{
}

void
run_testcases_tests (int argc, char **argv)
{
  BtorCharStack buffer;
  BtorMemMgr *mem;
  char *token;
  FILE *file;
  int ch, i;

  assert ((file = fopen ("tests/testcases", "r")));

  mem = btor_new_mem_mgr ();

  BTOR_INIT_STACK (g_args);
  BTOR_INIT_STACK (buffer);

  for (;;)
  {
    ch = fgetc (file);
    if (ch == EOF) break;

    if (isspace (ch)) continue;

    if (ch == '#')
    {
      while ((ch = getc (file)) != '\n' && ch != EOF)
        ;

      continue;
    }

    assert (BTOR_EMPTY_STACK (buffer));

    do
    {
      BTOR_PUSH_STACK (mem, buffer, ch);
      ch = fgetc (file);
    } while (ch != '\n' && ch != EOF);
    BTOR_PUSH_STACK (mem, buffer, 0);

    assert (BTOR_EMPTY_STACK (g_args));

    i     = 0;
    token = strtok (buffer.start, " \t");
    while (token)
    {
      BTOR_PUSH_STACK (mem, g_args, token);
      token = strtok (0, " \t");
    }
    if (g_rwwrites) BTOR_PUSH_STACK (mem, g_args, "-rww");
    if (g_rwreads) BTOR_PUSH_STACK (mem, g_args, "-rwr");

    BTOR_RESET_STACK (buffer);

    run_test_case (argc, argv, test_testcase, g_args.start[0], 1);

    BTOR_RESET_STACK (g_args);
  }

  fclose (file);

  BTOR_RELEASE_STACK (mem, buffer);
  BTOR_RELEASE_STACK (mem, g_args);

  btor_delete_mem_mgr (mem);
}

void
finish_testcases_tests (void)
{
}

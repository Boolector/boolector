/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012, 2014 Aina Niemetz
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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
  int i, len;
  char *syscall_string;

  /* Note: skip testcases name */
  for (i = 1, len = 0; i < BTOR_COUNT_STACK (g_args); i++)
    len += strlen (BTOR_PEEK_STACK (g_args, i));
  syscall_string = (char *) malloc (sizeof (char *) * len);
  sprintf (syscall_string, "./boolector ");
  len = strlen ("./boolector ");
  for (i = 1; i < BTOR_COUNT_STACK (g_args); i++)
  {
    sprintf (syscall_string + len, "%s ", BTOR_PEEK_STACK (g_args, i));
    len += strlen (BTOR_PEEK_STACK (g_args, i)) + 1;
  }
  (void) system (syscall_string);
  free (syscall_string);
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
  int ch;

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

    token = strtok (buffer.start, " \t");
    while (token)
    {
      BTOR_PUSH_STACK (mem, g_args, token);
      token = strtok (0, " \t");
    }
    if (g_rwreads) BTOR_PUSH_STACK (mem, g_args, "-bra");

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

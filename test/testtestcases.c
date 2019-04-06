/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include "testtestcases.h"

#include "btorconfig.h"
#include "testrunner.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>

static BtorCharPtrStack g_args;
static BtorMemMgr *g_mm;

static void
test_testcase (void)
{
  run_boolector (BTOR_COUNT_STACK (g_args), g_args.start);
}

void
init_testcases_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

void
run_testcases_tests (int32_t argc, char **argv)
{
  BtorCharStack buffer;
  char *s, *tmp, *token;
  int32_t ch, len;
  FILE *file;

  len = strlen (btor_test_dir) + 20;
  BTOR_NEWN (g_mm, s, len);
  sprintf (s, "%stestcases", btor_test_dir);
  assert ((file = fopen (s, "r")));
  BTOR_DELETEN (g_mm, s, len);

  BTOR_INIT_STACK (g_mm, g_args);
  BTOR_INIT_STACK (g_mm, buffer);

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
      BTOR_PUSH_STACK (buffer, ch);
      ch = fgetc (file);
    } while (ch != '\n' && ch != EOF);
    BTOR_PUSH_STACK (buffer, 0);

    assert (BTOR_EMPTY_STACK (g_args));

    token = strtok (buffer.start, " \t");
    while (token)
    {
      if ((s = strchr (token, '.')))
      {
        len = strlen (btor_log_dir) + strlen (token) + 1;
        BTOR_NEWN (g_mm, tmp, len);
        sprintf (tmp, "%s%s", btor_log_dir, token);
      }
      else
      {
        tmp = btor_mem_strdup (g_mm, token);
      }
      BTOR_PUSH_STACK (g_args, tmp);
      token = strtok (0, " \t");
    }
    if (g_rwreads) BTOR_PUSH_STACK (g_args, "-bra");

    BTOR_RESET_STACK (buffer);

    run_test_case (argc, argv, test_testcase, g_args.start[0], 1);

    while (!BTOR_EMPTY_STACK (g_args))
      btor_mem_freestr (g_mm, BTOR_POP_STACK (g_args));
    BTOR_RESET_STACK (g_args);
  }

  fclose (file);

  BTOR_RELEASE_STACK (buffer);
  BTOR_RELEASE_STACK (g_args);
}

void
finish_testcases_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

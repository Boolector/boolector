/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2016 Aina Niemetz
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include "testsmtaxioms.h"
#include "btorexit.h"
#include "btormain.h"
#include "testrunner.h"
#include "utils/btorstack.h"

#include <assert.h>
#include <stdio.h>

static BtorCharPtrStack g_args;

static char *axioms[] = {
    "bvashr",
    "bvnand",
    "bvnor",
    "bvsge",
    "bvsgt",
    "bvsle",
    "bvslt",
    "bvuge",
    "bvugt",
    "bvule",
    "bvxnor",
    "bvxor",
    "bvsub",
    0, /* below are the 'hard' test cases (no 16, 32, 64 bits) */
    "bvsmod",
    "bvsdiv",
    "bvsrem",
    0};

static void
test_g_args_unsat (void)
{
  assert (boolector_main (BTOR_COUNT_STACK (g_args), g_args.start)
          == BTOR_UNSAT_EXIT);
}

static void
test_smtaxiom (BtorMemMgr *mem, int argc, char **argv, char *p, int i)
{
  char *buffer, *name, *prefix = "smtaxiom";

  BTOR_PUSH_STACK (mem, g_args, p);

  BTOR_PUSH_STACK (mem, g_args, "-o");
  BTOR_PUSH_STACK (mem, g_args, "/dev/null");

  if (g_rwreads) BTOR_PUSH_STACK (mem, g_args, "-bra");

  name =
      (char *) malloc (sizeof (char) * (strlen (prefix) + strlen (p) + 10 + 1));
  sprintf (name, "smtaxiom%s%d", p, i);

  buffer = (char *) malloc (strlen (BTOR_LOG_DIR) + strlen (name) + 4 + 1);
  sprintf (buffer, "%s%s.smt", BTOR_LOG_DIR, name);
  BTOR_PUSH_STACK (mem, g_args, buffer);

  run_test_case (argc, argv, test_g_args_unsat, name, 0);

  BTOR_RESET_STACK (g_args);
  free (name);
  free (buffer);
}

void
init_smtaxioms_tests (void)
{
}

void
run_smtaxioms_tests (int argc, char **argv)
{
  BtorMemMgr *mem;
  int i, first;
  char **p;

  mem = btor_new_mem_mgr ();

  for (first = 1, p = axioms; first || *p; p++)
  {
    if (!*p)
    {
      first = 0;
      p++;
    }

    for (i = 1; i <= 8; i++) test_smtaxiom (mem, argc, argv, *p, i);

    if (first)
    {
      test_smtaxiom (mem, argc, argv, *p, 16);
      test_smtaxiom (mem, argc, argv, *p, 32);
      test_smtaxiom (mem, argc, argv, *p, 64);
    }
  }

  BTOR_RELEASE_STACK (mem, g_args);
  btor_delete_mem_mgr (mem);
}

void
finish_smtaxioms_tests (void)
{
}

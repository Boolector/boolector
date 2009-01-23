#ifdef NDEBUG
#undef NDEBUG
#endif

#include "testsmtaxioms.h"
#include "btorexit.h"
#include "btormain.h"
#include "btorstack.h"
#include "testrunner.h"

#include <assert.h>
#include <stdio.h>

static BtorCharPtrStack args;

static char* axioms[] = {
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
test_args_unsat (void)
{
  assert (boolector_main (BTOR_COUNT_STACK (args), args.start)
          == BTOR_UNSAT_EXIT);
}

static void
test_smtaxiom (BtorMemMgr* mem, int argc, char** argv, char* p, int i)
{
  static char buffer[80];
  static char name[80];

  BTOR_PUSH_STACK (mem, args, p);

  BTOR_PUSH_STACK (mem, args, "-q");

  sprintf (name, "smtaxiom%s%d", p, i);
  sprintf (buffer, "log/%s.smt", name);
  BTOR_PUSH_STACK (mem, args, buffer);

  run_test_case (argc, argv, test_args_unsat, name, 0);

  BTOR_RESET_STACK (args);
}

void
init_smtaxioms_tests (void)
{
}

void
run_smtaxioms_tests (int argc, char** argv)
{
  BtorMemMgr* mem;
  int i, first;
  char** p;

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

  BTOR_RELEASE_STACK (mem, args);
  btor_delete_mem_mgr (mem);
}

void
finish_smtaxioms_tests (void)
{
}

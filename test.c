#include "testaig.h"
#include "testaigvec.h"
#include "testarithmetic.h"
#include "testcomp.h"
#include "testconst.h"
#include "testexp.h"
#include "testlogic.h"
#include "testmem.h"
#include "testmisc.h"
#include "testoverflow.h"
#include "testrunner.h"
#include "testsat.h"
#include "testshift.h"
#include "testspecial.h"
#include "teststack.h"
#include "testutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <stdio.h>
#include <string.h>

#define BTOR_RUN_TESTS(name)         \
  do                                 \
  {                                  \
    init_##name##_tests ();          \
    print_test_suite_name (#name);   \
    run_##name##_tests (argc, argv); \
    finish_##name##_tests ();        \
  } while (0)

int
main (int argc, char **argv)
{
  int i    = 0;
  int fast = 0;
  for (i = 1; i < argc; i++)
  {
    if (strcmp (argv[i], "-h") == 0 || strcmp (argv[i], "--help") == 0)
    {
      printf ("./test [-h|--help]|[-f|--fast]|{pattern}\n");
      return 0;
    }
    if (strcmp (argv[i], "-f") == 0 || strcmp (argv[i], "--fast") == 0)
    {
      fast = 1;
    }
  }
  init_tests (fast);
  BTOR_RUN_TESTS (util);
  BTOR_RUN_TESTS (mem);
  BTOR_RUN_TESTS (stack);
  BTOR_RUN_TESTS (const);
  BTOR_RUN_TESTS (sat);
  BTOR_RUN_TESTS (aig);
  BTOR_RUN_TESTS (aigvec);
  BTOR_RUN_TESTS (exp);
  BTOR_RUN_TESTS (logic);
  BTOR_RUN_TESTS (comp);
  BTOR_RUN_TESTS (arithmetic);
  BTOR_RUN_TESTS (overflow);
  BTOR_RUN_TESTS (shift);
  BTOR_RUN_TESTS (misc);
  BTOR_RUN_TESTS (special);
  finish_tests ();
  return 0;
}

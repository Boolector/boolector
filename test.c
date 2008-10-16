#include "testaig.h"
#include "testaigvec.h"
#include "testarithmetic.h"
#include "testcomp.h"
#include "testconst.h"
#include "testexp.h"
#include "testhash.h"
#include "testinc.h"
#include "testlogic.h"
#include "testmem.h"
#include "testmisc.h"
#include "testoverflow.h"
#include "testqueue.h"
#include "testrunner.h"
#include "testsat.h"
#include "testshift.h"
#include "testsmtaxioms.h"
#include "testspecial.h"
#include "teststack.h"
#include "testtestcases.h"
#include "testutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <stdio.h>
#include <stdlib.h>
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
  BtorTestCaseSpeed speed = BTOR_NORMAL_TEST_CASE;
  int ret_val;
  int i = 0;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
    {
      printf ("./test [-h|--help]|[-s|--slow][-f|--fast]|{pattern}\n");
      return 0;
    }
    else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--fast"))
    {
      speed = BTOR_FAST_TEST_CASE;
    }
    else if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--slow"))
    {
      speed = BTOR_SLOW_TEST_CASE;
    }
    else if (argv[i][0] == '-')
    {
      printf ("*** test: invalid option '%s'\n", argv[i]);
      return 1;
    }
    else
    {
      /* assume test case pattern */
    }
  }

  init_tests (speed);
  BTOR_RUN_TESTS (util);
  BTOR_RUN_TESTS (mem);
  BTOR_RUN_TESTS (stack);
  BTOR_RUN_TESTS (queue);
  BTOR_RUN_TESTS (hash);
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
  BTOR_RUN_TESTS (testcases);
  BTOR_RUN_TESTS (smtaxioms);
  BTOR_RUN_TESTS (inc);
  printf ("Running model generation tests\n");
  ret_val = system ("./testmodelgeneration");
  if (ret_val != 0)
    printf ("%sError in model generation%s\n", "\e[1;31m", "\e[0;39m");
  else
    finish_tests ();
  return 0;
}

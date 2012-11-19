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

#include "testaig.h"
#include "testaigvec.h"
#include "testarithmetic.h"
#include "testcomp.h"
#include "testconst.h"
#include "testexp.h"
#include "testhash.h"
#include "testinc.h"
#include "testlambda.h"
#include "testlogic.h"
#include "testmem.h"
#include "testmisc.h"
#include "testmodelgen.h"
#include "testoverflow.h"
#include "testparseerror.h"
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

#define USAGE                                                                \
  "usage: test [options] [patterns]\n\n"                                     \
  "  options:\n"                                                             \
  "    -h, --help       print this message and exit\n"                       \
  "    -n, --norww      run boolector with rewriting of writes disabled\n"   \
  "    -s, --slow       run 'slow' testcases also\n"                         \
  "    -f, --fast       run 'fast' testcases only\n"                         \
  "                     (default: run 'fast' and 'normal' testcases)\n"      \
  "  patterns:\n"                                                            \
  "    a valid pattern is a substring of an existing test case out of the\n" \
  "    following test case sets:\n"                                          \
  "      aig, aigvec, arithmetic, comp, const, exp, hash, inc, logic,\n"     \
  "      mem, misc, modelgen, overflow, parseerror, queue, sat, shift,\n"    \
  "      smtaxioms, special, stack, util, testcases\n"

int
main (int argc, char **argv)
{
  BtorTestCaseSpeed speed = BTOR_NORMAL_TEST_CASE;
  int i = 0, rewrite_writes = 1;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
    {
      printf ("%s", USAGE);
      return 0;
    }
    else if (!strcmp (argv[i], "-n") || !strcmp (argv[i], "--norww"))
    {
      rewrite_writes = 0;
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
  //  BTOR_RUN_TESTS (lambda);
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
  BTOR_RUN_TESTS (modelgen);
  BTOR_RUN_TESTS (parseerror);
  finish_tests ();
  return 0;
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testaig.h"
#include "testaigvec.h"
#include "testarithmetic.h"
#include "testboolectornodemap.h"
#include "testbv.h"
#include "testcomp.h"
#include "testexp.h"
#include "testhash.h"
#include "testinc.h"
#include "testinthash.h"
#include "testinthashmap.h"
#include "testlambda.h"
#include "testlogic.h"
#include "testmap.h"
#include "testmc.h"
#include "testmem.h"
#include "testmisc.h"
#include "testmodelgen.h"
#include "testmodelgensmt2.h"
#include "testnormquant.h"
#include "testoverflow.h"
#include "testparseerror.h"
#include "testprop.h"
#include "testpropinv.h"
#include "testqueue.h"
#include "testrunner.h"
#include "testsat.h"
#include "testshift.h"
#include "testsmtaxioms.h"
#include "testsort.h"
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
  "    -R, --bra        run boolector with -bra\n"                           \
  "    -b, --broken     run 'broken' testcases also\n"                       \
  "    -s, --slow       run 'slow' testcases also\n"                         \
  "    -f, --fast       run 'fast' testcases only\n"                         \
  "                     (default: run 'fast' and 'normal' testcases)\n"      \
  "  patterns:\n"                                                            \
  "    a valid pattern is a substring of an existing test case out of the\n" \
  "    following test case sets:\n"                                          \
  "      aig, aigvec, arithmetic, bitvec, comp, exp, hash, inc,"             \
  "      int_hash_map, int_hash_table, lambda, logic, map, mc, mem,\n"       \
  "      misc, modelgen, modelgensmt2, overflow, parseerror, prop,\n"        \
  "      propinv, queue, sat, shift, smtaxioms, sort, special, stack,\n"     \
  "      util, testcases\n\n"

int32_t
main (int32_t argc, char **argv)
{
  int32_t i;
  bool skip_broken        = true;
  BtorTestCaseSpeed speed = BTOR_NORMAL_TEST_CASE;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
    {
      printf ("%s", USAGE);
      return 0;
    }
    else if (!strcmp (argv[i], "-R") || !strcmp (argv[i], "--bra"))
    {
      /* enable rewriting of reads on lambdas in resp. testcase sets */
    }
    else if (!strcmp (argv[i], "-b") || !strcmp (argv[i], "--broken"))
    {
      skip_broken = false;
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

  init_tests (speed, skip_broken);
  BTOR_RUN_TESTS (util);
  BTOR_RUN_TESTS (mem);
  BTOR_RUN_TESTS (stack);
  BTOR_RUN_TESTS (queue);
  BTOR_RUN_TESTS (hash);
  BTOR_RUN_TESTS (bitvec);
  BTOR_RUN_TESTS (prop);
  BTOR_RUN_TESTS (propinv);
  BTOR_RUN_TESTS (sat);
  BTOR_RUN_TESTS (aig);
  BTOR_RUN_TESTS (aigvec);
  BTOR_RUN_TESTS (exp);
  BTOR_RUN_TESTS (map);
  BTOR_RUN_TESTS (boolectornodemap);
  BTOR_RUN_TESTS (lambda);
  BTOR_RUN_TESTS (normquant);
  BTOR_RUN_TESTS (logic);
  BTOR_RUN_TESTS (comp);
  BTOR_RUN_TESTS (arithmetic);
  BTOR_RUN_TESTS (overflow);
  BTOR_RUN_TESTS (shift);
  BTOR_RUN_TESTS (misc);
#ifndef BTOR_WINDOWS_BUILD
  BTOR_RUN_TESTS (special);
#endif
  BTOR_RUN_TESTS (testcases);
  BTOR_RUN_TESTS (smtaxioms);
  BTOR_RUN_TESTS (inc);
  BTOR_RUN_TESTS (modelgen);
  BTOR_RUN_TESTS (modelgensmt2);
  BTOR_RUN_TESTS (parseerror);
  BTOR_RUN_TESTS (mc);
  BTOR_RUN_TESTS (sort);
  BTOR_RUN_TESTS (int_hash_table);
  BTOR_RUN_TESTS (int_hash_map);
  return finish_tests ();
}

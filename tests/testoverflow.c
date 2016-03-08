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

#include "testoverflow.h"

#include "btorexit.h"
#include "btormain.h"
#include "testrunner.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_OVERFLOW_TEMP_FILE_NAME "of.tmp"

#define BTOR_TEST_OVERFLOW_LOW 1
#define BTOR_TEST_OVERFLOW_HIGH 4

static int g_argc       = 6;
static char **g_argv    = NULL;
static char *g_btor_str = NULL;

void
init_overflow_tests (void)
{
  FILE *f = fopen (BTOR_TEST_OVERFLOW_TEMP_FILE_NAME, "w");
  int pos_rwr;

  assert (f != NULL);
  fclose (f);

  pos_rwr = 0;

  if (g_rwreads) pos_rwr = g_argc++ - 1;

  g_btor_str = (char *) malloc (sizeof (char *) * (strlen (BTOR_BIN_DIR) + 20));
  sprintf (g_btor_str, "%sboolector", BTOR_BIN_DIR);

  g_argv = (char **) malloc (g_argc * sizeof (char *));

  g_argv[0] = g_btor_str;
  g_argv[1] = "-rwl";
  g_argv[2] = "1";
  g_argv[3] = "-o";
  g_argv[4] = "/dev/null";

  if (g_rwreads) g_argv[pos_rwr] = "-bra";

  g_argv[g_argc - 1] = BTOR_TEST_OVERFLOW_TEMP_FILE_NAME;
}

// #define EXTRACTBENCHMARKS

#ifdef EXTRACTBENCHMARKS
static void
extract (const char *name, int n, int i, int j, int res)
{
  char cmd[200];
  sprintf (cmd,
           "cp of.tmp overflow/%s_%d_%d_%d_%s.btor",
           name,
           n,
           i,
           j,
           res == 10 ? "sat" : "unsat");
  system (cmd);
}
#endif

static void
u_overflow_test (int (*func) (int, int),
                 const char *func_name,
                 int low,
                 int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int result             = 0;
  int overflow_test      = 0;
  int overflow_boolector = 0;
  int num_bits           = 0;
  int max                = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  BtorExitCode exit_code = 0;
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        overflow_test      = 0;
        overflow_boolector = 0;
        result             = func (i, j);
        if (result < 0 || result >= max) overflow_test = 1;
        f = fopen (BTOR_TEST_OVERFLOW_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %d\n", num_bits, i);
        fprintf (f, "2 constd %d %d\n", num_bits, j);
        fprintf (f, "3 %s 1 1 2\n", func_name);
        fprintf (f, "4 root 1 3\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
#ifdef EXTRACTBENCHMARKS
        extract (func_name, num_bits, i, j, exit_code);
#endif
        assert (exit_code == BTOR_SAT_EXIT || exit_code == BTOR_UNSAT_EXIT);
        if (exit_code == BTOR_SAT_EXIT) overflow_boolector = 1;
        if (overflow_boolector) assert (overflow_test);
        if (overflow_test) assert (overflow_boolector);
      }
    }
  }
}

static void
s_overflow_test (int (*func) (int, int),
                 const char *func_name,
                 int exclude_second_zero,
                 int low,
                 int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int overflow_test      = 0;
  int overflow_boolector = 0;
  int const1_id          = 0;
  int const2_id          = 0;
  int result             = 0;
  int num_bits           = 0;
  int max                = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits - 1);
    for (i = -max; i < max; i++)
    {
      for (j = -max; j < max; j++)
      {
        if (!exclude_second_zero || j != 0)
        {
          overflow_test      = 0;
          overflow_boolector = 0;
          result             = func (i, j);
          if (!(result >= -max && result < max)) overflow_test = 1;
          f = fopen (BTOR_TEST_OVERFLOW_TEMP_FILE_NAME, "w");
          assert (f != NULL);
          if (i < 0)
          {
            fprintf (f, "1 constd %d %d\n", num_bits, -i);
            fprintf (f, "2 neg %d 1\n", num_bits);
            const1_id = 2;
          }
          else
          {
            fprintf (f, "1 constd %d %d\n", num_bits, i);
            const1_id = 1;
          }
          if (j < 0)
          {
            fprintf (f, "%d constd %d %d\n", const1_id + 1, num_bits, -j);
            fprintf (
                f, "%d neg %d %d\n", const1_id + 2, num_bits, const1_id + 1);
            const2_id = const1_id + 2;
          }
          else
          {
            fprintf (f, "%d constd %d %d\n", const1_id + 1, num_bits, j);
            const2_id = const1_id + 1;
          }

          fprintf (f,
                   "%d %s 1 %d %d\n",
                   const2_id + 1,
                   func_name,
                   const1_id,
                   const2_id);
          fprintf (f, "%d root 1 %d\n", const2_id + 2, const2_id + 1);
          fclose (f);
          exit_code = boolector_main (g_argc, g_argv);
#ifdef EXTRACTBENCHMARKS
          extract (func_name, num_bits, i, j, exit_code);
#endif
          assert (exit_code == BTOR_SAT_EXIT || exit_code == BTOR_UNSAT_EXIT);
          if (exit_code == BTOR_SAT_EXIT) overflow_boolector = 1;
          if (overflow_boolector) assert (overflow_test);
          if (overflow_test) assert (overflow_boolector);
        }
      }
    }
  }
}

static int
add (int x, int y)
{
  return x + y;
}

static int
sub (int x, int y)
{
  return x - y;
}

static int
mul (int x, int y)
{
  return x * y;
}

static int
divide (int x, int y)
{
  assert (y != 0);
  return x / y;
}

static void
test_uaddo_overflow (void)
{
  u_overflow_test (
      add, "uaddo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
test_usubo_overflow (void)
{
  u_overflow_test (
      sub, "usubo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
test_umulo_overflow (void)
{
  u_overflow_test (
      mul, "umulo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
test_saddo_overflow (void)
{
  s_overflow_test (
      add, "saddo", 0, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
test_ssubo_overflow (void)
{
  s_overflow_test (
      sub, "ssubo", 0, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
test_smulo_overflow (void)
{
  s_overflow_test (
      mul, "smulo", 0, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
test_sdivo_overflow (void)
{
  s_overflow_test (
      divide, "sdivo", 1, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH);
}

static void
run_all_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (uaddo_overflow);
  BTOR_RUN_TEST (usubo_overflow);
  BTOR_RUN_TEST (umulo_overflow);
  BTOR_RUN_TEST (saddo_overflow);
  BTOR_RUN_TEST (ssubo_overflow);
  BTOR_RUN_TEST (smulo_overflow);
  BTOR_RUN_TEST (sdivo_overflow);
}

void
run_overflow_tests (int argc, char **argv)
{
  run_all_tests (argc, argv);
  g_argv[1] = "-rwl";
  g_argv[2] = "0";
  run_all_tests (argc, argv);
}

void
finish_overflow_tests (void)
{
  int result = remove (BTOR_TEST_OVERFLOW_TEMP_FILE_NAME);
  assert (result == 0);
  free (g_btor_str);
  free (g_argv);
}

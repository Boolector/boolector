/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testarithmetic.h"

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

#define BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME "arith.tmp"

#define BTOR_TEST_ARITHMETIC_LOW 1
#define BTOR_TEST_ARITHMETIC_HIGH 4

static int32_t g_argc   = 6;
static char **g_argv    = NULL;
static char *g_btor_str = NULL;

void
init_arithmetic_tests (void)
{
  FILE *f = fopen (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, "w");
  int32_t pos_rwr;

  assert (f != NULL);
  fclose (f);

  pos_rwr = 0;

  if (g_rwreads) pos_rwr = g_argc++ - 1;

  g_btor_str = (char *) malloc (sizeof (char *) * (strlen (btor_bin_dir) + 20));
  sprintf (g_btor_str, "%sboolector", btor_bin_dir);

  g_argv = (char **) malloc (g_argc * sizeof (char *));

  g_argv[0] = g_btor_str;
  g_argv[1] = "-rwl";
  g_argv[2] = "1";
  g_argv[3] = "-o";
  g_argv[4] = "/dev/null";

  if (g_rwreads) g_argv[pos_rwr] = "-bra";

  g_argv[g_argc - 1] = BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME;
}

static void
u_arithmetic_test (int32_t (*func) (int32_t, int32_t),
                   const char *func_name,
                   int32_t low,
                   int32_t high)
{
  FILE *f          = NULL;
  int32_t i        = 0;
  int32_t j        = 0;
  int32_t result   = 0;
  int32_t max      = 0;
  int32_t num_bits = 0;
  int32_t const_id = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  BtorExitCode exit_code = 0;
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        result = func (i, j);
        if (result < max)
        {
          f = fopen (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, "w");
          assert (f != NULL);
          fprintf (f, "1 constd %d %d\n", num_bits, i);
          fprintf (f, "2 constd %d %d\n", num_bits, j);
          fprintf (f, "3 %s %d 1 2\n", func_name, num_bits);
          if (result >= 0)
          {
            fprintf (f, "4 constd %d %d\n", num_bits, result);
            const_id = 4;
          }
          else
          {
            fprintf (f, "4 constd %d %d\n", num_bits, -result);
            fprintf (f, "5 neg %d 4\n", num_bits);
            const_id = 5;
          }
          fprintf (f, "%d eq 1 3 %d\n", const_id + 1, const_id);
          fprintf (f, "%d root 1 %d\n", const_id + 2, const_id + 1);
          fclose (f);
          exit_code = boolector_main (g_argc, g_argv);
          assert (exit_code == BTOR_SAT_EXIT);
        }
      }
    }
  }
}

static void
s_arithmetic_test (int32_t (*func) (int32_t, int32_t),
                   const char *func_name,
                   int32_t low,
                   int32_t high)
{
  FILE *f                = NULL;
  int32_t i              = 0;
  int32_t j              = 0;
  int32_t const1_id      = 0;
  int32_t const2_id      = 0;
  int32_t const3_id      = 0;
  int32_t result         = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits - 1);
    for (i = -max; i < max; i++)
    {
      for (j = -max; j < max; j++)
      {
        result = func (i, j);
        if (result >= -max && result < max)
        {
          f = fopen (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, "w");
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
                   "%d %s %d %d %d\n",
                   const2_id + 1,
                   func_name,
                   num_bits,
                   const1_id,
                   const2_id);
          if (result < 0)
          {
            fprintf (f, "%d constd %d %d\n", const2_id + 2, num_bits, -result);
            fprintf (
                f, "%d neg %d %d\n", const2_id + 3, num_bits, const2_id + 2);
            const3_id = const2_id + 3;
          }
          else
          {
            fprintf (f, "%d constd %d %d\n", const2_id + 2, num_bits, result);
            const3_id = const2_id + 2;
          }
          fprintf (
              f, "%d eq 1 %d %d\n", const3_id + 1, const2_id + 1, const3_id);
          fprintf (f, "%d root 1 %d\n", const3_id + 2, const3_id + 1);
          fclose (f);
          exit_code = boolector_main (g_argc, g_argv);
          assert (exit_code == BTOR_SAT_EXIT);
        }
      }
    }
  }
}

static int32_t
add (int32_t x, int32_t y)
{
  return x + y;
}

static int32_t
sub (int32_t x, int32_t y)
{
  return x - y;
}

static int32_t
mul (int32_t x, int32_t y)
{
  return x * y;
}

static int32_t
divide (int32_t x, int32_t y)
{
  if (y == 0)
  {
    if (x < 0) return 1;
    return -1;
  }
  return x / y;
}

static int32_t
rem (int32_t x, int32_t y)
{
  if (y == 0) return x;

  return x % y;
}

static void
test_add_u_arithmetic (void)
{
  u_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_sub_u_arithmetic (void)
{
  u_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_mul_u_arithmetic (void)
{
  u_arithmetic_test (
      mul, "mul", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_udiv_arithmetic (void)
{
  u_arithmetic_test (
      divide, "udiv", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_urem_arithmetic (void)
{
  u_arithmetic_test (
      rem, "urem", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_add_s_arithmetic (void)
{
  s_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_sub_s_arithmetic (void)
{
  s_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_mul_s_arithmetic (void)
{
  s_arithmetic_test (
      mul, "mul", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_sdiv_arithmetic (void)
{
  s_arithmetic_test (
      divide, "sdiv", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
test_srem_arithmetic (void)
{
  s_arithmetic_test (
      rem, "srem", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH);
}

static void
run_all_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (add_u_arithmetic);
  BTOR_RUN_TEST (sub_u_arithmetic);
  BTOR_RUN_TEST (mul_u_arithmetic);
  BTOR_RUN_TEST (udiv_arithmetic);
  BTOR_RUN_TEST (urem_arithmetic);
  BTOR_RUN_TEST (add_s_arithmetic);
  BTOR_RUN_TEST (sub_s_arithmetic);
  BTOR_RUN_TEST (mul_s_arithmetic);
  BTOR_RUN_TEST (sdiv_arithmetic);
  BTOR_RUN_TEST (srem_arithmetic);
}

void
run_arithmetic_tests (int32_t argc, char **argv)
{
  run_all_tests (argc, argv);
  g_argv[1] = "-rwl";
  g_argv[2] = "0";
  run_all_tests (argc, argv);
}

void
finish_arithmetic_tests (void)
{
  int32_t result = remove (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME);
  assert (result == 0);
  free (g_btor_str);
  free (g_argv);
}

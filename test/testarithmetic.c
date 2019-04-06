/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testarithmetic.h"

#include "boolector.h"
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

#define BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME "arithin.tmp"
#define BTOR_TEST_ARITHMETIC_TEMP_OUTFILE_NAME "arithout.tmp"

#define BTOR_TEST_ARITHMETIC_LOW 1
#define BTOR_TEST_ARITHMETIC_HIGH 4

static Btor *g_btor;

void
init_arithmetic_tests (void)
{
}

static void
u_arithmetic_test (int32_t (*func) (int32_t, int32_t),
                   const char *func_name,
                   int32_t low,
                   int32_t high,
                   uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);

  FILE *fin        = NULL;
  FILE *fout       = NULL;
  int32_t i        = 0;
  int32_t j        = 0;
  int32_t result   = 0;
  int32_t max      = 0;
  int32_t num_bits = 0;
  int32_t const_id = 0;
  int32_t parse_res, parse_status;
  char *parse_err;

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
          g_btor = boolector_new ();
          boolector_set_opt (g_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
          if (g_rwreads)
            boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

          fin = fopen (BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME, "w");
          assert (fin != NULL);
          fprintf (fin, "1 constd %d %d\n", num_bits, i);
          fprintf (fin, "2 constd %d %d\n", num_bits, j);
          fprintf (fin, "3 %s %d 1 2\n", func_name, num_bits);
          if (result >= 0)
          {
            fprintf (fin, "4 constd %d %d\n", num_bits, result);
            const_id = 4;
          }
          else
          {
            fprintf (fin, "4 constd %d %d\n", num_bits, -result);
            fprintf (fin, "5 neg %d 4\n", num_bits);
            const_id = 5;
          }
          fprintf (fin, "%d eq 1 3 %d\n", const_id + 1, const_id);
          fprintf (fin, "%d root 1 %d\n", const_id + 2, const_id + 1);
          fclose (fin);
          fin = fopen (BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME, "r");
          assert (fin != NULL);
          fout = fopen (BTOR_TEST_ARITHMETIC_TEMP_OUTFILE_NAME, "w");
          assert (fout != NULL);
          parse_res =
              boolector_parse_btor (g_btor,
                                    fin,
                                    BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME,
                                    fout,
                                    &parse_err,
                                    &parse_status);
          assert (parse_res != BOOLECTOR_PARSE_ERROR);
          assert (boolector_sat (g_btor) == BOOLECTOR_SAT);
          fclose (fin);
          fclose (fout);
          boolector_delete (g_btor);
          assert (remove (BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME) == 0);
          assert (remove (BTOR_TEST_ARITHMETIC_TEMP_OUTFILE_NAME) == 0);
        }
      }
    }
  }
}

static void
s_arithmetic_test (int32_t (*func) (int32_t, int32_t),
                   const char *func_name,
                   int32_t low,
                   int32_t high,
                   uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);

  FILE *fin              = NULL;
  FILE *fout             = NULL;
  int32_t i              = 0;
  int32_t j              = 0;
  int32_t const1_id      = 0;
  int32_t const2_id      = 0;
  int32_t const3_id      = 0;
  int32_t result         = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
  int32_t parse_res, parse_status;
  char *parse_err;

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
          g_btor = boolector_new ();
          boolector_set_opt (g_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
          if (g_rwreads)
            boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

          fin = fopen (BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME, "w");
          assert (fin != NULL);
          if (i < 0)
          {
            fprintf (fin, "1 constd %d %d\n", num_bits, -i);
            fprintf (fin, "2 neg %d 1\n", num_bits);
            const1_id = 2;
          }
          else
          {
            fprintf (fin, "1 constd %d %d\n", num_bits, i);
            const1_id = 1;
          }
          if (j < 0)
          {
            fprintf (fin, "%d constd %d %d\n", const1_id + 1, num_bits, -j);
            fprintf (
                fin, "%d neg %d %d\n", const1_id + 2, num_bits, const1_id + 1);
            const2_id = const1_id + 2;
          }
          else
          {
            fprintf (fin, "%d constd %d %d\n", const1_id + 1, num_bits, j);
            const2_id = const1_id + 1;
          }
          fprintf (fin,
                   "%d %s %d %d %d\n",
                   const2_id + 1,
                   func_name,
                   num_bits,
                   const1_id,
                   const2_id);
          if (result < 0)
          {
            fprintf (
                fin, "%d constd %d %d\n", const2_id + 2, num_bits, -result);
            fprintf (
                fin, "%d neg %d %d\n", const2_id + 3, num_bits, const2_id + 2);
            const3_id = const2_id + 3;
          }
          else
          {
            fprintf (fin, "%d constd %d %d\n", const2_id + 2, num_bits, result);
            const3_id = const2_id + 2;
          }
          fprintf (
              fin, "%d eq 1 %d %d\n", const3_id + 1, const2_id + 1, const3_id);
          fprintf (fin, "%d root 1 %d\n", const3_id + 2, const3_id + 1);
          fclose (fin);
          fin = fopen (BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME, "r");
          assert (fin != NULL);
          fout = fopen (BTOR_TEST_ARITHMETIC_TEMP_OUTFILE_NAME, "w");
          assert (fout != NULL);
          parse_res =
              boolector_parse_btor (g_btor,
                                    fin,
                                    BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME,
                                    fout,
                                    &parse_err,
                                    &parse_status);
          assert (parse_res != BOOLECTOR_PARSE_ERROR);
          assert (boolector_sat (g_btor) == BOOLECTOR_SAT);
          fclose (fin);
          fclose (fout);
          boolector_delete (g_btor);
          assert (remove (BTOR_TEST_ARITHMETIC_TEMP_INFILE_NAME) == 0);
          assert (remove (BTOR_TEST_ARITHMETIC_TEMP_OUTFILE_NAME) == 0);
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
      add, "add", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  u_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_sub_u_arithmetic (void)
{
  u_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  u_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_mul_u_arithmetic (void)
{
  u_arithmetic_test (
      mul, "mul", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  u_arithmetic_test (
      mul, "mul", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_udiv_arithmetic (void)
{
  u_arithmetic_test (
      divide, "udiv", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  u_arithmetic_test (
      divide, "udiv", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_urem_arithmetic (void)
{
  u_arithmetic_test (
      rem, "urem", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  u_arithmetic_test (
      rem, "urem", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_add_s_arithmetic (void)
{
  s_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  s_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_sub_s_arithmetic (void)
{
  s_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  s_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_mul_s_arithmetic (void)
{
  s_arithmetic_test (
      mul, "mul", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  s_arithmetic_test (
      mul, "mul", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_sdiv_arithmetic (void)
{
  s_arithmetic_test (
      divide, "sdiv", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  s_arithmetic_test (
      divide, "sdiv", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
}

static void
test_srem_arithmetic (void)
{
  s_arithmetic_test (
      rem, "srem", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 1);
  s_arithmetic_test (
      rem, "srem", BTOR_TEST_ARITHMETIC_LOW, BTOR_TEST_ARITHMETIC_HIGH, 0);
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
  run_all_tests (argc, argv);
}

void
finish_arithmetic_tests (void)
{
}

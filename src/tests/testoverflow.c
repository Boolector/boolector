/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testoverflow.h"

#include "boolector.h"
#include "testrunner.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME "ofin.tmp"
#define BTOR_TEST_OVERFLOW_TEMP_OUTFILE_NAME "ofout.tmp"

#define BTOR_TEST_OVERFLOW_LOW 1
#define BTOR_TEST_OVERFLOW_HIGH 4

static Btor *g_btor;
static FILE *g_fin = NULL;
static FILE *g_fout = NULL;

void
init_overflow_tests (void)
{
}

// #define EXTRACTBENCHMARKS

#ifdef EXTRACTBENCHMARKS
static void
extract (const char *name, int32_t n, int32_t i, int32_t j, int32_t res)
{
  char cmd[200];
  sprintf (cmd,
           "cp of.tmp overflow/%s_%d_%d_%d_%s.btor",
           name,
           n,
           i,
           j,
           res == BOOLECTOR_SAT ? "sat" : "unsat");
  system (cmd);
}
#endif

static void
u_overflow_test (int32_t (*func) (int32_t, int32_t),
                 const char *func_name,
                 int32_t low,
                 int32_t high,
                 uint32_t rwl)
{
  assert (func);
  assert (func_name);
  assert (low > 0);
  assert (low <= high);

  FILE *g_fin  = NULL;
  FILE *g_fout = NULL;
  int32_t i, j, num_bits, max, result;
  bool overflow_test, overflow_boolector;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t sat_res;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        g_btor = boolector_new ();
        boolector_set_opt (g_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        overflow_test      = false;
        overflow_boolector = false;
        result             = func (i, j);
        if (result < 0 || result >= max) overflow_test = true;
        g_fin = fopen (BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %d\n", num_bits, i);
        fprintf (g_fin, "2 constd %d %d\n", num_bits, j);
        fprintf (g_fin, "3 %s 1 1 2\n", func_name);
        fprintf (g_fin, "4 root 1 3\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_OVERFLOW_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (g_btor,
                                          g_fin,
                                          BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        sat_res = boolector_sat (g_btor);
        assert (sat_res == BOOLECTOR_SAT || sat_res == BOOLECTOR_UNSAT);
#ifdef EXTRACTBENCHMARKS
        extract (func_name, num_bits, i, j, sat_res);
#endif
        if (sat_res == BOOLECTOR_SAT) overflow_boolector = true;
        if (overflow_boolector) assert (overflow_test);
        if (overflow_test) assert (overflow_boolector);
        fclose (g_fin);
        fclose (g_fout);
        boolector_delete (g_btor);
      }
    }
  }
}

static void
s_overflow_test (int32_t (*func) (int32_t, int32_t),
                 const char *func_name,
                 bool exclude_second_zero,
                 int32_t low,
                 int32_t high,
                 uint32_t rwl)
{
  assert (func);
  assert (func_name);
  assert (low > 0);
  assert (low <= high);

  FILE *g_fin  = NULL;
  FILE *g_fout = NULL;
  int32_t i, j;
  bool overflow_test, overflow_boolector;
  int32_t const1_id, const2_id, result, num_bits, max;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t sat_res;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits - 1);
    for (i = -max; i < max; i++)
    {
      for (j = -max; j < max; j++)
      {
        if (!exclude_second_zero || j != 0)
        {
          g_btor = boolector_new ();
          boolector_set_opt (g_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
          if (g_rwreads)
            boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

          overflow_test      = false;
          overflow_boolector = false;
          result             = func (i, j);
          if (!(result >= -max && result < max)) overflow_test = true;
          g_fin = fopen (BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME, "w");
          assert (g_fin != NULL);
          if (i < 0)
          {
            fprintf (g_fin, "1 constd %d %d\n", num_bits, -i);
            fprintf (g_fin, "2 neg %d 1\n", num_bits);
            const1_id = 2;
          }
          else
          {
            fprintf (g_fin, "1 constd %d %d\n", num_bits, i);
            const1_id = 1;
          }
          if (j < 0)
          {
            fprintf (g_fin, "%d constd %d %d\n", const1_id + 1, num_bits, -j);
            fprintf (
                g_fin, "%d neg %d %d\n", const1_id + 2, num_bits, const1_id + 1);
            const2_id = const1_id + 2;
          }
          else
          {
            fprintf (g_fin, "%d constd %d %d\n", const1_id + 1, num_bits, j);
            const2_id = const1_id + 1;
          }

          fprintf (g_fin,
                   "%d %s 1 %d %d\n",
                   const2_id + 1,
                   func_name,
                   const1_id,
                   const2_id);
          fprintf (g_fin, "%d root 1 %d\n", const2_id + 2, const2_id + 1);
          fclose (g_fin);
          g_fin = fopen (BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME, "r");
          assert (g_fin != NULL);
          g_fout = fopen (BTOR_TEST_OVERFLOW_TEMP_OUTFILE_NAME, "w");
          assert (g_fout != NULL);
          parse_res = boolector_parse_btor (g_btor,
                                            g_fin,
                                            BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME,
                                            g_fout,
                                            &parse_err,
                                            &parse_status);
          assert (parse_res != BOOLECTOR_PARSE_ERROR);
          sat_res = boolector_sat (g_btor);
          assert (sat_res == BOOLECTOR_SAT || sat_res == BOOLECTOR_UNSAT);
#ifdef EXTRACTBENCHMARKS
          extract (func_name, num_bits, i, j, sat_res);
#endif
          if (sat_res == BOOLECTOR_SAT) overflow_boolector = true;
          if (overflow_boolector) assert (overflow_test);
          if (overflow_test) assert (overflow_boolector);
          fclose (g_fin);
          fclose (g_fout);
          boolector_delete (g_btor);
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
  assert (y != 0);
  return x / y;
}

static void
test_uaddo_overflow (void)
{
  u_overflow_test (
      add, "uaddo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 1);
  u_overflow_test (
      add, "uaddo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 0);
}

static void
test_usubo_overflow (void)
{
  u_overflow_test (
      sub, "usubo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 1);
  u_overflow_test (
      sub, "usubo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 0);
}

static void
test_umulo_overflow (void)
{
  u_overflow_test (
      mul, "umulo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 1);
  u_overflow_test (
      mul, "umulo", BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 0);
}

static void
test_saddo_overflow (void)
{
  s_overflow_test (
      add, "saddo", false, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test (
      add, "saddo", false, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 0);
}

static void
test_ssubo_overflow (void)
{
  s_overflow_test (
      sub, "ssubo", false, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test (
      sub, "ssubo", false, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 0);
}

static void
test_smulo_overflow (void)
{
  s_overflow_test (
      mul, "smulo", false, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test (
      mul, "smulo", false, BTOR_TEST_OVERFLOW_LOW, BTOR_TEST_OVERFLOW_HIGH, 0);
}

static void
test_sdivo_overflow (void)
{
  s_overflow_test (divide,
                   "sdivo",
                   true,
                   BTOR_TEST_OVERFLOW_LOW,
                   BTOR_TEST_OVERFLOW_HIGH,
                   1);
  s_overflow_test (divide,
                   "sdivo",
                   true,
                   BTOR_TEST_OVERFLOW_LOW,
                   BTOR_TEST_OVERFLOW_HIGH,
                   0);
}

static void
run_all_tests (int32_t argc, char **argv)
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
run_overflow_tests (int32_t argc, char **argv)
{
  run_all_tests (argc, argv);
  run_all_tests (argc, argv);
}

void
finish_overflow_tests (void)
{
  assert (!g_fin || remove (BTOR_TEST_OVERFLOW_TEMP_INFILE_NAME) == 0);
  assert (!g_fout || remove (BTOR_TEST_OVERFLOW_TEMP_OUTFILE_NAME) == 0);
}

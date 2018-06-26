/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testlogic.h"

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

#define BTOR_TEST_LOGIC_TEMP_INFILE_NAME "logicin.tmp"
#define BTOR_TEST_LOGIC_TEMP_OUTFILE_NAME "logicout.tmp"

#define BTOR_TEST_LOGIC_LOW 1
#define BTOR_TEST_LOGIC_HIGH 4

#define BTOR_TEST_RED_LOGIC_LOW 2
#define BTOR_TEST_RED_LOGIC_HIGH 4

static FILE *g_fin  = NULL;
static FILE *g_fout = NULL;

void
init_logic_tests (void)
{
}

static void
not_logic_test (int32_t low, int32_t high, uint32_t rwl)
{
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  uint32_t i       = 0;
  uint32_t result  = 0;
  int32_t num_bits = 0;
  int32_t max      = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      btor = boolector_new ();
      boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
      if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

      result = ~i & (max - 1);
      g_fin  = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "w");
      assert (g_fin != NULL);
      fprintf (g_fin, "1 constd %d %u\n", num_bits, i);
      fprintf (g_fin, "2 constd %d %u\n", num_bits, result);
      fprintf (g_fin, "3 eq 1 -1 2\n");
      fprintf (g_fin, "4 root 1 3\n");
      fclose (g_fin);
      g_fin = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "r");
      assert (g_fin != NULL);
      g_fout = fopen (BTOR_TEST_LOGIC_TEMP_OUTFILE_NAME, "w");
      assert (g_fout != NULL);
      parse_res = boolector_parse_btor (btor,
                                        g_fin,
                                        BTOR_TEST_LOGIC_TEMP_INFILE_NAME,
                                        g_fout,
                                        &parse_err,
                                        &parse_status);
      assert (parse_res != BOOLECTOR_PARSE_ERROR);
      assert (boolector_sat (btor) == BOOLECTOR_SAT);
      fclose (g_fin);
      fclose (g_fout);
      boolector_delete (btor);
    }
  }
}

static void
binary_logic_test (uint32_t (*func) (uint32_t, uint32_t),
                   const char *func_name,
                   int32_t low,
                   int32_t high,
                   uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  uint32_t i       = 0;
  uint32_t j       = 0;
  uint32_t result  = 0;
  int32_t num_bits = 0;
  int32_t max      = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      for (j = 0; j < (uint32_t) max; j++)
      {
        btor = boolector_new ();
        boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = func (i, j);
        g_fin  = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %u\n", num_bits, i);
        fprintf (g_fin, "2 constd %d %u\n", num_bits, j);
        fprintf (g_fin, "3 %s %d 1 2\n", func_name, num_bits);
        fprintf (g_fin, "4 constd %d %u\n", num_bits, result);
        fprintf (g_fin, "5 eq 1 3 4\n");
        fprintf (g_fin, "6 root 1 5\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_LOGIC_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (btor,
                                          g_fin,
                                          BTOR_TEST_LOGIC_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        assert (boolector_sat (btor) == BOOLECTOR_SAT);
        fclose (g_fin);
        fclose (g_fout);
        boolector_delete (btor);
      }
    }
  }
}

static void
xnor_logic_test (int32_t low, int32_t high, uint32_t rwl)
{
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  uint32_t i       = 0;
  uint32_t j       = 0;
  uint32_t result  = 0;
  int32_t num_bits = 0;
  int32_t max      = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      for (j = 0; j < (uint32_t) max; j++)
      {
        btor = boolector_new ();
        boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = ~(i ^ j) & (max - 1);
        g_fin  = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %u\n", num_bits, i);
        fprintf (g_fin, "2 constd %d %u\n", num_bits, j);
        fprintf (g_fin, "3 xnor %d 1 2\n", num_bits);
        fprintf (g_fin, "4 constd %d %u\n", num_bits, result);
        fprintf (g_fin, "5 eq 1 3 4\n");
        fprintf (g_fin, "6 root 1 5\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_LOGIC_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (btor,
                                          g_fin,
                                          BTOR_TEST_LOGIC_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        assert (boolector_sat (btor) == BOOLECTOR_SAT);
        fclose (g_fin);
        fclose (g_fout);
        boolector_delete (btor);
      }
    }
  }
}

static void
red_logic_test (uint32_t (*func) (uint32_t, uint32_t),
                const char *func_name,
                int32_t low,
                int32_t high,
                uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t sat_res;
  int32_t parse_res, parse_status;
  char *parse_err;
  uint32_t i       = 0;
  uint32_t result  = 0;
  int32_t num_bits = 0;
  int32_t max      = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      btor = boolector_new ();
      boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
      if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

      result = func (i, (uint32_t) num_bits);
      g_fin  = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "w");
      assert (g_fin != NULL);
      fprintf (g_fin, "1 constd %d %u\n", num_bits, i);
      fprintf (g_fin, "2 %s 1 1\n", func_name);
      fprintf (g_fin, "3 root 1 2\n");
      fclose (g_fin);
      g_fin = fopen (BTOR_TEST_LOGIC_TEMP_INFILE_NAME, "r");
      assert (g_fin != NULL);
      g_fout = fopen (BTOR_TEST_LOGIC_TEMP_OUTFILE_NAME, "w");
      assert (g_fout != NULL);
      parse_res = boolector_parse_btor (btor,
                                        g_fin,
                                        BTOR_TEST_LOGIC_TEMP_INFILE_NAME,
                                        g_fout,
                                        &parse_err,
                                        &parse_status);
      assert (parse_res != BOOLECTOR_PARSE_ERROR);
      sat_res = boolector_sat (btor);
      assert ((result && sat_res == BOOLECTOR_SAT)
              || (!result && sat_res == BOOLECTOR_UNSAT));
      fclose (g_fin);
      fclose (g_fout);
      boolector_delete (btor);
    }
  }
}

static uint32_t and (uint32_t x, uint32_t y) { return x & y; }

static uint32_t or (uint32_t x, uint32_t y) { return x | y; }

static uint32_t
    xor (uint32_t x, uint32_t y) { return x ^ y; }

    static uint32_t redand (uint32_t x, uint32_t num_bits)
{
  uint32_t result = 1;
  uint32_t i      = 0;
  assert (num_bits > 1);
  assert (num_bits <= 32);
  for (i = 0; result && i < num_bits; i++) result = result && (x & (1 << i));
  return result;
}

static uint32_t
redor (uint32_t x, uint32_t num_bits)
{
  uint32_t result = 0;
  uint32_t i      = 0;
  assert (num_bits > 1);
  assert (num_bits <= 32);
  for (i = 0; !result && i < num_bits; i++) result = result || (x & (1 << i));
  return result;
}

#define BTOR_TEST_RED_LOGIC_XOR(a, b) (((a) || (b)) && !((a) && (b)))

static uint32_t
redxor (uint32_t x, uint32_t num_bits)
{
  uint32_t result = 0;
  uint32_t i      = 0;
  assert (num_bits > 1);
  assert (num_bits <= 32);
  result = BTOR_TEST_RED_LOGIC_XOR (x & 1, x & 2);
  for (i = 2; i < num_bits; i++)
    result = BTOR_TEST_RED_LOGIC_XOR (result, x & (1 << i));
  return result;
}

static void
test_not_logic ()
{
  not_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  not_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

static void
test_and_logic ()
{
  binary_logic_test (and, "and", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  binary_logic_test (and, "and", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

static void
test_or_logic ()
{
  binary_logic_test (or, "or", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  binary_logic_test (or, "or", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

static void
test_xor_logic ()
{
  binary_logic_test (xor, "xor", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  binary_logic_test (xor, "xor", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

static void
test_xnor_logic ()
{
  xnor_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  xnor_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

static void
test_redand_logic ()
{
  red_logic_test (
      redand, "redand", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH, 1);
  red_logic_test (
      redand, "redand", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH, 0);
}

static void
test_redor_logic ()
{
  red_logic_test (
      redor, "redor", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH, 1);
  red_logic_test (
      redor, "redor", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH, 0);
}

static void
test_redxor_logic ()
{
  red_logic_test (
      redxor, "redxor", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH, 1);
  red_logic_test (
      redxor, "redxor", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH, 0);
}

static void
run_all_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (not_logic);
  BTOR_RUN_TEST (and_logic);
  BTOR_RUN_TEST (or_logic);
  BTOR_RUN_TEST (xor_logic);
  BTOR_RUN_TEST (xnor_logic);
  BTOR_RUN_TEST (redand_logic);
  BTOR_RUN_TEST (redor_logic);
  BTOR_RUN_TEST (redxor_logic);
}

void
run_logic_tests (int32_t argc, char **argv)
{
  run_all_tests (argc, argv);
  run_all_tests (argc, argv);
}

void
finish_logic_tests (void)
{
  assert (!g_fin || remove (BTOR_TEST_LOGIC_TEMP_INFILE_NAME) == 0);
  assert (!g_fout || remove (BTOR_TEST_LOGIC_TEMP_OUTFILE_NAME) == 0);
}

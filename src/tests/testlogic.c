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

#include "testlogic.h"

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

#define BTOR_TEST_LOGIC_TEMP_FILE_NAME "logic.tmp"

#define BTOR_TEST_LOGIC_LOW 1
#define BTOR_TEST_LOGIC_HIGH 4

#define BTOR_TEST_RED_LOGIC_LOW 2
#define BTOR_TEST_RED_LOGIC_HIGH 4

static int32_t g_argc   = 6;
static char **g_argv    = NULL;
static char *g_btor_str = NULL;

void
init_logic_tests (void)
{
  FILE *f = fopen (BTOR_TEST_LOGIC_TEMP_FILE_NAME, "w");
  int32_t pos_rwr;

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

  g_argv[g_argc - 1] = BTOR_TEST_LOGIC_TEMP_FILE_NAME;
}

static void
not_logic_test (int32_t low, int32_t high)
{
  FILE *f                = NULL;
  uint32_t i             = 0;
  uint32_t result        = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      result = ~i & (max - 1);
      f      = fopen (BTOR_TEST_LOGIC_TEMP_FILE_NAME, "w");
      assert (f != NULL);
      fprintf (f, "1 constd %d %u\n", num_bits, i);
      fprintf (f, "2 constd %d %u\n", num_bits, result);
      fprintf (f, "3 eq 1 -1 2\n");
      fprintf (f, "4 root 1 3\n");
      fclose (f);
      exit_code = boolector_main (g_argc, g_argv);
      assert (exit_code == BTOR_SAT_EXIT || exit_code == BTOR_UNSAT_EXIT);
      assert (exit_code == BTOR_SAT_EXIT);
    }
  }
}

static void
binary_logic_test (uint32_t (*func) (uint32_t, uint32_t),
                   const char *func_name,
                   int32_t low,
                   int32_t high)
{
  FILE *f                = NULL;
  uint32_t i             = 0;
  uint32_t j             = 0;
  uint32_t result        = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      for (j = 0; j < (uint32_t) max; j++)
      {
        result = func (i, j);
        f      = fopen (BTOR_TEST_LOGIC_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %u\n", num_bits, i);
        fprintf (f, "2 constd %d %u\n", num_bits, j);
        fprintf (f, "3 %s %d 1 2\n", func_name, num_bits);
        fprintf (f, "4 constd %d %u\n", num_bits, result);
        fprintf (f, "5 eq 1 3 4\n");
        fprintf (f, "6 root 1 5\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
        assert (exit_code == BTOR_SAT_EXIT || exit_code == BTOR_UNSAT_EXIT);
        assert (exit_code == BTOR_SAT_EXIT);
      }
    }
  }
}

static void
xnor_logic_test (int32_t low, int32_t high)
{
  FILE *f                = NULL;
  uint32_t i             = 0;
  uint32_t j             = 0;
  uint32_t result        = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      for (j = 0; j < (uint32_t) max; j++)
      {
        result = ~(i ^ j) & (max - 1);
        f      = fopen (BTOR_TEST_LOGIC_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %u\n", num_bits, i);
        fprintf (f, "2 constd %d %u\n", num_bits, j);
        fprintf (f, "3 xnor %d 1 2\n", num_bits);
        fprintf (f, "4 constd %d %u\n", num_bits, result);
        fprintf (f, "5 eq 1 3 4\n");
        fprintf (f, "6 root 1 5\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
        assert (exit_code == BTOR_SAT_EXIT || exit_code == BTOR_UNSAT_EXIT);
        assert (exit_code == BTOR_SAT_EXIT);
      }
    }
  }
}

static void
red_logic_test (uint32_t (*func) (uint32_t, uint32_t),
                const char *func_name,
                int32_t low,
                int32_t high)
{
  FILE *f                = NULL;
  uint32_t i             = 0;
  uint32_t result        = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < (uint32_t) max; i++)
    {
      result = func (i, (uint32_t) num_bits);
      f      = fopen (BTOR_TEST_LOGIC_TEMP_FILE_NAME, "w");
      assert (f != NULL);
      fprintf (f, "1 constd %d %u\n", num_bits, i);
      fprintf (f, "2 %s 1 1\n", func_name);
      fprintf (f, "3 root 1 2\n");
      fclose (f);
      exit_code = boolector_main (g_argc, g_argv);
      assert (exit_code == BTOR_SAT_EXIT || exit_code == BTOR_UNSAT_EXIT);
      if (result)
        assert (exit_code == BTOR_SAT_EXIT);
      else
      {
        assert (exit_code == BTOR_UNSAT_EXIT);
        assert (!result);
      }
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
  not_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH);
}

static void
test_and_logic ()
{
  binary_logic_test (and, "and", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH);
}

static void
test_or_logic ()
{
  binary_logic_test (or, "or", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH);
}

static void
test_xor_logic ()
{
  binary_logic_test (xor, "xor", BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH);
}

static void
test_xnor_logic ()
{
  xnor_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH);
}

static void
test_redand_logic ()
{
  red_logic_test (
      redand, "redand", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH);
}

static void
test_redor_logic ()
{
  red_logic_test (
      redor, "redor", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH);
}

static void
test_redxor_logic ()
{
  red_logic_test (
      redxor, "redxor", BTOR_TEST_RED_LOGIC_LOW, BTOR_TEST_RED_LOGIC_HIGH);
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
  g_argv[1] = "-rwl";
  g_argv[2] = "0";
  run_all_tests (argc, argv);
}

void
finish_logic_tests (void)
{
  int32_t result = remove (BTOR_TEST_LOGIC_TEMP_FILE_NAME);
  assert (result == 0);
  free (g_btor_str);
  free (g_argv);
}

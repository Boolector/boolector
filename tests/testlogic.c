/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testlogic.h"
#include "btorexit.h"
#include "btormain.h"
#include "btorutil.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

#define BTOR_TEST_LOGIC_TEMP_FILE_NAME "logic.tmp"

#define BTOR_TEST_LOGIC_LOW 1
#define BTOR_TEST_LOGIC_HIGH 4

#define BTOR_TEST_RED_LOGIC_LOW 2
#define BTOR_TEST_RED_LOGIC_HIGH 4

static int g_argc    = 5;
static char **g_argv = NULL;

void
init_logic_tests (void)
{
  FILE *f = fopen (BTOR_TEST_LOGIC_TEMP_FILE_NAME, "w");
  int pos_rwr;

  assert (f != NULL);
  fclose (f);

  pos_rwr = 0;

  if (g_rwreads) pos_rwr = g_argc++ - 1;

  g_argv = (char **) malloc (g_argc * sizeof (char *));

  g_argv[0] = "./boolector";
  g_argv[1] = "-rwl1";
  g_argv[2] = "-o";
  g_argv[3] = "/dev/null";

  if (g_rwreads) g_argv[pos_rwr] = "-bra";

  g_argv[g_argc - 1] = BTOR_TEST_LOGIC_TEMP_FILE_NAME;
}

static void
not_logic_test (int low, int high)
{
  FILE *f                = NULL;
  unsigned int i         = 0;
  unsigned int result    = 0;
  int num_bits           = 0;
  int max                = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < (unsigned int) max; i++)
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
binary_logic_test (unsigned int (*func) (unsigned int, unsigned int),
                   const char *func_name,
                   int low,
                   int high)
{
  FILE *f                = NULL;
  unsigned int i         = 0;
  unsigned int j         = 0;
  unsigned int result    = 0;
  int num_bits           = 0;
  int max                = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < (unsigned int) max; i++)
    {
      for (j = 0; j < (unsigned int) max; j++)
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
xnor_logic_test (int low, int high)
{
  FILE *f                = NULL;
  unsigned int i         = 0;
  unsigned int j         = 0;
  unsigned int result    = 0;
  int num_bits           = 0;
  int max                = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < (unsigned int) max; i++)
    {
      for (j = 0; j < (unsigned int) max; j++)
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
red_logic_test (unsigned int (*func) (unsigned int, unsigned int),
                const char *func_name,
                int low,
                int high)
{
  FILE *f                = NULL;
  unsigned int i         = 0;
  unsigned int result    = 0;
  int num_bits           = 0;
  int max                = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < (unsigned int) max; i++)
    {
      result = func (i, (unsigned int) num_bits);
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

static unsigned int and (unsigned int x, unsigned int y) { return x & y; }

static unsigned int or (unsigned int x, unsigned int y) { return x | y; }

static unsigned int
    xor (unsigned int x, unsigned int y) { return x ^ y; }

    static unsigned int redand (unsigned int x, unsigned int num_bits)
{
  unsigned int result = 1;
  unsigned int i      = 0;
  assert (num_bits > 1);
  assert (num_bits <= 32);
  for (i = 0; result && i < num_bits; i++) result = result && (x & (1 << i));
  return result;
}

static unsigned int
redor (unsigned int x, unsigned int num_bits)
{
  unsigned int result = 0;
  unsigned int i      = 0;
  assert (num_bits > 1);
  assert (num_bits <= 32);
  for (i = 0; !result && i < num_bits; i++) result = result || (x & (1 << i));
  return result;
}

#define BTOR_TEST_RED_LOGIC_XOR(a, b) (((a) || (b)) && !((a) && (b)))

static unsigned int
redxor (unsigned int x, unsigned int num_bits)
{
  unsigned int result = 0;
  unsigned int i      = 0;
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
run_all_tests (int argc, char **argv)
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
run_logic_tests (int argc, char **argv)
{
  run_all_tests (argc, argv);
  g_argv[1] = "-rwl0";
  run_all_tests (argc, argv);
}

void
finish_logic_tests (void)
{
  int result = remove (BTOR_TEST_LOGIC_TEMP_FILE_NAME);
  assert (result == 0);
  free (g_argv);
}

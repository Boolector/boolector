/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012 Aina Niemetz
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testshift.h"
#include "btorexit.h"
#include "btormain.h"
#include "btormem.h"
#include "btorutil.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdio.h>

#define BTOR_TEST_SHIFT_TEMP_FILE_NAME "shift.tmp"

#define BTOR_TEST_SHIFT_LOW 2
#define BTOR_TEST_SHIFT_HIGH 8

static int g_argc    = 5;
static char **g_argv = NULL;

static BtorMemMgr *g_mm;

void
init_shift_tests (void)
{
  FILE *f = fopen (BTOR_TEST_SHIFT_TEMP_FILE_NAME, "w");
  int pos_rwr;

  assert (f != NULL);
  fclose (f);
  g_mm = btor_new_mem_mgr ();

  pos_rwr = 0;

  if (g_rwreads) pos_rwr = g_argc++ - 1;

  g_argv = (char **) malloc (g_argc * sizeof (char *));

  g_argv[0] = "./boolector";
  g_argv[1] = "-rwl1";
  g_argv[2] = "-o";
  g_argv[3] = "/dev/null";

  if (g_rwreads) g_argv[pos_rwr] = "-bra";

  g_argv[g_argc - 1] = BTOR_TEST_SHIFT_TEMP_FILE_NAME;
}

static char *
int_to_str (int x, int num_bits)
{
  char *result = NULL;
  int i        = 0;
  assert (x >= 0);
  assert (num_bits > 0);
  result = (char *) btor_malloc (g_mm, sizeof (char) * (num_bits + 1));
  for (i = num_bits - 1; i >= 0; i--)
  {
    result[i] = x % 2 ? '1' : '0';
    x >>= 1;
  }
  result[num_bits] = '\0';
  return result;
}

static void
shift_test (char *(*func) (int, int, int),
            const char *func_name,
            int low,
            int high)
{
  FILE *f      = NULL;
  int i        = 0;
  int j        = 0;
  char *result = 0;
  int num_bits = 0;
  int max      = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  btor_is_power_of_2_util (low);
  btor_is_power_of_2_util (high);
  BtorExitCode exit_code = 0;
  for (num_bits = low; num_bits <= high; num_bits <<= 1)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < num_bits; j++)
      {
        result = func (i, j, num_bits);
        f      = fopen (BTOR_TEST_SHIFT_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %d\n", num_bits, i);
        fprintf (f, "2 constd %d %d\n", btor_log_2_util (num_bits), j);
        fprintf (f, "3 %s %d 1 2\n", func_name, num_bits);
        fprintf (f, "4 const %d %s\n", num_bits, result);
        fprintf (f, "5 eq 1 3 4\n");
        fprintf (f, "6 root 1 5\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
        assert (exit_code == BTOR_SAT_EXIT);
        btor_freestr (g_mm, result);
      }
    }
  }
}

static char *
sll (int x, int y, int num_bits)
{
  int i        = 0;
  char *result = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 1);
  assert (y < num_bits);
  result = int_to_str (x, num_bits);
  for (i = 0; i < num_bits - y; i++) result[i] = result[i + y];
  for (i = num_bits - y; i < num_bits; i++) result[i] = '0';
  return result;
}

static char *
srl (int x, int y, int num_bits)
{
  int i        = 0;
  char *result = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 1);
  assert (y < num_bits);
  result = int_to_str (x, num_bits);
  for (i = num_bits - 1; i >= y; i--) result[i] = result[i - y];
  for (i = 0; i < y; i++) result[i] = '0';
  return result;
}

static char *
sra (int x, int y, int num_bits)
{
  int i        = 0;
  char *result = NULL;
  char sign    = '0';
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 1);
  assert (y < num_bits);
  result = int_to_str (x, num_bits);
  sign   = result[0];
  for (i = num_bits - 1; i >= y; i--) result[i] = result[i - y];
  for (i = 0; i < y; i++) result[i] = sign;
  return result;
}

static char *
rol (int x, int y, int num_bits)
{
  int i        = 0;
  int j        = 0;
  char temp    = '0';
  char *result = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 1);
  assert (y < num_bits);
  result = int_to_str (x, num_bits);
  for (i = 0; i < y; i++)
  {
    temp = result[0];
    for (j = 0; j < num_bits; j++) result[j] = result[j + 1];
    result[num_bits - 1] = temp;
  }
  return result;
}

static char *
ror (int x, int y, int num_bits)
{
  int i        = 0;
  int j        = 0;
  char temp    = '0';
  char *result = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 1);
  assert (y < num_bits);
  result = int_to_str (x, num_bits);
  for (i = 0; i < y; i++)
  {
    temp = result[num_bits - 1];
    for (j = num_bits - 1; j > 0; j--) result[j] = result[j - 1];
    result[0] = temp;
  }
  return result;
}

static void
test_sll_shift (void)
{
  shift_test (sll, "sll", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH);
}

static void
test_srl_shift (void)
{
  shift_test (srl, "srl", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH);
}

static void
test_sra_shift (void)
{
  shift_test (sra, "sra", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH);
}

static void
test_rol_shift (void)
{
  shift_test (rol, "rol", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH);
}

static void
test_ror_shift (void)
{
  shift_test (ror, "ror", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH);
}

static void
run_all_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (sll_shift);
  BTOR_RUN_TEST (srl_shift);
  BTOR_RUN_TEST (sra_shift);
  BTOR_RUN_TEST (rol_shift);
  BTOR_RUN_TEST (ror_shift);
}

void
run_shift_tests (int argc, char **argv)
{
  run_all_tests (argc, argv);
  g_argv[1] = "-rwl0";
  run_all_tests (argc, argv);
}

void
finish_shift_tests (void)
{
  int result = remove (BTOR_TEST_SHIFT_TEMP_FILE_NAME);
  assert (result == 0);
  btor_delete_mem_mgr (g_mm);
  free (g_argv);
}

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

#include "testmisc.h"
#include "btorexit.h"
#include "btormain.h"
#include "testrunner.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_MISC_TEMP_FILE_NAME "misc.tmp"

#define BTOR_TEST_MISC_LOW 1
#define BTOR_TEST_MISC_HIGH 4

static int g_argc       = 6;
static char **g_argv    = NULL;
static char *g_btor_str = NULL;

static BtorMemMgr *g_mm;

void
init_misc_tests (void)
{
  FILE *f = fopen (BTOR_TEST_MISC_TEMP_FILE_NAME, "w");
  int pos_rwr;

  assert (f != NULL);
  fclose (f);
  g_mm = btor_new_mem_mgr ();

  pos_rwr = 0;

  if (g_rwreads) pos_rwr = g_argc++ - 1;

  g_btor_str =
      (char *) malloc (sizeof (char *) * (strlen (BTOR_BUILD_DIR) + 20));
  sprintf (g_btor_str, "%sboolector", BTOR_BUILD_DIR);

  g_argv = (char **) malloc (g_argc * sizeof (char *));

  g_argv[0] = g_btor_str;
  g_argv[1] = "-rwl";
  g_argv[2] = "1";
  g_argv[3] = "-o";
  g_argv[4] = "/dev/null";

  if (g_rwreads) g_argv[pos_rwr] = "-bra";

  g_argv[g_argc - 1] = BTOR_TEST_MISC_TEMP_FILE_NAME;
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

static char *
slice (int x, int high, int low, int num_bits)
{
  char *temp   = NULL;
  char *result = NULL;
  int i        = 0;
  int counter  = 0;
  assert (high < num_bits);
  assert (low >= 0);
  assert (low <= high);
  temp = int_to_str (x, num_bits);
  assert (temp != NULL);
  result  = int_to_str (0, high - low + 1);
  counter = high - low;
  for (i = low; i <= high; i++) result[counter--] = temp[num_bits - 1 - i];
  btor_freestr (g_mm, temp);
  return result;
}

static void
slice_test_misc (int low, int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  char *result           = 0;
  int num_bits           = 0;
  const int x            = 11;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    for (i = num_bits - 1; i >= 0; i--)
    {
      for (j = i; j >= 0; j--)
      {
        result = slice (x, i, j, num_bits);
        f      = fopen (BTOR_TEST_MISC_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %d\n", high, x);
        fprintf (f, "2 slice %d 1 %d %d\n", i - j + 1, i, j);
        fprintf (f, "3 const %d %s\n", i - j + 1, result);
        fprintf (f, "4 eq 1 2 3\n");
        fprintf (f, "5 root 1 4\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
        assert (exit_code == BTOR_SAT_EXIT);
        btor_freestr (g_mm, result);
      }
    }
  }
}

static char *
uext (int x, int y, int num_bits)
{
  char *result = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits >= 1);
  result = int_to_str (x, num_bits + y);
  return result;
}

static char *
sext (int x, int y, int num_bits)
{
  char *result = NULL;
  int i        = 0;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits >= 1);
  result = int_to_str (x, num_bits + y);
  if (result[y] == '1')
  {
    for (i = 0; i < y; i++) result[i] = '1';
  }
  return result;
}

static void
ext_test_misc (char *(*func) (int, int, int),
               const char *func_name,
               int low,
               int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int max                = 0;
  char *result           = 0;
  int num_bits           = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  assert (func == uext || func == sext);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < num_bits; j++)
      {
        result = func (i, j, num_bits);
        f      = fopen (BTOR_TEST_MISC_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %d\n", num_bits, i);
        fprintf (f, "2 %s %d 1 %d\n", func_name, num_bits + j, j);
        fprintf (f, "3 const %d %s\n", num_bits + j, result);
        fprintf (f, "4 eq 1 2 3\n");
        fprintf (f, "5 root 1 4\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
        assert (exit_code == BTOR_SAT_EXIT);
        btor_freestr (g_mm, result);
      }
    }
  }
}

static char *
concat (int x, int y, int num_bits)
{
  char *x_string = NULL;
  char *y_string = NULL;
  char *result   = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 0);
  assert (num_bits <= INT_MAX / 2);
  x_string = int_to_str (x, num_bits);
  y_string = int_to_str (y, num_bits);
  result   = (char *) btor_malloc (g_mm, sizeof (char) * ((num_bits << 1) + 1));
  strcpy (result, x_string);
  strcat (result, y_string);
  btor_freestr (g_mm, x_string);
  btor_freestr (g_mm, y_string);
  return result;
}

static void
concat_test_misc (int low, int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int max                = 0;
  char *result           = 0;
  int num_bits           = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        result = concat (i, j, num_bits);
        f      = fopen (BTOR_TEST_MISC_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 constd %d %d\n", num_bits, i);
        fprintf (f, "2 constd %d %d\n", num_bits, j);
        fprintf (f, "3 concat %d 1 2\n", num_bits << 1);
        fprintf (f, "4 const %d %s\n", num_bits << 1, result);
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

static void
cond_test_misc (int low, int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int k                  = 0;
  int max                = 0;
  int result             = 0;
  int num_bits           = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        for (k = 0; k <= 1; k++)
        {
          result = k ? i : j;
          f      = fopen (BTOR_TEST_MISC_TEMP_FILE_NAME, "w");
          assert (f != NULL);
          fprintf (f, "1 constd %d %d\n", num_bits, i);
          fprintf (f, "2 constd %d %d\n", num_bits, j);
          fprintf (f, "3 const 1 %d\n", k);
          fprintf (f, "4 cond %d 3 1 2\n", num_bits);
          fprintf (f, "5 constd %d %d\n", num_bits, result);
          fprintf (f, "6 eq 1 4 5\n");
          fprintf (f, "7 root 1 6\n");
          fclose (f);
          exit_code = boolector_main (g_argc, g_argv);
          assert (exit_code == BTOR_SAT_EXIT);
        }
      }
    }
  }
}

static void
read_test_misc (int low, int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int max                = 0;
  int num_bits           = 0;
  BtorExitCode exit_code = 0;
  assert (low > 0);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        f = fopen (BTOR_TEST_MISC_TEMP_FILE_NAME, "w");
        assert (f != NULL);
        fprintf (f, "1 array %d 1\n", num_bits);
        fprintf (f, "2 const 1 0\n");
        fprintf (f, "3 const 1 1\n");
        fprintf (f, "4 constd %d %d\n", num_bits, i);
        fprintf (f, "5 constd %d %d\n", num_bits, j);
        fprintf (f, "6 read %d 1 2\n", num_bits);
        fprintf (f, "7 read %d 1 3\n", num_bits);
        fprintf (f, "8 eq 1 4 6\n");
        fprintf (f, "9 eq 1 5 7\n");
        fprintf (f, "10 and 1 8 9\n");
        fprintf (f, "11 root 1 10\n");
        fclose (f);
        exit_code = boolector_main (g_argc, g_argv);
        assert (exit_code == BTOR_SAT_EXIT);
      }
    }
  }
}

static void
test_slice_misc (void)
{
  slice_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH);
}

static void
test_uext_misc (void)
{
  ext_test_misc (uext, "uext", BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH);
}

static void
test_sext_misc (void)
{
  ext_test_misc (sext, "sext", BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH);
}

static void
test_concat_misc (void)
{
  concat_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH);
}

static void
test_cond_misc (void)
{
  cond_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH);
}

static void
test_read_misc (void)
{
  read_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH);
}

static void
run_all_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (slice_misc);
  BTOR_RUN_TEST (uext_misc);
  BTOR_RUN_TEST (sext_misc);
  BTOR_RUN_TEST (concat_misc);
  BTOR_RUN_TEST (cond_misc);
  BTOR_RUN_TEST (read_misc);
}

void
run_misc_tests (int argc, char **argv)
{
  run_all_tests (argc, argv);
  g_argv[1] = "-rwl";
  g_argv[2] = "0";
  run_all_tests (argc, argv);
}

void
finish_misc_tests (void)
{
  int result = remove (BTOR_TEST_MISC_TEMP_FILE_NAME);
  assert (result == 0);
  btor_delete_mem_mgr (g_mm);
  free (g_btor_str);
  free (g_argv);
}

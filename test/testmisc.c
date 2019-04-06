/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmisc.h"

#include "boolector.h"
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

#define BTOR_TEST_MISC_TEMP_INFILE_NAME "miscin.tmp"
#define BTOR_TEST_MISC_TEMP_OUTFILE_NAME "miscout.tmp"

#define BTOR_TEST_MISC_LOW 1
#define BTOR_TEST_MISC_HIGH 4

static FILE *g_fin  = NULL;
static FILE *g_fout = NULL;

static BtorMemMgr *g_mm;

void
init_misc_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

static char *
int_to_str (int32_t x, int32_t num_bits)
{
  char *result = NULL;
  int32_t i    = 0;
  assert (x >= 0);
  assert (num_bits > 0);
  result = (char *) btor_mem_malloc (g_mm, sizeof (char) * (num_bits + 1));
  for (i = num_bits - 1; i >= 0; i--)
  {
    result[i] = x % 2 ? '1' : '0';
    x >>= 1;
  }
  result[num_bits] = '\0';
  return result;
}

static char *
slice (int32_t x, int32_t high, int32_t low, int32_t num_bits)
{
  char *temp      = NULL;
  char *result    = NULL;
  int32_t i       = 0;
  int32_t counter = 0;
  assert (high < num_bits);
  assert (low >= 0);
  assert (low <= high);
  temp = int_to_str (x, num_bits);
  assert (temp != NULL);
  result  = int_to_str (0, high - low + 1);
  counter = high - low;
  for (i = low; i <= high; i++) result[counter--] = temp[num_bits - 1 - i];
  btor_mem_freestr (g_mm, temp);
  return result;
}

static void
slice_test_misc (int32_t low, int32_t high, uint32_t rwl)
{
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t i        = 0;
  int32_t j        = 0;
  char *result     = 0;
  int32_t num_bits = 0;
  const int32_t x  = 11;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    for (i = num_bits - 1; i >= 0; i--)
    {
      for (j = i; j >= 0; j--)
      {
        btor = boolector_new ();
        boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = slice (x, i, j, num_bits);
        g_fin  = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %d\n", high, x);
        fprintf (g_fin, "2 slice %d 1 %d %d\n", i - j + 1, i, j);
        fprintf (g_fin, "3 const %d %s\n", i - j + 1, result);
        fprintf (g_fin, "4 eq 1 2 3\n");
        fprintf (g_fin, "5 root 1 4\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_MISC_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (btor,
                                          g_fin,
                                          BTOR_TEST_MISC_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        assert (boolector_sat (btor) == BOOLECTOR_SAT);
        fclose (g_fin);
        fclose (g_fout);
        btor_mem_freestr (g_mm, result);
        boolector_delete (btor);
      }
    }
  }
}

static char *
uext (int32_t x, int32_t y, int32_t num_bits)
{
  char *result = NULL;
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits >= 1);
  result = int_to_str (x, num_bits + y);
  return result;
}

static char *
sext (int32_t x, int32_t y, int32_t num_bits)
{
  char *result = NULL;
  int32_t i    = 0;
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
ext_test_misc (char *(*func) (int32_t, int32_t, int32_t),
               const char *func_name,
               int32_t low,
               int32_t high,
               uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  assert (func == uext || func == sext);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t i        = 0;
  int32_t j        = 0;
  int32_t max      = 0;
  char *result     = 0;
  int32_t num_bits = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < num_bits; j++)
      {
        btor = boolector_new ();
        boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = func (i, j, num_bits);
        g_fin  = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %d\n", num_bits, i);
        fprintf (g_fin, "2 %s %d 1 %d\n", func_name, num_bits + j, j);
        fprintf (g_fin, "3 const %d %s\n", num_bits + j, result);
        fprintf (g_fin, "4 eq 1 2 3\n");
        fprintf (g_fin, "5 root 1 4\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_MISC_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (btor,
                                          g_fin,
                                          BTOR_TEST_MISC_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        assert (boolector_sat (btor) == BOOLECTOR_SAT);
        fclose (g_fin);
        fclose (g_fout);
        btor_mem_freestr (g_mm, result);
        boolector_delete (btor);
      }
    }
  }
}

static char *
concat (int32_t x, int32_t y, int32_t num_bits)
{
  assert (x >= 0);
  assert (y >= 0);
  assert (num_bits > 0);
  assert (num_bits <= INT32_MAX / 2);

  char *x_string = NULL;
  char *y_string = NULL;
  char *result   = NULL;

  x_string = int_to_str (x, num_bits);
  y_string = int_to_str (y, num_bits);
  result =
      (char *) btor_mem_malloc (g_mm, sizeof (char) * ((num_bits << 1) + 1));
  strcpy (result, x_string);
  strcat (result, y_string);
  btor_mem_freestr (g_mm, x_string);
  btor_mem_freestr (g_mm, y_string);
  return result;
}

static void
concat_test_misc (int32_t low, int32_t high, uint32_t rwl)
{
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t i        = 0;
  int32_t j        = 0;
  int32_t max      = 0;
  char *result     = 0;
  int32_t num_bits = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        btor = boolector_new ();
        boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = concat (i, j, num_bits);
        g_fin  = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %d\n", num_bits, i);
        fprintf (g_fin, "2 constd %d %d\n", num_bits, j);
        fprintf (g_fin, "3 concat %d 1 2\n", num_bits << 1);
        fprintf (g_fin, "4 const %d %s\n", num_bits << 1, result);
        fprintf (g_fin, "5 eq 1 3 4\n");
        fprintf (g_fin, "6 root 1 5\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_MISC_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (btor,
                                          g_fin,
                                          BTOR_TEST_MISC_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        assert (boolector_sat (btor) == BOOLECTOR_SAT);
        fclose (g_fin);
        fclose (g_fout);
        btor_mem_freestr (g_mm, result);
        boolector_delete (btor);
      }
    }
  }
}

static void
cond_test_misc (int32_t low, int32_t high, uint32_t rwl)
{
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t i        = 0;
  int32_t j        = 0;
  int32_t k        = 0;
  int32_t max      = 0;
  int32_t result   = 0;
  int32_t num_bits = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        for (k = 0; k <= 1; k++)
        {
          btor = boolector_new ();
          boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
          if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

          result = k ? i : j;
          g_fin  = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "w");
          assert (g_fin != NULL);
          fprintf (g_fin, "1 constd %d %d\n", num_bits, i);
          fprintf (g_fin, "2 constd %d %d\n", num_bits, j);
          fprintf (g_fin, "3 const 1 %d\n", k);
          fprintf (g_fin, "4 cond %d 3 1 2\n", num_bits);
          fprintf (g_fin, "5 constd %d %d\n", num_bits, result);
          fprintf (g_fin, "6 eq 1 4 5\n");
          fprintf (g_fin, "7 root 1 6\n");
          fclose (g_fin);
          g_fin = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "r");
          assert (g_fin != NULL);
          g_fout = fopen (BTOR_TEST_MISC_TEMP_OUTFILE_NAME, "w");
          assert (g_fout != NULL);
          parse_res = boolector_parse_btor (btor,
                                            g_fin,
                                            BTOR_TEST_MISC_TEMP_INFILE_NAME,
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
}

static void
read_test_misc (int32_t low, int32_t high, uint32_t rwl)
{
  assert (low > 0);
  assert (low <= high);

  Btor *btor;
  int32_t parse_res, parse_status;
  char *parse_err;
  int32_t i        = 0;
  int32_t j        = 0;
  int32_t max      = 0;
  int32_t num_bits = 0;

  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        btor = boolector_new ();
        boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        g_fin = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 array %d 1\n", num_bits);
        fprintf (g_fin, "2 const 1 0\n");
        fprintf (g_fin, "3 const 1 1\n");
        fprintf (g_fin, "4 constd %d %d\n", num_bits, i);
        fprintf (g_fin, "5 constd %d %d\n", num_bits, j);
        fprintf (g_fin, "6 read %d 1 2\n", num_bits);
        fprintf (g_fin, "7 read %d 1 3\n", num_bits);
        fprintf (g_fin, "8 eq 1 4 6\n");
        fprintf (g_fin, "9 eq 1 5 7\n");
        fprintf (g_fin, "10 and 1 8 9\n");
        fprintf (g_fin, "11 root 1 10\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_MISC_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_MISC_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (btor,
                                          g_fin,
                                          BTOR_TEST_MISC_TEMP_INFILE_NAME,
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
test_slice_misc (void)
{
  slice_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  slice_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

static void
test_uext_misc (void)
{
  ext_test_misc (uext, "uext", BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  ext_test_misc (uext, "uext", BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

static void
test_sext_misc (void)
{
  ext_test_misc (sext, "sext", BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  ext_test_misc (sext, "sext", BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

static void
test_concat_misc (void)
{
  concat_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  concat_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

static void
test_cond_misc (void)
{
  cond_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  cond_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

static void
test_read_misc (void)
{
  read_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 1);
  read_test_misc (BTOR_TEST_MISC_LOW, BTOR_TEST_MISC_HIGH, 0);
}

static void
run_all_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (slice_misc);
  BTOR_RUN_TEST (uext_misc);
  BTOR_RUN_TEST (sext_misc);
  BTOR_RUN_TEST (concat_misc);
  BTOR_RUN_TEST (cond_misc);
  BTOR_RUN_TEST (read_misc);
}

void
run_misc_tests (int32_t argc, char **argv)
{
  run_all_tests (argc, argv);
  run_all_tests (argc, argv);
}

void
finish_misc_tests (void)
{
  assert (!g_fin || remove (BTOR_TEST_MISC_TEMP_INFILE_NAME) == 0);
  assert (!g_fout || remove (BTOR_TEST_MISC_TEMP_OUTFILE_NAME) == 0);
  btor_mem_mgr_delete (g_mm);
}

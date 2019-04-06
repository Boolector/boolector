/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testcomp.h"

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

#define BTOR_TEST_COMP_TEMP_INFILE_NAME "compin.tmp"
#define BTOR_TEST_COMP_TEMP_OUTFILE_NAME "compout.tmp"

#define BTOR_TEST_COMP_LOW 1
#define BTOR_TEST_COMP_HIGH 4

static Btor *g_btor;
static FILE *g_fin = NULL;
static FILE *g_fout = NULL;

void
init_comp_tests (void)
{
}

static void
u_comp_test (int32_t (*func) (int32_t, int32_t),
             const char *func_name,
             int32_t low,
             int32_t high,
             uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);

  int32_t i        = 0;
  int32_t j        = 0;
  int32_t result   = 0;
  int32_t num_bits = 0;
  int32_t max      = 0;
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

        result = func (i, j);
        g_fin    = fopen (BTOR_TEST_COMP_TEMP_INFILE_NAME, "w");
        assert (g_fin != NULL);
        fprintf (g_fin, "1 constd %d %d\n", num_bits, i);
        fprintf (g_fin, "2 constd %d %d\n", num_bits, j);
        fprintf (g_fin, "3 %s 1 1 2\n", func_name);
        fprintf (g_fin, "4 root 1 3\n");
        fclose (g_fin);
        g_fin = fopen (BTOR_TEST_COMP_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_COMP_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (g_btor,
                                          g_fin,
                                          BTOR_TEST_COMP_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        sat_res = boolector_sat (g_btor);
        assert ((result && sat_res == BOOLECTOR_SAT)
                || (!result && sat_res == BOOLECTOR_UNSAT));
        fclose (g_fin);
        fclose (g_fout);
        boolector_delete (g_btor);
      }
    }
  }
}

static void
s_comp_test (int32_t (*func) (int32_t, int32_t),
             const char *func_name,
             int32_t low,
             int32_t high,
             uint32_t rwl)
{
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);

  FILE *g_fin              = NULL;
  FILE *g_fout             = NULL;
  int32_t i              = 0;
  int32_t j              = 0;
  int32_t const1_id      = 0;
  int32_t const2_id      = 0;
  int32_t result         = 0;
  int32_t num_bits       = 0;
  int32_t max            = 0;
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
        g_btor = boolector_new ();
        boolector_set_opt (g_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = func (i, j);
        g_fin    = fopen (BTOR_TEST_COMP_TEMP_INFILE_NAME, "w");
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
        g_fin = fopen (BTOR_TEST_COMP_TEMP_INFILE_NAME, "r");
        assert (g_fin != NULL);
        g_fout = fopen (BTOR_TEST_COMP_TEMP_OUTFILE_NAME, "w");
        assert (g_fout != NULL);
        parse_res = boolector_parse_btor (g_btor,
                                          g_fin,
                                          BTOR_TEST_COMP_TEMP_INFILE_NAME,
                                          g_fout,
                                          &parse_err,
                                          &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        sat_res = boolector_sat (g_btor);
        assert (sat_res == BOOLECTOR_SAT || sat_res == BOOLECTOR_UNSAT);
        if (sat_res == BOOLECTOR_SAT)
          assert (result);
        else
        {
          assert (sat_res == BOOLECTOR_UNSAT);
          assert (!result);
        }
        fclose (g_fin);
        fclose (g_fout);
        boolector_delete (g_btor);
      }
    }
  }
}

static int32_t
eq (int32_t x, int32_t y)
{
  return x == y;
}

static int32_t
ne (int32_t x, int32_t y)
{
  return x != y;
}

static int32_t
lt (int32_t x, int32_t y)
{
  return x < y;
}

static int32_t
lte (int32_t x, int32_t y)
{
  return x <= y;
}

static int32_t
gt (int32_t x, int32_t y)
{
  return x > y;
}

static int32_t
gte (int32_t x, int32_t y)
{
  return x >= y;
}

static void
test_eq_1_comp (void)
{
  u_comp_test (eq, "eq", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (eq, "eq", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_ne_1_comp (void)
{
  u_comp_test (ne, "ne", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (ne, "ne", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_ult_comp (void)
{
  u_comp_test (lt, "ult", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (lt, "ult", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_ulte_comp (void)
{
  u_comp_test (lte, "ulte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (lte, "ulte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_ugt_comp (void)
{
  u_comp_test (gt, "ugt", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (gt, "ugt", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_ugte_comp (void)
{
  u_comp_test (gte, "ugte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (gte, "ugte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_eq_2_comp (void)
{
  s_comp_test (eq, "eq", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (eq, "eq", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_ne_2_comp (void)
{
  s_comp_test (ne, "ne", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (ne, "ne", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_slt_comp (void)
{
  s_comp_test (lt, "slt", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (lt, "slt", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_slte_comp (void)
{
  s_comp_test (lte, "slte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (lte, "slte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_sgt_comp (void)
{
  s_comp_test (gt, "sgt", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (gt, "sgt", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
test_sgte_comp (void)
{
  s_comp_test (gte, "sgte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (gte, "sgte", BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

static void
run_all_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (eq_1_comp);
  BTOR_RUN_TEST (ne_1_comp);
  BTOR_RUN_TEST (ult_comp);
  BTOR_RUN_TEST (ulte_comp);
  BTOR_RUN_TEST (ugt_comp);
  BTOR_RUN_TEST (ugte_comp);
  BTOR_RUN_TEST (eq_2_comp);
  BTOR_RUN_TEST (ne_2_comp);
  BTOR_RUN_TEST (slt_comp);
  BTOR_RUN_TEST (slte_comp);
  BTOR_RUN_TEST (sgt_comp);
  BTOR_RUN_TEST (sgte_comp);
}

void
run_comp_tests (int32_t argc, char **argv)
{
  run_all_tests (argc, argv);
  run_all_tests (argc, argv);
}

void
finish_comp_tests (void)
{
  assert (!g_fin || remove (BTOR_TEST_COMP_TEMP_INFILE_NAME) == 0);
  assert (!g_fout || remove (BTOR_TEST_COMP_TEMP_OUTFILE_NAME) == 0);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testshift.h"

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

#define BTOR_TEST_SHIFT_LOW 2
#define BTOR_TEST_SHIFT_HIGH 8

static Btor *g_btor;
static BtorMemMgr *g_mm;

void
init_shift_tests (void)
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

static void
shift_test (char *(*func) (int32_t, int32_t, int32_t),
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
  char *result     = 0;
  int32_t num_bits = 0;
  int32_t max      = 0;
  int32_t parse_res, parse_status;
  char *parse_err;
  FILE *fin, *fout;

  btor_util_is_power_of_2 (low);
  btor_util_is_power_of_2 (high);
  for (num_bits = low; num_bits <= high; num_bits <<= 1)
  {
    max = btor_util_pow_2 (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < num_bits; j++)
      {
        char infilename[]  = "btortmp-XXXXXX";
        char outfilename[] = "btortmp-XXXXXX";

        g_btor = boolector_new ();
        boolector_set_opt (g_btor, BTOR_OPT_REWRITE_LEVEL, rwl);
        if (g_rwreads) boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

        result = func (i, j, num_bits);
        fin    = mk_temp_file (infilename, "r+");
        assert (fin != NULL);
        fprintf (fin, "1 constd %d %d\n", num_bits, i);
        fprintf (fin, "2 constd %d %d\n", btor_util_log_2 (num_bits), j);
        fprintf (fin, "3 %s %d 1 2\n", func_name, num_bits);
        fprintf (fin, "4 const %d %s\n", num_bits, result);
        fprintf (fin, "5 eq 1 3 4\n");
        fprintf (fin, "6 root 1 5\n");

        rewind (fin);
        fout      = mk_temp_file (outfilename, "w");
        parse_res = boolector_parse_btor (
            g_btor, fin, infilename, fout, &parse_err, &parse_status);
        assert (parse_res != BOOLECTOR_PARSE_ERROR);
        assert (boolector_sat (g_btor) == BOOLECTOR_SAT);
        btor_mem_freestr (g_mm, result);
        fclose (fin);
        fclose (fout);
        boolector_delete (g_btor);
      }
    }
  }
}

static char *
sll (int32_t x, int32_t y, int32_t num_bits)
{
  int32_t i    = 0;
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
srl (int32_t x, int32_t y, int32_t num_bits)
{
  int32_t i    = 0;
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
sra (int32_t x, int32_t y, int32_t num_bits)
{
  int32_t i    = 0;
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
rol (int32_t x, int32_t y, int32_t num_bits)
{
  int32_t i    = 0;
  int32_t j    = 0;
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
ror (int32_t x, int32_t y, int32_t num_bits)
{
  int32_t i    = 0;
  int32_t j    = 0;
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
  shift_test (sll, "sll", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (sll, "sll", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

static void
test_srl_shift (void)
{
  shift_test (srl, "srl", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (srl, "srl", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

static void
test_sra_shift (void)
{
  shift_test (sra, "sra", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (sra, "sra", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

static void
test_rol_shift (void)
{
  shift_test (rol, "rol", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (rol, "rol", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

static void
test_ror_shift (void)
{
  shift_test (ror, "ror", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (ror, "ror", BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

static void
run_all_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (sll_shift);
  BTOR_RUN_TEST (srl_shift);
  BTOR_RUN_TEST (sra_shift);
  BTOR_RUN_TEST (rol_shift);
  BTOR_RUN_TEST (ror_shift);
}

void
run_shift_tests (int32_t argc, char **argv)
{
  run_all_tests (argc, argv);
}

void
finish_shift_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}

#include "testarithmetic.h"
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

#define BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME "arith.tmp"

#define BTOR_TEST_ARITHMETIC_U_LOW 1
#define BTOR_TEST_ARITHMETIC_U_HIGH 4

#define BTOR_TEST_ARITHMETIC_S_LOW 2
#define BTOR_TEST_ARITHMETIC_S_HIGH 4

static int g_argc     = 3;
static char *g_argv[] = {
    "./boolector", "-q", BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, ""};

void
init_arithmetic_tests (void)
{
  FILE *f = fopen (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, "w");
  assert (f != NULL);
  fclose (f);
}

static void
u_arithmetic_test (int (*func) (int, int),
                   const char *func_name,
                   int low,
                   int high)
{
  FILE *f      = NULL;
  int i        = 0;
  int j        = 0;
  int result   = 0;
  int max      = 0;
  int num_bits = 0;
  int const_id = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 0);
  assert (low <= high);
  BtorExitCode exit_code = 0;
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits);
    for (i = 0; i < max; i++)
    {
      for (j = 0; j < max; j++)
      {
        result = func (i, j);
        if (result < max)
        {
          f = fopen (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, "w");
          assert (f != NULL);
          fprintf (f, "1 %d constd %d\n", num_bits, i);
          fprintf (f, "2 %d constd %d\n", num_bits, j);
          fprintf (f, "3 %d %s 1 2\n", num_bits, func_name);
          if (result >= 0)
          {
            fprintf (f, "4 %d constd %d\n", num_bits, result);
            const_id = 4;
          }
          else
          {
            fprintf (f, "4 %d constd %d\n", num_bits, -result);
            fprintf (f, "5 %d neg 4\n", num_bits);
            const_id = 5;
          }
          fprintf (f, "%d 1 eq 3 %d\n", const_id + 1, const_id);
          fprintf (f, "%d 1 root %d\n", const_id + 2, const_id + 1);
          fclose (f);
          exit_code = btor_main (g_argc, g_argv);
          assert (exit_code == BTOR_SAT_EXIT);
        }
      }
    }
  }
}

static void
s_arithmetic_test (int (*func) (int, int),
                   const char *func_name,
                   int low,
                   int high)
{
  FILE *f                = NULL;
  int i                  = 0;
  int j                  = 0;
  int const1_id          = 0;
  int const2_id          = 0;
  int const3_id          = 0;
  int result             = 0;
  int num_bits           = 0;
  int max                = 0;
  BtorExitCode exit_code = 0;
  assert (func != NULL);
  assert (func_name != NULL);
  assert (low > 1);
  assert (low <= high);
  for (num_bits = low; num_bits <= high; num_bits++)
  {
    max = btor_pow_2_util (num_bits - 1);
    for (i = -max; i < max; i++)
    {
      for (j = -max; j < max; j++)
      {
        result = func (i, j);
        if (result >= -max && result < max)
        {
          f = fopen (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME, "w");
          assert (f != NULL);
          if (i < 0)
          {
            fprintf (f, "1 %d constd %d\n", num_bits, -i);
            fprintf (f, "2 %d neg 1\n", num_bits);
            const1_id = 2;
          }
          else
          {
            fprintf (f, "1 %d constd %d\n", num_bits, i);
            const1_id = 1;
          }
          if (j < 0)
          {
            fprintf (f, "%d %d constd %d\n", const1_id + 1, num_bits, -j);
            fprintf (
                f, "%d %d neg %d\n", const1_id + 2, num_bits, const1_id + 1);
            const2_id = const1_id + 2;
          }
          else
          {
            fprintf (f, "%d %d constd %d\n", const1_id + 1, num_bits, j);
            const2_id = const1_id + 1;
          }
          fprintf (f,
                   "%d %d %s %d %d\n",
                   const2_id + 1,
                   num_bits,
                   func_name,
                   const1_id,
                   const2_id);
          if (result < 0)
          {
            fprintf (f, "%d %d constd %d\n", const2_id + 2, num_bits, -result);
            fprintf (
                f, "%d %d neg %d\n", const2_id + 3, num_bits, const2_id + 2);
            const3_id = const2_id + 3;
          }
          else
          {
            fprintf (f, "%d %d constd %d\n", const2_id + 2, num_bits, result);
            const3_id = const2_id + 2;
          }
          fprintf (
              f, "%d 1 eq %d %d\n", const3_id + 1, const2_id + 1, const3_id);
          fprintf (f, "%d 1 root %d\n", const3_id + 2, const3_id + 1);
          fclose (f);
          exit_code = btor_main (g_argc, g_argv);
          assert (exit_code == BTOR_SAT_EXIT);
        }
      }
    }
  }
}

static int
add (int x, int y)
{
  return x + y;
}

static int
sub (int x, int y)
{
  return x - y;
}

static int
mul (int x, int y)
{
  return x * y;
}

static int
divide (int x, int y)
{
  if (y == 0)
  {
    if (x < 0)
      return 1;
    else
      return -1;
  }
  return x / y;
}

static int
mod (int x, int y)
{
  if (y == 0) return x;
  return x % y;
}

static void
test_add_1_arithmetic (void)
{
  u_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_U_LOW, BTOR_TEST_ARITHMETIC_U_HIGH);
}

static void
test_sub_1_arithmetic (void)
{
  u_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_U_LOW, BTOR_TEST_ARITHMETIC_U_HIGH);
}

static void
test_umul_arithmetic (void)
{
  u_arithmetic_test (
      mul, "umul", BTOR_TEST_ARITHMETIC_U_LOW, BTOR_TEST_ARITHMETIC_U_HIGH);
}

static void
test_udiv_arithmetic (void)
{
  u_arithmetic_test (
      divide, "udiv", BTOR_TEST_ARITHMETIC_U_LOW, BTOR_TEST_ARITHMETIC_U_HIGH);
}

static void
test_umod_arithmetic (void)
{
  u_arithmetic_test (
      mod, "umod", BTOR_TEST_ARITHMETIC_U_LOW, BTOR_TEST_ARITHMETIC_U_HIGH);
}

static void
test_add_2_arithmetic (void)
{
  s_arithmetic_test (
      add, "add", BTOR_TEST_ARITHMETIC_S_LOW, BTOR_TEST_ARITHMETIC_S_HIGH);
}

static void
test_sub_2_arithmetic (void)
{
  s_arithmetic_test (
      sub, "sub", BTOR_TEST_ARITHMETIC_S_LOW, BTOR_TEST_ARITHMETIC_S_HIGH);
}

static void
test_smul_arithmetic (void)
{
  s_arithmetic_test (
      mul, "smul", BTOR_TEST_ARITHMETIC_S_LOW, BTOR_TEST_ARITHMETIC_S_HIGH);
}

static void
test_sdiv_arithmetic (void)
{
  s_arithmetic_test (
      divide, "sdiv", BTOR_TEST_ARITHMETIC_S_LOW, BTOR_TEST_ARITHMETIC_S_HIGH);
}

static void
test_smod_arithmetic (void)
{
  s_arithmetic_test (
      mod, "smod", BTOR_TEST_ARITHMETIC_S_LOW, BTOR_TEST_ARITHMETIC_S_HIGH);
}

static void
run_all_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (add_1_arithmetic);
  BTOR_RUN_TEST (sub_1_arithmetic);
  BTOR_RUN_TEST (umul_arithmetic);
  BTOR_RUN_TEST (udiv_arithmetic);
  BTOR_RUN_TEST (umod_arithmetic);
  BTOR_RUN_TEST (add_2_arithmetic);
  BTOR_RUN_TEST (sub_2_arithmetic);
  BTOR_RUN_TEST (smul_arithmetic);
  BTOR_RUN_TEST (sdiv_arithmetic);
  BTOR_RUN_TEST (smod_arithmetic);
}

void
run_arithmetic_tests (int argc, char **argv)
{
  run_all_tests (argc, argv);
  g_argc    = 4;
  g_argv[3] = "-rwl0";
  run_all_tests (argc, argv);
}

void
finish_arithmetic_tests (void)
{
  int result = remove (BTOR_TEST_ARITHMETIC_TEMP_FILE_NAME);
  assert (result == 0);
}

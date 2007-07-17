#include "testconst.h"
#include "btorconst.h"
#include "btormem.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_CONST_NUM_BITS 8
#define BTOR_TEST_CONST_MAX (1 << BTOR_TEST_CONST_NUM_BITS)

static BtorMemMgr *g_mm;

void
init_const_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_int_to_bin (void)
{
  char *result = btor_int_to_bin (g_mm, 5, 8);
  assert (strcmp (result, "00000101") == 0);
  btor_delete_const (g_mm, result);
  result = btor_int_to_bin (g_mm, 0, 8);
  assert (strcmp (result, "00000000") == 0);
  btor_delete_const (g_mm, result);
  result = btor_int_to_bin (g_mm, 127, 8);
  assert (strcmp (result, "01111111") == 0);
  btor_delete_const (g_mm, result);
  result = btor_int_to_bin (g_mm, 126, 8);
  assert (strcmp (result, "01111110") == 0);
  btor_delete_const (g_mm, result);
  result = btor_int_to_bin (g_mm, 255, 8);
  assert (strcmp (result, "11111111") == 0);
  btor_delete_const (g_mm, result);
  result = btor_int_to_bin (g_mm, 7, 3);
  assert (strcmp (result, "111") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_add_unbounded_const_aux (FILE *fout, const char *a, const char *b)
{
  char *c = btor_add_unbounded_const (g_mm, a, b);
  char fmt[80];
  size_t len = strlen (a);
  if (strlen (b) > len) len = strlen (b);
  sprintf (fmt,
           "  %%%ds\n+ %%%ds\n= %%%ds\n\n",
           (int) len + 2,
           (int) len + 2,
           (int) len + 2);
  fprintf (fout, fmt, a, b, c);
  btor_delete_const (g_mm, c);
}

static void
test_add_unbounded_const (void)
{
  FILE *fout = fopen ("log/add_unbounded_const.log", "w");
  test_add_unbounded_const_aux (fout, "1", "1");
  test_add_unbounded_const_aux (fout, "", "");
  test_add_unbounded_const_aux (fout, "0", "");
  test_add_unbounded_const_aux (fout, "", "0");
  test_add_unbounded_const_aux (fout, "1", "");
  test_add_unbounded_const_aux (fout, "", "1");
  test_add_unbounded_const_aux (fout, "0", "0");
  test_add_unbounded_const_aux (fout, "1", "0");
  test_add_unbounded_const_aux (fout, "0", "1");
  test_add_unbounded_const_aux (fout, "111", "1101");
  test_add_unbounded_const_aux (fout, "11111111", "100000000001");
  fclose (fout);
}

static void
test_mult_unbounded_const_aux (FILE *fout, const char *a, const char *b)
{
  char *c = btor_mult_unbounded_const (g_mm, a, b);
  char fmt[80];
  int len;
  len = strlen (a) + strlen (b);
  sprintf (fmt, "  %%%ds\n* %%%ds\n= %%%ds\n\n", len + 1, len + 1, len + 1);
  fprintf (fout, fmt, a, b, c);
  btor_delete_const (g_mm, c);
}

static void
test_mult_unbounded_const (void)
{
  FILE *fout = fopen ("log/mult_unbounded_const.log", "w");
  test_mult_unbounded_const_aux (fout, "", "");
  test_mult_unbounded_const_aux (fout, "0", "");
  test_mult_unbounded_const_aux (fout, "", "0");
  test_mult_unbounded_const_aux (fout, "1", "");
  test_mult_unbounded_const_aux (fout, "", "1");
  test_mult_unbounded_const_aux (fout, "0", "0");
  test_mult_unbounded_const_aux (fout, "1", "0");
  test_mult_unbounded_const_aux (fout, "0", "1");
  test_mult_unbounded_const_aux (fout, "1", "1");
  test_mult_unbounded_const_aux (fout, "1", "11");
  test_mult_unbounded_const_aux (fout, "10", "11");
  test_mult_unbounded_const_aux (fout, "11", "11");
  test_mult_unbounded_const_aux (fout, "0011", "0011");
  test_mult_unbounded_const_aux (fout, "111", "11");
  test_mult_unbounded_const_aux (fout, "111", "1101");
  test_mult_unbounded_const_aux (fout, "1010", "11111");
  fclose (fout);
}

static void
test_cmp_const_aux (FILE *fout, const char *a, const char *b)
{
  int res = btor_cmp_const (a, b);
  fprintf (fout, "%s %c %s\n", a, (res ? ((res < 0) ? '<' : '>') : '='), b);
}

static void
test_cmp_const (void)
{
  FILE *fout = fopen ("log/cmp_const.log", "w");
  test_cmp_const_aux (fout, "01", "1");
  test_cmp_const_aux (fout, "", "");
  test_cmp_const_aux (fout, "0", "");
  test_cmp_const_aux (fout, "", "0");
  test_cmp_const_aux (fout, "1", "");
  test_cmp_const_aux (fout, "", "1");
  test_cmp_const_aux (fout, "0", "0");
  test_cmp_const_aux (fout, "0", "1");
  test_cmp_const_aux (fout, "1", "0");
  test_cmp_const_aux (fout, "1", "1");
  test_cmp_const_aux (fout, "10", "");
  test_cmp_const_aux (fout, "10", "0");
  test_cmp_const_aux (fout, "10", "1");
  test_cmp_const_aux (fout, "10", "01");
  test_cmp_const_aux (fout, "10", "10");
  test_cmp_const_aux (fout, "10", "010");
  test_cmp_const_aux (fout, "10", "00010");
  test_cmp_const_aux (fout, "10", "00011");
  test_cmp_const_aux (fout, "", "10");
  test_cmp_const_aux (fout, "0", "10");
  test_cmp_const_aux (fout, "1", "10");
  test_cmp_const_aux (fout, "01", "10");
  test_cmp_const_aux (fout, "10", "10");
  test_cmp_const_aux (fout, "010", "10");
  test_cmp_const_aux (fout, "00010", "10");
  test_cmp_const_aux (fout, "00011", "10");
  fclose (fout);
}

static void
test_sub_unbounded_const_aux (FILE *fout, const char *a, const char *b)
{
  char *c = btor_sub_unbounded_const (g_mm, a, b);
  char fmt[80];
  size_t len = strlen (a);
  sprintf (fmt,
           "  %%%ds\n- %%%ds\n= %%%ds\n\n",
           (int) len + 1,
           (int) len + 1,
           (int) len + 1);
  fprintf (fout, fmt, a, b, c);
  btor_delete_const (g_mm, c);
}

static void
test_sub_unbounded_const (void)
{
  FILE *fout = fopen ("log/sub_unbounded_const.log", "w");
  test_sub_unbounded_const_aux (fout, "", "");
  test_sub_unbounded_const_aux (fout, "1", "");
  test_sub_unbounded_const_aux (fout, "001", "01");
  test_sub_unbounded_const_aux (fout, "10", "1");
  test_sub_unbounded_const_aux (fout, "10", "10");
  test_sub_unbounded_const_aux (fout, "11", "");
  test_sub_unbounded_const_aux (fout, "11", "1");
  test_sub_unbounded_const_aux (fout, "11", "10");
  test_sub_unbounded_const_aux (fout, "11", "11");
  test_sub_unbounded_const_aux (fout, "00100", "");
  test_sub_unbounded_const_aux (fout, "00100", "000");
  test_sub_unbounded_const_aux (fout, "00100", "001");
  test_sub_unbounded_const_aux (fout, "00100", "010");
  test_sub_unbounded_const_aux (fout, "0100", "10");
  test_sub_unbounded_const_aux (fout, "0100", "11");
  test_sub_unbounded_const_aux (fout, "100", "100");
  test_sub_unbounded_const_aux (fout, "101", "0");
  test_sub_unbounded_const_aux (fout, "101", "010");
  fclose (fout);
}

static int not(int x) { return ~x; }

static int
neg (int x)
{
  return -x;
}

static void
unary_const_test (int (*int_func) (int),
                  char *(*const_func) (BtorMemMgr *, const char *) )
{
  int i        = 0;
  char *a      = NULL;
  char *result = NULL;
  assert (int_func != NULL);
  assert (const_func != NULL);
  for (i = 0; i < BTOR_TEST_CONST_MAX; i++)
  {
    a      = btor_int_to_bin (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    result = const_func (g_mm, a);
    assert ((int_func (i) & (BTOR_TEST_CONST_MAX - 1))
            == (int) strtol (result, (char **) NULL, 2));
    btor_delete_const (g_mm, a);
    btor_delete_const (g_mm, result);
  }
}

static void
test_not_const (void)
{
  unary_const_test (not, btor_not_const);
}

static void
test_neg_const (void)
{
  /* This test case assumes that the compiler uses two's complement */
  unary_const_test (neg, btor_neg_const);
}

static int and (int x, int y) { return x & y; }

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

/* This function assumes that the compiler uses two's complement */
static int
divide (int x, int y)
{
  if (y == 0) return -1;
  return x / y;
}

static int
mod (int x, int y)
{
  if (y == 0) return x;
  return x % y;
}

static void
binary_const_test (int (*int_func) (int, int),
                   char *(*const_func) (BtorMemMgr *,
                                        const char *,
                                        const char *) )
{
  int i        = 0;
  int j        = 0;
  char *a      = NULL;
  char *b      = NULL;
  char *result = NULL;
  assert (int_func != NULL);
  assert (const_func != NULL);
  for (i = 0; i < BTOR_TEST_CONST_MAX; i++)
  {
    a = btor_int_to_bin (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b      = btor_int_to_bin (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
      result = const_func (g_mm, a, b);
      assert ((int) strlen (result) == BTOR_TEST_CONST_NUM_BITS);
      assert ((int_func (i, j) & (BTOR_TEST_CONST_MAX - 1))
              == (int) strtol (result, (char **) NULL, 2));
      btor_delete_const (g_mm, b);
      btor_delete_const (g_mm, result);
    }
    btor_delete_const (g_mm, a);
  }
}

static void
test_and_const (void)
{
  binary_const_test (and, btor_and_const);
}

static void
test_add_const (void)
{
  binary_const_test (add, btor_add_const);
}

/* This test case assumes that the compiler uses two's complement */
static void
test_sub_const (void)
{
  binary_const_test (sub, btor_sub_const);
}

static void
test_umul_const (void)
{
  binary_const_test (mul, btor_umul_const);
}

static void
test_udiv_const (void)
{
  binary_const_test (divide, btor_udiv_const);
}

static void
test_umod_const (void)
{
  binary_const_test (mod, btor_umod_const);
}

static void
binary_const_test_boolean_result (int (*int_func) (int, int),
                                  char *(*const_func) (BtorMemMgr *,
                                                       const char *,
                                                       const char *) )
{
  int i        = 0;
  int j        = 0;
  char *a      = NULL;
  char *b      = NULL;
  char *result = NULL;
  assert (int_func != NULL);
  assert (const_func != NULL);
  for (i = 0; i < BTOR_TEST_CONST_MAX; i++)
  {
    a = btor_int_to_bin (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b      = btor_int_to_bin (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
      result = const_func (g_mm, a, b);
      assert ((int) strlen (result) == 1);
      if (int_func (i, j))
        assert (result[0] == '1');
      else
        assert (result[0] == '0');
      btor_delete_const (g_mm, b);
      btor_delete_const (g_mm, result);
    }
    btor_delete_const (g_mm, a);
  }
}

static int
eq (int x, int y)
{
  return x == y;
}

static int
ult (int x, int y)
{
  return x < y;
}

static void
test_eq_const (void)
{
  binary_const_test_boolean_result (eq, btor_eq_const);
}

static void
test_ult_const (void)
{
  binary_const_test_boolean_result (ult, btor_ult_const);
}

static void
test_concat_const (void)
{
  int i        = 0;
  int j        = 0;
  char *a      = NULL;
  char *b      = NULL;
  char *result = NULL;
  for (i = 0; i < BTOR_TEST_CONST_MAX; i++)
  {
    a = btor_int_to_bin (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b      = btor_int_to_bin (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
      result = btor_concat_const (g_mm, a, b);
      assert (i * (1 << BTOR_TEST_CONST_NUM_BITS) + j
              == (int) strtol (result, (char **) NULL, 2));
      btor_delete_const (g_mm, b);
      btor_delete_const (g_mm, result);
    }
    btor_delete_const (g_mm, a);
  }
}

static void
test_cond_const (void)
{
  int i        = 0;
  int j        = 0;
  int k        = 0;
  char *a      = NULL;
  char *b      = NULL;
  char *c      = NULL;
  char *result = NULL;
  for (i = 0; i <= 1; i++)
  {
    a = btor_int_to_bin (g_mm, i, 1);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b = btor_int_to_bin (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
      for (k = 0; k < BTOR_TEST_CONST_MAX; k++)
      {
        c      = btor_int_to_bin (g_mm, k, BTOR_TEST_CONST_NUM_BITS);
        result = btor_cond_const (g_mm, a, b, c);
        if (i == 1)
          assert (strcmp (b, result) == 0);
        else
          assert (strcmp (c, result) == 0);
        btor_delete_const (g_mm, c);
        btor_delete_const (g_mm, result);
      }
      btor_delete_const (g_mm, b);
    }
    btor_delete_const (g_mm, a);
  }
}

void
run_const_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (int_to_bin);
  BTOR_RUN_TEST_CHECK_LOG (cmp_const);
  BTOR_RUN_TEST_CHECK_LOG (add_unbounded_const);
  BTOR_RUN_TEST_CHECK_LOG (mult_unbounded_const);
  BTOR_RUN_TEST_CHECK_LOG (sub_unbounded_const);
  BTOR_RUN_TEST (not_const);
  BTOR_RUN_TEST (neg_const);
  BTOR_RUN_TEST (and_const);
  BTOR_RUN_TEST (add_const);
  BTOR_RUN_TEST (sub_const);
  BTOR_RUN_TEST (umul_const);
  BTOR_RUN_TEST (udiv_const);
  BTOR_RUN_TEST (umod_const);
  BTOR_RUN_TEST (eq_const);
  BTOR_RUN_TEST (ult_const);
  BTOR_RUN_TEST (concat_const);
  BTOR_RUN_TEST (cond_const);
}

void
finish_const_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

#include "testconst.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorutil.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_CONST_NUM_BITS 4
#define BTOR_TEST_CONST_MAX (1 << BTOR_TEST_CONST_NUM_BITS)

static BtorMemMgr *g_mm;

void
init_const_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_int_to_const (void)
{
  char *result = btor_int_to_const (g_mm, 5, 8);
  assert (strcmp (result, "00000101") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, 0, 8);
  assert (strcmp (result, "00000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, 127, 8);
  assert (strcmp (result, "01111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, 126, 8);
  assert (strcmp (result, "01111110") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, 255, 8);
  assert (strcmp (result, "11111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, 7, 3);
  assert (strcmp (result, "111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, -1, 1);
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, -2, 2);
  assert (strcmp (result, "10") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, -3, 31);
  assert (strcmp (result, "1111111111111111111111111111101") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, -4, 32);
  assert (strcmp (result, "11111111111111111111111111111100") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, INT_MIN, 32);
  assert (strcmp (result, "10000000000000000000000000000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, 2147483647, 32);
  assert (strcmp (result, "01111111111111111111111111111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_int_to_const (g_mm, -5, 33);
  assert (strcmp (result, "111111111111111111111111111111011") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_unsigned_to_const (void)
{
  char *result = btor_unsigned_to_const (g_mm, 5u, 8);
  assert (strcmp (result, "00000101") == 0);
  btor_delete_const (g_mm, result);

  result = btor_unsigned_to_const (g_mm, UINT_MAX, 31);
  assert (strcmp (result, "1111111111111111111111111111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_unsigned_to_const (g_mm, UINT_MAX, 32);
  assert (strcmp (result, "11111111111111111111111111111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_unsigned_to_const (g_mm, UINT_MAX, 33);
  assert (strcmp (result, "011111111111111111111111111111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_unsigned_to_const (g_mm, UINT_MAX, 40);
  assert (strcmp (result, "0000000011111111111111111111111111111111") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_add_unbounded_const_aux (FILE *fout, const char *a, const char *b)
{
  char *c = btor_add_unbounded_const (g_mm, a, b);
  char fmt[80];
  int len = (int) strlen (a);
  if ((int) strlen (b) > len) len = (int) strlen (b);
  sprintf (fmt, "  %%%ds\n+ %%%ds\n= %%%ds\n\n", len + 2, len + 2, len + 2);
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
  len = (int) strlen (a) + (int) strlen (b);
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
  int len = (int) strlen (a) + 1;
  sprintf (fmt, "  %%%ds\n- %%%ds\n= %%%ds\n\n", len, len, len);
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

static void
test_udiv_unbounded_const_aux (FILE *fout, const char *a, const char *b)
{
  char *d, *c = btor_udiv_unbounded_const (g_mm, a, b, &d);
  char fmt[80];
  int len = (int) strlen (a);
  sprintf (
      fmt, "  %%%ds\n/ %%%ds\n= %%%ds\n%%%% %%%ds\n\n", len, len, len, len);
  fprintf (fout, fmt, a, b, c, d);
  btor_delete_const (g_mm, c);
  btor_delete_const (g_mm, d);
}

static void
test_udiv_unbounded_const (void)
{
  FILE *fout = fopen ("log/udiv_unbounded_const.log", "w");
  test_udiv_unbounded_const_aux (fout, "", "1");
  test_udiv_unbounded_const_aux (fout, "0", "1");
  test_udiv_unbounded_const_aux (fout, "00", "00100");
  test_udiv_unbounded_const_aux (fout, "1", "1");
  test_udiv_unbounded_const_aux (fout, "10", "1");
  test_udiv_unbounded_const_aux (fout, "10", "10");
  test_udiv_unbounded_const_aux (fout, "10", "11");
  test_udiv_unbounded_const_aux (fout, "11", "10");
  test_udiv_unbounded_const_aux (fout, "11", "11");
  test_udiv_unbounded_const_aux (fout, "11", "100");
  test_udiv_unbounded_const_aux (fout, "100", "1");
  test_udiv_unbounded_const_aux (fout, "100", "10");
  test_udiv_unbounded_const_aux (fout, "100", "11");
  test_udiv_unbounded_const_aux (fout, "100", "100");
  test_udiv_unbounded_const_aux (fout, "101", "100");
  test_udiv_unbounded_const_aux (fout, "110", "100");
  test_udiv_unbounded_const_aux (fout, "111", "100");
  test_udiv_unbounded_const_aux (fout, "100", "101");
  test_udiv_unbounded_const_aux (fout, "101", "101");
  test_udiv_unbounded_const_aux (fout, "110", "101");
  test_udiv_unbounded_const_aux (fout, "111", "101");
  test_udiv_unbounded_const_aux (fout, "00011110000", "01101");
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
    a      = btor_int_to_const (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    result = const_func (g_mm, a);
    assert ((int_func (i) & (BTOR_TEST_CONST_MAX - 1))
            == (int) strtol (result, (char **) NULL, 2));
    btor_delete_const (g_mm, a);
    btor_delete_const (g_mm, result);
  }
}

static void
test_invert_const (void)
{
  char bits[] = {'1', '0', '1', '1', '\0'};
  btor_invert_const (g_mm, bits);
  assert (bits[0] == '0');
  assert (bits[1] == '1');
  assert (bits[2] == '0');
  assert (bits[3] == '0');
  btor_invert_const (g_mm, bits);
  assert (bits[0] == '1');
  assert (bits[1] == '0');
  assert (bits[2] == '1');
  assert (bits[3] == '1');
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

/* This test case assumes that the compiler uses two's complement */
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
    a = btor_int_to_const (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b      = btor_int_to_const (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
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
test_mul_const (void)
{
  binary_const_test (mul, btor_mul_const);
}

static void
test_udiv_const (void)
{
  binary_const_test (divide, btor_udiv_const);
}

static void
test_urem_const (void)
{
  binary_const_test (mod, btor_urem_const);
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
    a = btor_int_to_const (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b      = btor_int_to_const (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
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
    a = btor_int_to_const (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < BTOR_TEST_CONST_MAX; j++)
    {
      b      = btor_int_to_const (g_mm, j, BTOR_TEST_CONST_NUM_BITS);
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
shift_const_test (int (*int_func) (int, int),
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
  assert (btor_is_power_of_2_util (BTOR_TEST_CONST_NUM_BITS));
  for (i = 0; i < BTOR_TEST_CONST_MAX; i++)
  {
    a = btor_int_to_const (g_mm, i, BTOR_TEST_CONST_NUM_BITS);
    for (j = 0; j < btor_log_2_util (BTOR_TEST_CONST_MAX); j++)
    {
      b = btor_int_to_const (
          g_mm, j, btor_log_2_util (BTOR_TEST_CONST_NUM_BITS));
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

static int
sll (int x, int y)
{
  return ((unsigned int) x) << ((unsigned int) y);
}

static int
srl (int x, int y)
{
  return ((unsigned int) x) >> ((unsigned int) y);
}

static void
test_sll_const (void)
{
  shift_const_test (sll, btor_sll_const);
}

static void
test_srl_const (void)
{
  shift_const_test (srl, btor_srl_const);
}

static void
test_const_to_hex_aux (FILE *fout, const char *c)
{
  char *h = btor_const_to_hex (g_mm, c);
  fprintf (fout, "2'%s = 16'%s\n", c, h);
  btor_freestr (g_mm, h);
}

static void
test_const_to_hex (void)
{
  FILE *fout = fopen ("log/const_to_hex.log", "w");
  test_const_to_hex_aux (fout, "");
  test_const_to_hex_aux (fout, "1");
  test_const_to_hex_aux (fout, "10");
  test_const_to_hex_aux (fout, "11");
  test_const_to_hex_aux (fout, "100");
  test_const_to_hex_aux (fout, "101");
  test_const_to_hex_aux (fout, "110");
  test_const_to_hex_aux (fout, "111");
  test_const_to_hex_aux (fout, "1000");
  test_const_to_hex_aux (fout, "1001");
  test_const_to_hex_aux (fout, "1010");
  test_const_to_hex_aux (fout, "1011");
  test_const_to_hex_aux (fout, "1100");
  test_const_to_hex_aux (fout, "1101");
  test_const_to_hex_aux (fout, "1110");
  test_const_to_hex_aux (fout, "1111");
  test_const_to_hex_aux (fout, "10000");
  test_const_to_hex_aux (fout, "10001");
  test_const_to_hex_aux (fout, "1111111111111111");
  test_const_to_hex_aux (fout, "11111111111111111");
  test_const_to_hex_aux (fout, "00001111111111111111");
  test_const_to_hex_aux (fout, "000011111111111111111");
  fclose (fout);
}

static void
test_const_to_dec_aux (FILE *fout, const char *c)
{
  char *d = btor_const_to_decimal (g_mm, c);
  fprintf (fout, "2'%s = 10'%s\n", c, d);
  btor_freestr (g_mm, d);
}

static void
test_const_to_dec (void)
{
  FILE *fout = fopen ("log/const_to_dec.log", "w");
  test_const_to_dec_aux (fout, "");
  test_const_to_dec_aux (fout, "1");
  test_const_to_dec_aux (fout, "10");
  test_const_to_dec_aux (fout, "11");
  test_const_to_dec_aux (fout, "100");
  test_const_to_dec_aux (fout, "101");
  test_const_to_dec_aux (fout, "110");
  test_const_to_dec_aux (fout, "111");
  test_const_to_dec_aux (fout, "1000");
  test_const_to_dec_aux (fout, "1001");
  test_const_to_dec_aux (fout, "1010");
  test_const_to_dec_aux (fout, "1011");
  test_const_to_dec_aux (fout, "1100");
  test_const_to_dec_aux (fout, "1101");
  test_const_to_dec_aux (fout, "1110");
  test_const_to_dec_aux (fout, "1111");
  test_const_to_dec_aux (fout, "10000");
  test_const_to_dec_aux (fout, "10001");
  test_const_to_dec_aux (fout, "10000000000000000");
  test_const_to_dec_aux (fout,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  test_const_to_dec_aux (fout,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  test_const_to_dec_aux (fout,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  fclose (fout);
}

static void
test_hex_to_const_aux (FILE *file, const char *h)
{
  char *c = btor_hex_to_const (g_mm, h);
  fprintf (file, "16'%s = 2'%s\n", h, c);
  btor_freestr (g_mm, c);
}

static void
test_hex_to_const (void)
{
  FILE *file = fopen ("log/hex_to_const.log", "w");
  test_hex_to_const_aux (file, "");
  test_hex_to_const_aux (file, "1");
  test_hex_to_const_aux (file, "2");
  test_hex_to_const_aux (file, "3");
  test_hex_to_const_aux (file, "4");
  test_hex_to_const_aux (file, "5");
  test_hex_to_const_aux (file, "6");
  test_hex_to_const_aux (file, "7");
  test_hex_to_const_aux (file, "8");
  test_hex_to_const_aux (file, "9");
  test_hex_to_const_aux (file, "a");
  test_hex_to_const_aux (file, "A");
  test_hex_to_const_aux (file, "b");
  test_hex_to_const_aux (file, "B");
  test_hex_to_const_aux (file, "c");
  test_hex_to_const_aux (file, "C");
  test_hex_to_const_aux (file, "d");
  test_hex_to_const_aux (file, "D");
  test_hex_to_const_aux (file, "e");
  test_hex_to_const_aux (file, "E");
  test_hex_to_const_aux (file, "f");
  test_hex_to_const_aux (file, "F");
  test_hex_to_const_aux (file, "10");
  test_hex_to_const_aux (file, "13");
  test_hex_to_const_aux (file, "2e");
  test_hex_to_const_aux (file, "ff");
  fclose (file);
}

static void
test_decimal_to_const_aux (FILE *file, const char *d)
{
  char *c = btor_decimal_to_const (g_mm, d);
  fprintf (file, "10'%s = 2'%s\n", d, c);
  btor_freestr (g_mm, c);
}

static void
test_decimal_to_const (void)
{
  FILE *file = fopen ("log/decimal_to_const.log", "w");
  test_decimal_to_const_aux (file, "");
  test_decimal_to_const_aux (file, "256");
  test_decimal_to_const_aux (file, "100");
  test_decimal_to_const_aux (file, "65537");
  test_decimal_to_const_aux (file, "4294967296");
  test_decimal_to_const_aux (file, "18446744073709551616");
  fclose (file);
}

static void
test_slice_const_aux (FILE *file, const char *c, int upper, int lower)
{
  char *r = btor_slice_const (g_mm, c, upper, lower);
  fprintf (file, "%s[%d:%d] = %s\n", c, upper, lower, r);
  btor_delete_const (g_mm, r);
}

static void
test_slice_const (void)
{
  FILE *file = fopen ("log/slice_const.log", "w");

  test_slice_const_aux (file, "01", 0, 0);
  test_slice_const_aux (file, "01", 1, 0);
  test_slice_const_aux (file, "01", 1, 1);

  test_slice_const_aux (file, "101", 0, 0);
  test_slice_const_aux (file, "101", 1, 0);
  test_slice_const_aux (file, "101", 2, 0);
  test_slice_const_aux (file, "101", 1, 1);
  test_slice_const_aux (file, "101", 2, 1);
  test_slice_const_aux (file, "101", 2, 2);

  test_slice_const_aux (file, "11110000", 7, 4);
  test_slice_const_aux (file, "11110000", 5, 2);
  test_slice_const_aux (file, "11110000", 3, 0);

  fclose (file);
}

static void
test_inverse_const_aux (FILE *file, const char *c)
{
  char *i = btor_inverse_const (g_mm, c);
  fprintf (file, "1 / %s = %s mod 2^%ld\n", c, i, strlen (c));
  btor_delete_const (g_mm, i);
}

static void
test_inverse_const (void)
{
  FILE *file = fopen ("log/inverse_const.log", "w");
  test_inverse_const_aux (file, "1");
  test_inverse_const_aux (file, "01");
  test_inverse_const_aux (file, "001");
  test_inverse_const_aux (file, "0001");
  test_inverse_const_aux (file, "11");
  test_inverse_const_aux (file, "101");
  test_inverse_const_aux (file, "111");
  test_inverse_const_aux (file, "1001");
  test_inverse_const_aux (file, "1011");
  test_inverse_const_aux (file, "1101");
  test_inverse_const_aux (file, "1111");
  test_inverse_const_aux (file, "01010101010101010101010101010101");
  fclose (file);
}

void
run_const_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (int_to_const);
  BTOR_RUN_TEST (unsigned_to_const);
  BTOR_RUN_TEST_CHECK_LOG (cmp_const);
  BTOR_RUN_TEST_CHECK_LOG (add_unbounded_const);
  BTOR_RUN_TEST_CHECK_LOG (mult_unbounded_const);
  BTOR_RUN_TEST_CHECK_LOG (sub_unbounded_const);
  BTOR_RUN_TEST_CHECK_LOG (udiv_unbounded_const);
  BTOR_RUN_TEST (invert_const);
  BTOR_RUN_TEST (not_const);
  BTOR_RUN_TEST (neg_const);
  BTOR_RUN_TEST (and_const);
  BTOR_RUN_TEST (add_const);
  BTOR_RUN_TEST (sub_const);
  BTOR_RUN_TEST (mul_const);
  BTOR_RUN_TEST (udiv_const);
  BTOR_RUN_TEST (urem_const);
  BTOR_RUN_TEST (eq_const);
  BTOR_RUN_TEST (ult_const);
  BTOR_RUN_TEST (concat_const);
  BTOR_RUN_TEST (sll_const);
  BTOR_RUN_TEST (srl_const);
  BTOR_RUN_TEST_CHECK_LOG (const_to_hex);
  BTOR_RUN_TEST_CHECK_LOG (const_to_dec);
  BTOR_RUN_TEST_CHECK_LOG (hex_to_const);
  BTOR_RUN_TEST_CHECK_LOG (decimal_to_const);
  BTOR_RUN_TEST_CHECK_LOG (slice_const);
  BTOR_RUN_TEST_CHECK_LOG (inverse_const);
}

void
finish_const_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

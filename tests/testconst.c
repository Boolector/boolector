/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2007-2012 Robert Daniel Brummayer, Armin Biere
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "testconst.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorstack.h"
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

#define BTOR_TEST_CONST_3VL_LOW 1
#define BTOR_TEST_CONST_3VL_HIGH 4

static BtorMemMgr *g_mm;

void
init_const_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_zero_const (void)
{
  char *result = btor_zero_const (g_mm, 1);
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 2);
  assert (strcmp (result, "00") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 3);
  assert (strcmp (result, "000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 4);
  assert (strcmp (result, "0000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 5);
  assert (strcmp (result, "00000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 8);
  assert (strcmp (result, "00000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 16);
  assert (strcmp (result, "0000000000000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 32);
  assert (strcmp (result, "00000000000000000000000000000000") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_one_const (void)
{
  char *result = btor_one_const (g_mm, 1);
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 2);
  assert (strcmp (result, "01") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 3);
  assert (strcmp (result, "001") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 4);
  assert (strcmp (result, "0001") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 5);
  assert (strcmp (result, "00001") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 8);
  assert (strcmp (result, "00000001") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 16);
  assert (strcmp (result, "0000000000000001") == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 32);
  assert (strcmp (result, "00000000000000000000000000000001") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_ones_const (void)
{
  char *result = btor_ones_const (g_mm, 1);
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 2);
  assert (strcmp (result, "11") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 3);
  assert (strcmp (result, "111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 4);
  assert (strcmp (result, "1111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 5);
  assert (strcmp (result, "11111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 8);
  assert (strcmp (result, "11111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 16);
  assert (strcmp (result, "1111111111111111") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 32);
  assert (strcmp (result, "11111111111111111111111111111111") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_is_zero_const (void)
{
  char *result = btor_zero_const (g_mm, 1);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 2);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 3);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 4);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 5);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 8);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 16);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 32);
  assert (btor_is_zero_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 1);
  assert (btor_is_zero_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 2);
  assert (btor_is_zero_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 32);
  assert (btor_is_zero_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 32);
  assert (btor_is_zero_const (result) == 0);
  btor_delete_const (g_mm, result);
}

static void
test_is_one_const (void)
{
  char *result = btor_one_const (g_mm, 1);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 2);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 3);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 4);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 5);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 8);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 16);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 32);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 1);
  assert (btor_is_one_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 2);
  assert (btor_is_one_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 32);
  assert (btor_is_one_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 1);
  assert (btor_is_one_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 32);
  assert (btor_is_one_const (result) == 0);
  btor_delete_const (g_mm, result);
}

static void
test_is_ones_const (void)
{
  char *result = btor_ones_const (g_mm, 1);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 2);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 3);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 4);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 5);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 8);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 16);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_ones_const (g_mm, 32);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 1);
  assert (btor_is_ones_const (result) == 1);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 2);
  assert (btor_is_ones_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_one_const (g_mm, 32);
  assert (btor_is_ones_const (result) == 0);
  btor_delete_const (g_mm, result);

  result = btor_zero_const (g_mm, 32);
  assert (btor_is_ones_const (result) == 0);
  btor_delete_const (g_mm, result);
}

static void
test_is_special_const (void)
{
  assert (btor_is_special_const ("0") == BTOR_SPECIAL_CONST_ZERO);
  assert (btor_is_special_const ("1") == BTOR_SPECIAL_CONST_ONE_ONES);

  assert (btor_is_special_const ("00") == BTOR_SPECIAL_CONST_ZERO);
  assert (btor_is_special_const ("01") == BTOR_SPECIAL_CONST_ONE);
  assert (btor_is_special_const ("10") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("11") == BTOR_SPECIAL_CONST_ONES);

  assert (btor_is_special_const ("000") == BTOR_SPECIAL_CONST_ZERO);
  assert (btor_is_special_const ("001") == BTOR_SPECIAL_CONST_ONE);
  assert (btor_is_special_const ("010") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("011") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("100") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("101") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("110") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("111") == BTOR_SPECIAL_CONST_ONES);

  assert (btor_is_special_const ("0000") == BTOR_SPECIAL_CONST_ZERO);
  assert (btor_is_special_const ("0001") == BTOR_SPECIAL_CONST_ONE);
  assert (btor_is_special_const ("0010") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("0011") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("0100") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("0101") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("0110") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("0111") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1000") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1001") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1010") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1011") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1100") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1101") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1110") == BTOR_SPECIAL_CONST_NONE);
  assert (btor_is_special_const ("1111") == BTOR_SPECIAL_CONST_ONES);
}

static void
test_is_small_positive_int_const (void)
{
  assert (btor_is_small_positive_int ("000") == 0);
  assert (btor_is_small_positive_int ("001") == 1);
  assert (btor_is_small_positive_int ("0010") == 2);
  assert (btor_is_small_positive_int ("00100") == 4);
  assert (btor_is_small_positive_int ("001000") == 8);
  assert (btor_is_small_positive_int ("0010000") == 16);
  assert (btor_is_small_positive_int ("000100000") == 32);
  assert (btor_is_small_positive_int ("0001000000") == 64);
  assert (btor_is_small_positive_int ("00010000000") == 128);
  assert (btor_is_small_positive_int ("000100000000") == 256);
  assert (btor_is_small_positive_int ("0001000000000") == 512);
  assert (btor_is_small_positive_int ("0000010000000000") == 1024);
  assert (btor_is_small_positive_int ("10000000000000000000000000000")
          == (1 << 28));
  assert (btor_is_small_positive_int ("100000000000000000000000000000")
          == (1 << 29));
  assert (btor_is_small_positive_int ("1000000000000000000000000000000")
          == (1 << 30));
  assert (btor_is_small_positive_int ("01000000000000000000000000000000")
          == (1 << 30));
  assert (btor_is_small_positive_int ("10000000000000000000000000000000") < 0);
  assert (btor_is_small_positive_int ("0010000000000000000000000000000000")
          < 0);
  assert (
      btor_is_small_positive_int (
          "0000000000000000000000000000000000000000000000000000000000000000")
      == 0);
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
test_const_to_hex_aux (FILE *g_logfile, const char *c)
{
  char *h = btor_const_to_hex (g_mm, c);
  fprintf (g_logfile, "2'%s = 16'%s\n", c, h);
  btor_freestr (g_mm, h);
}

static void
test_const_to_hex (void)
{
  test_const_to_hex_aux (g_logfile, "");
  test_const_to_hex_aux (g_logfile, "1");
  test_const_to_hex_aux (g_logfile, "10");
  test_const_to_hex_aux (g_logfile, "11");
  test_const_to_hex_aux (g_logfile, "100");
  test_const_to_hex_aux (g_logfile, "101");
  test_const_to_hex_aux (g_logfile, "110");
  test_const_to_hex_aux (g_logfile, "111");
  test_const_to_hex_aux (g_logfile, "1000");
  test_const_to_hex_aux (g_logfile, "1001");
  test_const_to_hex_aux (g_logfile, "1010");
  test_const_to_hex_aux (g_logfile, "1011");
  test_const_to_hex_aux (g_logfile, "1100");
  test_const_to_hex_aux (g_logfile, "1101");
  test_const_to_hex_aux (g_logfile, "1110");
  test_const_to_hex_aux (g_logfile, "1111");
  test_const_to_hex_aux (g_logfile, "10000");
  test_const_to_hex_aux (g_logfile, "10001");
  test_const_to_hex_aux (g_logfile, "1111111111111111");
  test_const_to_hex_aux (g_logfile, "11111111111111111");
  test_const_to_hex_aux (g_logfile, "00001111111111111111");
  test_const_to_hex_aux (g_logfile, "000011111111111111111");
}

static void
test_const_to_dec_aux (FILE *g_logfile, const char *c)
{
  char *d = btor_const_to_decimal (g_mm, c);
  fprintf (g_logfile, "2'%s = 10'%s\n", c, d);
  btor_freestr (g_mm, d);
}

static void
test_const_to_dec (void)
{
  test_const_to_dec_aux (g_logfile, "");
  test_const_to_dec_aux (g_logfile, "1");
  test_const_to_dec_aux (g_logfile, "10");
  test_const_to_dec_aux (g_logfile, "11");
  test_const_to_dec_aux (g_logfile, "100");
  test_const_to_dec_aux (g_logfile, "101");
  test_const_to_dec_aux (g_logfile, "110");
  test_const_to_dec_aux (g_logfile, "111");
  test_const_to_dec_aux (g_logfile, "1000");
  test_const_to_dec_aux (g_logfile, "1001");
  test_const_to_dec_aux (g_logfile, "1010");
  test_const_to_dec_aux (g_logfile, "1011");
  test_const_to_dec_aux (g_logfile, "1100");
  test_const_to_dec_aux (g_logfile, "1101");
  test_const_to_dec_aux (g_logfile, "1110");
  test_const_to_dec_aux (g_logfile, "1111");
  test_const_to_dec_aux (g_logfile, "10000");
  test_const_to_dec_aux (g_logfile, "10001");
  test_const_to_dec_aux (g_logfile, "10000000000000000");
  test_const_to_dec_aux (g_logfile,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  test_const_to_dec_aux (g_logfile,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  test_const_to_dec_aux (g_logfile,
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
}

static void
test_hex_to_const_aux (FILE *g_logfile, const char *h)
{
  char *c = btor_hex_to_const (g_mm, h);
  fprintf (g_logfile, "16'%s = 2'%s\n", h, c);
  btor_freestr (g_mm, c);
}

static void
test_hex_to_const (void)
{
  test_hex_to_const_aux (g_logfile, "");
  test_hex_to_const_aux (g_logfile, "1");
  test_hex_to_const_aux (g_logfile, "2");
  test_hex_to_const_aux (g_logfile, "3");
  test_hex_to_const_aux (g_logfile, "4");
  test_hex_to_const_aux (g_logfile, "5");
  test_hex_to_const_aux (g_logfile, "6");
  test_hex_to_const_aux (g_logfile, "7");
  test_hex_to_const_aux (g_logfile, "8");
  test_hex_to_const_aux (g_logfile, "9");
  test_hex_to_const_aux (g_logfile, "a");
  test_hex_to_const_aux (g_logfile, "A");
  test_hex_to_const_aux (g_logfile, "b");
  test_hex_to_const_aux (g_logfile, "B");
  test_hex_to_const_aux (g_logfile, "c");
  test_hex_to_const_aux (g_logfile, "C");
  test_hex_to_const_aux (g_logfile, "d");
  test_hex_to_const_aux (g_logfile, "D");
  test_hex_to_const_aux (g_logfile, "e");
  test_hex_to_const_aux (g_logfile, "E");
  test_hex_to_const_aux (g_logfile, "f");
  test_hex_to_const_aux (g_logfile, "F");
  test_hex_to_const_aux (g_logfile, "10");
  test_hex_to_const_aux (g_logfile, "13");
  test_hex_to_const_aux (g_logfile, "2e");
  test_hex_to_const_aux (g_logfile, "ff");
}

static void
test_decimal_to_const_aux (FILE *g_logfile, const char *d)
{
  char *c = btor_decimal_to_const (g_mm, d);
  fprintf (g_logfile, "10'%s = 2'%s\n", d, c);
  btor_freestr (g_mm, c);
}

static void
test_decimal_to_const (void)
{
  test_decimal_to_const_aux (g_logfile, "");
  test_decimal_to_const_aux (g_logfile, "256");
  test_decimal_to_const_aux (g_logfile, "100");
  test_decimal_to_const_aux (g_logfile, "65537");
  test_decimal_to_const_aux (g_logfile, "4294967296");
  test_decimal_to_const_aux (g_logfile, "18446744073709551616");
}

static void
test_slice_const_aux (FILE *g_logfile, const char *c, int upper, int lower)
{
  char *r = btor_slice_const (g_mm, c, upper, lower);
  fprintf (g_logfile, "%s[%d:%d] = %s\n", c, upper, lower, r);
  btor_delete_const (g_mm, r);
}

static void
test_slice_const (void)
{
  test_slice_const_aux (g_logfile, "01", 0, 0);
  test_slice_const_aux (g_logfile, "01", 1, 0);
  test_slice_const_aux (g_logfile, "01", 1, 1);

  test_slice_const_aux (g_logfile, "101", 0, 0);
  test_slice_const_aux (g_logfile, "101", 1, 0);
  test_slice_const_aux (g_logfile, "101", 2, 0);
  test_slice_const_aux (g_logfile, "101", 1, 1);
  test_slice_const_aux (g_logfile, "101", 2, 1);
  test_slice_const_aux (g_logfile, "101", 2, 2);

  test_slice_const_aux (g_logfile, "11110000", 7, 4);
  test_slice_const_aux (g_logfile, "11110000", 5, 2);
  test_slice_const_aux (g_logfile, "11110000", 3, 0);
}

static void
test_inverse_const_aux (FILE *g_logfile, const char *c)
{
  char *i = btor_inverse_const (g_mm, c);
  fprintf (g_logfile, "1 / %s = %s mod 2^%ld\n", c, i, (long) strlen (c));
  btor_delete_const (g_mm, i);
}

static void
test_inverse_const (void)
{
  test_inverse_const_aux (g_logfile, "1");
  test_inverse_const_aux (g_logfile, "01");
  test_inverse_const_aux (g_logfile, "001");
  test_inverse_const_aux (g_logfile, "0001");
  test_inverse_const_aux (g_logfile, "11");
  test_inverse_const_aux (g_logfile, "101");
  test_inverse_const_aux (g_logfile, "111");
  test_inverse_const_aux (g_logfile, "1001");
  test_inverse_const_aux (g_logfile, "1011");
  test_inverse_const_aux (g_logfile, "1101");
  test_inverse_const_aux (g_logfile, "1111");
  test_inverse_const_aux (g_logfile, "01010101010101010101010101010101");
}

static void
generate_consts_from_3vl_const (const char *const_3vl, BtorCharPtrStack *stack)
{
  const char *p;
  char *temp, *cur;
  int len, i, num_elements, pos;

  assert (const_3vl != NULL);
  assert (stack != NULL);
  assert (BTOR_EMPTY_STACK (*stack));
  len = (int) strlen (const_3vl);
  assert (len > 0);

  p = const_3vl;
  assert (*p == '0' || *p == '1' || *p == 'x');

  if (*p == '0' || *p == 'x')
  {
    temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
    *temp     = '0';
    temp[len] = '\0';
    BTOR_PUSH_STACK (g_mm, *stack, temp);
  }
  if (*p == '1' || *p == 'x')
  {
    temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
    *temp     = '1';
    temp[len] = '\0';
    BTOR_PUSH_STACK (g_mm, *stack, temp);
  }

  assert (!BTOR_EMPTY_STACK (*stack));
  for (p = const_3vl + 1; *p; p++)
  {
    assert (*p == '0' || *p == '1' || *p == 'x');

    pos          = p - const_3vl;
    num_elements = BTOR_COUNT_STACK (*stack);

    if (*p != 'x')
    {
      for (i = 0; i < num_elements; i++)
      {
        cur = stack->start[i];
        if (*p != 'x') cur[pos] = *p;
      }
    }
    else
    {
      for (i = 0; i < num_elements; i++)
      {
        cur       = stack->start[i];
        temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
        temp[len] = '\0';
        strncpy (temp, cur, pos);
        cur[pos]  = '0';
        temp[pos] = '1';
        BTOR_PUSH_STACK (g_mm, *stack, temp);
      }
    }
  }
}

static int
strcmp_qsort (const void *a, const void *b)
{
  return strcmp (*((char **) a), *((char **) b));
}

static void
test_generate_concrete_consts_from_3vl_const (void)
{
  int i = 0;
  BtorCharPtrStack stack;

  BTOR_INIT_STACK (stack);
  generate_consts_from_3vl_const ("1001", &stack);
  assert (BTOR_COUNT_STACK (stack) == 1);
  assert (strcmp (stack.start[0], "1001") == 0);
  btor_freestr (g_mm, stack.start[0]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("x001", &stack);
  assert (BTOR_COUNT_STACK (stack) == 2);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0001") == 0);
  assert (strcmp (stack.start[1], "1001") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("0x01", &stack);
  assert (BTOR_COUNT_STACK (stack) == 2);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0001") == 0);
  assert (strcmp (stack.start[1], "0101") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("11x1", &stack);
  assert (BTOR_COUNT_STACK (stack) == 2);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "1101") == 0);
  assert (strcmp (stack.start[1], "1111") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("100x", &stack);
  assert (BTOR_COUNT_STACK (stack) == 2);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "1000") == 0);
  assert (strcmp (stack.start[1], "1001") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("x00x", &stack);
  assert (BTOR_COUNT_STACK (stack) == 4);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0000") == 0);
  assert (strcmp (stack.start[1], "0001") == 0);
  assert (strcmp (stack.start[2], "1000") == 0);
  assert (strcmp (stack.start[3], "1001") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("0xx1", &stack);
  assert (BTOR_COUNT_STACK (stack) == 4);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0001") == 0);
  assert (strcmp (stack.start[1], "0011") == 0);
  assert (strcmp (stack.start[2], "0101") == 0);
  assert (strcmp (stack.start[3], "0111") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("xx0x", &stack);
  assert (BTOR_COUNT_STACK (stack) == 8);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0000") == 0);
  assert (strcmp (stack.start[1], "0001") == 0);
  assert (strcmp (stack.start[2], "0100") == 0);
  assert (strcmp (stack.start[3], "0101") == 0);
  assert (strcmp (stack.start[4], "1000") == 0);
  assert (strcmp (stack.start[5], "1001") == 0);
  assert (strcmp (stack.start[6], "1100") == 0);
  assert (strcmp (stack.start[7], "1101") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_consts_from_3vl_const ("xxxx", &stack);
  assert (BTOR_COUNT_STACK (stack) == 16);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0000") == 0);
  assert (strcmp (stack.start[1], "0001") == 0);
  assert (strcmp (stack.start[2], "0010") == 0);
  assert (strcmp (stack.start[3], "0011") == 0);
  assert (strcmp (stack.start[4], "0100") == 0);
  assert (strcmp (stack.start[5], "0101") == 0);
  assert (strcmp (stack.start[6], "0110") == 0);
  assert (strcmp (stack.start[7], "0111") == 0);
  assert (strcmp (stack.start[8], "1000") == 0);
  assert (strcmp (stack.start[9], "1001") == 0);
  assert (strcmp (stack.start[10], "1010") == 0);
  assert (strcmp (stack.start[11], "1011") == 0);
  assert (strcmp (stack.start[12], "1100") == 0);
  assert (strcmp (stack.start[13], "1101") == 0);
  assert (strcmp (stack.start[14], "1110") == 0);
  assert (strcmp (stack.start[15], "1111") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);

  BTOR_RELEASE_STACK (g_mm, stack);
}

static void
generate_all_3vl_consts (int len, BtorCharPtrStack *stack)
{
  char *temp, *cur;
  int i, j, num_elements;

  assert (len > 0);
  assert (stack != NULL);
  assert (BTOR_EMPTY_STACK (*stack));

  temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
  *temp     = '0';
  temp[len] = '\0';
  BTOR_PUSH_STACK (g_mm, *stack, temp);

  temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
  *temp     = '1';
  temp[len] = '\0';
  BTOR_PUSH_STACK (g_mm, *stack, temp);

  temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
  *temp     = 'x';
  temp[len] = '\0';
  BTOR_PUSH_STACK (g_mm, *stack, temp);

  assert (!BTOR_EMPTY_STACK (*stack));
  for (i = 1; i < len; i++)
  {
    num_elements = BTOR_COUNT_STACK (*stack);
    for (j = 0; j < num_elements; j++)
    {
      cur = stack->start[j];

      temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
      temp[len] = '\0';
      strncpy (temp, cur, i);
      temp[i] = '0';
      BTOR_PUSH_STACK (g_mm, *stack, temp);

      temp      = (char *) btor_malloc (g_mm, sizeof (char) * (len + 1));
      temp[len] = '\0';
      strncpy (temp, cur, i);
      temp[i] = '1';
      BTOR_PUSH_STACK (g_mm, *stack, temp);

      cur[i] = 'x';
    }
  }
}

static void
test_generate_all_3vl_consts (void)
{
  int i;
  BtorCharPtrStack stack;
  BTOR_INIT_STACK (stack);

  generate_all_3vl_consts (1, &stack);
  assert (BTOR_COUNT_STACK (stack) == 3);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "0") == 0);
  assert (strcmp (stack.start[1], "1") == 0);
  assert (strcmp (stack.start[2], "x") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_all_3vl_consts (2, &stack);
  assert (BTOR_COUNT_STACK (stack) == 9);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "00") == 0);
  assert (strcmp (stack.start[1], "01") == 0);
  assert (strcmp (stack.start[2], "0x") == 0);
  assert (strcmp (stack.start[3], "10") == 0);
  assert (strcmp (stack.start[4], "11") == 0);
  assert (strcmp (stack.start[5], "1x") == 0);
  assert (strcmp (stack.start[6], "x0") == 0);
  assert (strcmp (stack.start[7], "x1") == 0);
  assert (strcmp (stack.start[8], "xx") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);
  BTOR_RESET_STACK (stack);

  generate_all_3vl_consts (3, &stack);
  assert (BTOR_COUNT_STACK (stack) == 27);
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (char *), strcmp_qsort);
  assert (strcmp (stack.start[0], "000") == 0);
  assert (strcmp (stack.start[1], "001") == 0);
  assert (strcmp (stack.start[2], "00x") == 0);
  assert (strcmp (stack.start[3], "010") == 0);
  assert (strcmp (stack.start[4], "011") == 0);
  assert (strcmp (stack.start[5], "01x") == 0);
  assert (strcmp (stack.start[6], "0x0") == 0);
  assert (strcmp (stack.start[7], "0x1") == 0);
  assert (strcmp (stack.start[8], "0xx") == 0);
  assert (strcmp (stack.start[9], "100") == 0);
  assert (strcmp (stack.start[10], "101") == 0);
  assert (strcmp (stack.start[11], "10x") == 0);
  assert (strcmp (stack.start[12], "110") == 0);
  assert (strcmp (stack.start[13], "111") == 0);
  assert (strcmp (stack.start[14], "11x") == 0);
  assert (strcmp (stack.start[15], "1x0") == 0);
  assert (strcmp (stack.start[16], "1x1") == 0);
  assert (strcmp (stack.start[17], "1xx") == 0);
  assert (strcmp (stack.start[18], "x00") == 0);
  assert (strcmp (stack.start[19], "x01") == 0);
  assert (strcmp (stack.start[20], "x0x") == 0);
  assert (strcmp (stack.start[21], "x10") == 0);
  assert (strcmp (stack.start[22], "x11") == 0);
  assert (strcmp (stack.start[23], "x1x") == 0);
  assert (strcmp (stack.start[24], "xx0") == 0);
  assert (strcmp (stack.start[25], "xx1") == 0);
  assert (strcmp (stack.start[26], "xxx") == 0);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    btor_freestr (g_mm, stack.start[i]);

  BTOR_RELEASE_STACK (g_mm, stack);
}

static void
test_x_const_3vl (void)
{
  char *result = btor_x_const_3vl (g_mm, 1);
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 2);
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 3);
  assert (strcmp (result, "xxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 4);
  assert (strcmp (result, "xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 5);
  assert (strcmp (result, "xxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 8);
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 16);
  assert (strcmp (result, "xxxxxxxxxxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_x_const_3vl (g_mm, 32);
  assert (strcmp (result, "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx") == 0);
  btor_delete_const (g_mm, result);
}

static void
check_const_3vl_compatible (const char *c_3vl, const char *c)
{
  int i, len;

  assert (c_3vl != NULL);
  assert (c != NULL);
  len = (int) strlen (c);
  assert (len == (int) strlen (c));

  for (i = 0; i < len; i++)
  {
    assert (c_3vl[i] == '0' || c_3vl[i] == '1' || c_3vl[i] == 'x');
    assert (c[i] == '0' || c[i] == '1');
    assert (!(c_3vl[i] == '0' && c[i] == '1'));
    assert (!(c_3vl[i] == '1' && c[i] == '0'));
  }
}

static void
test_not_const_3vl (void)
{
  char *result = btor_not_const_3vl (g_mm, "x01x");
  assert (strcmp (result, "x10x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_not_const_3vl (g_mm, "1xx0");
  assert (strcmp (result, "0xx1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_not_const_3vl (g_mm, "xxx0");
  assert (strcmp (result, "xxx1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_not_const_3vl (g_mm, "x1xx");
  assert (strcmp (result, "x0xx") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_not_const_3vl_exhaustive_range (void)
{
  BtorCharPtrStack consts_3vl, consts_concrete;
  char *const_3vl, *const_concrete, *not_const_3vl, *not_const_concrete;
  int i;

  BTOR_INIT_STACK (consts_3vl);
  BTOR_INIT_STACK (consts_concrete);
  for (i = BTOR_TEST_CONST_3VL_LOW; i <= BTOR_TEST_CONST_3VL_HIGH; i++)
  {
    assert (BTOR_EMPTY_STACK (consts_3vl));
    generate_all_3vl_consts (i, &consts_3vl);
    while (!BTOR_EMPTY_STACK (consts_3vl))
    {
      const_3vl = BTOR_POP_STACK (consts_3vl);
      assert (BTOR_EMPTY_STACK (consts_concrete));
      generate_consts_from_3vl_const (const_3vl, &consts_concrete);
      not_const_3vl = btor_not_const_3vl (g_mm, const_3vl);
      while (!BTOR_EMPTY_STACK (consts_concrete))
      {
        const_concrete     = BTOR_POP_STACK (consts_concrete);
        not_const_concrete = btor_not_const (g_mm, const_concrete);
        check_const_3vl_compatible (not_const_3vl, not_const_concrete);
        btor_freestr (g_mm, const_concrete);
        btor_freestr (g_mm, not_const_concrete);
      }
      btor_freestr (g_mm, const_3vl);
      btor_freestr (g_mm, not_const_3vl);
    }
  }
  BTOR_RELEASE_STACK (g_mm, consts_3vl);
  BTOR_RELEASE_STACK (g_mm, consts_concrete);
}

static void
test_get_num_leading_zeros_const (void)
{
  assert (btor_get_num_leading_zeros_const (g_mm, "0010") == 2);
  assert (btor_get_num_leading_zeros_const (g_mm, "x010") == 0);
  assert (btor_get_num_leading_zeros_const (g_mm, "1010") == 0);
  assert (btor_get_num_leading_zeros_const (g_mm, "1010") == 0);
  assert (btor_get_num_leading_zeros_const (g_mm, "0x10") == 1);
  assert (btor_get_num_leading_zeros_const (g_mm, "0110") == 1);
  assert (btor_get_num_leading_zeros_const (g_mm, "0000") == 4);
  assert (btor_get_num_leading_zeros_const (g_mm, "0") == 1);
}

static void
test_get_num_leading_ones_const (void)
{
  assert (btor_get_num_leading_ones_const (g_mm, "1101") == 2);
  assert (btor_get_num_leading_ones_const (g_mm, "x101") == 0);
  assert (btor_get_num_leading_ones_const (g_mm, "0101") == 0);
  assert (btor_get_num_leading_ones_const (g_mm, "0101") == 0);
  assert (btor_get_num_leading_ones_const (g_mm, "1x01") == 1);
  assert (btor_get_num_leading_ones_const (g_mm, "1001") == 1);
  assert (btor_get_num_leading_ones_const (g_mm, "1111") == 4);
  assert (btor_get_num_leading_ones_const (g_mm, "1") == 1);
}

void
run_const_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (zero_const);
  BTOR_RUN_TEST (one_const);
  BTOR_RUN_TEST (ones_const);
  BTOR_RUN_TEST (is_zero_const);
  BTOR_RUN_TEST (is_one_const);
  BTOR_RUN_TEST (is_ones_const);
  BTOR_RUN_TEST (is_special_const);
  BTOR_RUN_TEST (is_small_positive_int_const);
  BTOR_RUN_TEST (int_to_const);
  BTOR_RUN_TEST (unsigned_to_const);
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
  BTOR_RUN_TEST (generate_all_3vl_consts);
  BTOR_RUN_TEST (x_const_3vl);
  BTOR_RUN_TEST (not_const_3vl);
  BTOR_RUN_TEST (not_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (get_num_leading_zeros_const);
  BTOR_RUN_TEST (get_num_leading_ones_const);
  BTOR_RUN_TEST (generate_concrete_consts_from_3vl_const);
}

void
finish_const_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

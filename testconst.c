/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2010  Robert Daniel Brummayer, Armin Biere
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
  fprintf (file, "1 / %s = %s mod 2^%ld\n", c, i, (long) strlen (c));
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
test_invert_const_3vl (void)
{
  char x_const[5] = {'0', '1', 'x', '0', '\0'};
  btor_invert_const_3vl (g_mm, x_const);
  assert (strcmp (x_const, "10x1") == 0);

  btor_invert_const_3vl (g_mm, x_const);
  assert (strcmp (x_const, "01x0") == 0);

  x_const[0] = 'x';
  btor_invert_const_3vl (g_mm, x_const);
  assert (strcmp (x_const, "x0x1") == 0);

  btor_invert_const_3vl (g_mm, x_const);
  assert (strcmp (x_const, "x1x0") == 0);
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
test_invert_const_3vl_exhaustive_range (void)
{
  BtorCharPtrStack consts_3vl, consts_concrete;
  char *const_3vl, *const_concrete;
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
      btor_invert_const_3vl (g_mm, const_3vl);
      while (!BTOR_EMPTY_STACK (consts_concrete))
      {
        const_concrete = BTOR_POP_STACK (consts_concrete);
        btor_invert_const (g_mm, const_concrete);
        check_const_3vl_compatible (const_3vl, const_concrete);
        btor_freestr (g_mm, const_concrete);
      }
      btor_freestr (g_mm, const_3vl);
    }
  }
  BTOR_RELEASE_STACK (g_mm, consts_3vl);
  BTOR_RELEASE_STACK (g_mm, consts_concrete);
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
check_binary_3vl_compatible (const char *result_3vl,
                             const BtorCharPtrStack *consts_a,
                             const BtorCharPtrStack *consts_b,
                             char *(*f) (BtorMemMgr *,
                                         const char *,
                                         const char *) )
{
  char *a, *b, *result;
  int i, j;

  assert (result_3vl != NULL);
  assert (consts_a != NULL);
  assert (consts_b != NULL);
  assert (f != NULL);
  assert (!BTOR_EMPTY_STACK (*consts_a));
  assert (!BTOR_EMPTY_STACK (*consts_b));

  for (i = 0; i < BTOR_COUNT_STACK (*consts_a); i++)
  {
    a = consts_a->start[i];
    for (j = 0; j < BTOR_COUNT_STACK (*consts_b); j++)
    {
      b      = consts_b->start[j];
      result = f (g_mm, a, b);
      check_const_3vl_compatible (result_3vl, result);
      btor_freestr (g_mm, result);
    }
  }
}

static void
test_binary_const_3vl_exhaustive_range (
    char *(*f_3vl) (BtorMemMgr *, const char *, const char *),
    char *(*f) (BtorMemMgr *, const char *, const char *) )
{
  BtorCharPtrStack consts_3vl_a, consts_3vl_b, consts_a, consts_b;
  char *const_3vl_a, *const_3vl_b, *result_3vl;
  int i;

  assert (f_3vl != NULL);
  assert (f != NULL);

  BTOR_INIT_STACK (consts_3vl_a);
  BTOR_INIT_STACK (consts_3vl_b);
  BTOR_INIT_STACK (consts_a);
  BTOR_INIT_STACK (consts_b);

  for (i = BTOR_TEST_CONST_3VL_LOW; i <= BTOR_TEST_CONST_3VL_HIGH; i++)
  {
    if ((f_3vl == btor_sll_const_3vl || f_3vl == btor_srl_const_3vl)
        && (i == 1 || !btor_is_power_of_2_util (i)))
      continue;

    assert (BTOR_EMPTY_STACK (consts_3vl_a));
    generate_all_3vl_consts (i, &consts_3vl_a);
    while (!BTOR_EMPTY_STACK (consts_3vl_a))
    {
      const_3vl_a = BTOR_POP_STACK (consts_3vl_a);
      assert (BTOR_EMPTY_STACK (consts_a));
      generate_consts_from_3vl_const (const_3vl_a, &consts_a);
      assert (BTOR_EMPTY_STACK (consts_3vl_b));

      if (f_3vl == btor_sll_const_3vl || f_3vl == btor_srl_const_3vl)
        generate_all_3vl_consts (btor_log_2_util (i), &consts_3vl_b);
      else
        generate_all_3vl_consts (i, &consts_3vl_b);

      while (!BTOR_EMPTY_STACK (consts_3vl_b))
      {
        const_3vl_b = BTOR_POP_STACK (consts_3vl_b);
        result_3vl  = f_3vl (g_mm, const_3vl_a, const_3vl_b);
        assert (BTOR_EMPTY_STACK (consts_b));
        generate_consts_from_3vl_const (const_3vl_b, &consts_b);
        check_binary_3vl_compatible (result_3vl, &consts_a, &consts_b, f);
        btor_freestr (g_mm, result_3vl);
        btor_freestr (g_mm, const_3vl_b);
        while (!BTOR_EMPTY_STACK (consts_b))
          btor_freestr (g_mm, BTOR_POP_STACK (consts_b));
      }
      btor_freestr (g_mm, const_3vl_a);

      while (!BTOR_EMPTY_STACK (consts_a))
        btor_freestr (g_mm, BTOR_POP_STACK (consts_a));
    }
  }

  BTOR_RELEASE_STACK (g_mm, consts_3vl_a);
  BTOR_RELEASE_STACK (g_mm, consts_3vl_b);
  BTOR_RELEASE_STACK (g_mm, consts_a);
  BTOR_RELEASE_STACK (g_mm, consts_b);
}

static void
test_and_const_3vl (void)
{
  char *result = btor_and_const_3vl (g_mm, "10", "1x");
  assert (strcmp (result, "10") == 0);
  btor_delete_const (g_mm, result);

  result = btor_and_const_3vl (g_mm, "10", "xx");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_and_const_3vl (g_mm, "10", "x1");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_and_const_3vl (g_mm, "00", "x1");
  assert (strcmp (result, "00") == 0);
  btor_delete_const (g_mm, result);

  result = btor_and_const_3vl (g_mm, "00", "xx");
  assert (strcmp (result, "00") == 0);
  btor_delete_const (g_mm, result);

  result = btor_and_const_3vl (g_mm, "11", "xx");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_and_const_3vl (g_mm, "11", "x0");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_and_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_and_const_3vl, btor_and_const);
}

static void
test_eq_const_3vl (void)
{
  char *result = btor_eq_const_3vl (g_mm, "10", "0x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_eq_const_3vl (g_mm, "10", "xx");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_eq_const_3vl (g_mm, "10", "x1");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_eq_const_3vl (g_mm, "00", "x1");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_eq_const_3vl (g_mm, "00", "xx");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_eq_const_3vl (g_mm, "1x", "1x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_eq_const_3vl (g_mm, "11", "x0");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_eq_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_eq_const_3vl, btor_eq_const);
}

static void
test_ult_const_3vl (void)
{
  char *result = btor_ult_const_3vl (g_mm, "00", "0x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "01", "0x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "10", "0x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "11", "0x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x", "0x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x", "0x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x0", "0x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x1", "0x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "00", "1x");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "01", "1x");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "10", "1x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "11", "1x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x", "1x");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x", "1x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x0", "1x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x1", "1x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "00", "x0");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "01", "x0");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "10", "x0");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "11", "x0");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x", "x0");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x", "x0");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x0", "x0");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x1", "x0");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "00", "x1");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "01", "x1");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "10", "x1");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "11", "x1");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x", "x1");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x", "x1");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x0", "x1");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "x1", "x1");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x1", "x10");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0xx1", "x1x0");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "01x1", "x110");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x10", "x100");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x0", "x11");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x00", "x101");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x01", "x111");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x00", "x101");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "0x01", "x110");
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x0", "x01");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x0x", "x01x");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x01", "x011");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x00", "x010");
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x1", "x00");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x10", "x000");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x11", "x001");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_ult_const_3vl (g_mm, "1x1x", "x00x");
  assert (strcmp (result, "0") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_ult_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_ult_const_3vl, btor_ult_const);
}

static void
test_add_const_3vl (void)
{
  char *result = btor_add_const_3vl (g_mm, "00", "0x");
  assert (strcmp (result, "0x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "01", "0x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "10", "0x");
  assert (strcmp (result, "1x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "11", "0x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "0x", "0x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "1x", "0x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x0", "0x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x1", "0x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "00", "1x");
  assert (strcmp (result, "1x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "01", "1x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "10", "1x");
  assert (strcmp (result, "0x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "11", "1x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "0x", "1x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "1x", "1x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x0", "1x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x1", "1x");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "00", "x0");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "01", "x0");
  assert (strcmp (result, "x1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "10", "x0");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "11", "x0");
  assert (strcmp (result, "x1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "0x", "x0");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "1x", "x0");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x0", "x0");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x1", "x0");
  assert (strcmp (result, "x1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "00", "x1");
  assert (strcmp (result, "x1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "01", "x1");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "10", "x1");
  assert (strcmp (result, "x1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "11", "x1");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "0x", "x1");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "1x", "x1");
  assert (strcmp (result, "xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x0", "x1");
  assert (strcmp (result, "x1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_add_const_3vl (g_mm, "x1", "x1");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_add_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_add_const_3vl, btor_add_const);
}

static void
test_sll_const_3vl (void)
{
  char *result = btor_sll_const_3vl (g_mm, "10101001", "00x");
  assert (strcmp (result, "xxxxx0xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "01x");
  assert (strcmp (result, "xxxxxx00") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "10x");
  assert (strcmp (result, "xxxx0000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "11x");
  assert (strcmp (result, "xx000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "0x0");
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "0x1");
  assert (strcmp (result, "xxxxxxx0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "1x0");
  assert (strcmp (result, "xxxx0000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "1x1");
  assert (strcmp (result, "xxx00000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "1xx");
  assert (strcmp (result, "xxxx0000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "xxx");
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "xx0");
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "10101001", "xx1");
  assert (strcmp (result, "xxxxxxx0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "xxxxxxxx", "111");
  assert (strcmp (result, "x0000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "xxx10101", "010");
  assert (strcmp (result, "x1010100") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "101xx001", "011");
  assert (strcmp (result, "xx001000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "xx010111", "111");
  assert (strcmp (result, "10000000") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "111001xx", "00x");
  assert (strcmp (result, "11x0xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "111100xx", "0x1");
  assert (strcmp (result, "1xxxxxx0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "11111111", "xxx");
  assert (strcmp (result, "1xxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_sll_const_3vl (g_mm, "0xxxxxx1", "1xx");
  assert (strcmp (result, "xxxx0000") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_sll_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_sll_const_3vl, btor_sll_const);
}

static void
test_srl_const_3vl (void)
{
  char *result = btor_srl_const_3vl (g_mm, "10101001", "00x");
  assert (strcmp (result, "xxxxxx0x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "01x");
  assert (strcmp (result, "00xxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "10x");
  assert (strcmp (result, "0000xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "11x");
  assert (strcmp (result, "000000xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "0x0");
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "0x1");
  assert (strcmp (result, "0xxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "1x0");
  assert (strcmp (result, "0000xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "1x1");
  assert (strcmp (result, "00000xxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "1xx");
  assert (strcmp (result, "0000xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "xxx");
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "xx0");
  assert (strcmp (result, "xxxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "10101001", "xx1");
  assert (strcmp (result, "0xxxxxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "xxxxxxxx", "111");
  assert (strcmp (result, "0000000x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "xxx10101", "010");
  assert (strcmp (result, "00xxx101") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "101xx001", "011");
  assert (strcmp (result, "000101xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "xx010111", "111");
  assert (strcmp (result, "0000000x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "111001xx", "00x");
  assert (strcmp (result, "x11x0xxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "111100xx", "0x1");
  assert (strcmp (result, "0xx1xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "11111111", "xxx");
  assert (strcmp (result, "xxxxxxx1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_srl_const_3vl (g_mm, "0xxxxxx1", "1xx");
  assert (strcmp (result, "0000xxxx") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_srl_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_srl_const_3vl, btor_srl_const);
}

static void
test_mul_const_3vl (void)
{
  char *result = btor_mul_const_3vl (g_mm, "x0", "01");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);

  result = btor_mul_const_3vl (g_mm, "x0", "00");
  assert (strcmp (result, "00") == 0);
  btor_delete_const (g_mm, result);

  result = btor_mul_const_3vl (g_mm, "x0", "1x");
  assert (strcmp (result, "x0") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_mul_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_mul_const_3vl, btor_mul_const);
}

static void
test_concat_const_3vl (void)
{
  char *result = btor_concat_const_3vl (g_mm, "x00x", "x11x");
  assert (strcmp (result, "x00xx11x") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_concat_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_concat_const_3vl,
                                          btor_concat_const);
}

static void
test_udiv_const_3vl (void)
{
  char *result = btor_udiv_const_3vl (g_mm, "0000", "000x");
  assert (strcmp (result, "xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_udiv_const_3vl (g_mm, "00xx", "xxx1");
  assert (strcmp (result, "00xx") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_udiv_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_udiv_const_3vl, btor_udiv_const);
}

static void
test_urem_const_3vl (void)
{
  char *result = btor_urem_const_3vl (g_mm, "0000", "000x");
  assert (strcmp (result, "xxxx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_urem_const_3vl (g_mm, "00xx", "xxx1");
  assert (strcmp (result, "00xx") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_urem_const_3vl_exhaustive_range (void)
{
  test_binary_const_3vl_exhaustive_range (btor_urem_const_3vl, btor_urem_const);
}

static void
test_slice_const_3vl (void)
{
  char *result = btor_slice_const_3vl (g_mm, "x00x", 3, 0);
  assert (strcmp (result, "x00x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_slice_const_3vl (g_mm, "100x", 3, 3);
  assert (strcmp (result, "1") == 0);
  btor_delete_const (g_mm, result);

  result = btor_slice_const_3vl (g_mm, "100x", 3, 2);
  assert (strcmp (result, "10") == 0);
  btor_delete_const (g_mm, result);

  result = btor_slice_const_3vl (g_mm, "100x", 0, 0);
  assert (strcmp (result, "x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_slice_const_3vl (g_mm, "100x", 2, 0);
  assert (strcmp (result, "00x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_slice_const_3vl (g_mm, "100x", 3, 1);
  assert (strcmp (result, "100") == 0);
  btor_delete_const (g_mm, result);
}

static void
check_cond_const_3vl_compatible (const char *result_3vl,
                                 const BtorCharPtrStack *consts_a,
                                 const BtorCharPtrStack *consts_b,
                                 const BtorCharPtrStack *consts_c)
{
  char *a, *b, *c, *result;
  int i, j, k;

  assert (result_3vl != NULL);
  assert (consts_a != NULL);
  assert (consts_b != NULL);
  assert (consts_c != NULL);
  assert (!BTOR_EMPTY_STACK (*consts_a));
  assert (!BTOR_EMPTY_STACK (*consts_b));
  assert (!BTOR_EMPTY_STACK (*consts_c));

  for (i = 0; i < BTOR_COUNT_STACK (*consts_a); i++)
  {
    a = consts_a->start[i];
    assert (*a == '0' || *a == '1');
    for (j = 0; j < BTOR_COUNT_STACK (*consts_b); j++)
    {
      b = consts_b->start[j];
      for (k = 0; k < BTOR_COUNT_STACK (*consts_c); k++)
      {
        c = consts_c->start[k];
        if (*a == '1')
          result = b;
        else
          result = c;
        check_const_3vl_compatible (result_3vl, result);
      }
    }
  }
}

static void
test_cond_const_3vl (void)
{
  char *result = btor_cond_const_3vl (g_mm, "1", "100x", "x011");
  assert (strcmp (result, "100x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "0", "100x", "x011");
  assert (strcmp (result, "x011") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "x", "100x", "x011");
  assert (strcmp (result, "x0xx") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "x", "1001", "1001");
  assert (strcmp (result, "1001") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "x", "1000", "1001");
  assert (strcmp (result, "100x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "x", "100x", "1001");
  assert (strcmp (result, "100x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "x", "1000", "100x");
  assert (strcmp (result, "100x") == 0);
  btor_delete_const (g_mm, result);

  result = btor_cond_const_3vl (g_mm, "x", "100x", "100x");
  assert (strcmp (result, "100x") == 0);
  btor_delete_const (g_mm, result);
}

static void
test_cond_const_3vl_exhaustive_range ()
{
  BtorCharPtrStack consts_3vl_a, consts_3vl_b, consts_3vl_c;
  BtorCharPtrStack consts_a, consts_b, consts_c;
  char *const_3vl_a, *const_3vl_b, *const_3vl_c, *result_3vl;
  int i;

  BTOR_INIT_STACK (consts_3vl_a);
  BTOR_INIT_STACK (consts_3vl_b);
  BTOR_INIT_STACK (consts_3vl_c);
  BTOR_INIT_STACK (consts_a);
  BTOR_INIT_STACK (consts_b);
  BTOR_INIT_STACK (consts_c);

  for (i = BTOR_TEST_CONST_3VL_LOW; i <= BTOR_TEST_CONST_3VL_HIGH; i++)
  {
    assert (BTOR_EMPTY_STACK (consts_3vl_a));
    generate_all_3vl_consts (1, &consts_3vl_a);
    while (!BTOR_EMPTY_STACK (consts_3vl_a))
    {
      const_3vl_a = BTOR_POP_STACK (consts_3vl_a);
      assert (BTOR_EMPTY_STACK (consts_a));
      generate_consts_from_3vl_const (const_3vl_a, &consts_a);
      assert (BTOR_EMPTY_STACK (consts_3vl_b));
      generate_all_3vl_consts (i, &consts_3vl_b);
      while (!BTOR_EMPTY_STACK (consts_3vl_b))
      {
        const_3vl_b = BTOR_POP_STACK (consts_3vl_b);
        assert (BTOR_EMPTY_STACK (consts_b));
        generate_consts_from_3vl_const (const_3vl_b, &consts_b);
        assert (BTOR_EMPTY_STACK (consts_3vl_c));
        generate_all_3vl_consts (i, &consts_3vl_c);
        while (!BTOR_EMPTY_STACK (consts_3vl_c))
        {
          const_3vl_c = BTOR_POP_STACK (consts_3vl_c);
          result_3vl =
              btor_cond_const_3vl (g_mm, const_3vl_a, const_3vl_b, const_3vl_c);
          assert (BTOR_EMPTY_STACK (consts_c));
          generate_consts_from_3vl_const (const_3vl_c, &consts_c);
          check_cond_const_3vl_compatible (
              result_3vl, &consts_a, &consts_b, &consts_c);
          btor_freestr (g_mm, result_3vl);
          btor_freestr (g_mm, const_3vl_c);
          while (!BTOR_EMPTY_STACK (consts_c))
            btor_freestr (g_mm, BTOR_POP_STACK (consts_c));
        }
        btor_freestr (g_mm, const_3vl_b);

        while (!BTOR_EMPTY_STACK (consts_b))
          btor_freestr (g_mm, BTOR_POP_STACK (consts_b));
      }

      btor_freestr (g_mm, const_3vl_a);
      while (!BTOR_EMPTY_STACK (consts_a))
        btor_freestr (g_mm, BTOR_POP_STACK (consts_a));
    }
  }

  BTOR_RELEASE_STACK (g_mm, consts_3vl_a);
  BTOR_RELEASE_STACK (g_mm, consts_3vl_b);
  BTOR_RELEASE_STACK (g_mm, consts_3vl_c);
  BTOR_RELEASE_STACK (g_mm, consts_a);
  BTOR_RELEASE_STACK (g_mm, consts_b);
  BTOR_RELEASE_STACK (g_mm, consts_c);
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
  BTOR_RUN_TEST (generate_concrete_consts_from_3vl_const);
  BTOR_RUN_TEST (generate_all_3vl_consts);
  BTOR_RUN_TEST (x_const_3vl);
  BTOR_RUN_TEST (invert_const_3vl);
  BTOR_RUN_TEST (invert_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (not_const_3vl);
  BTOR_RUN_TEST (not_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (and_const_3vl);
  BTOR_RUN_TEST (and_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (eq_const_3vl);
  BTOR_RUN_TEST (eq_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (ult_const_3vl);
  BTOR_RUN_TEST (ult_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (add_const_3vl);
  BTOR_RUN_TEST (add_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (sll_const_3vl);
  BTOR_RUN_TEST (sll_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (srl_const_3vl);
  BTOR_RUN_TEST (srl_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (mul_const_3vl);
  BTOR_RUN_TEST (mul_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (concat_const_3vl);
  BTOR_RUN_TEST (concat_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (udiv_const_3vl);
  BTOR_RUN_TEST (udiv_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (urem_const_3vl);
  BTOR_RUN_TEST (urem_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (slice_const_3vl);
  BTOR_RUN_TEST (cond_const_3vl);
  BTOR_RUN_TEST (cond_const_3vl_exhaustive_range);
  BTOR_RUN_TEST (get_num_leading_zeros_const);
  BTOR_RUN_TEST (get_num_leading_ones_const);
}

void
finish_const_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}

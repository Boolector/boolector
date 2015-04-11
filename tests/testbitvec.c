/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Mathias Preiner.
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testbitvec.h"
#include "btorbitvec.h"
#include "btorconst.h"
#include "btorcore.h"
#include "testrunner.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_BITVEC_NUM_BITS 65
#define BTOR_TEST_BITVEC_TESTS 100000
#define BTOR_TEST_BITVEC_PERF_TESTS 1000000

static Btor *g_btor;
static BtorMemMgr *g_mm;

void
init_bitvec_tests (void)
{
  g_btor = btor_new_btor ();
  g_mm   = btor_get_mem_mgr_btor (g_btor);
}

static void
test_new_bitvec (void)
{
  BitVector *bv;

  bv = btor_new_bv (g_mm, BTOR_BV_TYPE_BW);
  assert (bv->len == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_new_bv (g_mm, BTOR_BV_TYPE_BW - 1);
  assert (bv->len == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_new_bv (g_mm, BTOR_BV_TYPE_BW + 1);
  assert (bv->len == 2);
  btor_free_bv (g_mm, bv);
}

static BitVector *
random_bv (int bw)
{
  int i;
  BitVector *res;
  res = btor_new_bv (g_mm, bw);

  for (i = 0; i < res->len; i++) res->bits[i] = (BTOR_BV_TYPE) rand ();

  res->bits[0] &= ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1)
                   >> (BTOR_BV_TYPE_BW - 1 - (res->width % BTOR_BV_TYPE_BW)));

  return res;
}

static void
unary_bitvec (char *(*const_func) (BtorMemMgr *, const char *),
              BitVector *(*bitvec_func) (BtorMemMgr *, BitVector *),
              int num_tests,
              int bit_width)
{
  int i;
  char *c_a, *c_res, *str;
  BitVector *a, *res;

  printf (" %d", bit_width);
  fflush (stdout);
  for (i = 0; i < num_tests; i++)
  {
    a     = random_bv (bit_width);
    res   = bitvec_func (g_mm, a);
    c_a   = btor_bv_to_char_bv (g_mm, a);
    c_res = const_func (g_mm, c_a);
    str   = btor_bv_to_char_bv (g_mm, res);

    assert (strlen (str) == strlen (c_res));
    assert (memcmp (c_res, str, strlen (str)) == 0);

    btor_freestr (g_mm, str);
    btor_delete_const (g_mm, c_res);
    btor_delete_const (g_mm, c_a);
    btor_free_bv (g_mm, res);
    btor_free_bv (g_mm, a);
  }
}

static void
slice_bitvec (int num_tests, int bit_width)
{
  int i, upper, lower;
  char *c_a, *c_res, *str;
  BitVector *a, *res;

  printf (" %d", bit_width);
  fflush (stdout);
  for (i = 0; i < num_tests; i++)
  {
    a     = random_bv (bit_width);
    lower = rand () % bit_width;
    upper = rand () % (bit_width - lower) + lower;
    assert (upper >= lower);
    assert (upper < bit_width);
    assert (lower < bit_width);

    res   = btor_slice_bv (g_mm, a, upper, lower);
    c_a   = btor_bv_to_char_bv (g_mm, a);
    c_res = btor_slice_const (g_mm, c_a, upper, lower);
    str   = btor_bv_to_char_bv (g_mm, res);

    assert (strlen (str) == strlen (c_res));
    assert (memcmp (c_res, str, strlen (str)) == 0);

    btor_freestr (g_mm, str);
    btor_delete_const (g_mm, c_res);
    btor_delete_const (g_mm, c_a);
    btor_free_bv (g_mm, res);
    btor_free_bv (g_mm, a);
  }
}

static void
shift_bitvec (char *(*const_func) (BtorMemMgr *, const char *, const char *),
              BitVector *(*bitvec_func) (BtorMemMgr *,
                                         BitVector *,
                                         BitVector *),
              int num_tests,
              int bit_width)
{
  int i;
  char *c_a, *c_b, *c_res, *str;
  BitVector *a, *b, *res;

  printf (" %d", bit_width);
  fflush (stdout);
  for (i = 0; i < num_tests; i++)
  {
    a   = random_bv (bit_width);
    b   = random_bv (btor_log_2_util (bit_width));
    res = bitvec_func (g_mm, a, b);

    c_a   = btor_bv_to_char_bv (g_mm, a);
    c_b   = btor_bv_to_char_bv (g_mm, b);
    c_res = const_func (g_mm, c_a, c_b);
    str   = btor_bv_to_char_bv (g_mm, res);

    assert (strlen (str) == strlen (c_res));
    assert (memcmp (c_res, str, strlen (str)) == 0);

    btor_freestr (g_mm, str);
    btor_delete_const (g_mm, c_res);
    btor_delete_const (g_mm, c_a);
    btor_delete_const (g_mm, c_b);
    btor_free_bv (g_mm, res);
    btor_free_bv (g_mm, a);
    btor_free_bv (g_mm, b);
  }
}

static void
shift_cont_bitvec (
    char *(*const_func) (BtorMemMgr *, const char *, const char *),
    BitVector *(*bitvec_func) (BtorMemMgr *, BitVector *, BitVector *),
    int bit_width)
{
  int i, shift_width;
  char *c_a, *c_b, *c_res, *str;
  BitVector *a, *b, *res;

  a           = random_bv (bit_width);
  shift_width = btor_log_2_util (bit_width);
  for (i = 0; i < bit_width; i++)
  {
    b   = btor_uint64_to_bv (g_mm, (uint64_t) i, shift_width);
    res = bitvec_func (g_mm, a, b);

    c_a   = btor_bv_to_char_bv (g_mm, a);
    c_b   = btor_bv_to_char_bv (g_mm, b);
    c_res = const_func (g_mm, c_a, c_b);
    str   = btor_bv_to_char_bv (g_mm, res);

    assert (strlen (str) == strlen (c_res));
    assert (memcmp (c_res, str, strlen (str)) == 0);

    btor_freestr (g_mm, str);
    btor_delete_const (g_mm, c_res);
    btor_delete_const (g_mm, c_a);
    btor_delete_const (g_mm, c_b);
    btor_free_bv (g_mm, res);
    btor_free_bv (g_mm, b);
  }
  btor_free_bv (g_mm, a);
}

static void
binary_bitvec (char *(*const_func) (BtorMemMgr *, const char *, const char *),
               BitVector *(*bitvec_func) (BtorMemMgr *,
                                          BitVector *,
                                          BitVector *),
               int num_tests,
               int bit_width)
{
  assert (const_func);
  assert (bitvec_func);

  int i;
  char *c_a, *c_b, *c_res, *str;
  BitVector *a, *b, *res;

  printf (" %d", bit_width);
  fflush (stdout);
  for (i = 0; i < num_tests; i++)
  {
    a     = random_bv (bit_width);
    c_a   = btor_bv_to_char_bv (g_mm, a);
    b     = random_bv (bit_width);
    c_b   = btor_bv_to_char_bv (g_mm, b);
    c_res = const_func (g_mm, c_a, c_b);
    res   = bitvec_func (g_mm, a, b);
    str   = btor_bv_to_char_bv (g_mm, res);

    assert (strlen (str) == strlen (c_res));
    assert (memcmp (c_res, str, strlen (str)) == 0);

    btor_freestr (g_mm, str);
    btor_delete_const (g_mm, c_b);
    btor_delete_const (g_mm, c_res);
    btor_free_bv (g_mm, b);
    btor_free_bv (g_mm, res);
    btor_delete_const (g_mm, c_a);
    btor_free_bv (g_mm, a);
  }
}

static void
test_not_bitvec (void)
{
  unary_bitvec (btor_not_const, btor_not_bv, BTOR_TEST_BITVEC_TESTS, 1);
  unary_bitvec (btor_not_const, btor_not_bv, BTOR_TEST_BITVEC_TESTS, 7);
  unary_bitvec (btor_not_const, btor_not_bv, BTOR_TEST_BITVEC_TESTS, 31);
  unary_bitvec (btor_not_const, btor_not_bv, BTOR_TEST_BITVEC_TESTS, 33);
  unary_bitvec (btor_not_const,
                btor_not_bv,
                BTOR_TEST_BITVEC_TESTS,
                BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_neg_bitvec (void)
{
  unary_bitvec (btor_neg_const, btor_neg_bv, BTOR_TEST_BITVEC_TESTS, 1);
  unary_bitvec (btor_neg_const, btor_neg_bv, BTOR_TEST_BITVEC_TESTS, 7);
  unary_bitvec (btor_neg_const, btor_neg_bv, BTOR_TEST_BITVEC_TESTS, 31);
  unary_bitvec (btor_neg_const, btor_neg_bv, BTOR_TEST_BITVEC_TESTS, 33);
  unary_bitvec (btor_neg_const,
                btor_neg_bv,
                BTOR_TEST_BITVEC_TESTS,
                BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_slice_bitvec (void)
{
  slice_bitvec (100, 1);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 7);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 31);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 33);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_eq_bitvec (void)
{
  binary_bitvec (btor_eq_const, btor_eq_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_eq_const, btor_eq_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_eq_const, btor_eq_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_eq_const, btor_eq_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_eq_const,
                 btor_eq_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_ult_bitvec (void)
{
  binary_bitvec (btor_ult_const, btor_ult_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_ult_const, btor_ult_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_ult_const, btor_ult_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_ult_const, btor_ult_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_ult_const,
                 btor_ult_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_and_bitvec (void)
{
  binary_bitvec (btor_and_const, btor_and_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_and_const, btor_and_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_and_const, btor_and_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_and_const, btor_and_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_and_const,
                 btor_and_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_concat_bitvec (void)
{
  binary_bitvec (btor_concat_const, btor_concat_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_concat_const, btor_concat_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_concat_const, btor_concat_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_concat_const, btor_concat_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_concat_const,
                 btor_concat_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_add_bitvec (void)
{
  binary_bitvec (btor_add_const, btor_add_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_add_const, btor_add_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_add_const, btor_add_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_add_const, btor_add_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_add_const,
                 btor_add_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_mul_bitvec (void)
{
  binary_bitvec (btor_mul_const, btor_mul_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_mul_const, btor_mul_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_mul_const, btor_mul_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_mul_const, btor_mul_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_mul_const,
                 btor_mul_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_udiv_bitvec (void)
{
  binary_bitvec (btor_udiv_const, btor_udiv_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_udiv_const, btor_udiv_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_udiv_const, btor_udiv_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_udiv_const, btor_udiv_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_udiv_const,
                 btor_udiv_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_urem_bitvec (void)
{
  binary_bitvec (btor_urem_const, btor_urem_bv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (btor_urem_const, btor_urem_bv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (btor_urem_const, btor_urem_bv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (btor_urem_const, btor_urem_bv, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (btor_urem_const,
                 btor_urem_bv,
                 BTOR_TEST_BITVEC_TESTS,
                 BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_sll_bitvec (void)
{
  shift_cont_bitvec (btor_sll_const, btor_sll_bv, 2);
  shift_cont_bitvec (btor_sll_const, btor_sll_bv, 8);
  shift_cont_bitvec (btor_sll_const, btor_sll_bv, 32);
  shift_cont_bitvec (btor_sll_const, btor_sll_bv, 64);
  shift_cont_bitvec (btor_sll_const, btor_sll_bv, 128);

  shift_bitvec (btor_sll_const, btor_sll_bv, BTOR_TEST_BITVEC_TESTS, 2);
  shift_bitvec (btor_sll_const, btor_sll_bv, BTOR_TEST_BITVEC_TESTS, 8);
  shift_bitvec (btor_sll_const, btor_sll_bv, BTOR_TEST_BITVEC_TESTS, 32);
  shift_bitvec (btor_sll_const, btor_sll_bv, BTOR_TEST_BITVEC_TESTS, 64);
  shift_bitvec (btor_sll_const, btor_sll_bv, BTOR_TEST_BITVEC_TESTS, 128);
}

static void
test_srl_bitvec (void)
{
  shift_cont_bitvec (btor_srl_const, btor_srl_bv, 2);
  shift_cont_bitvec (btor_srl_const, btor_srl_bv, 8);
  shift_cont_bitvec (btor_srl_const, btor_srl_bv, 32);
  shift_cont_bitvec (btor_srl_const, btor_srl_bv, 64);
  shift_cont_bitvec (btor_srl_const, btor_srl_bv, 128);

  shift_bitvec (btor_srl_const, btor_srl_bv, BTOR_TEST_BITVEC_TESTS, 2);
  shift_bitvec (btor_srl_const, btor_srl_bv, BTOR_TEST_BITVEC_TESTS, 8);
  shift_bitvec (btor_srl_const, btor_srl_bv, BTOR_TEST_BITVEC_TESTS, 32);
  shift_bitvec (btor_srl_const, btor_srl_bv, BTOR_TEST_BITVEC_TESTS, 64);
  shift_bitvec (btor_srl_const, btor_srl_bv, BTOR_TEST_BITVEC_TESTS, 128);
}

static void
perf_test_bitvec (
    char *(*const_func) (BtorMemMgr *, const char *, const char *),
    BitVector *(*bitvec_func) (BtorMemMgr *, BitVector *, BitVector *),
    int num_tests)
{
  assert (const_func);
  assert (bitvec_func);

  double start_const, start_bitvec, total_const, total_bitvec;
  int k;
  long long i, tests;
  char *c_a, *c_b, *c_res, *str;
  BitVector *a, *b, *res;

  printf ("\n");
  printf ("  %10s | %5s | %10s | %10s\n",
          "tests",
          "bw",
          "time const",
          "time bitvec");

  for (k = 1; k < 10; k++)
  {
    tests        = 0;
    total_const  = 0;
    total_bitvec = 0;
    for (i = 0; i < num_tests; i++)
    {
      tests++;
      a   = random_bv (2 << k);
      c_a = btor_bv_to_char_bv (g_mm, a);
      b   = random_bv (2 << k);
      c_b = btor_bv_to_char_bv (g_mm, b);

      start_const = btor_time_stamp ();
      c_res       = const_func (g_mm, c_a, c_b);
      total_const += btor_time_stamp () - start_const;

      start_bitvec = btor_time_stamp ();
      res          = bitvec_func (g_mm, a, b);
      total_bitvec += btor_time_stamp () - start_bitvec;
      str = btor_bv_to_char_bv (g_mm, res);

      assert (strlen (str) == strlen (c_res));
      assert (memcmp (c_res, str, strlen (str) * sizeof (*str)) == 0);

      btor_freestr (g_mm, str);
      btor_delete_const (g_mm, c_b);
      btor_delete_const (g_mm, c_res);
      btor_free_bv (g_mm, b);
      btor_free_bv (g_mm, res);
      btor_delete_const (g_mm, c_a);
      btor_free_bv (g_mm, a);
    }

    printf ("  %10llu | %5d | %10.5f | %10.5f\n",
            tests,
            2 << k,
            total_const,
            total_bitvec);
  }
}

static void
perf_test_shift_bitvec (
    char *(*const_func) (BtorMemMgr *, const char *, const char *),
    BitVector *(*bitvec_func) (BtorMemMgr *, BitVector *, BitVector *),
    int num_tests)
{
  assert (const_func);
  assert (bitvec_func);

  double start_const, start_bitvec, total_const, total_bitvec;
  int k;
  long long i, tests;
  char *c_a, *c_b, *c_res, *str;
  BitVector *a, *b, *res;

  printf ("\n");
  printf ("  %10s | %5s | %10s | %10s\n",
          "tests",
          "bw",
          "time const",
          "time bitvec");

  for (k = 1; k < 10; k++)
  {
    tests        = 0;
    total_const  = 0;
    total_bitvec = 0;
    for (i = 0; i < num_tests; i++)
    {
      tests++;
      a   = random_bv (2 << k);
      c_a = btor_bv_to_char_bv (g_mm, a);
      b   = random_bv (btor_log_2_util (2 << k));
      c_b = btor_bv_to_char_bv (g_mm, b);

      start_const = btor_time_stamp ();
      c_res       = const_func (g_mm, c_a, c_b);
      total_const += btor_time_stamp () - start_const;

      start_bitvec = btor_time_stamp ();
      res          = bitvec_func (g_mm, a, b);
      total_bitvec += btor_time_stamp () - start_bitvec;
      str = btor_bv_to_char_bv (g_mm, res);

      assert (strlen (str) == strlen (c_res));
      assert (memcmp (c_res, str, strlen (str) * sizeof (*str)) == 0);

      btor_freestr (g_mm, str);
      btor_delete_const (g_mm, c_b);
      btor_delete_const (g_mm, c_res);
      btor_free_bv (g_mm, b);
      btor_free_bv (g_mm, res);
      btor_delete_const (g_mm, c_a);
      btor_free_bv (g_mm, a);
    }

    printf ("  %10llu | %5d | %10.5f | %10.5f\n",
            tests,
            2 << k,
            total_const,
            total_bitvec);
  }
}

static void
test_perf_and_bitvec (void)
{
  perf_test_bitvec (btor_and_const, btor_and_bv, BTOR_TEST_BITVEC_PERF_TESTS);
}

static void
test_perf_eq_bitvec (void)
{
  perf_test_bitvec (btor_eq_const, btor_eq_bv, BTOR_TEST_BITVEC_PERF_TESTS);
}

static void
test_perf_ult_bitvec (void)
{
  perf_test_bitvec (btor_ult_const, btor_ult_bv, BTOR_TEST_BITVEC_PERF_TESTS);
}

static void
test_perf_add_bitvec (void)
{
  perf_test_bitvec (btor_add_const, btor_add_bv, BTOR_TEST_BITVEC_PERF_TESTS);
}

static void
test_perf_mul_bitvec (void)
{
  perf_test_bitvec (btor_mul_const, btor_mul_bv, 10000);
}

static void
test_perf_udiv_bitvec (void)
{
  perf_test_bitvec (btor_udiv_const, btor_udiv_bv, 10000);
}

static void
test_perf_urem_bitvec (void)
{
  perf_test_bitvec (btor_urem_const, btor_urem_bv, 10000);
}

static void
test_perf_sll_bitvec (void)
{
  perf_test_shift_bitvec (
      btor_sll_const, btor_sll_bv, BTOR_TEST_BITVEC_PERF_TESTS);
}

static void
test_perf_srl_bitvec (void)
{
  perf_test_shift_bitvec (
      btor_srl_const, btor_srl_bv, BTOR_TEST_BITVEC_PERF_TESTS);
}

static void
test_bv_to_ll_bitvec (void)
{
  uint64_t i, x, y;
  BitVector *a;

  for (i = 0; i < 10000000; i++)
  {
    x = ((uint64_t) rand ()) << 32;
    x |= (uint64_t) rand ();
    a = btor_uint64_to_bv (g_mm, x, 64);
    y = btor_bv_to_uint64_bv (a);
    assert (x == y);
    btor_free_bv (g_mm, a);
  }
}

void
run_bitvec_tests (int argc, char **argv)
{
  srand (42);
  BTOR_RUN_TEST (bv_to_ll_bitvec);
  BTOR_RUN_TEST (new_bitvec);
  BTOR_RUN_TEST (not_bitvec);
  BTOR_RUN_TEST (neg_bitvec);
  BTOR_RUN_TEST (slice_bitvec);
  BTOR_RUN_TEST (eq_bitvec);
  BTOR_RUN_TEST (ult_bitvec);
  BTOR_RUN_TEST (and_bitvec);
  BTOR_RUN_TEST (concat_bitvec);
  BTOR_RUN_TEST (add_bitvec);
  BTOR_RUN_TEST (sll_bitvec);
  BTOR_RUN_TEST (srl_bitvec);
  BTOR_RUN_TEST (mul_bitvec);
  BTOR_RUN_TEST (udiv_bitvec);
  BTOR_RUN_TEST (urem_bitvec);

  BTOR_RUN_TEST (perf_and_bitvec);
  BTOR_RUN_TEST (perf_eq_bitvec);
  BTOR_RUN_TEST (perf_ult_bitvec);
  BTOR_RUN_TEST (perf_add_bitvec);
  BTOR_RUN_TEST (perf_mul_bitvec);
  BTOR_RUN_TEST (perf_udiv_bitvec);
  BTOR_RUN_TEST (perf_urem_bitvec);
  BTOR_RUN_TEST (perf_sll_bitvec);
  BTOR_RUN_TEST (perf_srl_bitvec);
}

void
finish_bitvec_tests (void)
{
  btor_delete_btor (g_btor);
}

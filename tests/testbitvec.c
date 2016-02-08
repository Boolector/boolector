/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Mathias Preiner.
 *  Copyright (C) 2015-2016 Aina Niemetz.
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
  btor_init_rng (&g_btor->rng, g_btor->options.seed.val);
}

static void
test_new_bitvec (void)
{
  BtorBitVector *bv;

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

static BtorBitVector *
random_bv (uint32_t bw)
{
  uint32_t i;
  BtorBitVector *res;
  res = btor_new_bv (g_mm, bw);

  for (i = 0; i < res->len; i++) res->bits[i] = (BTOR_BV_TYPE) rand ();

  if (bw != BTOR_BV_TYPE_BW * res->len)
    res->bits[0] &= ((((BTOR_BV_TYPE) 1 << (BTOR_BV_TYPE_BW - 1)) - 1)
                     >> (BTOR_BV_TYPE_BW - 1 - (bw % BTOR_BV_TYPE_BW)));

  return res;
}

static void
test_new_random_range_bitvec (void)
{
  uint32_t bw;
  uint64_t val;
  BtorBitVector *bv, *from, *to, *tmp;

  for (bw = 1; bw <= 64; bw++)
  {
    from = random_bv (bw);
    // from == to
    bv  = btor_new_random_range_bv (g_mm, &g_btor->rng, bw, from, from);
    val = btor_bv_to_uint64_bv (bv);
    assert (val == btor_bv_to_uint64_bv (from));
    btor_free_bv (g_mm, bv);
    // from < to
    to = random_bv (bw);
    while (!btor_compare_bv (from, to))
    {
      btor_free_bv (g_mm, to);
      to = random_bv (bw);
    }
    if (btor_bv_to_uint64_bv (to) < btor_bv_to_uint64_bv (from))
    {
      tmp  = to;
      to   = from;
      from = tmp;
    }
    bv  = btor_new_random_range_bv (g_mm, &g_btor->rng, bw, from, to);
    val = btor_bv_to_uint64_bv (bv);
    assert (val >= btor_bv_to_uint64_bv (from));
    assert (val <= btor_bv_to_uint64_bv (to));
    btor_free_bv (g_mm, from);
    btor_free_bv (g_mm, to);
    btor_free_bv (g_mm, bv);
  }
}

static void
test_uint64_to_bitvec (void)
{
  uint64_t i, j, k, l;
  BtorBitVector *bv;

  bv = btor_uint64_to_bv (g_mm, 0, 32);
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_uint64_to_bv (g_mm, UINT_MAX, 32);
  assert (btor_bv_to_uint64_bv (bv) == UINT_MAX);
  btor_free_bv (g_mm, bv);

  for (i = 0; i < 10; i++)
  {
    for (j = 0; j < 5; j++)
    {
      l  = rand () % 32 + 1;
      bv = random_bv (l);
      k  = btor_bv_to_uint64_bv (bv);
      btor_free_bv (g_mm, bv);
      bv = btor_uint64_to_bv (g_mm, k, l);
      assert (btor_bv_to_uint64_bv (bv) == k);
      btor_free_bv (g_mm, bv);
    }
  }
}

static void
test_char_to_bitvec (void)
{
  BtorBitVector *bv;

  bv = btor_char_to_bv (g_mm, "0");
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1");
  assert (btor_bv_to_uint64_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00");
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "01");
  assert (btor_bv_to_uint64_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10");
  assert (btor_bv_to_uint64_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11");
  assert (btor_bv_to_uint64_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000");
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "001");
  assert (btor_bv_to_uint64_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "010");
  assert (btor_bv_to_uint64_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "011");
  assert (btor_bv_to_uint64_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "100");
  assert (btor_bv_to_uint64_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "101");
  assert (btor_bv_to_uint64_bv (bv) == 5);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "110");
  assert (btor_bv_to_uint64_bv (bv) == 6);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111");
  assert (btor_bv_to_uint64_bv (bv) == 7);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000000001");
  assert (btor_bv_to_uint64_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000000010");
  assert (btor_bv_to_uint64_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000000100");
  assert (btor_bv_to_uint64_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000001000");
  assert (btor_bv_to_uint64_bv (bv) == 8);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000010000");
  assert (btor_bv_to_uint64_bv (bv) == 16);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000000100000");
  assert (btor_bv_to_uint64_bv (bv) == 32);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000001000000");
  assert (btor_bv_to_uint64_bv (bv) == 64);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000010000000");
  assert (btor_bv_to_uint64_bv (bv) == 128);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000000100000000");
  assert (btor_bv_to_uint64_bv (bv) == 256);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000001000000000");
  assert (btor_bv_to_uint64_bv (bv) == 512);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000010000000000");
  assert (btor_bv_to_uint64_bv (bv) == 1024);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000000100000000000");
  assert (btor_bv_to_uint64_bv (bv) == 2048);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000001000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 4096);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000010000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 8192);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000000100000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 16384);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000001000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 32768);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000010000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 65536);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000000100000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 131072);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000001000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 262144);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000010000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 524288);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000000100000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 1048576);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000001000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 2097152);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000010000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 4194304);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000000100000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 8388608);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000001000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 16777216);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000010000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 33554432);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00000100000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 67108864);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00001000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 134217728);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00010000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 268435456);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00100000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 536870912);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "01000000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 1073741824);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 2147483648);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11111111111111111111111111111111");
  assert (btor_bv_to_uint64_bv (bv) == UINT_MAX);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000000000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000000000000000000000000000000001");
  assert (btor_bv_to_uint64_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111111111111111111111111111111111");
  assert (btor_bv_to_uint64_bv (bv) == 8589934591);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000000000000000000000000000000000");
  assert (btor_bv_to_uint64_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000000000000000000000000000000001");
  assert (btor_bv_to_uint64_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1111111111111111111111111111111111");
  assert (btor_bv_to_uint64_bv (bv) == 17179869183);
  btor_free_bv (g_mm, bv);
}

static void
unary_bitvec (char *(*const_func) (BtorMemMgr *, const char *),
              BtorBitVector *(*bitvec_func) (BtorMemMgr *, BtorBitVector *),
              int num_tests,
              int bit_width)
{
  int i;
  char *c_a, *c_res, *str;
  BtorBitVector *a, *res;

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
  BtorBitVector *a, *res;

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
              BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                             BtorBitVector *,
                                             BtorBitVector *),
              int num_tests,
              int bit_width)
{
  int i;
  char *c_a, *c_b, *c_res, *str;
  BtorBitVector *a, *b, *res;

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
shift_cont_bitvec (char *(*const_func) (BtorMemMgr *,
                                        const char *,
                                        const char *),
                   BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                                  BtorBitVector *,
                                                  BtorBitVector *),
                   int bit_width)
{
  int i, shift_width;
  char *c_a, *c_b, *c_res, *str;
  BtorBitVector *a, *b, *res;

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
               BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                              BtorBitVector *,
                                              BtorBitVector *),
               int num_tests,
               int bit_width)
{
  assert (const_func);
  assert (bitvec_func);

  int i;
  char *c_a, *c_b, *c_res, *str;
  BtorBitVector *a, *b, *res;

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
ext_bitvec (char *(*const_func) (BtorMemMgr *, const char *, uint32_t),
            BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                           BtorBitVector *,
                                           uint32_t),
            int num_tests,
            uint32_t bit_width)
{
  assert (const_func);
  assert (bitvec_func);

  int i, bw;
  char *c_a, *c_res, *str;
  BtorBitVector *a, *res;

  printf (" %d", bit_width);
  fflush (stdout);
  for (i = 0; i < num_tests; i++)
  {
    a     = random_bv (bit_width);
    c_a   = btor_bv_to_char_bv (g_mm, a);
    bw    = btor_pick_rand_rng (&g_btor->rng, a->width + 1, 100);
    c_res = const_func (g_mm, c_a, bw);
    res   = bitvec_func (g_mm, a, bw);
    str   = btor_bv_to_char_bv (g_mm, res);

    assert (strlen (str) == strlen (c_res));
    assert (memcmp (c_res, str, strlen (str)) == 0);

    btor_freestr (g_mm, str);
    btor_delete_const (g_mm, c_res);
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
  binary_bitvec (btor_ult_const, btor_ult_bv, BTOR_TEST_BITVEC_TESTS, 1);
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
test_uext_bitvec (void)
{
  ext_bitvec (btor_uext_const, btor_uext_bv, BTOR_TEST_BITVEC_TESTS, 1);
  ext_bitvec (btor_uext_const, btor_uext_bv, BTOR_TEST_BITVEC_TESTS, 7);
  ext_bitvec (btor_uext_const, btor_uext_bv, BTOR_TEST_BITVEC_TESTS, 31);
  ext_bitvec (btor_uext_const, btor_uext_bv, BTOR_TEST_BITVEC_TESTS, 33);
  ext_bitvec (btor_uext_const,
              btor_uext_bv,
              BTOR_TEST_BITVEC_TESTS,
              BTOR_TEST_BITVEC_NUM_BITS);
}

static void
test_sext_bitvec (void)
{
  ext_bitvec (btor_sext_const, btor_sext_bv, BTOR_TEST_BITVEC_TESTS, 1);
  ext_bitvec (btor_sext_const, btor_sext_bv, BTOR_TEST_BITVEC_TESTS, 7);
  ext_bitvec (btor_sext_const, btor_sext_bv, BTOR_TEST_BITVEC_TESTS, 31);
  ext_bitvec (btor_sext_const, btor_sext_bv, BTOR_TEST_BITVEC_TESTS, 33);
  ext_bitvec (btor_sext_const,
              btor_sext_bv,
              BTOR_TEST_BITVEC_TESTS,
              BTOR_TEST_BITVEC_NUM_BITS);
}

#define TEST_IS_UMULO_BITVEC(bw, v0, v1, res)          \
  do                                                   \
  {                                                    \
    bv0 = btor_uint64_to_bv (g_mm, v0, bw);            \
    bv1 = btor_uint64_to_bv (g_mm, v1, bw);            \
    assert (btor_is_umulo_bv (g_mm, bv0, bv1) == res); \
    btor_free_bv (g_mm, bv0);                          \
    btor_free_bv (g_mm, bv1);                          \
  } while (0)

static void
is_umulo_bitvec (int bw)
{
  BtorBitVector *bv0, *bv1;

  switch (bw)
  {
    case 1:
      TEST_IS_UMULO_BITVEC (bw, 0, 0, false);
      TEST_IS_UMULO_BITVEC (bw, 0, 1, false);
      TEST_IS_UMULO_BITVEC (bw, 1, 1, false);
      break;
    case 7:
      TEST_IS_UMULO_BITVEC (bw, 3, 6, false);
      TEST_IS_UMULO_BITVEC (bw, 124, 2, true);
      break;
    case 31:
      TEST_IS_UMULO_BITVEC (bw, 15, 78, false);
      TEST_IS_UMULO_BITVEC (bw, 1073742058, 2, true);
      break;
    case 33:
      TEST_IS_UMULO_BITVEC (bw, 15, 78, false);
      TEST_IS_UMULO_BITVEC (bw, 4294967530, 4294967530, true);
      break;
  }
}

static void
test_is_umulo_bitvec (void)
{
  is_umulo_bitvec (1);
  is_umulo_bitvec (7);
  is_umulo_bitvec (31);
  is_umulo_bitvec (33);
}

static void
perf_test_bitvec (char *(*const_func) (BtorMemMgr *,
                                       const char *,
                                       const char *),
                  BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                                 BtorBitVector *,
                                                 BtorBitVector *),
                  int num_tests)
{
  assert (const_func);
  assert (bitvec_func);

  double start_const, start_bitvec, total_const, total_bitvec;
  int k;
  long long i, tests;
  char *c_a, *c_b, *c_res, *str;
  BtorBitVector *a, *b, *res;

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
perf_test_shift_bitvec (char *(*const_func) (BtorMemMgr *,
                                             const char *,
                                             const char *),
                        BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                                       BtorBitVector *,
                                                       BtorBitVector *),
                        int num_tests)
{
  assert (const_func);
  assert (bitvec_func);

  double start_const, start_bitvec, total_const, total_bitvec;
  int k;
  long long i, tests;
  char *c_a, *c_b, *c_res, *str;
  BtorBitVector *a, *b, *res;

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
  BtorBitVector *a;

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

static void
test_compare_bitvec (void)
{
  int i, j, k;
  BtorBitVector *bv1, *bv2;

  for (i = 0; i < 15; i++)
  {
    bv1 = btor_uint64_to_bv (g_btor->mm, i, 4);
    bv2 = btor_uint64_to_bv (g_btor->mm, i, 4);
    assert (!btor_compare_bv (bv1, bv2));
    btor_free_bv (g_btor->mm, bv1);
    btor_free_bv (g_btor->mm, bv2);
  }

  for (i = 0; i < 15 - 1; i++)
  {
    bv1 = btor_uint64_to_bv (g_btor->mm, i, 4);
    bv2 = btor_uint64_to_bv (g_btor->mm, i + 1, 4);
    assert (btor_compare_bv (bv1, bv2) < 0);
    assert (btor_compare_bv (bv2, bv1) > 0);
    btor_free_bv (g_btor->mm, bv1);
    btor_free_bv (g_btor->mm, bv2);
  }

  for (i = 0, j = 0, k = 0; i < 15; i++)
  {
    k = rand () % 16;
    do
      j = rand () % 16;
    while (j == k);
    bv1 = btor_uint64_to_bv (g_btor->mm, j, 4);
    bv2 = btor_uint64_to_bv (g_btor->mm, k, 4);
    if (j > k)
    {
      assert (btor_compare_bv (bv1, bv2) > 0);
      assert (btor_compare_bv (bv2, bv1) < 0);
    }
    if (j < k)
    {
      assert (btor_compare_bv (bv1, bv2) < 0);
      assert (btor_compare_bv (bv2, bv1) > 0);
    }
    btor_free_bv (g_btor->mm, bv1);
    btor_free_bv (g_btor->mm, bv2);
  }
}

static void
test_is_one_bitvec (void)
{
  int i;
  char *s;
  BtorBitVector *bv1, *bv2, *bv3;

  for (i = 1; i < 32; i++)
  {
    bv1 = btor_one_bv (g_btor->mm, i);
    bv2 = btor_uint64_to_bv (g_btor->mm, 1, i);
    BTOR_CNEWN (g_btor->mm, s, i + 1);
    memset (s, '0', i - 1);
    s[i - 1] = '1';
    bv3      = btor_char_to_bv (g_btor->mm, s);
    assert (btor_is_one_bv (bv1));
    assert (btor_is_one_bv (bv2));
    assert (btor_is_one_bv (bv3));
    assert (!btor_compare_bv (bv1, bv2));
    assert (!btor_compare_bv (bv1, bv3));
    btor_free_bv (g_btor->mm, bv1);
    btor_free_bv (g_btor->mm, bv2);
    btor_free_bv (g_btor->mm, bv3);
    BTOR_DELETEN (g_btor->mm, s, i + 1);
  }
}

static void
test_is_ones_bitvec (void)
{
  int i;
  char *s;
  BtorBitVector *bv1, *bv2, *bv3;

  for (i = 1; i < 32; i++)
  {
    bv1 = btor_ones_bv (g_btor->mm, i);
    bv2 = btor_uint64_to_bv (g_btor->mm, UINT_MAX, i);
    BTOR_CNEWN (g_btor->mm, s, i + 1);
    memset (s, '1', i);
    bv3 = btor_char_to_bv (g_btor->mm, s);
    assert (btor_is_ones_bv (bv1));
    assert (btor_is_ones_bv (bv2));
    assert (btor_is_ones_bv (bv3));
    assert (!btor_compare_bv (bv1, bv2));
    assert (!btor_compare_bv (bv1, bv3));
    btor_free_bv (g_btor->mm, bv1);
    btor_free_bv (g_btor->mm, bv2);
    btor_free_bv (g_btor->mm, bv3);
    BTOR_DELETEN (g_btor->mm, s, i + 1);
  }
}

static void
test_is_zero_bitvec (void)
{
  int i;
  char *s;
  BtorBitVector *bv1, *bv2, *bv3;

  for (i = 1; i < 32; i++)
  {
    bv1 = btor_new_bv (g_btor->mm, i);
    bv2 = btor_uint64_to_bv (g_btor->mm, 0, i);
    BTOR_CNEWN (g_btor->mm, s, i + 1);
    memset (s, '0', i);
    bv3 = btor_char_to_bv (g_btor->mm, s);
    assert (btor_is_zero_bv (bv1));
    assert (btor_is_zero_bv (bv2));
    assert (btor_is_zero_bv (bv3));
    assert (!btor_compare_bv (bv1, bv2));
    assert (!btor_compare_bv (bv1, bv3));
    btor_free_bv (g_btor->mm, bv1);
    btor_free_bv (g_btor->mm, bv2);
    btor_free_bv (g_btor->mm, bv3);
    BTOR_DELETEN (g_btor->mm, s, i + 1);
  }
}

static void
test_is_special_const_bitvec (void)
{
  int i;
  BtorBitVector *bv;

  bv = btor_char_to_bv (g_mm, "0");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ZERO);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONE_ONES);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ZERO);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "01");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONE);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_NONE);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONES);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ZERO);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "001");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONE);
  btor_free_bv (g_mm, bv);

  for (i = 2; i < 7; i++)
  {
    bv = btor_uint64_to_bv (g_mm, i, 3);
    assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_NONE);
    btor_free_bv (g_mm, bv);
  }

  bv = btor_char_to_bv (g_mm, "111");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONES);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ZERO);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONE);
  btor_free_bv (g_mm, bv);

  for (i = 2; i < 15; i++)
  {
    bv = btor_uint64_to_bv (g_mm, i, 4);
    assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_NONE);
    btor_free_bv (g_mm, bv);
  }

  bv = btor_char_to_bv (g_mm, "1111");
  assert (btor_is_special_const_bv (bv) == BTOR_SPECIAL_CONST_BV_ONES);
  btor_free_bv (g_mm, bv);
}

static void
test_is_power_of_two_bitvec (void)
{
  BtorBitVector *bv;

  bv = btor_char_to_bv (
      g_mm, "0000000000000000000000000000000000000000000000000000000000000000");
  assert (btor_is_power_of_two_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000");
  assert (btor_is_power_of_two_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "001");
  assert (btor_is_power_of_two_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010");
  assert (btor_is_power_of_two_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00100");
  assert (btor_is_power_of_two_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "001000");
  assert (btor_is_power_of_two_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010000");
  assert (btor_is_power_of_two_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100000");
  assert (btor_is_power_of_two_bv (bv) == 5);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001000000");
  assert (btor_is_power_of_two_bv (bv) == 6);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00010000000");
  assert (btor_is_power_of_two_bv (bv) == 7);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100000000");
  assert (btor_is_power_of_two_bv (bv) == 8);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001000000000");
  assert (btor_is_power_of_two_bv (bv) == 9);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000010000000000");
  assert (btor_is_power_of_two_bv (bv) == 10);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000000000000000000000000000");
  assert (btor_is_power_of_two_bv (bv) == 28);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "100000000000000000000000000000");
  assert (btor_is_power_of_two_bv (bv) == 29);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1000000000000000000000000000000");
  assert (btor_is_power_of_two_bv (bv) == 30);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "01000000000000000000000000000000");
  assert (btor_is_power_of_two_bv (bv) == 30);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "1110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "11110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "1111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "111111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "1111111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "11111111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "111111111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "1111111111110");
  assert (btor_is_power_of_two_bv (bv) == -1);

  btor_free_bv (g_mm, bv);
  bv = btor_char_to_bv (g_mm, "1111111111111110");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "011");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0011");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00101");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "101101");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010001");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100111");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1001000001");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11010000001");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100000011");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001000000111");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000010000001111");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000000000000000000000000010");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "100000000000000000000001000000");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1000000000000100000000000000000");
  assert (btor_is_power_of_two_bv (bv) == -1);
  btor_free_bv (g_mm, bv);
}

static void
test_is_small_positive_int_bitvec (void)
{
  BtorBitVector *bv;

  bv = btor_char_to_bv (
      g_mm, "0000000000000000000000000000000000000000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000");
  assert (btor_is_small_positive_int_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "001");
  assert (btor_is_small_positive_int_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010");
  assert (btor_is_small_positive_int_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00100");
  assert (btor_is_small_positive_int_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "001000");
  assert (btor_is_small_positive_int_bv (bv) == 8);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010000");
  assert (btor_is_small_positive_int_bv (bv) == 16);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100000");
  assert (btor_is_small_positive_int_bv (bv) == 32);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001000000");
  assert (btor_is_small_positive_int_bv (bv) == 64);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00010000000");
  assert (btor_is_small_positive_int_bv (bv) == 128);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100000000");
  assert (btor_is_small_positive_int_bv (bv) == 256);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001000000000");
  assert (btor_is_small_positive_int_bv (bv) == 512);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000010000000000");
  assert (btor_is_small_positive_int_bv (bv) == 1024);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) == (1 << 28));
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "100000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) == (1 << 29));
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1000000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) == (1 << 30));
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "01000000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) == (1 << 30));
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "110");
  assert (btor_is_small_positive_int_bv (bv) == 6);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1110");
  assert (btor_is_small_positive_int_bv (bv) == 14);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11110");
  assert (btor_is_small_positive_int_bv (bv) == 30);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111110");
  assert (btor_is_small_positive_int_bv (bv) == 62);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1111110");
  assert (btor_is_small_positive_int_bv (bv) == 126);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111111110");
  assert (btor_is_small_positive_int_bv (bv) == 510);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1111111110");
  assert (btor_is_small_positive_int_bv (bv) == 1022);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11111111110");
  assert (btor_is_small_positive_int_bv (bv) == 2046);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111111111110");
  assert (btor_is_small_positive_int_bv (bv) == 4094);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1111111111110");
  assert (btor_is_small_positive_int_bv (bv) == 8190);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1111111111111110");
  assert (btor_is_small_positive_int_bv (bv) == 65534);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "011");
  assert (btor_is_small_positive_int_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "111");
  assert (btor_is_small_positive_int_bv (bv) == 7);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0011");
  assert (btor_is_small_positive_int_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00101");
  assert (btor_is_small_positive_int_bv (bv) == 5);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "101101");
  assert (btor_is_small_positive_int_bv (bv) == 45);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "00100001");
  assert (btor_is_small_positive_int_bv (bv) == 33);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100111");
  assert (btor_is_small_positive_int_bv (bv) == 39);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1001000001");
  assert (btor_is_small_positive_int_bv (bv) == 577);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "11010000001");
  assert (btor_is_small_positive_int_bv (bv) == 1665);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "000100000011");
  assert (btor_is_small_positive_int_bv (bv) == 259);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0001000000111");
  assert (btor_is_small_positive_int_bv (bv) == 519);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0000010000001111");
  assert (btor_is_small_positive_int_bv (bv) == 1039);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000000000000000000000000010");
  assert (btor_is_small_positive_int_bv (bv) == 268435458);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "100000000000000000000001000000");
  assert (btor_is_small_positive_int_bv (bv) == 536870976);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "1000000000000100000000000000000");
  assert (btor_is_small_positive_int_bv (bv) == 1073872896);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) < 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "10000100000000000000000011100000");
  assert (btor_is_small_positive_int_bv (bv) < 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010000000000000000000000000000000");
  assert (btor_is_small_positive_int_bv (bv) < 0);
  btor_free_bv (g_mm, bv);

  bv = btor_char_to_bv (g_mm, "0010000000000100000000000011110000");
  assert (btor_is_small_positive_int_bv (bv) < 0);
  btor_free_bv (g_mm, bv);
}

static void
test_get_num_trailing_zeros_bitvec (void)
{
  BtorBitVector *bv;

  // 1000
  bv = btor_uint64_to_bv (g_mm, 8, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  // 0100
  bv = btor_uint64_to_bv (g_mm, 4, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  // 0010
  bv = btor_uint64_to_bv (g_mm, 2, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 0001
  bv = btor_uint64_to_bv (g_mm, 1, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 0000
  bv = btor_uint64_to_bv (g_mm, 0, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  // 1111
  bv = btor_uint64_to_bv (g_mm, 15, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 0110
  bv = btor_uint64_to_bv (g_mm, 6, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 0111
  bv = btor_uint64_to_bv (g_mm, 7, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 1010
  bv = btor_uint64_to_bv (g_mm, 10, 4);
  assert (btor_get_num_trailing_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 0
  bv = btor_uint64_to_bv (g_mm, 0, 1);
  assert (btor_get_num_trailing_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 1
  bv = btor_uint64_to_bv (g_mm, 1, 1);
  assert (btor_get_num_trailing_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);
}

static void
test_get_num_leading_zeros_bitvec (void)
{
  BtorBitVector *bv;

  // 1000
  bv = btor_uint64_to_bv (g_mm, 8, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 0100
  bv = btor_uint64_to_bv (g_mm, 4, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 0010
  bv = btor_uint64_to_bv (g_mm, 2, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  // 0001
  bv = btor_uint64_to_bv (g_mm, 1, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  // 0000
  bv = btor_uint64_to_bv (g_mm, 0, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  // 1111
  bv = btor_uint64_to_bv (g_mm, 15, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 0110
  bv = btor_uint64_to_bv (g_mm, 6, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 0111
  bv = btor_uint64_to_bv (g_mm, 7, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 1010
  bv = btor_uint64_to_bv (g_mm, 10, 4);
  assert (btor_get_num_leading_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 0
  bv = btor_uint64_to_bv (g_mm, 0, 1);
  assert (btor_get_num_leading_zeros_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 1
  bv = btor_uint64_to_bv (g_mm, 1, 1);
  assert (btor_get_num_leading_zeros_bv (bv) == 0);
  btor_free_bv (g_mm, bv);
}

static void
test_get_num_leading_ones_bitvec (void)
{
  BtorBitVector *bv;

  // 1000
  bv = btor_uint64_to_bv (g_mm, 8, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 1100
  bv = btor_uint64_to_bv (g_mm, 12, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  // 1110
  bv = btor_uint64_to_bv (g_mm, 14, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 3);
  btor_free_bv (g_mm, bv);

  // 1111
  bv = btor_uint64_to_bv (g_mm, 15, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 4);
  btor_free_bv (g_mm, bv);

  // 0000
  bv = btor_uint64_to_bv (g_mm, 0, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 1011
  bv = btor_uint64_to_bv (g_mm, 11, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 1101
  bv = btor_uint64_to_bv (g_mm, 13, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 2);
  btor_free_bv (g_mm, bv);

  // 1001
  bv = btor_uint64_to_bv (g_mm, 9, 4);
  assert (btor_get_num_leading_ones_bv (bv) == 1);
  btor_free_bv (g_mm, bv);

  // 0
  bv = btor_uint64_to_bv (g_mm, 0, 1);
  assert (btor_get_num_leading_ones_bv (bv) == 0);
  btor_free_bv (g_mm, bv);

  // 1
  bv = btor_uint64_to_bv (g_mm, 1, 1);
  assert (btor_get_num_leading_ones_bv (bv) == 1);
  btor_free_bv (g_mm, bv);
}

void
run_bitvec_tests (int argc, char **argv)
{
  srand (42);
  BTOR_RUN_TEST (bv_to_ll_bitvec);
  BTOR_RUN_TEST (new_bitvec);
  BTOR_RUN_TEST (new_random_range_bitvec);
  BTOR_RUN_TEST (uint64_to_bitvec);
  BTOR_RUN_TEST (char_to_bitvec);
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
  BTOR_RUN_TEST (uext_bitvec);
  BTOR_RUN_TEST (sext_bitvec);
  BTOR_RUN_TEST (is_umulo_bitvec);

  BTOR_RUN_TEST (perf_and_bitvec);
  BTOR_RUN_TEST (perf_eq_bitvec);
  BTOR_RUN_TEST (perf_ult_bitvec);
  BTOR_RUN_TEST (perf_add_bitvec);
  BTOR_RUN_TEST (perf_mul_bitvec);
  BTOR_RUN_TEST (perf_udiv_bitvec);
  BTOR_RUN_TEST (perf_urem_bitvec);
  BTOR_RUN_TEST (perf_sll_bitvec);
  BTOR_RUN_TEST (perf_srl_bitvec);

  BTOR_RUN_TEST (compare_bitvec);

  BTOR_RUN_TEST (is_one_bitvec);
  BTOR_RUN_TEST (is_ones_bitvec);
  BTOR_RUN_TEST (is_zero_bitvec);
  BTOR_RUN_TEST (is_special_const_bitvec);
  BTOR_RUN_TEST (is_small_positive_int_bitvec);
  BTOR_RUN_TEST (is_power_of_two_bitvec);
  BTOR_RUN_TEST (get_num_trailing_zeros_bitvec);
  BTOR_RUN_TEST (get_num_leading_zeros_bitvec);
  BTOR_RUN_TEST (get_num_leading_ones_bitvec);
}

void
finish_bitvec_tests (void)
{
  btor_delete_btor (g_btor);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Mathias Preiner.
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

#include <math.h>

extern "C" {
#include "btorbv.h"
}

#define TEST_BV_IS_UMULO_BITVEC(bw, v0, v1, res)        \
  do                                                    \
  {                                                     \
    bv0 = btor_bv_uint64_to_bv (d_mm, v0, bw);          \
    bv1 = btor_bv_uint64_to_bv (d_mm, v1, bw);          \
    ASSERT_EQ (btor_bv_is_umulo (d_mm, bv0, bv1), res); \
    btor_bv_free (d_mm, bv0);                           \
    btor_bv_free (d_mm, bv1);                           \
  } while (0)

#define TEST_BV_CHECK_CHAR_TO_BV(bv, i)             \
  do                                                \
  {                                                 \
    s = btor_bv_to_char (d_mm, bv);                 \
    ASSERT_EQ (strlen (s), btor_bv_get_width (bv)); \
    for (k = 0; k < i; k++)                         \
    {                                               \
      b = s[i - k - 1] == '0' ? 0 : 1;              \
      ASSERT_EQ (b, btor_bv_get_bit (bv, k));       \
    }                                               \
    btor_mem_freestr (d_mm, s);                     \
    btor_bv_free (d_mm, bv);                        \
  } while (0)

class TestBv : public TestBtor
{
 protected:
  static constexpr uint32_t BTOR_TEST_BITVEC_NUM_BITS   = 65;
  static constexpr uint32_t BTOR_TEST_BITVEC_TESTS      = 100000;
  static constexpr uint32_t BTOR_TEST_BITVEC_PERF_TESTS = 1000000;

  void SetUp () override
  {
    TestBtor::SetUp ();
    d_mm = d_btor->mm;
    d_rng = &d_btor->rng;
  }

  void bv_to_hex_char_bitvec (FILE *g_logfile, const char *c)
  {
    BtorBitVector *bv = btor_bv_char_to_bv (d_mm, c);
    char *h           = btor_bv_to_hex_char (d_mm, bv);
    fprintf (g_logfile, "2'%s = 16'%s\n", c, h);
    btor_mem_freestr (d_mm, h);
    btor_bv_free (d_mm, bv);
  }

  void bv_to_dec_char_bitvec (FILE *g_logfile, const char *c)
  {
    BtorBitVector *bv = btor_bv_char_to_bv (d_mm, c);
    char *d           = btor_bv_to_dec_char (d_mm, bv);
    fprintf (g_logfile, "2'%s = 10'%s\n", c, d);
    btor_mem_freestr (d_mm, d);
    btor_bv_free (d_mm, bv);
  }

  static uint64_t _not (uint64_t x, uint32_t bw)
  {
    return ~x % (uint64_t) pow (2, bw);
  }

  static uint64_t neg (uint64_t x, uint32_t bw)
  {
    return -x % (uint64_t) pow (2, bw);
  }

  static uint64_t inc (uint64_t x, uint32_t bw)
  {
    return (x + 1) % (uint64_t) pow (2, bw);
  }

  static uint64_t dec (uint64_t x, uint32_t bw)
  {
    return (x - 1) % (uint64_t) pow (2, bw);
  }

  static uint64_t add (uint64_t x, uint64_t y, uint32_t bw)
  {
    return (x + y) % (uint64_t) pow (2, bw);
  }

  static uint64_t sub (uint64_t x, uint64_t y, uint32_t bw)
  {
    return (x - y) % (uint64_t) pow (2, bw);
  }

  static uint64_t _and (uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x & y;
  }

  static uint64_t implies (uint64_t x, uint64_t y, uint32_t bw)
  {
    assert (bw == 1);
    (void) bw;
    return ((~x | y) << 63) >> 63;
  }

  static uint64_t _xor (uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x ^ y;
  }

  static uint64_t eq (uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x == y;
  }

  static uint64_t ult (uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x < y;
  }

  static uint64_t sll (uint64_t x, uint64_t y, uint32_t bw)
  {
    assert (bw <= 64);
    if (y >= bw) return 0;
    return (x << y) % (uint64_t) pow (2, bw);
  }

  static uint64_t srl (uint64_t x, uint64_t y, uint32_t bw)
  {
    assert (bw <= 64);
    if (y >= bw) return 0;
    return (x >> y) % (uint64_t) pow (2, bw);
  }

  static uint64_t mul (uint64_t x, uint64_t y, uint32_t bw)
  {
    return (x * y) % (uint64_t) pow (2, bw);
  }

  static uint64_t udiv (uint64_t x, uint64_t y, uint32_t bw)
  {
    if (y == 0) return UINT64_MAX % (uint64_t) pow (2, bw);
    return (x / y) % (uint64_t) pow (2, bw);
  }

  static uint64_t urem (uint64_t x, uint64_t y, uint32_t bw)
  {
    if (y == 0) return x;
    return (x % y) % (uint64_t) pow (2, bw);
  }

  void unary_bitvec (uint64_t (*int_func) (uint64_t, uint32_t),
                     BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                                    const BtorBitVector *),
                     uint32_t num_tests,
                     uint32_t bit_width)
  {
    uint32_t i;
    BtorBitVector *bv, *res;
    uint64_t a, ares, bres;

    for (i = 0; i < num_tests; i++)
    {
      bv   = btor_bv_new_random (d_mm, d_rng, bit_width);
      res  = bitvec_func (d_mm, bv);
      a    = btor_bv_to_uint64 (bv);
      ares = int_func (a, bit_width);
      bres = btor_bv_to_uint64 (res);
      ASSERT_EQ (ares, bres);
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv);
    }
  }

  void binary_bitvec (uint64_t (*int_func) (uint64_t, uint64_t, uint32_t),
                      BtorBitVector *(*bitvec_func) (BtorMemMgr *,
                                                     const BtorBitVector *,
                                                     const BtorBitVector *),
                      uint32_t num_tests,
                      uint32_t bit_width)
  {
    uint32_t i;
    BtorBitVector *bv1, *bv2, *zero, *res;
    uint64_t a1, a2, ares, bres;

    zero = btor_bv_new (d_mm, bit_width);
    for (i = 0; i < num_tests; i++)
    {
      bv1 = btor_bv_new_random (d_mm, d_rng, bit_width);
      bv2 = btor_bv_new_random (d_mm, d_rng, bit_width);
      a1  = btor_bv_to_uint64 (bv1);
      a2  = btor_bv_to_uint64 (bv2);
      /* test for x = 0 explicitly */
      res  = bitvec_func (d_mm, zero, bv2);
      ares = int_func (0, a2, bit_width);
      bres = btor_bv_to_uint64 (res);
      ASSERT_EQ (ares, bres);
      btor_bv_free (d_mm, res);
      /* test for y = 0 explicitly */
      res  = bitvec_func (d_mm, bv1, zero);
      ares = int_func (a1, 0, bit_width);
      bres = btor_bv_to_uint64 (res);
      ASSERT_EQ (ares, bres);
      btor_bv_free (d_mm, res);
      /* test x, y random */
      res  = bitvec_func (d_mm, bv1, bv2);
      ares = int_func (a1, a2, bit_width);
      bres = btor_bv_to_uint64 (res);
      ASSERT_EQ (ares, bres);
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv1);
      btor_bv_free (d_mm, bv2);
    }
    btor_bv_free (d_mm, zero);
  }

  void concat_bitvec (int32_t num_tests, uint32_t bit_width)
  {
    int32_t i;
    uint32_t bw1, bw2;
    BtorBitVector *bv1, *bv2, *res;
    uint64_t a1, a2, ares, bres;

    for (i = 0; i < num_tests; i++)
    {
      bw1 = btor_rng_pick_rand (d_rng, 1, bit_width - 1);
      bw2 = bit_width - bw1;
      bv1 = btor_bv_new_random (d_mm, d_rng, bw1);
      bv2 = btor_bv_new_random (d_mm, d_rng, bw2);
      res = btor_bv_concat (d_mm, bv1, bv2);
      ASSERT_EQ (btor_bv_get_width (res), bw1 + bw2);
      a1   = btor_bv_to_uint64 (bv1);
      a2   = btor_bv_to_uint64 (bv2);
      ares = (a1 << bw2) | a2;
      bres = btor_bv_to_uint64 (res);
      ASSERT_EQ (ares, bres);
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv1);
      btor_bv_free (d_mm, bv2);
    }
  }

  void slice_bitvec (uint32_t num_tests, uint32_t bit_width)
  {
    uint32_t i, upper, lower;
    char *sbv, *sres;
    BtorBitVector *bv, *res;

    for (i = 0; i < num_tests; i++)
    {
      bv    = btor_bv_new_random (d_mm, d_rng, bit_width);
      lower = rand () % bit_width;
      upper = rand () % (bit_width - lower) + lower;
      ASSERT_GE (upper, lower);
      ASSERT_LT (upper, bit_width);
      ASSERT_LT (lower, bit_width);

      res = btor_bv_slice (d_mm, bv, upper, lower);
      ASSERT_EQ (btor_bv_get_width (res), upper - lower + 1);
      sres = btor_bv_to_char (d_mm, res);
      sbv  = btor_bv_to_char (d_mm, bv);

      ASSERT_EQ (strncmp (sbv + bit_width - upper - 1, sres, upper - lower + 1),
                 0);

      btor_mem_freestr (d_mm, sbv);
      btor_mem_freestr (d_mm, sres);
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv);
    }
  }

  void ext_bitvec (BtorBitVector *(*ext_func) (BtorMemMgr *,
                                               const BtorBitVector *,
                                               uint32_t),
                   uint32_t num_tests,
                   uint32_t bit_width)
  {
    uint32_t i, j, len;
    char *sbv, *sres;
    BtorBitVector *bv, *res;

    for (i = 0; i < num_tests; i++)
    {
      len = btor_rng_pick_rand (d_rng, 1, bit_width - 1);
      bv  = btor_bv_new_random (d_mm, d_rng, bit_width - len);

      res = ext_func (d_mm, bv, len);
      ASSERT_EQ (btor_bv_get_width (bv) + len, btor_bv_get_width (res));
      sres = btor_bv_to_char (d_mm, res);
      sbv  = btor_bv_to_char (d_mm, bv);

      ASSERT_EQ (strncmp (sbv, sres + len, bit_width - len), 0);

      for (j = 0; j < len; j++)
        ASSERT_EQ (sres[j], (ext_func == btor_bv_uext ? '0' : sbv[0]));

      btor_mem_freestr (d_mm, sbv);
      btor_mem_freestr (d_mm, sres);
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv);
    }
  }

  void flipped_bit_bitvec (uint32_t num_tests, uint32_t bit_width)
  {
    uint32_t i, j, pos;
    BtorBitVector *bv, *res;

    for (i = 0; i < num_tests; i++)
    {
      pos = btor_rng_pick_rand (d_rng, 0, bit_width - 1);
      bv  = btor_bv_new_random (d_mm, d_rng, bit_width);
      res = btor_bv_flipped_bit (d_mm, bv, pos);
      ASSERT_EQ (btor_bv_get_bit (bv, pos), !btor_bv_get_bit (res, pos));
      for (j = 0; j < bit_width; j++)
      {
        if (j == pos) continue;
        ASSERT_EQ (btor_bv_get_bit (bv, j), btor_bv_get_bit (res, j));
      }
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv);
    }
  }

  void flipped_bit_range_bitvec (uint32_t num_tests, uint32_t bit_width)
  {
    uint32_t i, j, up, lo;
    BtorBitVector *bv, *res;

    for (i = 0; i < num_tests; i++)
    {
      lo = btor_rng_pick_rand (d_rng, 0, bit_width - 1);
      up = lo == bit_width - 1
               ? bit_width - 1
               : btor_rng_pick_rand (d_rng, lo + 1, bit_width - 1);
      bv  = btor_bv_new_random (d_mm, d_rng, bit_width);
      res = btor_bv_flipped_bit_range (d_mm, bv, up, lo);
      for (j = lo; j <= up; j++)
        ASSERT_EQ (btor_bv_get_bit (bv, j), !btor_bv_get_bit (res, j));
      for (j = 0; j < lo; j++)
        ASSERT_EQ (btor_bv_get_bit (bv, j), btor_bv_get_bit (res, j));
      for (j = up + 1; j < bit_width; j++)
        ASSERT_EQ (btor_bv_get_bit (bv, j), btor_bv_get_bit (res, j));
      btor_bv_free (d_mm, res);
      btor_bv_free (d_mm, bv);
    }
  }

  void is_umulo_bitvec (uint32_t bw)
  {
    BtorBitVector *bv0, *bv1;

    switch (bw)
    {
      case 1:
        TEST_BV_IS_UMULO_BITVEC (bw, 0, 0, false);
        TEST_BV_IS_UMULO_BITVEC (bw, 0, 1, false);
        TEST_BV_IS_UMULO_BITVEC (bw, 1, 1, false);
        break;
      case 7:
        TEST_BV_IS_UMULO_BITVEC (bw, 3, 6, false);
        TEST_BV_IS_UMULO_BITVEC (bw, 124, 2, true);
        break;
      case 31:
        TEST_BV_IS_UMULO_BITVEC (bw, 15, 78, false);
        TEST_BV_IS_UMULO_BITVEC (bw, 1073742058, 2, true);
        break;
      case 33:
        TEST_BV_IS_UMULO_BITVEC (bw, 15, 78, false);
        TEST_BV_IS_UMULO_BITVEC (bw, 4294967530, 4294967530, true);
        break;
    }
  }

  BtorMemMgr *d_mm;
  BtorRNG *d_rng;
};

/* -------------------------------------------------------------------------- */

TEST_F (TestBv, new)
{
  BtorBitVector *bv;

  bv = btor_bv_new (d_mm, BTOR_BV_TYPE_BW);
  ASSERT_EQ (btor_bv_get_len (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_new (d_mm, BTOR_BV_TYPE_BW - 1);
  ASSERT_EQ (btor_bv_get_len (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_new (d_mm, BTOR_BV_TYPE_BW + 1);
  ASSERT_EQ (btor_bv_get_len (bv), 2u);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, new_random_range)
{
  uint32_t bw;
  uint64_t val;
  BtorBitVector *bv, *from, *to, *tmp;

  for (bw = 1; bw <= 64; bw++)
  {
    from = btor_bv_new_random (d_mm, d_rng, bw);
    // from == to
    bv  = btor_bv_new_random_range (d_mm, d_rng, bw, from, from);
    val = btor_bv_to_uint64 (bv);
    ASSERT_EQ (val, btor_bv_to_uint64 (from));
    btor_bv_free (d_mm, bv);
    // from < to
    to = btor_bv_new_random (d_mm, d_rng, bw);
    while (!btor_bv_compare (from, to))
    {
      btor_bv_free (d_mm, to);
      to = btor_bv_new_random (d_mm, d_rng, bw);
    }
    if (btor_bv_to_uint64 (to) < btor_bv_to_uint64 (from))
    {
      tmp  = to;
      to   = from;
      from = tmp;
    }
    bv  = btor_bv_new_random_range (d_mm, d_rng, bw, from, to);
    val = btor_bv_to_uint64 (bv);
    ASSERT_GE (val, btor_bv_to_uint64 (from));
    ASSERT_LE (val, btor_bv_to_uint64 (to));
    btor_bv_free (d_mm, from);
    btor_bv_free (d_mm, to);
    btor_bv_free (d_mm, bv);
  }
}

/*------------------------------------------------------------------------*/

TEST_F (TestBv, uint64_to_bv)
{
  uint64_t i, j, k, l;
  BtorBitVector *bv;

  bv = btor_bv_uint64_to_bv (d_mm, 0, 32);
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_uint64_to_bv (d_mm, UINT32_MAX, 32);
  ASSERT_EQ (btor_bv_to_uint64 (bv), UINT32_MAX);
  btor_bv_free (d_mm, bv);

  for (i = 0; i < 10; i++)
  {
    for (j = 0; j < 5; j++)
    {
      l  = rand () % 32 + 1;
      bv = btor_bv_new_random (d_mm, d_rng, l);
      k  = btor_bv_to_uint64 (bv);
      btor_bv_free (d_mm, bv);
      bv = btor_bv_uint64_to_bv (d_mm, k, l);
      ASSERT_EQ (btor_bv_to_uint64 (bv), k);
      btor_bv_free (d_mm, bv);
    }
  }
}

TEST_F (TestBv, uint64_to_bv_to_uint64)
{
  uint64_t i, x, y;
  BtorBitVector *a;

  for (i = 0; i < 10000000; i++)
  {
    x = ((uint64_t) rand ()) << 32;
    x |= (uint64_t) rand ();
    a = btor_bv_uint64_to_bv (d_mm, x, 64);
    y = btor_bv_to_uint64 (a);
    ASSERT_EQ (x, y);
    btor_bv_free (d_mm, a);
  }
}

TEST_F (TestBv, int64_to_bv)
{
  uint64_t i;
  BtorBitVector *a;
  char *str_a;
  const char *s;
  int64_t x[] = {
      -1,
      -2,
      -3,
      -123,
      3,
  };
  const char *str_x[] = {
      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111111111111",

      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111111111110",

      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "1111111111111111111111111111101",

      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111110000101",

      "00000000000000000000000000000000"
      "00000000000000000000000000000000"
      "00000000000000000000000000000011",

      0};

  for (i = 0; str_x[i]; i++)
  {
    s     = str_x[i];
    a     = btor_bv_int64_to_bv (d_mm, x[i], strlen (s));
    str_a = btor_bv_to_char (d_mm, a);
    ASSERT_EQ (strcmp (str_a, s), 0);
    btor_bv_free (d_mm, a);
    btor_mem_freestr (d_mm, str_a);
  }
}

/*------------------------------------------------------------------------*/

TEST_F (TestBv, char_to_bv)
{
  BtorBitVector *bv;

  bv = btor_bv_char_to_bv (d_mm, "0");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "01");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 2u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 3u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "001");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "010");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 2u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "011");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 3u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "100");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 4u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "101");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 5u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "110");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 6u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 7u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000000001");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000000010");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 2u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000000100");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 4u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000001000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 8u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000010000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 16u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000000100000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 32u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000001000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 64u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000010000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 128u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000000100000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 256u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000001000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 512u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000010000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1024u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000000100000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 2048u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000001000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 4096u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000010000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 8192u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000000100000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 16384u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000001000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 32768u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000010000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 65536u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000000100000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 131072u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000001000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 262144u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000010000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 524288u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000000100000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1048576u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000001000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 2097152u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000010000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 4194304u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000000100000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 8388608u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000001000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 16777216u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000010000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 33554432u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00000100000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 67108864u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00001000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 134217728u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00010000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 268435456u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00100000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 536870912u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "01000000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1073741824u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 2147483648u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11111111111111111111111111111111");
  ASSERT_EQ (btor_bv_to_uint64 (bv), UINT32_MAX);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000000000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000000000000000000000000000000001");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111111111111111111111111111111111");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 8589934591u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000000000000000000000000000000000");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 0u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000000000000000000000000000000001");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 1u);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1111111111111111111111111111111111");
  ASSERT_EQ (btor_bv_to_uint64 (bv), 17179869183u);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, bv_to_char)
{
  uint32_t i, j, k;
  uint32_t b;
  char *s;
  BtorBitVector *bv;

  for (i = 1; i < 4; i++)
  {
    for (j = 0; j < (1u << i); j++)
    {
      bv = btor_bv_uint64_to_bv (d_mm, j, i);
      TEST_BV_CHECK_CHAR_TO_BV (bv, i);
    }
  }

  bv = btor_bv_uint64_to_bv (d_mm, UINT32_MAX, 32);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 32);

  bv = btor_bv_uint64_to_bv (d_mm, 0, 32);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 32);

  bv = btor_bv_uint64_to_bv (d_mm, 1, 32);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 32);

  for (i = 0; i < 20; i++)
  {
    bv = btor_bv_new_random (d_mm, d_rng, 32);
    TEST_BV_CHECK_CHAR_TO_BV (bv, 32);
  }

  bv = btor_bv_uint64_to_bv (d_mm, 8589934591, 33);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 33);

  bv = btor_bv_uint64_to_bv (d_mm, 0, 33);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 33);

  bv = btor_bv_uint64_to_bv (d_mm, 1, 33);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 33);

  bv = btor_bv_uint64_to_bv (d_mm, 17179869183, 34);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 34);

  bv = btor_bv_uint64_to_bv (d_mm, 0, 34);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 34);

  bv = btor_bv_uint64_to_bv (d_mm, 1, 34);
  TEST_BV_CHECK_CHAR_TO_BV (bv, 34);
}

/*------------------------------------------------------------------------*/

TEST_F (TestBv, bv_to_hex_char)
{
  open_log_file ("bv_to_hex_char_bitvec");
  bv_to_hex_char_bitvec (d_log_file, "1");
  bv_to_hex_char_bitvec (d_log_file, "10");
  bv_to_hex_char_bitvec (d_log_file, "11");
  bv_to_hex_char_bitvec (d_log_file, "100");
  bv_to_hex_char_bitvec (d_log_file, "101");
  bv_to_hex_char_bitvec (d_log_file, "110");
  bv_to_hex_char_bitvec (d_log_file, "111");
  bv_to_hex_char_bitvec (d_log_file, "1000");
  bv_to_hex_char_bitvec (d_log_file, "1001");
  bv_to_hex_char_bitvec (d_log_file, "1010");
  bv_to_hex_char_bitvec (d_log_file, "1011");
  bv_to_hex_char_bitvec (d_log_file, "1100");
  bv_to_hex_char_bitvec (d_log_file, "1101");
  bv_to_hex_char_bitvec (d_log_file, "1110");
  bv_to_hex_char_bitvec (d_log_file, "1111");
  bv_to_hex_char_bitvec (d_log_file, "10000");
  bv_to_hex_char_bitvec (d_log_file, "10001");
  bv_to_hex_char_bitvec (d_log_file, "1111111111111111");
  bv_to_hex_char_bitvec (d_log_file, "11111111111111111");
  bv_to_hex_char_bitvec (d_log_file, "00001111111111111111");
  bv_to_hex_char_bitvec (d_log_file, "000011111111111111111");
}

TEST_F (TestBv, bv_to_dec_char)
{
  open_log_file ("bv_to_dec_char_bitvec");
  bv_to_dec_char_bitvec (d_log_file, "1");
  bv_to_dec_char_bitvec (d_log_file, "10");
  bv_to_dec_char_bitvec (d_log_file, "11");
  bv_to_dec_char_bitvec (d_log_file, "100");
  bv_to_dec_char_bitvec (d_log_file, "101");
  bv_to_dec_char_bitvec (d_log_file, "110");
  bv_to_dec_char_bitvec (d_log_file, "111");
  bv_to_dec_char_bitvec (d_log_file, "1000");
  bv_to_dec_char_bitvec (d_log_file, "1001");
  bv_to_dec_char_bitvec (d_log_file, "1010");
  bv_to_dec_char_bitvec (d_log_file, "1011");
  bv_to_dec_char_bitvec (d_log_file, "1100");
  bv_to_dec_char_bitvec (d_log_file, "1101");
  bv_to_dec_char_bitvec (d_log_file, "1110");
  bv_to_dec_char_bitvec (d_log_file, "1111");
  bv_to_dec_char_bitvec (d_log_file, "10000");
  bv_to_dec_char_bitvec (d_log_file, "10001");
  bv_to_dec_char_bitvec (d_log_file, "10000000000000000");
  bv_to_dec_char_bitvec (d_log_file,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  bv_to_dec_char_bitvec (d_log_file,
                         "1"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000"
                         "00000000");
  bv_to_dec_char_bitvec (d_log_file,
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

/*------------------------------------------------------------------------*/

TEST_F (TestBv, one)
{
  int32_t i;
  char *s, *sbv;
  BtorBitVector *bv;

  for (i = 1; i < 32; i++)
  {
    bv = btor_bv_one (d_mm, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '0', i - 1);
    s[i - 1] = '1';
    sbv      = btor_bv_to_char (d_mm, bv);
    ASSERT_EQ (strcmp (s, sbv), 0);
    btor_bv_free (d_mm, bv);
    BTOR_DELETEN (d_mm, s, i + 1);
    btor_mem_freestr (d_mm, sbv);
  }
}

TEST_F (TestBv, ones)
{
  int32_t i;
  char *s, *sbv;
  BtorBitVector *bv;

  for (i = 1; i < 32; i++)
  {
    bv = btor_bv_ones (d_mm, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '1', i);
    sbv = btor_bv_to_char (d_mm, bv);
    ASSERT_EQ (strcmp (s, sbv), 0);
    btor_bv_free (d_mm, bv);
    BTOR_DELETEN (d_mm, s, i + 1);
    btor_mem_freestr (d_mm, sbv);
  }
}

TEST_F (TestBv, min_signed)
{
  int32_t i;
  char *s, *sbv;
  BtorBitVector *bv;

  for (i = 1; i < 32; i++)
  {
    bv = btor_bv_min_signed (d_mm, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '0', i);
    s[0] = '1';
    sbv  = btor_bv_to_char (d_mm, bv);
    ASSERT_TRUE (btor_bv_is_min_signed (bv));
    ASSERT_EQ (strcmp (s, sbv), 0);
    btor_bv_free (d_mm, bv);
    BTOR_DELETEN (d_mm, s, i + 1);
    btor_mem_freestr (d_mm, sbv);
  }
}

TEST_F (TestBv, max_signed)
{
  int32_t i;
  char *s, *sbv;
  BtorBitVector *bv;

  for (i = 1; i < 32; i++)
  {
    bv = btor_bv_max_signed (d_mm, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '1', i);
    s[0] = '0';
    sbv  = btor_bv_to_char (d_mm, bv);
    ASSERT_TRUE (btor_bv_is_max_signed (bv));
    ASSERT_EQ (strcmp (s, sbv), 0);
    btor_bv_free (d_mm, bv);
    BTOR_DELETEN (d_mm, s, i + 1);
    btor_mem_freestr (d_mm, sbv);
  }
}

TEST_F (TestBv, not)
{
  unary_bitvec (_not, btor_bv_not, BTOR_TEST_BITVEC_TESTS, 1);
  unary_bitvec (_not, btor_bv_not, BTOR_TEST_BITVEC_TESTS, 7);
  unary_bitvec (_not, btor_bv_not, BTOR_TEST_BITVEC_TESTS, 31);
  unary_bitvec (_not, btor_bv_not, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, neg)
{
  unary_bitvec (neg, btor_bv_neg, BTOR_TEST_BITVEC_TESTS, 1);
  unary_bitvec (neg, btor_bv_neg, BTOR_TEST_BITVEC_TESTS, 7);
  unary_bitvec (neg, btor_bv_neg, BTOR_TEST_BITVEC_TESTS, 31);
  unary_bitvec (neg, btor_bv_neg, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, inc)
{
  unary_bitvec (inc, btor_bv_inc, BTOR_TEST_BITVEC_TESTS, 1);
  unary_bitvec (inc, btor_bv_inc, BTOR_TEST_BITVEC_TESTS, 7);
  unary_bitvec (inc, btor_bv_inc, BTOR_TEST_BITVEC_TESTS, 31);
  unary_bitvec (inc, btor_bv_inc, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, dec)
{
  unary_bitvec (dec, btor_bv_dec, BTOR_TEST_BITVEC_TESTS, 1);
  unary_bitvec (dec, btor_bv_dec, BTOR_TEST_BITVEC_TESTS, 7);
  unary_bitvec (dec, btor_bv_dec, BTOR_TEST_BITVEC_TESTS, 31);
  unary_bitvec (dec, btor_bv_dec, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, add)
{
  binary_bitvec (add, btor_bv_add, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (add, btor_bv_add, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (add, btor_bv_add, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (add, btor_bv_add, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, sub)
{
  binary_bitvec (sub, btor_bv_sub, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (sub, btor_bv_sub, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (sub, btor_bv_sub, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (sub, btor_bv_sub, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, and)
{
  binary_bitvec (_and, btor_bv_and, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (_and, btor_bv_and, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (_and, btor_bv_and, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (_and, btor_bv_and, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (_and, btor_bv_and, BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, implies)
{
  binary_bitvec (implies, btor_bv_implies, BTOR_TEST_BITVEC_TESTS, 1);
}

TEST_F (TestBv, xor)
{
  binary_bitvec (_xor, btor_bv_xor, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (_xor, btor_bv_xor, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (_xor, btor_bv_xor, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (_xor, btor_bv_xor, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (_xor, btor_bv_xor, BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, eq)
{
  binary_bitvec (eq, btor_bv_eq, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (eq, btor_bv_eq, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (eq, btor_bv_eq, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (eq, btor_bv_eq, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (eq, btor_bv_eq, BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, ult)
{
  binary_bitvec (ult, btor_bv_ult, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (ult, btor_bv_ult, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (ult, btor_bv_ult, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (ult, btor_bv_ult, BTOR_TEST_BITVEC_TESTS, 33);
  binary_bitvec (ult, btor_bv_ult, BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, sll)
{
  binary_bitvec (sll, btor_bv_sll, BTOR_TEST_BITVEC_TESTS, 2);
  binary_bitvec (sll, btor_bv_sll, BTOR_TEST_BITVEC_TESTS, 8);
  binary_bitvec (sll, btor_bv_sll, BTOR_TEST_BITVEC_TESTS, 16);
  binary_bitvec (sll, btor_bv_sll, BTOR_TEST_BITVEC_TESTS, 32);
}

TEST_F (TestBv, srl)
{
  binary_bitvec (srl, btor_bv_srl, BTOR_TEST_BITVEC_TESTS, 2);
  binary_bitvec (srl, btor_bv_srl, BTOR_TEST_BITVEC_TESTS, 8);
  binary_bitvec (srl, btor_bv_srl, BTOR_TEST_BITVEC_TESTS, 16);
  binary_bitvec (srl, btor_bv_srl, BTOR_TEST_BITVEC_TESTS, 32);
}

TEST_F (TestBv, mul)
{
  binary_bitvec (mul, btor_bv_mul, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (mul, btor_bv_mul, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (mul, btor_bv_mul, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (mul, btor_bv_mul, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, udiv)
{
  binary_bitvec (udiv, btor_bv_udiv, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (udiv, btor_bv_udiv, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (udiv, btor_bv_udiv, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (udiv, btor_bv_udiv, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, urem)
{
  binary_bitvec (urem, btor_bv_urem, BTOR_TEST_BITVEC_TESTS, 1);
  binary_bitvec (urem, btor_bv_urem, BTOR_TEST_BITVEC_TESTS, 7);
  binary_bitvec (urem, btor_bv_urem, BTOR_TEST_BITVEC_TESTS, 31);
  binary_bitvec (urem, btor_bv_urem, BTOR_TEST_BITVEC_TESTS, 33);
}

TEST_F (TestBv, concat)
{
  concat_bitvec (BTOR_TEST_BITVEC_TESTS, 2);
  concat_bitvec (BTOR_TEST_BITVEC_TESTS, 7);
  concat_bitvec (BTOR_TEST_BITVEC_TESTS, 31);
  concat_bitvec (BTOR_TEST_BITVEC_TESTS, 33);
  concat_bitvec (BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, slice)
{
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 1);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 7);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 31);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 33);
  slice_bitvec (BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, uext)
{
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 2);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 3);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 4);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 5);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 6);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 7);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 31);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 33);
  ext_bitvec (btor_bv_uext, BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, sext)
{
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 2);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 3);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 4);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 5);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 6);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 7);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 31);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 33);
  ext_bitvec (btor_bv_sext, BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, flipped_bit)
{
  flipped_bit_bitvec (BTOR_TEST_BITVEC_TESTS, 1);
  flipped_bit_bitvec (BTOR_TEST_BITVEC_TESTS, 7);
  flipped_bit_bitvec (BTOR_TEST_BITVEC_TESTS, 31);
  flipped_bit_bitvec (BTOR_TEST_BITVEC_TESTS, 33);
  flipped_bit_bitvec (BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, flipped_bit_range)
{
  flipped_bit_range_bitvec (BTOR_TEST_BITVEC_TESTS, 1);
  flipped_bit_range_bitvec (BTOR_TEST_BITVEC_TESTS, 7);
  flipped_bit_range_bitvec (BTOR_TEST_BITVEC_TESTS, 31);
  flipped_bit_range_bitvec (BTOR_TEST_BITVEC_TESTS, 33);
  flipped_bit_range_bitvec (BTOR_TEST_BITVEC_TESTS, 64);
}

TEST_F (TestBv, is_umulo)
{
  is_umulo_bitvec (1);
  is_umulo_bitvec (7);
  is_umulo_bitvec (31);
  is_umulo_bitvec (33);
}

TEST_F (TestBv, compare)
{
  int32_t i, j, k;
  BtorBitVector *bv1, *bv2;

  for (i = 0; i < 15; i++)
  {
    bv1 = btor_bv_uint64_to_bv (d_mm, i, 4);
    bv2 = btor_bv_uint64_to_bv (d_mm, i, 4);
    ASSERT_EQ (btor_bv_compare (bv1, bv2), 0);
    btor_bv_free (d_mm, bv1);
    btor_bv_free (d_mm, bv2);
  }

  for (i = 0; i < 15 - 1; i++)
  {
    bv1 = btor_bv_uint64_to_bv (d_mm, i, 4);
    bv2 = btor_bv_uint64_to_bv (d_mm, i + 1, 4);
    ASSERT_LT (btor_bv_compare (bv1, bv2), 0);
    ASSERT_GT (btor_bv_compare (bv2, bv1), 0);
    btor_bv_free (d_mm, bv1);
    btor_bv_free (d_mm, bv2);
  }

  for (i = 0, j = 0, k = 0; i < 15; i++)
  {
    k = rand () % 16;
    do
      j = rand () % 16;
    while (j == k);
    bv1 = btor_bv_uint64_to_bv (d_mm, j, 4);
    bv2 = btor_bv_uint64_to_bv (d_mm, k, 4);
    if (j > k)
    {
      ASSERT_GT (btor_bv_compare (bv1, bv2), 0);
      ASSERT_LT (btor_bv_compare (bv2, bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT (btor_bv_compare (bv1, bv2), 0);
      ASSERT_GT (btor_bv_compare (bv2, bv1), 0);
    }
    btor_bv_free (d_mm, bv1);
    btor_bv_free (d_mm, bv2);
  }
}

TEST_F (TestBv, is_one)
{
  int32_t i;
  char *s;
  BtorBitVector *bv1, *bv2, *bv3;

  for (i = 1; i < 32; i++)
  {
    bv1 = btor_bv_one (d_mm, i);
    bv2 = btor_bv_uint64_to_bv (d_mm, 1, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '0', i - 1);
    s[i - 1] = '1';
    bv3      = btor_bv_char_to_bv (d_mm, s);
    ASSERT_TRUE (btor_bv_is_one (bv1));
    ASSERT_TRUE (btor_bv_is_one (bv2));
    ASSERT_TRUE (btor_bv_is_one (bv3));
    ASSERT_EQ (btor_bv_compare (bv1, bv2), 0);
    ASSERT_EQ (btor_bv_compare (bv1, bv3), 0);
    btor_bv_free (d_mm, bv1);
    btor_bv_free (d_mm, bv2);
    btor_bv_free (d_mm, bv3);
    BTOR_DELETEN (d_mm, s, i + 1);
  }
}

TEST_F (TestBv, is_ones)
{
  int32_t i;
  char *s;
  BtorBitVector *bv1, *bv2, *bv3;

  for (i = 1; i < 32; i++)
  {
    bv1 = btor_bv_ones (d_mm, i);
    bv2 = btor_bv_uint64_to_bv (d_mm, UINT32_MAX, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '1', i);
    bv3 = btor_bv_char_to_bv (d_mm, s);
    ASSERT_TRUE (btor_bv_is_ones (bv1));
    ASSERT_TRUE (btor_bv_is_ones (bv2));
    ASSERT_TRUE (btor_bv_is_ones (bv3));
    ASSERT_EQ (btor_bv_compare (bv1, bv2), 0);
    ASSERT_EQ (btor_bv_compare (bv1, bv3), 0);
    btor_bv_free (d_mm, bv1);
    btor_bv_free (d_mm, bv2);
    btor_bv_free (d_mm, bv3);
    BTOR_DELETEN (d_mm, s, i + 1);
  }
}

TEST_F (TestBv, is_zero)
{
  int32_t i;
  char *s;
  BtorBitVector *bv1, *bv2, *bv3;

  for (i = 1; i < 32; i++)
  {
    bv1 = btor_bv_new (d_mm, i);
    bv2 = btor_bv_uint64_to_bv (d_mm, 0, i);
    BTOR_CNEWN (d_mm, s, i + 1);
    memset (s, '0', i);
    bv3 = btor_bv_char_to_bv (d_mm, s);
    ASSERT_TRUE (btor_bv_is_zero (bv1));
    ASSERT_TRUE (btor_bv_is_zero (bv2));
    ASSERT_TRUE (btor_bv_is_zero (bv3));
    ASSERT_EQ (btor_bv_compare (bv1, bv2), 0);
    ASSERT_EQ (btor_bv_compare (bv1, bv3), 0);
    btor_bv_free (d_mm, bv1);
    btor_bv_free (d_mm, bv2);
    btor_bv_free (d_mm, bv3);
    BTOR_DELETEN (d_mm, s, i + 1);
  }
}

TEST_F (TestBv, is_special_const)
{
  int32_t i;
  BtorBitVector *bv;

  bv = btor_bv_char_to_bv (d_mm, "0");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ZERO);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONE_ONES);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ZERO);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "01");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONE);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_NONE);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONES);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ZERO);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "001");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONE);
  btor_bv_free (d_mm, bv);

  for (i = 2; i < 7; i++)
  {
    bv = btor_bv_uint64_to_bv (d_mm, i, 3);
    ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_NONE);
    btor_bv_free (d_mm, bv);
  }

  bv = btor_bv_char_to_bv (d_mm, "111");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONES);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ZERO);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONE);
  btor_bv_free (d_mm, bv);

  for (i = 2; i < 15; i++)
  {
    bv = btor_bv_uint64_to_bv (d_mm, i, 4);
    ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_NONE);
    btor_bv_free (d_mm, bv);
  }

  bv = btor_bv_char_to_bv (d_mm, "1111");
  ASSERT_EQ (btor_bv_is_special_const (bv), BTOR_SPECIAL_CONST_BV_ONES);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, power_of_two)
{
  BtorBitVector *bv;

  bv = btor_bv_char_to_bv (
      d_mm, "0000000000000000000000000000000000000000000000000000000000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "001");
  ASSERT_EQ (btor_bv_power_of_two (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010");
  ASSERT_EQ (btor_bv_power_of_two (bv), 1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00100");
  ASSERT_EQ (btor_bv_power_of_two (bv), 2);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "001000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 3);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 4);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 5);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 6);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00010000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 7);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 8);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 9);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000010000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 10);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000000000000000000000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 28);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "100000000000000000000000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 29);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1000000000000000000000000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 30);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "01000000000000000000000000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), 30);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "1110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "11110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "1111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "111111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "1111111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "11111111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "111111111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "1111111111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);

  btor_bv_free (d_mm, bv);
  bv = btor_bv_char_to_bv (d_mm, "1111111111111110");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "011");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0011");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00101");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "101101");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010001");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100111");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1001000001");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11010000001");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100000011");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001000000111");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000010000001111");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000000000000000000000000010");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "100000000000000000000001000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1000000000000100000000000000000");
  ASSERT_EQ (btor_bv_power_of_two (bv), -1);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, small_positive_int)
{
  BtorBitVector *bv;

  bv = btor_bv_char_to_bv (
      d_mm, "0000000000000000000000000000000000000000000000000000000000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "001");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 1);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 2);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00100");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 4);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "001000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 8);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 16);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 32);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 64);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00010000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 128);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 256);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 512);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000010000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 1024);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000000000000000000000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), (1 << 28));
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "100000000000000000000000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), (1 << 29));
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1000000000000000000000000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), (1 << 30));
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "01000000000000000000000000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), (1 << 30));
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 6);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 14);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 30);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 62);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 126);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 510);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1111111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 1022);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11111111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 2046);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111111111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 4094);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1111111111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 8190);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1111111111111110");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 65534);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "011");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 3);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "111");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 7);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0011");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 3);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00101");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 5);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "101101");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 45);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "00100001");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 33);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100111");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 39);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1001000001");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 577);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "11010000001");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 1665);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "000100000011");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 259);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0001000000111");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 519);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0000010000001111");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 1039);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000000000000000000000000010");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 268435458);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "100000000000000000000001000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 536870976);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "1000000000000100000000000000000");
  ASSERT_EQ (btor_bv_small_positive_int (bv), 1073872896);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000000000000000000000000000000");
  ASSERT_LT (btor_bv_small_positive_int (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "10000100000000000000000011100000");
  ASSERT_LT (btor_bv_small_positive_int (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010000000000000000000000000000000");
  ASSERT_LT (btor_bv_small_positive_int (bv), 0);
  btor_bv_free (d_mm, bv);

  bv = btor_bv_char_to_bv (d_mm, "0010000000000100000000000011110000");
  ASSERT_LT (btor_bv_small_positive_int (bv), 0);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, get_num_trailing_zeros)
{
  BtorBitVector *bv;

  // 1000
  bv = btor_bv_uint64_to_bv (d_mm, 8, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 3u);
  btor_bv_free (d_mm, bv);

  // 0100
  bv = btor_bv_uint64_to_bv (d_mm, 4, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 2u);
  btor_bv_free (d_mm, bv);

  // 0010
  bv = btor_bv_uint64_to_bv (d_mm, 2, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 0001
  bv = btor_bv_uint64_to_bv (d_mm, 1, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 0000
  bv = btor_bv_uint64_to_bv (d_mm, 0, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 4u);
  btor_bv_free (d_mm, bv);

  // 1111
  bv = btor_bv_uint64_to_bv (d_mm, 15, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 0110
  bv = btor_bv_uint64_to_bv (d_mm, 6, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 0111
  bv = btor_bv_uint64_to_bv (d_mm, 7, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 1010
  bv = btor_bv_uint64_to_bv (d_mm, 10, 4);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 0
  bv = btor_bv_uint64_to_bv (d_mm, 0, 1);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 1
  bv = btor_bv_uint64_to_bv (d_mm, 1, 1);
  ASSERT_EQ (btor_bv_get_num_trailing_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, test_get_num_leading_zeros)
{
  BtorBitVector *bv;

  // 1000
  bv = btor_bv_uint64_to_bv (d_mm, 8, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 0100
  bv = btor_bv_uint64_to_bv (d_mm, 4, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 0010
  bv = btor_bv_uint64_to_bv (d_mm, 2, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 2u);
  btor_bv_free (d_mm, bv);

  // 0001
  bv = btor_bv_uint64_to_bv (d_mm, 1, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 3u);
  btor_bv_free (d_mm, bv);

  // 0000
  bv = btor_bv_uint64_to_bv (d_mm, 0, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 4u);
  btor_bv_free (d_mm, bv);

  // 1111
  bv = btor_bv_uint64_to_bv (d_mm, 15, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 0110
  bv = btor_bv_uint64_to_bv (d_mm, 6, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 0111
  bv = btor_bv_uint64_to_bv (d_mm, 7, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 1010
  bv = btor_bv_uint64_to_bv (d_mm, 10, 4);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 0
  bv = btor_bv_uint64_to_bv (d_mm, 0, 1);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 1
  bv = btor_bv_uint64_to_bv (d_mm, 1, 1);
  ASSERT_EQ (btor_bv_get_num_leading_zeros (bv), 0u);
  btor_bv_free (d_mm, bv);
}

TEST_F (TestBv, test_get_num_leading_ones)
{
  BtorBitVector *bv;

  // 1000
  bv = btor_bv_uint64_to_bv (d_mm, 8, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 1100
  bv = btor_bv_uint64_to_bv (d_mm, 12, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 2u);
  btor_bv_free (d_mm, bv);

  // 1110
  bv = btor_bv_uint64_to_bv (d_mm, 14, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 3u);
  btor_bv_free (d_mm, bv);

  // 1111
  bv = btor_bv_uint64_to_bv (d_mm, 15, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 4u);
  btor_bv_free (d_mm, bv);

  // 0000
  bv = btor_bv_uint64_to_bv (d_mm, 0, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 1011
  bv = btor_bv_uint64_to_bv (d_mm, 11, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 1101
  bv = btor_bv_uint64_to_bv (d_mm, 13, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 2u);
  btor_bv_free (d_mm, bv);

  // 1001
  bv = btor_bv_uint64_to_bv (d_mm, 9, 4);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 1u);
  btor_bv_free (d_mm, bv);

  // 0
  bv = btor_bv_uint64_to_bv (d_mm, 0, 1);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 0u);
  btor_bv_free (d_mm, bv);

  // 1
  bv = btor_bv_uint64_to_bv (d_mm, 1, 1);
  ASSERT_EQ (btor_bv_get_num_leading_ones (bv), 1u);
  btor_bv_free (d_mm, bv);
}

// TODO btor_bv_new_random
// TODO btor_bv_new_random_bit_range
// TODO btor_bv_dec_to_bv
// TODO btor_bv_const
// TODO btor_bv_constd
// TODO btor_bv_consth
// TODO btor_bv_get_assignment
// TODO btor_bv_copy

// TODO btor_bv_hash

// TODO btor_bv_get_bit
// TODO btor_bv_set_bit
// TODO btor_bv_flip_bit
// TODO btor_bv_nand
// TODO btor_bv_or
// TODO btor_bv_nor
// TODO btor_bv_xnor
// TODO btor_bv_ne
// TODO btor_bv_ulte
// TODO btor_bv_redor
// TODO btor_bv_redand
// TODO btor_bv_ite
// TODO btor_bv_mod_inverse
// TODO btor_bv_is_true
// TODO btor_bv_is_false

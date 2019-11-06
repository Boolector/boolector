/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/btorutil.h"
}

#define BTOR_TEST_RED_LOGIC_XOR(a, b) (((a) || (b)) && !((a) && (b)))

class TestLogic : public TestBoolector
{
 protected:
  static constexpr uint32_t BTOR_TEST_LOGIC_LOW  = 1;
  static constexpr uint32_t BTOR_TEST_LOGIC_HIGH = 4;

  static constexpr uint32_t BTOR_TEST_RED_LOGIC_LOW  = 2;
  static constexpr uint32_t BTOR_TEST_RED_LOGIC_HIGH = 4;

  void not_logic_test (int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    uint32_t i       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        BoolectorSort sort;
        BoolectorNode *const1, *const2, *eq, *inv;

        if (d_btor) boolector_delete (d_btor);
        d_btor = boolector_new ();

        boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);

        result = ~i & (max - 1);

        sort   = boolector_bitvec_sort (d_btor, num_bits);
        const1 = boolector_unsigned_int (d_btor, i, sort);
        const2 = boolector_unsigned_int (d_btor, result, sort);
        inv    = boolector_not (d_btor, const1);
        eq     = boolector_eq (d_btor, inv, const2);
        boolector_assert (d_btor, eq);

        ASSERT_EQ (boolector_sat (d_btor), BOOLECTOR_SAT);
        boolector_release (d_btor, inv);
        boolector_release (d_btor, eq);
        boolector_release (d_btor, const1);
        boolector_release (d_btor, const2);
        boolector_release_sort (d_btor, sort);
        boolector_delete (d_btor);
        d_btor = nullptr;
      }
    }
  }

  void binary_logic_test (uint32_t (*func) (uint32_t, uint32_t),
                          BoolectorNode *(*btor_fun) (Btor *,
                                                      BoolectorNode *,
                                                      BoolectorNode *),
                          int32_t low,
                          int32_t high,
                          uint32_t rwl)
  {
    assert (func != NULL);
    assert (low > 0);
    assert (low <= high);

    uint32_t i       = 0;
    uint32_t j       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        for (j = 0; j < (uint32_t) max; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *const3, *eq, *bfun;

          if (d_btor) boolector_delete (d_btor);
          d_btor = boolector_new ();
          boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          result = func (i, j);

          sort   = boolector_bitvec_sort (d_btor, num_bits);
          const1 = boolector_unsigned_int (d_btor, i, sort);
          const2 = boolector_unsigned_int (d_btor, j, sort);
          bfun   = btor_fun (d_btor, const1, const2);
          const3 = boolector_unsigned_int (d_btor, result, sort);
          eq     = boolector_eq (d_btor, bfun, const3);
          boolector_assert (d_btor, eq);

          ASSERT_EQ (boolector_sat (d_btor), BOOLECTOR_SAT);
          boolector_release (d_btor, eq);
          boolector_release (d_btor, const1);
          boolector_release (d_btor, const2);
          boolector_release (d_btor, const3);
          boolector_release (d_btor, bfun);
          boolector_release_sort (d_btor, sort);
          boolector_delete (d_btor);
          d_btor = nullptr;
        }
      }
    }
  }

  void xnor_logic_test (int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    uint32_t i       = 0;
    uint32_t j       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        for (j = 0; j < (uint32_t) max; j++)
        {
          for (j = 0; j < (uint32_t) max; j++)
          {
            BoolectorSort sort;
            BoolectorNode *const1, *const2, *const3, *eq, *xnor;

            if (d_btor) boolector_delete (d_btor);
            d_btor = boolector_new ();
            boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);

            result = ~(i ^ j) & (max - 1);

            sort   = boolector_bitvec_sort (d_btor, num_bits);
            const1 = boolector_unsigned_int (d_btor, i, sort);
            const2 = boolector_unsigned_int (d_btor, j, sort);
            xnor   = boolector_xnor (d_btor, const1, const2);
            const3 = boolector_unsigned_int (d_btor, result, sort);
            eq     = boolector_eq (d_btor, xnor, const3);
            boolector_assert (d_btor, eq);

            ASSERT_EQ (boolector_sat (d_btor), BOOLECTOR_SAT);
            boolector_release (d_btor, eq);
            boolector_release (d_btor, const1);
            boolector_release (d_btor, const2);
            boolector_release (d_btor, const3);
            boolector_release (d_btor, xnor);
            boolector_release_sort (d_btor, sort);
            boolector_delete (d_btor);
            d_btor = nullptr;
          }
        }
      }
    }
  }

  void red_logic_test (uint32_t (*func) (uint32_t, uint32_t),
                       BoolectorNode *(*btor_fun) (Btor *, BoolectorNode *),
                       int32_t low,
                       int32_t high,
                       uint32_t rwl)
  {
    assert (func != NULL);
    assert (low > 0);
    assert (low <= high);

    int32_t sat_res;
    uint32_t i       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        BoolectorSort sort;
        BoolectorNode *const1, *bfun;

        if (d_btor) boolector_delete (d_btor);
        d_btor = boolector_new ();
        boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);

        result = func (i, (uint32_t) num_bits);

        sort   = boolector_bitvec_sort (d_btor, num_bits);
        const1 = boolector_unsigned_int (d_btor, i, sort);
        bfun   = btor_fun (d_btor, const1);
        boolector_assert (d_btor, bfun);

        sat_res = boolector_sat (d_btor);
        ASSERT_TRUE ((result && sat_res == BOOLECTOR_SAT)
                     || (!result && sat_res == BOOLECTOR_UNSAT));
        boolector_release (d_btor, const1);
        boolector_release (d_btor, bfun);
        boolector_release_sort (d_btor, sort);
        boolector_delete (d_btor);
        d_btor = nullptr;
      }
    }
  }

  static uint32_t _and (uint32_t x, uint32_t y) { return x & y; }

  static uint32_t _or (uint32_t x, uint32_t y) { return x | y; }

  static uint32_t _xor (uint32_t x, uint32_t y) { return x ^ y; }

  static uint32_t redand (uint32_t x, uint32_t num_bits)
  {
    uint32_t result = 1;
    uint32_t i      = 0;
    assert (num_bits > 1);
    assert (num_bits <= 32);
    for (i = 0; result && i < num_bits; i++) result = result && (x & (1 << i));
    return result;
  }

  static uint32_t redor (uint32_t x, uint32_t num_bits)
  {
    uint32_t result = 0;
    uint32_t i      = 0;
    assert (num_bits > 1);
    assert (num_bits <= 32);
    for (i = 0; !result && i < num_bits; i++) result = result || (x & (1 << i));
    return result;
  }

  static uint32_t redxor (uint32_t x, uint32_t num_bits)
  {
    uint32_t result = 0;
    uint32_t i      = 0;
    assert (num_bits > 1);
    assert (num_bits <= 32);
    result = BTOR_TEST_RED_LOGIC_XOR (x & 1, x & 2);
    for (i = 2; i < num_bits; i++)
      result = BTOR_TEST_RED_LOGIC_XOR (result, x & (1 << i));
    return result;
  }
};

TEST_F (TestLogic, not)
{
  not_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  not_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

TEST_F (TestLogic, and)
{
  binary_logic_test (
      _and, boolector_and, BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  binary_logic_test (
      _and, boolector_and, BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

TEST_F (TestLogic, or)
{
  binary_logic_test (
      _or, boolector_or, BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  binary_logic_test (
      _or, boolector_or, BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

TEST_F (TestLogic, xor)
{
  binary_logic_test (
      _xor, boolector_xor, BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  binary_logic_test (
      _xor, boolector_xor, BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

TEST_F (TestLogic, xnor)
{
  xnor_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 1);
  xnor_logic_test (BTOR_TEST_LOGIC_LOW, BTOR_TEST_LOGIC_HIGH, 0);
}

TEST_F (TestLogic, redand)
{
  red_logic_test (redand,
                  boolector_redand,
                  BTOR_TEST_RED_LOGIC_LOW,
                  BTOR_TEST_RED_LOGIC_HIGH,
                  1);
  red_logic_test (redand,
                  boolector_redand,
                  BTOR_TEST_RED_LOGIC_LOW,
                  BTOR_TEST_RED_LOGIC_HIGH,
                  0);
}

TEST_F (TestLogic, redor)
{
  red_logic_test (redor,
                  boolector_redor,
                  BTOR_TEST_RED_LOGIC_LOW,
                  BTOR_TEST_RED_LOGIC_HIGH,
                  1);
  red_logic_test (redor,
                  boolector_redor,
                  BTOR_TEST_RED_LOGIC_LOW,
                  BTOR_TEST_RED_LOGIC_HIGH,
                  0);
}

TEST_F (TestLogic, redxor)
{
  red_logic_test (redxor,
                  boolector_redxor,
                  BTOR_TEST_RED_LOGIC_LOW,
                  BTOR_TEST_RED_LOGIC_HIGH,
                  1);
  red_logic_test (redxor,
                  boolector_redxor,
                  BTOR_TEST_RED_LOGIC_LOW,
                  BTOR_TEST_RED_LOGIC_HIGH,
                  0);
}

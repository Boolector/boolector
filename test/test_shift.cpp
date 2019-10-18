/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
#include "utils/btorutil.h"
}

class TestShift : public TestMm
{
 protected:
  static constexpr uint32_t BTOR_TEST_SHIFT_LOW  = 2;
  static constexpr uint32_t BTOR_TEST_SHIFT_HIGH = 8;

  enum Op
  {
    SLL,
    SRL,
    SRA,
    ROL,
    ROR
  };

  char *int_to_str (int32_t x, int32_t num_bits)
  {
    assert (x >= 0);
    assert (num_bits > 0);
    char *result = NULL;
    int32_t i    = 0;
    result = (char *) btor_mem_malloc (d_mm, sizeof (char) * (num_bits + 1));
    for (i = num_bits - 1; i >= 0; i--)
    {
      result[i] = x % 2 ? '1' : '0';
      x >>= 1;
    }
    result[num_bits] = '\0';
    return result;
  }

  char *sll (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits > 1);
    assert (y < num_bits);
    int32_t i    = 0;
    char *result = NULL;
    result       = int_to_str (x, num_bits);
    for (i = 0; i < num_bits - y; i++) result[i] = result[i + y];
    for (i = num_bits - y; i < num_bits; i++) result[i] = '0';
    return result;
  }

  char *srl (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits > 1);
    assert (y < num_bits);
    int32_t i    = 0;
    char *result = NULL;
    result       = int_to_str (x, num_bits);
    for (i = num_bits - 1; i >= y; i--) result[i] = result[i - y];
    for (i = 0; i < y; i++) result[i] = '0';
    return result;
  }

  char *sra (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits > 1);
    assert (y < num_bits);
    int32_t i    = 0;
    char *result = NULL;
    char sign    = '0';
    result       = int_to_str (x, num_bits);
    sign         = result[0];
    for (i = num_bits - 1; i >= y; i--) result[i] = result[i - y];
    for (i = 0; i < y; i++) result[i] = sign;
    return result;
  }

  char *rol (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits > 1);
    assert (y < num_bits);
    int32_t i    = 0;
    int32_t j    = 0;
    char temp    = '0';
    char *result = NULL;
    result       = int_to_str (x, num_bits);
    for (i = 0; i < y; i++)
    {
      temp = result[0];
      for (j = 0; j < num_bits; j++) result[j] = result[j + 1];
      result[num_bits - 1] = temp;
    }
    return result;
  }

  char *ror (int32_t x, int32_t y, int32_t num_bits)
  {
    assert (x >= 0);
    assert (y >= 0);
    assert (num_bits > 1);
    assert (y < num_bits);
    int32_t i    = 0;
    int32_t j    = 0;
    char temp    = '0';
    char *result = NULL;
    result       = int_to_str (x, num_bits);
    for (i = 0; i < y; i++)
    {
      temp = result[num_bits - 1];
      for (j = num_bits - 1; j > 0; j--) result[j] = result[j - 1];
      result[0] = temp;
    }
    return result;
  }

  void shift_test (Op op, int32_t low, int32_t high, uint32_t rwl)
  {
    assert (low > 0);
    assert (low <= high);

    BoolectorNode *(*btor_fun) (Btor *, BoolectorNode *, BoolectorNode *);

    int32_t i        = 0;
    int32_t j        = 0;
    char *result     = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    btor_util_is_power_of_2 (low);
    btor_util_is_power_of_2 (high);
    for (num_bits = low; num_bits <= high; num_bits <<= 1)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < num_bits; j++)
        {
          Btor *btor;
          BoolectorSort sort1, sort2;
          BoolectorNode *const1, *const2, *const3, *bfun, *eq;

          btor = boolector_new ();
          boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          switch (op)
          {
            case SLL:
              btor_fun = boolector_sll;
              result   = sll (i, j, num_bits);
              break;
            case SRL:
              btor_fun = boolector_srl;
              result   = srl (i, j, num_bits);
              break;
            case SRA:
              btor_fun = boolector_sra;
              result   = sra (i, j, num_bits);
              break;
            case ROL:
              btor_fun = boolector_rol;
              result   = rol (i, j, num_bits);
              break;
            default:
              assert (op == ROR);
              btor_fun = boolector_ror;
              result   = ror (i, j, num_bits);
          }

          sort1  = boolector_bitvec_sort (btor, num_bits);
          sort2  = boolector_bitvec_sort (btor, btor_util_log_2 (num_bits));
          const1 = boolector_unsigned_int (btor, i, sort1);
          const2 = boolector_unsigned_int (btor, j, sort2);
          bfun   = btor_fun (btor, const1, const2);
          ASSERT_EQ (boolector_get_sort (btor, bfun), sort1);
          const3 = boolector_const (btor, result);
          eq     = boolector_eq (btor, bfun, const3);
          boolector_assert (btor, eq);

          ASSERT_EQ (boolector_sat (btor), BOOLECTOR_SAT);
          btor_mem_freestr (d_mm, result);
          boolector_release_sort (btor, sort1);
          boolector_release_sort (btor, sort2);
          boolector_release (btor, const1);
          boolector_release (btor, const2);
          boolector_release (btor, const3);
          boolector_release (btor, bfun);
          boolector_release (btor, eq);
          boolector_delete (btor);
        }
      }
    }
  }
};

TEST_F (TestShift, sll)
{
  shift_test (SLL, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (SLL, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

TEST_F (TestShift, srl)
{
  shift_test (SRL, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (SRL, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

TEST_F (TestShift, sra)
{
  shift_test (SRA, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (SRA, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

TEST_F (TestShift, rol)
{
  shift_test (ROL, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (ROL, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

TEST_F (TestShift, ror)
{
  shift_test (ROR, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 1);
  shift_test (ROR, BTOR_TEST_SHIFT_LOW, BTOR_TEST_SHIFT_HIGH, 0);
}

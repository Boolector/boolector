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

class TestComp : public TestBoolector
{
 protected:
  static constexpr uint32_t BTOR_TEST_COMP_LOW  = 1;
  static constexpr uint32_t BTOR_TEST_COMP_HIGH = 4;

  void u_comp_test (int32_t (*func) (int32_t, int32_t),
                    BoolectorNode *(*btorfun) (Btor *,
                                               BoolectorNode *,
                                               BoolectorNode *),
                    int32_t low,
                    int32_t high,
                    uint32_t rwl)
  {
    assert (func != NULL);
    assert (low > 0);
    assert (low <= high);

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t result   = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          result = func (i, j);

          if (d_btor) boolector_delete (d_btor);
          d_btor = boolector_new ();
          boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          BoolectorSort sort = boolector_bitvec_sort (d_btor, num_bits);
          BoolectorNode *const1, *const2, *bfun;

          const1 = boolector_unsigned_int (d_btor, i, sort);
          const2 = boolector_unsigned_int (d_btor, j, sort);
          bfun   = btorfun (d_btor, const1, const2);
          boolector_assert (d_btor, bfun);

          sat_res = boolector_sat (d_btor);
          ASSERT_TRUE ((result && sat_res == BOOLECTOR_SAT)
                       || (!result && sat_res == BOOLECTOR_UNSAT));
          boolector_release_sort (d_btor, sort);
          boolector_release (d_btor, const1);
          boolector_release (d_btor, const2);
          boolector_release (d_btor, bfun);
          boolector_delete (d_btor);
          d_btor = nullptr;
        }
      }
    }
  }

  void s_comp_test (int32_t (*func) (int32_t, int32_t),
                    BoolectorNode *(*btorfun) (Btor *,
                                               BoolectorNode *,
                                               BoolectorNode *),
                    int32_t low,
                    int32_t high,
                    uint32_t rwl)
  {
    assert (func != NULL);
    assert (low > 0);
    assert (low <= high);

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t result   = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = btor_util_pow_2 (num_bits - 1);
      for (i = -max; i < max; i++)
      {
        for (j = -max; j < max; j++)
        {
          result = func (i, j);

          if (d_btor) boolector_delete (d_btor);
          d_btor = boolector_new ();
          boolector_set_opt (d_btor, BTOR_OPT_REWRITE_LEVEL, rwl);

          BoolectorSort sort = boolector_bitvec_sort (d_btor, num_bits);
          BoolectorNode *const1, *const2, *bfun;

          const1 = boolector_int (d_btor, i, sort);
          const2 = boolector_int (d_btor, j, sort);
          bfun   = btorfun (d_btor, const1, const2);
          boolector_assert (d_btor, bfun);

          sat_res = boolector_sat (d_btor);
          ASSERT_TRUE (sat_res == BOOLECTOR_SAT || sat_res == BOOLECTOR_UNSAT);
          if (sat_res == BOOLECTOR_SAT)
          {
            ASSERT_TRUE (result > 0);
          }
          else
          {
            ASSERT_EQ (sat_res, BOOLECTOR_UNSAT);
            ASSERT_TRUE (result == 0);
          }
          boolector_release_sort (d_btor, sort);
          boolector_release (d_btor, const1);
          boolector_release (d_btor, const2);
          boolector_release (d_btor, bfun);
          boolector_delete (d_btor);
          d_btor = nullptr;
        }
      }
    }
  }

  static int32_t eq (int32_t x, int32_t y) { return x == y; }

  static int32_t ne (int32_t x, int32_t y) { return x != y; }

  static int32_t lt (int32_t x, int32_t y) { return x < y; }

  static int32_t lte (int32_t x, int32_t y) { return x <= y; }

  static int32_t gt (int32_t x, int32_t y) { return x > y; }

  static int32_t gte (int32_t x, int32_t y) { return x >= y; }
};

TEST_F (TestComp, test_eq_1)
{
  u_comp_test (eq, boolector_eq, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (eq, boolector_eq, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_ne_1)
{
  u_comp_test (ne, boolector_ne, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (ne, boolector_ne, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_ult)
{
  u_comp_test (lt, boolector_ult, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (lt, boolector_ult, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_ulte)
{
  u_comp_test (lte, boolector_ulte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (lte, boolector_ulte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_ugt)
{
  u_comp_test (gt, boolector_ugt, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (gt, boolector_ugt, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_ugte)
{
  u_comp_test (gte, boolector_ugte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  u_comp_test (gte, boolector_ugte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_eq_2)
{
  s_comp_test (eq, boolector_eq, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (eq, boolector_eq, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_ne_2)
{
  s_comp_test (ne, boolector_ne, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (ne, boolector_ne, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_slt)
{
  s_comp_test (lt, boolector_slt, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (lt, boolector_slt, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_slte)
{
  s_comp_test (lte, boolector_slte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (lte, boolector_slte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_sgt)
{
  s_comp_test (gt, boolector_sgt, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (gt, boolector_sgt, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

TEST_F (TestComp, test_sgte)
{
  s_comp_test (gte, boolector_sgte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 1);
  s_comp_test (gte, boolector_sgte, BTOR_TEST_COMP_LOW, BTOR_TEST_COMP_HIGH, 0);
}

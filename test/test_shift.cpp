/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

#include <bitset>

extern "C" {
#include "btorbv.h"
#include "utils/btorutil.h"
}

class TestShift : public TestCommon
{
 protected:
  void test_shift (uint32_t bw, const char *shift, bool left)
  {
    assert (bw > 1);
    assert (bw == strlen (shift));

    int32_t res;
    uint32_t bw_log2, ushift;
    BoolectorSort sort, sort_log2;
    BoolectorNode *shift0, *shift0_e1;
    BoolectorNode *shift1;
    BoolectorNode *shift2, *shift2_e1;
    BoolectorNode *e0;
    BoolectorNode *ne0, *ne1, *ne2;
    BoolectorNode *zero, *two, *cond, *tmp;
    Btor *btor;

    BoolectorNode *(*shift_fun) (Btor *, BoolectorNode *, BoolectorNode *);
    BoolectorNode *(*fun) (Btor *, BoolectorNode *, BoolectorNode *);

    if (left)
    {
      shift_fun = boolector_sll;
      fun       = boolector_mul;
    }
    else
    {
      shift_fun = boolector_srl;
      fun       = boolector_udiv;
    }

    btor = boolector_new ();
    boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
    boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);

    sort   = boolector_bitvec_sort (btor, bw);
    e0     = boolector_var (btor, sort, "e0");
    ushift = std::stol (shift, nullptr, 2);

    shift0_e1 = boolector_const (btor, shift);
    shift0    = shift_fun (btor, e0, shift0_e1);

    shift1 = boolector_copy (btor, e0);
    two    = boolector_unsigned_int (btor, 2u, sort);
    for (uint32_t i = 0; i < ushift; ++i)
    {
      BoolectorNode *tmp = fun (btor, shift1, two);
      boolector_release (btor, shift1);
      shift1 = tmp;
    }
    zero = boolector_zero (btor, sort);
    tmp  = boolector_unsigned_int (btor, bw, sort);
    cond = boolector_ugte (btor, shift0_e1, tmp);
    boolector_release (btor, tmp);
    tmp = boolector_cond (btor, cond, zero, shift1);
    boolector_release (btor, cond);
    boolector_release (btor, shift1);
    shift1 = tmp;

    ne0 = boolector_ne (btor, shift0, shift1);
    boolector_assert (btor, ne0);

    if (btor_util_is_power_of_2 (bw))
    {
      bw_log2 = btor_util_log_2 (bw);
      if (bw_log2 && ushift < (1u << bw_log2))
      {
        sort_log2 = boolector_bitvec_sort (btor, bw_log2);
        shift2_e1 = boolector_unsigned_int (btor, ushift, sort_log2);
        shift2    = shift_fun (btor, e0, shift2_e1);
        ne1       = boolector_ne (btor, shift2, shift0);
        ne2       = boolector_ne (btor, shift2, shift1);
        boolector_assert (btor, ne1);
        boolector_assert (btor, ne2);
        boolector_release (btor, ne1);
        boolector_release (btor, ne2);
        boolector_release (btor, shift2);
        boolector_release (btor, shift2_e1);
        boolector_release_sort (btor, sort_log2);
      }
    }

    res = boolector_sat (btor);
    if (res == BOOLECTOR_SAT)
    {
      const char *se0  = boolector_bv_assignment (btor, e0);
      const char *s0   = boolector_bv_assignment (btor, shift0);
      const char *s0e1 = boolector_bv_assignment (btor, shift0_e1);
      const char *s1   = boolector_bv_assignment (btor, shift1);
      printf ("e0 %s\n", se0);
      printf ("s0e1 %s\n", s0e1);
      printf ("s0 %s\n", s0);
      printf ("s1 %s\n", s1);
    }
    assert (res == BOOLECTOR_UNSAT);

    boolector_release (btor, ne0);
    boolector_release (btor, zero);
    boolector_release (btor, two);
    boolector_release (btor, shift0);
    boolector_release (btor, shift0_e1);
    boolector_release (btor, shift1);
    boolector_release (btor, e0);
    boolector_release_sort (btor, sort);

    boolector_delete (btor);
  }
};

TEST_F (TestShift, sll_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift (2, std::bitset<2> (i).to_string ().c_str (), true);
  }
}

TEST_F (TestShift, sll_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift (3, std::bitset<3> (i).to_string ().c_str (), true);
  }
}

TEST_F (TestShift, sll_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift (4, std::bitset<4> (i).to_string ().c_str (), true);
  }
}

TEST_F (TestShift, sll_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift (5, std::bitset<5> (i).to_string ().c_str (), true);
  }
}

TEST_F (TestShift, sll_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift (8, std::bitset<8> (i).to_string ().c_str (), true);
  }
}

TEST_F (TestShift, srl_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift (2, std::bitset<2> (i).to_string ().c_str (), false);
  }
}

TEST_F (TestShift, srl_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift (3, std::bitset<3> (i).to_string ().c_str (), false);
  }
}

TEST_F (TestShift, srl_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift (4, std::bitset<4> (i).to_string ().c_str (), false);
  }
}

TEST_F (TestShift, srl_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift (5, std::bitset<5> (i).to_string ().c_str (), false);
  }
}

TEST_F (TestShift, srl_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift (8, std::bitset<8> (i).to_string ().c_str (), false);
  }
}

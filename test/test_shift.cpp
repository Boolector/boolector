/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <bitset>

#include "test.h"

extern "C" {
#include "btorbv.h"
#include "utils/btorutil.h"
}

class TestShift : public TestCommon
{
 protected:
  void test_shift (
      uint32_t bw,
      const char *shift,
      BoolectorNode *(*shift_fun) (Btor *, BoolectorNode *, BoolectorNode *),
      BoolectorNode *(*fun) (Btor *, BoolectorNode *, BoolectorNode *) )
  {
    assert (bw > 1);
    assert (bw == strlen (shift));

    int32_t res;
    uint32_t bw_log2, ushift;
    BoolectorSort sort;
    BoolectorNode *res_shift0, *shift0;
    BoolectorNode *res_shift1;
    BoolectorNode *res_shift2;
    BoolectorNode *e0;
    BoolectorNode *ne0, *ne1, *ne2;
    BoolectorNode *two, *tmp;
    Btor *btor;

    btor = boolector_new ();
    boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
    boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);

    sort   = boolector_bitvec_sort (btor, bw);
    e0     = boolector_var (btor, sort, "e0");
    ushift = std::stol (shift, nullptr, 2);

    shift0     = boolector_const (btor, shift);
    res_shift0 = shift_fun (btor, e0, shift0);

    res_shift1 = boolector_copy (btor, e0);
    two        = boolector_unsigned_int (btor, 2u, sort);
    for (uint32_t i = 0; i < ushift; ++i)
    {
      tmp = fun (btor, res_shift1, two);
      boolector_release (btor, res_shift1);
      res_shift1 = tmp;
    }
    if (shift_fun == boolector_sra)
    {
      /* if msb = 1, shift in 1 bits instead of 0 bits */
      if (ushift > 0)
      {
        BoolectorNode *msb = boolector_slice (btor, e0, bw - 1, bw - 1);
        if (ushift < bw)
        {
          BoolectorNode *slice =
              boolector_slice (btor, res_shift1, bw - ushift - 1, 0);
          BoolectorSort sort_sra_ones = boolector_bitvec_sort (btor, ushift);
          BoolectorNode *ones         = boolector_ones (btor, sort_sra_ones);
          boolector_release_sort (btor, sort_sra_ones);
          BoolectorNode *concat = boolector_concat (btor, ones, slice);
          boolector_release (btor, slice);
          boolector_release (btor, ones);
          tmp = boolector_cond (btor, msb, concat, res_shift1);
          boolector_release (btor, concat);
          boolector_release (btor, res_shift1);
          res_shift1 = tmp;
        }
        else
        {
          BoolectorNode *ones = boolector_ones (btor, sort);
          tmp                 = boolector_cond (btor, msb, ones, res_shift1);
          boolector_release (btor, ones);
          boolector_release (btor, res_shift1);
          res_shift1 = tmp;
        }
        boolector_release (btor, msb);
      }
    }

    ne0 = boolector_ne (btor, res_shift0, res_shift1);
    boolector_assert (btor, ne0);

    if (btor_util_is_power_of_2 (bw))
    {
      bw_log2 = btor_util_log_2 (bw);
      if (bw_log2 && ushift < (1u << bw_log2))
      {
        BoolectorSort sort_log2 = boolector_bitvec_sort (btor, bw_log2);
        BoolectorNode *shift2_e1 =
            boolector_unsigned_int (btor, ushift, sort_log2);
        res_shift2 = shift_fun (btor, e0, shift2_e1);
        ne1        = boolector_ne (btor, res_shift2, res_shift0);
        ne2        = boolector_ne (btor, res_shift2, res_shift1);
        boolector_assert (btor, ne1);
        boolector_assert (btor, ne2);
        boolector_release (btor, ne1);
        boolector_release (btor, ne2);
        boolector_release (btor, res_shift2);
        boolector_release (btor, shift2_e1);
        boolector_release_sort (btor, sort_log2);
      }
    }

    res = boolector_sat (btor);
    if (res == BOOLECTOR_SAT)
    {
      const char *se0    = boolector_bv_assignment (btor, e0);
      const char *res_s0 = boolector_bv_assignment (btor, res_shift0);
      const char *s0     = boolector_bv_assignment (btor, shift0);
      const char *res_s1 = boolector_bv_assignment (btor, res_shift1);
      printf ("e0 %s\n", se0);
      printf ("s0 %s\n", s0);
      printf ("res_shift0 %s\n", res_s0);
      printf ("res_shift1 %s\n", res_s1);
    }
    assert (res == BOOLECTOR_UNSAT);

    boolector_release (btor, ne0);
    boolector_release (btor, two);
    boolector_release (btor, res_shift0);
    boolector_release (btor, shift0);
    boolector_release (btor, res_shift1);
    boolector_release (btor, e0);
    boolector_release_sort (btor, sort);

    boolector_delete (btor);
  }
};

TEST_F (TestShift, sll_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift (2,
                std::bitset<2> (i).to_string ().c_str (),
                boolector_sll,
                boolector_mul);
  }
}

TEST_F (TestShift, sll_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift (3,
                std::bitset<3> (i).to_string ().c_str (),
                boolector_sll,
                boolector_mul);
  }
}

TEST_F (TestShift, sll_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift (4,
                std::bitset<4> (i).to_string ().c_str (),
                boolector_sll,
                boolector_mul);
  }
}

TEST_F (TestShift, sll_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift (5,
                std::bitset<5> (i).to_string ().c_str (),
                boolector_sll,
                boolector_mul);
  }
}

TEST_F (TestShift, sll_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift (8,
                std::bitset<8> (i).to_string ().c_str (),
                boolector_sll,
                boolector_mul);
  }
}

TEST_F (TestShift, srl_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift (2,
                std::bitset<2> (i).to_string ().c_str (),
                boolector_srl,
                boolector_udiv);
  }
}

TEST_F (TestShift, srl_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift (3,
                std::bitset<3> (i).to_string ().c_str (),
                boolector_srl,
                boolector_udiv);
  }
}

TEST_F (TestShift, srl_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift (4,
                std::bitset<4> (i).to_string ().c_str (),
                boolector_srl,
                boolector_udiv);
  }
}

TEST_F (TestShift, srl_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift (5,
                std::bitset<5> (i).to_string ().c_str (),
                boolector_srl,
                boolector_udiv);
  }
}

TEST_F (TestShift, srl_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift (8,
                std::bitset<8> (i).to_string ().c_str (),
                boolector_srl,
                boolector_udiv);
  }
}

TEST_F (TestShift, sra_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift (2,
                std::bitset<2> (i).to_string ().c_str (),
                boolector_sra,
                boolector_udiv);
  }
}

TEST_F (TestShift, sra_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift (3,
                std::bitset<3> (i).to_string ().c_str (),
                boolector_sra,
                boolector_udiv);
  }
}

TEST_F (TestShift, sra_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift (4,
                std::bitset<4> (i).to_string ().c_str (),
                boolector_sra,
                boolector_udiv);
  }
}

TEST_F (TestShift, sra_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift (5,
                std::bitset<5> (i).to_string ().c_str (),
                boolector_sra,
                boolector_udiv);
  }
}

TEST_F (TestShift, sra_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift (8,
                std::bitset<8> (i).to_string ().c_str (),
                boolector_sra,
                boolector_udiv);
  }
}

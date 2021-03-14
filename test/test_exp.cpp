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
#include "btorcore.h"
#include "btorexp.h"
#include "dumper/btordumpbtor.h"
}

class TestExp : public TestBtor
{
 protected:
  void unary_exp_test (BtorNode *(*func) (Btor *, BtorNode *) )
  {
    const uint32_t len = 8;
    BtorNode *exp1, *exp2, *exp3;
    BtorSortId sort;

    sort = btor_sort_bv (d_btor, 8);
    exp1 = btor_exp_var (d_btor, sort, "v1");
    exp2 = func (d_btor, exp1);
    exp3 = func (d_btor, exp1);

    ASSERT_EQ (exp2, exp3);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), len);
    if (func == btor_exp_bv_not || func == btor_exp_bv_neg)
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), len);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), len);
      if (func == btor_exp_bv_neg)
      {
        ASSERT_TRUE (btor_node_bv_is_neg (d_btor, exp2, 0));
        ASSERT_TRUE (btor_node_bv_is_neg (d_btor, exp3, 0));
      }
      else
      {
        ASSERT_FALSE (btor_node_bv_is_neg (d_btor, exp2, 0));
        ASSERT_FALSE (btor_node_bv_is_neg (d_btor, exp3, 0));
      }
    }
    else
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 1u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 1u);
    }
    btor_dumpbtor_dump_node (d_btor, d_log_file, exp3);
    btor_sort_release (d_btor, sort);
    btor_node_release (d_btor, exp1);
    btor_node_release (d_btor, exp2);
    btor_node_release (d_btor, exp3);
  }

  void ext_exp_test (BtorNode *(*func) (Btor *, BtorNode *, uint32_t))
  {
    BtorNode *exp1, *exp2, *exp3;
    BtorSortId sort;

    sort = btor_sort_bv (d_btor, 32);

    exp1 = btor_exp_var (d_btor, sort, "v1");
    exp2 = func (d_btor, exp1, 32);
    exp3 = func (d_btor, exp1, 32);

    ASSERT_EQ (exp2, exp3);
    btor_dumpbtor_dump_node (d_btor, d_log_file, exp3);
    btor_sort_release (d_btor, sort);
    btor_node_release (d_btor, exp1);
    btor_node_release (d_btor, exp2);
    btor_node_release (d_btor, exp3);
  }

  void binary_commutative_exp_test (BtorNode *(*func) (Btor *,
                                                       BtorNode *,
                                                       BtorNode *) )
  {
    BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
    BtorSortId sort;

    sort = btor_sort_bv (d_btor, 8);

    exp1 = btor_exp_var (d_btor, sort, "v1");
    exp2 = btor_exp_var (d_btor, sort, "v2");
    exp3 = func (d_btor, exp1, exp2);
    exp4 = func (d_btor, exp1, exp2);
    exp5 = func (d_btor, exp2, exp1);

    ASSERT_EQ (exp3, exp4);
    ASSERT_EQ (exp4, exp5);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
    if (func == btor_exp_eq || func == btor_exp_ne || func == btor_exp_bv_uaddo
        || func == btor_exp_bv_saddo || func == btor_exp_bv_umulo)
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 1u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 1u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 1u);
    }
    else
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 8u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 8u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 8u);
    }
    btor_dumpbtor_dump_node (d_btor, d_log_file, exp3);
    btor_sort_release (d_btor, sort);
    btor_node_release (d_btor, exp1);
    btor_node_release (d_btor, exp2);
    btor_node_release (d_btor, exp3);
    btor_node_release (d_btor, exp4);
    btor_node_release (d_btor, exp5);
  }

  void binary_non_commutative_exp_test (BtorNode *(*func) (Btor *,
                                                           BtorNode *,
                                                           BtorNode *) )
  {
    BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
    BtorSortId sort;

    sort = btor_sort_bv (d_btor, 32);
    exp1 = btor_exp_var (d_btor, sort, "v1");
    exp2 = btor_exp_var (d_btor, sort, "v2");
    exp3 = func (d_btor, exp1, exp2);
    exp4 = func (d_btor, exp1, exp2);
    exp5 = func (d_btor, exp2, exp1);

    ASSERT_EQ (exp3, exp4);
    ASSERT_NE (exp4, exp5);
    if (func == btor_exp_bv_sub || func == btor_exp_bv_udiv
        || func == btor_exp_bv_sdiv || func == btor_exp_bv_urem
        || func == btor_exp_bv_srem || func == btor_exp_bv_smod)
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 32u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 32u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 32u);
    }
    else if (func == btor_exp_bv_concat)
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 64u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 64u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 64u);
    }
    else
    {
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 1u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 1u);
      ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 1u);
    }
    btor_dumpbtor_dump_node (d_btor, d_log_file, exp4);
    btor_sort_release (d_btor, sort);
    btor_node_release (d_btor, exp1);
    btor_node_release (d_btor, exp2);
    btor_node_release (d_btor, exp3);
    btor_node_release (d_btor, exp4);
    btor_node_release (d_btor, exp5);
  }

  void mulo_exp_test (BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
  {
    BtorNode *exp1, *exp2, *exp3, *exp4, *exp5;
    BtorSortId sort;

    sort = btor_sort_bv (d_btor, 3);

    exp1 = btor_exp_var (d_btor, sort, "v1");
    exp2 = btor_exp_var (d_btor, sort, "v2");
    exp3 = func (d_btor, exp1, exp2);
    exp4 = func (d_btor, exp1, exp2);
    exp5 = func (d_btor, exp2, exp1);

    ASSERT_EQ (exp3, exp4);
    if (func == btor_exp_bv_umulo)
      ASSERT_NE (exp4, exp5);
    else
      ASSERT_EQ (exp4, exp5);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 1u);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 1u);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 1u);
    btor_dumpbtor_dump_node (d_btor, d_log_file, exp4);
    btor_node_release (d_btor, exp1);
    btor_node_release (d_btor, exp2);
    btor_node_release (d_btor, exp3);
    btor_node_release (d_btor, exp4);
    btor_node_release (d_btor, exp5);
    btor_sort_release (d_btor, sort);
  }

  void shift_exp_test (uint32_t bw1,
                       uint32_t bw2,
                       BtorNode *(*func) (Btor *, BtorNode *, BtorNode *) )
  {
    BtorNode *exp1, *exp2, *exp3, *exp4;
    BtorSortId sort;

    sort = btor_sort_bv (d_btor, bw1);
    exp1 = btor_exp_var (d_btor, sort, "v1");
    btor_sort_release (d_btor, sort);
    sort = btor_sort_bv (d_btor, bw2);
    exp2 = btor_exp_var (d_btor, sort, "v2");
    btor_sort_release (d_btor, sort);
    exp3 = func (d_btor, exp1, exp2);
    exp4 = func (d_btor, exp1, exp2);

    ASSERT_EQ (exp3, exp4);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), bw1);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), bw2);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), bw1);
    ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), bw1);
    btor_dumpbtor_dump_node (d_btor, d_log_file, exp4);
    btor_node_release (d_btor, exp1);
    btor_node_release (d_btor, exp2);
    btor_node_release (d_btor, exp3);
    btor_node_release (d_btor, exp4);
  }
};

TEST_F (TestExp, new_delete_btor) {}

TEST_F (TestExp, const)
{
  open_log_file ("const_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv1, *bv2, *bv3;

  bv1  = btor_bv_char_to_bv (d_btor->mm, "00010011");
  bv2  = btor_bv_char_to_bv (d_btor->mm, "00010011");
  bv3  = btor_bv_char_to_bv (d_btor->mm, "0000000000010011");
  exp1 = btor_exp_bv_const (d_btor, bv1);
  exp2 = btor_exp_bv_const (d_btor, bv2);
  exp3 = btor_exp_bv_const (d_btor, bv3);
  ASSERT_EQ (exp1, exp2);
  ASSERT_NE (exp2, exp3);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 16u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp2);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_bv_free (d_btor->mm, bv1);
  btor_bv_free (d_btor->mm, bv2);
  btor_bv_free (d_btor->mm, bv3);
}

TEST_F (TestExp, zero)
{
  open_log_file ("zero_exp");

  BtorNode *exp1, *exp2;
  BtorBitVector *bv2;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);
  exp1 = btor_exp_bv_zero (d_btor, sort);
  btor_sort_release (d_btor, sort);
  bv2  = btor_bv_new (d_btor->mm, 8);
  exp2 = btor_exp_bv_const (d_btor, bv2);
  ASSERT_EQ (exp1, exp2);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_TRUE (btor_node_is_bv_const_zero (d_btor, exp1));
  ASSERT_TRUE (btor_node_is_bv_const_zero (d_btor, exp2));
  ASSERT_FALSE (btor_node_is_bv_const_zero (d_btor, btor_node_invert (exp1)));
  ASSERT_FALSE (btor_node_is_bv_const_zero (d_btor, btor_node_invert (exp2)));
  ASSERT_TRUE (btor_node_is_bv_const_ones (d_btor, btor_node_invert (exp1)));
  ASSERT_TRUE (btor_node_is_bv_const_ones (d_btor, btor_node_invert (exp2)));
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp1);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_bv_free (d_btor->mm, bv2);
}

TEST_F (TestExp, ones)
{
  open_log_file ("ones_exp");

  BtorNode *exp1, *exp2;
  BtorBitVector *bv2;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);
  exp1 = btor_exp_bv_ones (d_btor, sort);
  btor_sort_release (d_btor, sort);
  bv2  = btor_bv_ones (d_btor->mm, 8);
  exp2 = btor_exp_bv_const (d_btor, bv2);
  ASSERT_EQ (exp1, exp2);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_TRUE (btor_node_is_bv_const_ones (d_btor, exp1));
  ASSERT_TRUE (btor_node_is_bv_const_ones (d_btor, exp2));
  ASSERT_FALSE (btor_node_is_bv_const_ones (d_btor, btor_node_invert (exp1)));
  ASSERT_FALSE (btor_node_is_bv_const_ones (d_btor, btor_node_invert (exp2)));
  ASSERT_TRUE (btor_node_is_bv_const_zero (d_btor, btor_node_invert (exp1)));
  ASSERT_TRUE (btor_node_is_bv_const_zero (d_btor, btor_node_invert (exp2)));
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp1);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_bv_free (d_btor->mm, bv2);
}

TEST_F (TestExp, one)
{
  open_log_file ("one_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv2, *bv3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);
  exp1 = btor_exp_bv_one (d_btor, sort);
  btor_sort_release (d_btor, sort);
  bv2  = btor_bv_one (d_btor->mm, 8);
  exp2 = btor_exp_bv_const (d_btor, bv2);
  ASSERT_EQ (exp1, exp2);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_TRUE (btor_node_is_bv_const_one (d_btor, exp1));
  ASSERT_TRUE (btor_node_is_bv_const_one (d_btor, exp2));
  ASSERT_FALSE (btor_node_is_bv_const_one (d_btor, btor_node_invert (exp1)));
  ASSERT_FALSE (btor_node_is_bv_const_one (d_btor, btor_node_invert (exp2)));
  bv3  = btor_bv_char_to_bv (d_btor->mm, "11111110");
  exp3 = btor_exp_bv_const (d_btor, bv3);
  ASSERT_FALSE (btor_node_is_bv_const_one (d_btor, exp3));
  ASSERT_TRUE (btor_node_is_bv_const_one (d_btor, btor_node_invert (exp3)));
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp1);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_bv_free (d_btor->mm, bv2);
  btor_bv_free (d_btor->mm, bv3);
}

TEST_F (TestExp, min_signed)
{
  open_log_file ("min_signed_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv2, *bv3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);
  exp1 = btor_exp_bv_min_signed (d_btor, sort);
  btor_sort_release (d_btor, sort);
  bv2  = btor_bv_min_signed (d_btor->mm, 8);
  exp2 = btor_exp_bv_const (d_btor, bv2);
  ASSERT_EQ (exp1, exp2);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_TRUE (btor_node_is_bv_const_min_signed (d_btor, exp1));
  ASSERT_TRUE (btor_node_is_bv_const_min_signed (d_btor, exp2));
  ASSERT_FALSE (
      btor_node_is_bv_const_min_signed (d_btor, btor_node_invert (exp1)));
  ASSERT_FALSE (
      btor_node_is_bv_const_min_signed (d_btor, btor_node_invert (exp2)));
  bv3  = btor_bv_char_to_bv (d_btor->mm, "01111111");
  exp3 = btor_exp_bv_const (d_btor, bv3);
  ASSERT_FALSE (btor_node_is_bv_const_min_signed (d_btor, exp3));
  ASSERT_TRUE (
      btor_node_is_bv_const_min_signed (d_btor, btor_node_invert (exp3)));
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp1);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_bv_free (d_btor->mm, bv2);
  btor_bv_free (d_btor->mm, bv3);
}

TEST_F (TestExp, max_signed)
{
  open_log_file ("max_signed_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorBitVector *bv2, *bv3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);
  exp1 = btor_exp_bv_max_signed (d_btor, sort);
  btor_sort_release (d_btor, sort);
  bv2  = btor_bv_max_signed (d_btor->mm, 8);
  exp2 = btor_exp_bv_const (d_btor, bv2);
  ASSERT_EQ (exp1, exp2);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_TRUE (btor_node_is_bv_const_max_signed (d_btor, exp1));
  ASSERT_TRUE (btor_node_is_bv_const_max_signed (d_btor, exp2));
  ASSERT_FALSE (
      btor_node_is_bv_const_max_signed (d_btor, btor_node_invert (exp1)));
  ASSERT_FALSE (
      btor_node_is_bv_const_max_signed (d_btor, btor_node_invert (exp2)));
  bv3  = btor_bv_char_to_bv (d_btor->mm, "10000000");
  exp3 = btor_exp_bv_const (d_btor, bv3);
  ASSERT_FALSE (btor_node_is_bv_const_max_signed (d_btor, exp3));
  ASSERT_TRUE (
      btor_node_is_bv_const_max_signed (d_btor, btor_node_invert (exp3)));
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp1);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_bv_free (d_btor->mm, bv2);
  btor_bv_free (d_btor->mm, bv3);
}

TEST_F (TestExp, unsigned_to)
{
  open_log_file ("unsigned_to_exp");

  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7, *exp8;
  BtorBitVector *bv5, *bv6, *bv7, *bv8;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);
  exp1 = btor_exp_bv_unsigned (d_btor, 32u, sort);
  exp2 = btor_exp_bv_unsigned (d_btor, 49u, sort);
  exp3 = btor_exp_bv_unsigned (d_btor, 3u, sort);
  exp4 = btor_exp_bv_unsigned (d_btor, 57u, sort);
  btor_sort_release (d_btor, sort);
  bv5  = btor_bv_char_to_bv (d_btor->mm, "00100000");
  bv6  = btor_bv_char_to_bv (d_btor->mm, "00110001");
  bv7  = btor_bv_char_to_bv (d_btor->mm, "00000011");
  bv8  = btor_bv_char_to_bv (d_btor->mm, "00111001");
  exp5 = btor_exp_bv_const (d_btor, bv5);
  exp6 = btor_exp_bv_const (d_btor, bv6);
  exp7 = btor_exp_bv_const (d_btor, bv7);
  exp8 = btor_exp_bv_const (d_btor, bv8);

  ASSERT_EQ (exp1, exp5);
  ASSERT_EQ (exp2, exp6);
  ASSERT_EQ (exp3, exp7);
  ASSERT_EQ (exp4, exp8);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp6), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp7), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp8), 8u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp4);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_node_release (d_btor, exp4);
  btor_node_release (d_btor, exp5);
  btor_node_release (d_btor, exp6);
  btor_node_release (d_btor, exp7);
  btor_node_release (d_btor, exp8);
  btor_bv_free (d_btor->mm, bv5);
  btor_bv_free (d_btor->mm, bv6);
  btor_bv_free (d_btor->mm, bv7);
  btor_bv_free (d_btor->mm, bv8);
}

TEST_F (TestExp, var)
{
  open_log_file ("var_exp");

  BtorNode *exp1, *exp2;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);

  exp1 = btor_exp_var (d_btor, sort, "v1");
  exp2 = btor_node_copy (d_btor, exp1);

  ASSERT_EQ (exp1, exp2);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp2);
  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
}

TEST_F (TestExp, array)
{
  open_log_file ("array_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorSortId index_sort, elem_sort, array_sort;

  elem_sort  = btor_sort_bv (d_btor, 32);
  index_sort = btor_sort_bv (d_btor, 8);
  array_sort = btor_sort_array (d_btor, index_sort, elem_sort);
  exp1       = btor_exp_array (d_btor, array_sort, "array1");
  exp2       = btor_node_copy (d_btor, exp1);
  exp3       = btor_exp_array (d_btor, array_sort, "array2");
  btor_sort_release (d_btor, elem_sort);
  btor_sort_release (d_btor, index_sort);
  btor_sort_release (d_btor, array_sort);

  ASSERT_EQ (exp1, exp2);
  ASSERT_NE (exp1, exp3);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp1), 32u);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp2), 32u);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp3), 32u);
  ASSERT_EQ (btor_node_array_get_index_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_array_get_index_width (d_btor, exp2), 8u);
  ASSERT_EQ (btor_node_array_get_index_width (d_btor, exp3), 8u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp2);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
}

TEST_F (TestExp, not)
{
  open_log_file ("not_exp");
  unary_exp_test (btor_exp_bv_not);
}

TEST_F (TestExp, neg)
{
  open_log_file ("neg_exp");
  unary_exp_test (btor_exp_bv_neg);
}

TEST_F (TestExp, redor)
{
  open_log_file ("redor_exp");
  unary_exp_test (btor_exp_bv_redor);
}

TEST_F (TestExp, redxor)
{
  open_log_file ("redxor_exp");
  unary_exp_test (btor_exp_bv_redxor);
}

TEST_F (TestExp, redand)
{
  open_log_file ("redand_exp");
  unary_exp_test (btor_exp_bv_redand);
}

TEST_F (TestExp, slice)
{
  open_log_file ("slice_exp");
  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 32);

  exp1 = btor_exp_var (d_btor, sort, "v1");
  exp2 = btor_exp_bv_slice (d_btor, exp1, 31, 30);
  exp3 = btor_exp_bv_slice (d_btor, exp1, 31, 30);

  ASSERT_EQ (exp2, exp3);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp3);
  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
}

TEST_F (TestExp, uext)
{
  open_log_file ("uext_exp");
  ext_exp_test (btor_exp_bv_uext);
}

TEST_F (TestExp, sext)
{
  open_log_file ("sext_exp");
  ext_exp_test (btor_exp_bv_sext);
}

TEST_F (TestExp, or)
{
  open_log_file ("or_exp");
  binary_commutative_exp_test (btor_exp_bv_or);
}

TEST_F (TestExp, xor)
{
  open_log_file ("xor_exp");
  binary_commutative_exp_test (btor_exp_bv_xor);
}

TEST_F (TestExp, xnor)
{
  open_log_file ("xnor_exp");
  binary_commutative_exp_test (btor_exp_bv_xnor);
}

TEST_F (TestExp, and)
{
  open_log_file ("and_exp");
  binary_commutative_exp_test (btor_exp_bv_and);
}

TEST_F (TestExp, eq)
{
  open_log_file ("eq_exp");
  binary_commutative_exp_test (btor_exp_eq);
}

TEST_F (TestExp, ne)
{
  open_log_file ("ne_exp");
  binary_commutative_exp_test (btor_exp_ne);
}

TEST_F (TestExp, add)
{
  open_log_file ("add_exp");
  binary_commutative_exp_test (btor_exp_bv_add);
}

TEST_F (TestExp, uaddo)
{
  open_log_file ("uaddo_exp");
  binary_commutative_exp_test (btor_exp_bv_uaddo);
}

TEST_F (TestExp, saddo)
{
  open_log_file ("saddo_exp");
  binary_commutative_exp_test (btor_exp_bv_saddo);
}

TEST_F (TestExp, mul)
{
  open_log_file ("mul_exp");
  binary_commutative_exp_test (btor_exp_bv_mul);
}

TEST_F (TestExp, ult)
{
  open_log_file ("ult_exp");
  binary_non_commutative_exp_test (btor_exp_bv_ult);
}

TEST_F (TestExp, slt)
{
  open_log_file ("slt_exp");
  binary_non_commutative_exp_test (btor_exp_bv_slt);
}

TEST_F (TestExp, ulte)
{
  open_log_file ("ulte_exp");
  binary_non_commutative_exp_test (btor_exp_bv_ulte);
}

TEST_F (TestExp, slte)
{
  open_log_file ("slte_exp");
  binary_non_commutative_exp_test (btor_exp_bv_slte);
}

TEST_F (TestExp, ugt)
{
  open_log_file ("ugt_exp");
  binary_non_commutative_exp_test (btor_exp_bv_ugt);
}

TEST_F (TestExp, sgt)
{
  open_log_file ("sgt_exp");
  binary_non_commutative_exp_test (btor_exp_bv_sgt);
}

TEST_F (TestExp, ugte)
{
  open_log_file ("ugte_exp");
  binary_non_commutative_exp_test (btor_exp_bv_ugte);
}

TEST_F (TestExp, sgte)
{
  open_log_file ("sgte_exp");
  binary_non_commutative_exp_test (btor_exp_bv_sgte);
}

TEST_F (TestExp, sub)
{
  open_log_file ("sub_exp");
  binary_non_commutative_exp_test (btor_exp_bv_sub);
}

TEST_F (TestExp, usubo)
{
  open_log_file ("usubo_exp");
  binary_non_commutative_exp_test (btor_exp_bv_usubo);
}

TEST_F (TestExp, ssubo)
{
  open_log_file ("ssubo_exp");
  binary_non_commutative_exp_test (btor_exp_bv_ssubo);
}

TEST_F (TestExp, udiv)
{
  open_log_file ("udiv_exp");
  binary_non_commutative_exp_test (btor_exp_bv_udiv);
}

TEST_F (TestExp, sdiv)
{
  open_log_file ("sdiv_exp");
  binary_non_commutative_exp_test (btor_exp_bv_sdiv);
}

TEST_F (TestExp, sdivo)
{
  open_log_file ("sdivo_exp");
  binary_non_commutative_exp_test (btor_exp_bv_sdivo);
}

TEST_F (TestExp, urem)
{
  open_log_file ("urem_exp");
  binary_non_commutative_exp_test (btor_exp_bv_urem);
}

TEST_F (TestExp, srem)
{
  open_log_file ("srem_exp");
  binary_non_commutative_exp_test (btor_exp_bv_srem);
}

TEST_F (TestExp, smod)
{
  open_log_file ("smod_exp");
  binary_non_commutative_exp_test (btor_exp_bv_smod);
}

TEST_F (TestExp, concat)
{
  open_log_file ("concat_exp");
  binary_non_commutative_exp_test (btor_exp_bv_concat);
}

TEST_F (TestExp, umulo)
{
  open_log_file ("umulo_exp");
  /* Implementation is not symmetric */
  mulo_exp_test (btor_exp_bv_umulo);
}

TEST_F (TestExp, smulo)
{
  open_log_file ("smulo_exp");
  mulo_exp_test (btor_exp_bv_smulo);
}

TEST_F (TestExp, sll)
{
  open_log_file ("sll_exp");
  shift_exp_test (5, 5, btor_exp_bv_sll);
}

TEST_F (TestExp, srl)
{
  open_log_file ("srl_exp");
  shift_exp_test (5, 5, btor_exp_bv_srl);
}

TEST_F (TestExp, sra)
{
  open_log_file ("sra_exp");
  shift_exp_test (5, 5, btor_exp_bv_sra);
}

TEST_F (TestExp, rol)
{
  open_log_file ("rol_exp");
  shift_exp_test (5, 5, btor_exp_bv_rol);
}

TEST_F (TestExp, ror)
{
  open_log_file ("ror_exp");
  shift_exp_test (5, 5, btor_exp_bv_ror);
}

TEST_F (TestExp, read)
{
  open_log_file ("read_exp");

  BtorNode *exp1, *exp2, *exp3, *exp4;
  BtorSortId elem_sort, index_sort, array_sort;

  elem_sort  = btor_sort_bv (d_btor, 32);
  index_sort = btor_sort_bv (d_btor, 8);
  array_sort = btor_sort_array (d_btor, index_sort, elem_sort);

  exp1 = btor_exp_array (d_btor, array_sort, "array1");
  exp2 = btor_exp_var (d_btor, index_sort, "v1");
  exp3 = btor_exp_read (d_btor, exp1, exp2);
  exp4 = btor_exp_read (d_btor, exp1, exp2);

  ASSERT_EQ (exp4, exp3);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp1), 32u);
  ASSERT_EQ (btor_node_array_get_index_width (d_btor, exp1), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 8u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 32u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 32u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp4);
  btor_sort_release (d_btor, elem_sort);
  btor_sort_release (d_btor, index_sort);
  btor_sort_release (d_btor, array_sort);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_node_release (d_btor, exp4);
}

TEST_F (TestExp, cond)
{
  open_log_file ("cond_exp");

  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6;
  BtorBitVector *bv3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 1);
  exp1 = btor_exp_var (d_btor, sort, "v1");
  btor_sort_release (d_btor, sort);
  sort = btor_sort_bv (d_btor, 32);
  exp2 = btor_exp_var (d_btor, sort, "v2");
  btor_sort_release (d_btor, sort);
  bv3  = btor_bv_char_to_bv (d_btor->mm, "00110111001101010001010100110100");
  exp3 = btor_exp_bv_const (d_btor, bv3);
  exp4 = btor_exp_cond (d_btor, exp1, exp2, exp3);
  exp5 = btor_exp_cond (d_btor, exp1, exp2, exp3);
  exp6 = btor_exp_cond (d_btor, exp1, exp3, exp2);

  ASSERT_EQ (exp4, exp5);
  ASSERT_NE (exp4, exp6);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp1), 1u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 32u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 32u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp4), 32u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp5), 32u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp6), 32u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp4);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_node_release (d_btor, exp4);
  btor_node_release (d_btor, exp5);
  btor_node_release (d_btor, exp6);
  btor_bv_free (d_btor->mm, bv3);
}

TEST_F (TestExp, write)
{
  open_log_file ("write_exp");

  BtorNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7;
  BtorSortId sort, array_sort;

  sort       = btor_sort_bv (d_btor, 1);
  array_sort = btor_sort_array (d_btor, sort, sort);

  exp1 = btor_exp_array (d_btor, array_sort, "array1");
  exp2 = btor_exp_var (d_btor, sort, "v1");
  exp3 = btor_exp_var (d_btor, sort, "v2");
  exp4 = btor_exp_write (d_btor, exp1, exp2, exp3);
  exp5 = btor_exp_write (d_btor, exp1, exp2, exp3);
  exp6 = btor_exp_write (d_btor, exp1, exp3, exp2);
  exp7 = btor_exp_read (d_btor, exp5, exp2);

  ASSERT_EQ (exp4, exp5);
  ASSERT_NE (exp4, exp6);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp1), 1u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp2), 1u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp3), 1u);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp4), 1u);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp5), 1u);
  ASSERT_EQ (btor_node_fun_get_width (d_btor, exp6), 1u);
  ASSERT_EQ (btor_node_bv_get_width (d_btor, exp7), 1u);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp7);
  btor_sort_release (d_btor, sort);
  btor_sort_release (d_btor, array_sort);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
  btor_node_release (d_btor, exp4);
  btor_node_release (d_btor, exp5);
  btor_node_release (d_btor, exp6);
  btor_node_release (d_btor, exp7);
}

TEST_F (TestExp, inc)
{
  open_log_file ("inc_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);

  exp1 = btor_exp_var (d_btor, sort, "v1");
  exp2 = btor_exp_bv_inc (d_btor, exp1);
  exp3 = btor_exp_bv_inc (d_btor, exp1);

  ASSERT_EQ (exp2, exp3);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp3);
  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
}

TEST_F (TestExp, dec)
{
  open_log_file ("dec_exp");

  BtorNode *exp1, *exp2, *exp3;
  BtorSortId sort;

  sort = btor_sort_bv (d_btor, 8);

  exp1 = btor_exp_var (d_btor, sort, "v1");
  exp2 = btor_exp_bv_dec (d_btor, exp1);
  exp3 = btor_exp_bv_dec (d_btor, exp1);

  ASSERT_EQ (exp2, exp3);
  btor_dumpbtor_dump_node (d_btor, d_log_file, exp3);
  btor_sort_release (d_btor, sort);
  btor_node_release (d_btor, exp1);
  btor_node_release (d_btor, exp2);
  btor_node_release (d_btor, exp3);
}

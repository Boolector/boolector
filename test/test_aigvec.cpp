/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2014-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btoraigvec.h"
#include "btorbv.h"
}

class TestAigvec : public TestBtor
{
};

TEST_F (TestAigvec, new_delete_aigvec_mgr)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, const)
{
  BtorBitVector *bits  = btor_bv_uint64_to_bv (d_btor->mm, 11, 4);  // "1011"
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av       = btor_aigvec_const (avmgr, bits);
  ASSERT_EQ (av->width, 4u);
  btor_aigvec_release_delete (avmgr, av);
  btor_aigvec_mgr_delete (avmgr);
  btor_bv_free (d_btor->mm, bits);
}

TEST_F (TestAigvec, zero)
{
  BtorAIGVec *av1, *av2;
  BtorBitVector *bits;
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);

  bits = btor_bv_zero (d_btor->mm, 4);
  av1  = btor_aigvec_const (avmgr, bits);
  av2  = btor_aigvec_zero (avmgr, 4);
  ASSERT_EQ (av1->width, 4u);
  ASSERT_EQ (av1->width, av2->width);
  ASSERT_EQ (memcmp (av1->aigs, av2->aigs, sizeof (BtorAIG *) * av1->width), 0);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_bv_free (d_btor->mm, bits);

  bits = btor_bv_ones (d_btor->mm, 4);
  av1  = btor_aigvec_const (avmgr, bits);
  av2  = btor_aigvec_zero (avmgr, 4);
  ASSERT_EQ (av1->width, 4u);
  ASSERT_EQ (av1->width, av2->width);
  ASSERT_GT (memcmp (av1->aigs, av2->aigs, sizeof (BtorAIG *) * av1->width), 0);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_bv_free (d_btor->mm, bits);

  bits = btor_bv_one (d_btor->mm, 4);
  av1  = btor_aigvec_const (avmgr, bits);
  av2  = btor_aigvec_zero (avmgr, 4);
  ASSERT_EQ (av1->width, 4u);
  ASSERT_EQ (av1->width, av2->width);
  ASSERT_GT (memcmp (av1->aigs, av2->aigs, sizeof (BtorAIG *) * av1->width), 0);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_bv_free (d_btor->mm, bits);

  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, var)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av       = btor_aigvec_var (avmgr, 32);
  ASSERT_TRUE (av->width == 32);
  btor_aigvec_release_delete (avmgr, av);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, invert)
{
  int32_t i            = 0;
  int32_t width        = 0;
  BtorBitVector *bits  = btor_bv_uint64_to_bv (d_btor->mm, 11, 4);  // "1011"
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_const (avmgr, bits);
  width                = av1->width;
  ASSERT_TRUE (width == 32);
  for (i = 0; i < width; i++)
  {
    ASSERT_TRUE (!BTOR_IS_INVERTED_AIG (av1->aigs[i]));
    ASSERT_TRUE (btor_aig_is_var (av1->aigs[i]));
  }
  btor_aigvec_invert (avmgr, av1);
  for (i = 0; i < width; i++) ASSERT_TRUE (BTOR_IS_INVERTED_AIG (av1->aigs[i]));
  btor_aigvec_invert (avmgr, av1);
  for (i = 0; i < width; i++)
  {
    ASSERT_TRUE (!BTOR_IS_INVERTED_AIG (av1->aigs[i]));
    ASSERT_TRUE (btor_aig_is_var (av1->aigs[i]));
  }
  ASSERT_TRUE (av2->aigs[0] == BTOR_AIG_TRUE);
  ASSERT_TRUE (av2->aigs[1] == BTOR_AIG_FALSE);
  ASSERT_TRUE (av2->aigs[2] == BTOR_AIG_TRUE);
  ASSERT_TRUE (av2->aigs[3] == BTOR_AIG_TRUE);
  btor_aigvec_invert (avmgr, av2);
  ASSERT_TRUE (av2->aigs[0] == BTOR_AIG_FALSE);
  ASSERT_TRUE (av2->aigs[1] == BTOR_AIG_TRUE);
  ASSERT_TRUE (av2->aigs[2] == BTOR_AIG_FALSE);
  ASSERT_TRUE (av2->aigs[3] == BTOR_AIG_FALSE);
  btor_aigvec_invert (avmgr, av2);
  ASSERT_TRUE (av2->aigs[0] == BTOR_AIG_TRUE);
  ASSERT_TRUE (av2->aigs[1] == BTOR_AIG_FALSE);
  ASSERT_TRUE (av2->aigs[2] == BTOR_AIG_TRUE);
  ASSERT_TRUE (av2->aigs[3] == BTOR_AIG_TRUE);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_mgr_delete (avmgr);
  btor_bv_free (d_btor->mm, bits);
}

TEST_F (TestAigvec, not)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_not (avmgr, av1);
  ASSERT_TRUE (av2->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, slice)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_slice (avmgr, av1, 17, 2);
  ASSERT_TRUE (av2->width == 16);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, and)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_and (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, ult)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_ult (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 1);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, eq)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_eq (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 1);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, add)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_add (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, sll)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_sll (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, srl)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_srl (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, mul)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_mul (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, udiv)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_udiv (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, urem)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_urem (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, concat)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 16);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_concat (avmgr, av1, av2);
  ASSERT_TRUE (av3->width == 48);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_mgr_delete (avmgr);
}

TEST_F (TestAigvec, cond)
{
  BtorAIGVecMgr *avmgr = btor_aigvec_mgr_new (d_btor);
  BtorAIGVec *av1      = btor_aigvec_var (avmgr, 1);
  BtorAIGVec *av2      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av3      = btor_aigvec_var (avmgr, 32);
  BtorAIGVec *av4      = btor_aigvec_cond (avmgr, av1, av2, av3);
  ASSERT_TRUE (av4->width == 32);
  btor_aigvec_release_delete (avmgr, av1);
  btor_aigvec_release_delete (avmgr, av2);
  btor_aigvec_release_delete (avmgr, av3);
  btor_aigvec_release_delete (avmgr, av4);
  btor_aigvec_mgr_delete (avmgr);
}

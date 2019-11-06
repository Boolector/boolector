/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btorexp.h"
#include "utils/btorunionfind.h"
}

class TestUnionFind : public TestBtor
{
 protected:
  void SetUp () override
  {
    TestBtor::SetUp ();
    d_mm   = d_btor->mm;
    d_sort = btor_sort_bv (d_btor, 32);
  }

  void TearDown () override
  {
    btor_sort_release (d_btor, d_sort);
    TestBtor::TearDown ();
  }

  BtorMemMgr *d_mm  = nullptr;
  BtorSortId d_sort = 0;
};

TEST_F (TestUnionFind, test1)
{
  BtorUnionFind *ufind = btor_ufind_new (d_mm);

  BtorNode *x = btor_exp_var (d_btor, d_sort, "x");

  btor_ufind_add (ufind, x);

  ASSERT_EQ (btor_ufind_get_repr (ufind, x), x);

  btor_ufind_add (ufind, x);

  ASSERT_EQ (btor_ufind_get_repr (ufind, x), x);

  btor_node_release (d_btor, x);

  btor_ufind_delete (ufind);
}

TEST_F (TestUnionFind, test2)
{
  BtorUnionFind *ufind = btor_ufind_new (d_mm);

  BtorNode *x = btor_exp_var (d_btor, d_sort, "x");
  BtorNode *y = btor_exp_var (d_btor, d_sort, "y");

  btor_ufind_merge (ufind, x, y);
  ASSERT_EQ (btor_ufind_get_repr (ufind, x), btor_ufind_get_repr (ufind, y));
  ASSERT_TRUE (btor_ufind_is_equal (ufind, x, y));
  ASSERT_EQ (btor_ufind_get_repr (ufind, y), x);

  btor_node_release (d_btor, x);
  btor_node_release (d_btor, y);

  btor_ufind_delete (ufind);
}

TEST_F (TestUnionFind, test3)
{
  BtorUnionFind *ufind = btor_ufind_new (d_mm);

  BtorNode *x = btor_exp_var (d_btor, d_sort, "x");
  BtorNode *y = btor_exp_var (d_btor, d_sort, "y");
  BtorNode *z = btor_exp_var (d_btor, d_sort, "z");

  btor_ufind_merge (ufind, x, y);
  btor_ufind_merge (ufind, y, z);
  ASSERT_EQ (btor_ufind_get_repr (ufind, x), btor_ufind_get_repr (ufind, z));
  ASSERT_EQ (btor_ufind_get_repr (ufind, z), x);

  btor_node_release (d_btor, x);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, z);

  btor_ufind_delete (ufind);
}

TEST_F (TestUnionFind, test4)
{
  BtorUnionFind *ufind = btor_ufind_new (d_mm);

  BtorNode *w = btor_exp_var (d_btor, d_sort, "w");
  BtorNode *x = btor_exp_var (d_btor, d_sort, "x");
  BtorNode *y = btor_exp_var (d_btor, d_sort, "y");
  BtorNode *z = btor_exp_var (d_btor, d_sort, "z");

  btor_ufind_merge (ufind, w, x);
  btor_ufind_merge (ufind, y, z);
  ASSERT_NE (btor_ufind_get_repr (ufind, x), btor_ufind_get_repr (ufind, y));

  btor_ufind_merge (ufind, x, z);

  ASSERT_EQ (btor_ufind_get_repr (ufind, x), btor_ufind_get_repr (ufind, y));
  ASSERT_EQ (btor_ufind_get_repr (ufind, w), btor_ufind_get_repr (ufind, z));

  btor_node_release (d_btor, w);
  btor_node_release (d_btor, x);
  btor_node_release (d_btor, y);
  btor_node_release (d_btor, z);

  btor_ufind_delete (ufind);
}

TEST_F (TestUnionFind, test5)
{
  BtorUnionFind *ufind = btor_ufind_new (d_mm);

  BtorNode *x     = btor_exp_var (d_btor, d_sort, "x");
  BtorNode *not_x = btor_exp_bv_not (d_btor, x);

  btor_ufind_add (ufind, x);
  btor_ufind_add (ufind, not_x);

  ASSERT_EQ (btor_ufind_get_repr (ufind, x), x);
  ASSERT_EQ (btor_ufind_get_repr (ufind, not_x), not_x);
  ASSERT_FALSE (btor_ufind_is_equal (ufind, x, not_x));

  btor_ufind_merge (ufind, x, not_x);

  ASSERT_TRUE (btor_ufind_is_equal (ufind, x, not_x));

  btor_node_release (d_btor, x);
  btor_node_release (d_btor, not_x);

  btor_ufind_delete (ufind);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btorsort.h"
}

class TestSort : public TestBtor
{
};

TEST_F (TestSort, bool)
{
  BtorSortId s0, s1;

  s0 = btor_sort_bool (d_btor);
  s1 = btor_sort_bool (d_btor);
  ASSERT_EQ (s0, s1);
  btor_sort_release (d_btor, s0);
  btor_sort_release (d_btor, s1);
}

TEST_F (TestSort, bitvec)
{
  int32_t i, j;
  BtorSortId s0, s1;

  for (i = 1; i <= 128; i++)
  {
    s0 = btor_sort_bv (d_btor, i);
    for (j = 1; j <= 128; j++)
    {
      s1 = btor_sort_bv (d_btor, j);
      ASSERT_TRUE (i != j || s0 == s1);
      ASSERT_TRUE (i == j || s0 != s1);
      btor_sort_release (d_btor, s1);
    }
    btor_sort_release (d_btor, s0);
  }
}

TEST_F (TestSort, array)
{
  int32_t i, j, k, l;
  BtorSortId s0, s1, s2, s3, a0, a1;

  for (i = 1; i <= 16; i++)
  {
    s0 = btor_sort_bv (d_btor, i);
    for (j = 1; j <= 8; j++)
    {
      s1 = btor_sort_bv (d_btor, j);
      a0 = btor_sort_array (d_btor, s0, s1);
      for (k = 1; k <= 16; k++)
      {
        s2 = btor_sort_bv (d_btor, k);
        for (l = 1; l <= 8; l++)
        {
          s3 = btor_sort_bv (d_btor, l);
          a1 = btor_sort_array (d_btor, s2, s3);
          ASSERT_TRUE (!(i == k && j == l) || a0 == a1);
          ASSERT_TRUE ((i == k && j == l) || a0 != a1);
          btor_sort_release (d_btor, a1);
          btor_sort_release (d_btor, s3);
        }
        btor_sort_release (d_btor, s2);
      }
      btor_sort_release (d_btor, a0);
      btor_sort_release (d_btor, s1);
    }
    btor_sort_release (d_btor, s0);
  }
}

#if 0
// TODO: more tests with different sorts (not only bitvec)
TEST_F (TestSort, lst)
{
  BtorSortId a, b, c, d, l0, l1, l2, l3, l4, l5, l6;

  a = btor_sort_bv (d_btor, 2);
  b = btor_sort_bv (d_btor, 7);
  c = btor_sort_bv (d_btor, 1023);
  d = btor_sort_bv (d_btor, 53);

  l0 = btor_sort_lst (d_btor, a, b);
  l1 = btor_sort_lst (d_btor, l0, c);
  l2 = btor_sort_lst (d_btor, l1, d);

  l3 = btor_sort_lst (d_btor, a, b);
  l4 = btor_sort_lst (d_btor, l3, c);
  l5 = btor_sort_lst (d_btor, l4, d);

  ASSERT_EQ (l2, l5);

  btor_sort_release (d_btor, l3);
  btor_sort_release (d_btor, l4);
  btor_sort_release (d_btor, l5);

  l3 = btor_sort_lst (d_btor, b, a);
  l4 = btor_sort_lst (d_btor, l3, c);
  l5 = btor_sort_lst (d_btor, l4, d);

  ASSERT_NE (l2, l5);

  l6 = btor_sort_lst (d_btor, l5, l5);

  ASSERT_NE (l6, l2);
  ASSERT_NE (l5, l6);

  btor_sort_release (d_btor, a);
  btor_sort_release (d_btor, b);
  btor_sort_release (d_btor, c);
  btor_sort_release (d_btor, d);
  btor_sort_release (d_btor, l0);
  btor_sort_release (d_btor, l1);
  btor_sort_release (d_btor, l2);
  btor_sort_release (d_btor, l3);
  btor_sort_release (d_btor, l4);
  btor_sort_release (d_btor, l5);
  btor_sort_release (d_btor, l6);
}
#endif

TEST_F (TestSort, fun)
{
  BtorSortId a, b, c, s0[2], s1[2], f0, f1, f2, t0, t1, t2;

  a     = btor_sort_bv (d_btor, 53);
  b     = btor_sort_bv (d_btor, 1);
  c     = btor_sort_bool (d_btor);
  s0[0] = a;
  s0[1] = b;
  t0    = btor_sort_tuple (d_btor, s0, 2);
  f0    = btor_sort_fun (d_btor, t0, c);

  s1[0] = b;
  s1[1] = a;
  t1    = btor_sort_tuple (d_btor, s1, 2);
  f1    = btor_sort_fun (d_btor, t1, c);
  ASSERT_NE (f0, f1);

  t2 = btor_sort_tuple (d_btor, s0, 2);
  f2 = btor_sort_fun (d_btor, t2, c);
  ASSERT_EQ (f0, f2);

  btor_sort_release (d_btor, a);
  btor_sort_release (d_btor, b);
  btor_sort_release (d_btor, c);
  btor_sort_release (d_btor, f0);
  btor_sort_release (d_btor, f1);
  btor_sort_release (d_btor, f2);
  btor_sort_release (d_btor, t0);
  btor_sort_release (d_btor, t1);
  btor_sort_release (d_btor, t2);
}

TEST_F (TestSort, tuple)
{
  BtorSortId a, b, c, d, e[4], t0, t1;

  a = btor_sort_bv (d_btor, 53);
  b = btor_sort_bv (d_btor, 7);
  c = btor_sort_bool (d_btor);
  d = btor_sort_array (d_btor, b, a);

  e[0] = a;
  e[1] = b;
  e[2] = c;
  e[3] = d;

  t0 = btor_sort_tuple (d_btor, e, 4);
  t1 = btor_sort_tuple (d_btor, e, 4);
  ASSERT_EQ (t0, t1);
  btor_sort_release (d_btor, t1);

  e[0] = d;
  e[1] = c;
  e[2] = b;
  e[3] = a;
  t1   = btor_sort_tuple (d_btor, e, 4);
  ASSERT_NE (t1, t0);

  btor_sort_release (d_btor, t0);
  t0 = btor_sort_tuple (d_btor, e, 3);
  ASSERT_NE (t0, t1);

  btor_sort_release (d_btor, a);
  btor_sort_release (d_btor, b);
  btor_sort_release (d_btor, c);
  btor_sort_release (d_btor, d);
  btor_sort_release (d_btor, t0);
  btor_sort_release (d_btor, t1);
}

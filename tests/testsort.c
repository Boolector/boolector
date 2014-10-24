/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testsort.h"
#include "btorcore.h"
#include "btorsort.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor                 = NULL;
static BtorSortUniqueTable *g_sorts = NULL;

void
init_sort_test (void)
{
  g_btor  = btor_new_btor ();
  g_sorts = &(g_btor->sorts_unique_table);
}

void
finish_sort_test (void)
{
  btor_delete_btor (g_btor);
  g_sorts = 0;
}

void
init_sort_tests (void)
{
}

void
test_bool_sort (void)
{
  init_sort_test ();
  BtorSort *s0, *s1;

  s0 = btor_bool_sort (g_sorts);
  s1 = btor_bool_sort (g_sorts);
  assert (s0 == s1);
  btor_release_sort (g_sorts, s0);
  btor_release_sort (g_sorts, s1);
  finish_sort_test ();
}

void
test_bitvec_sort (void)
{
  init_sort_test ();
  int i, j;
  BtorSort *s0, *s1;

  for (i = 1; i <= 128; i++)
  {
    s0 = btor_bitvec_sort (g_sorts, i);
    for (j = 1; j <= 128; j++)
    {
      s1 = btor_bitvec_sort (g_sorts, j);
      assert (i != j || s0 == s1);
      assert (i == j || s0 != s1);
      btor_release_sort (g_sorts, s1);
    }
    btor_release_sort (g_sorts, s0);
  }
  finish_sort_test ();
}

void
test_array_sort (void)
{
  init_sort_test ();
  int i, j, k, l;
  BtorSort *s0, *s1, *s2, *s3, *a0, *a1;

  for (i = 1; i <= 16; i++)
  {
    s0 = btor_bitvec_sort (g_sorts, i);
    for (j = 1; j <= 8; j++)
    {
      s1 = btor_bitvec_sort (g_sorts, j);
      a0 = btor_array_sort (g_sorts, s0, s1);
      for (k = 1; k <= 16; k++)
      {
        s2 = btor_bitvec_sort (g_sorts, k);
        for (l = 1; l <= 8; l++)
        {
          s3 = btor_bitvec_sort (g_sorts, l);
          a1 = btor_array_sort (g_sorts, s2, s3);
          assert (!(i == k && j == l) || a0 == a1);
          assert ((i == k && j == l) || a0 != a1);
          btor_release_sort (g_sorts, a1);
          btor_release_sort (g_sorts, s3);
        }
        btor_release_sort (g_sorts, s2);
      }
      btor_release_sort (g_sorts, a0);
      btor_release_sort (g_sorts, s1);
    }
    btor_release_sort (g_sorts, s0);
  }
  finish_sort_test ();
}

// TODO: more tests with different sorts (not only bitvec)
void
test_lst_sort (void)
{
  init_sort_test ();
  BtorSort *a, *b, *c, *d, *l0, *l1, *l2, *l3, *l4, *l5, *l6;

  a = btor_bitvec_sort (g_sorts, 2);
  b = btor_bitvec_sort (g_sorts, 7);
  c = btor_bitvec_sort (g_sorts, 1023);
  d = btor_bitvec_sort (g_sorts, 53);

  l0 = btor_lst_sort (g_sorts, a, b);
  l1 = btor_lst_sort (g_sorts, l0, c);
  l2 = btor_lst_sort (g_sorts, l1, d);

  l3 = btor_lst_sort (g_sorts, a, b);
  l4 = btor_lst_sort (g_sorts, l3, c);
  l5 = btor_lst_sort (g_sorts, l4, d);

  assert (l2 == l5);

  btor_release_sort (g_sorts, l3);
  btor_release_sort (g_sorts, l4);
  btor_release_sort (g_sorts, l5);

  l3 = btor_lst_sort (g_sorts, b, a);
  l4 = btor_lst_sort (g_sorts, l3, c);
  l5 = btor_lst_sort (g_sorts, l4, d);

  assert (l2 != l5);

  l6 = btor_lst_sort (g_sorts, l5, l5);

  assert (l6 != l2);
  assert (l5 != l6);

  btor_release_sort (g_sorts, a);
  btor_release_sort (g_sorts, b);
  btor_release_sort (g_sorts, c);
  btor_release_sort (g_sorts, d);
  btor_release_sort (g_sorts, l0);
  btor_release_sort (g_sorts, l1);
  btor_release_sort (g_sorts, l2);
  btor_release_sort (g_sorts, l3);
  btor_release_sort (g_sorts, l4);
  btor_release_sort (g_sorts, l5);
  btor_release_sort (g_sorts, l6);
  finish_sort_test ();
}

void
test_fun_sort (void)
{
  init_sort_test ();
  BtorSort *a, *b, *c, *s0[2], *s1[2], *f0, *f1, *f2;

  a     = btor_bitvec_sort (g_sorts, 53);
  b     = btor_bitvec_sort (g_sorts, 1);
  c     = btor_bool_sort (g_sorts);
  s0[0] = a;
  s0[1] = b;
  f0    = btor_fun_sort (g_sorts, s0, 2, c);

  s1[0] = b;
  s1[1] = a;
  f1    = btor_fun_sort (g_sorts, s1, 2, c);
  assert (f0 != f1);

  f2 = btor_fun_sort (g_sorts, s0, 2, c);
  assert (f0 == f2);

  btor_release_sort (g_sorts, a);
  btor_release_sort (g_sorts, b);
  btor_release_sort (g_sorts, c);
  btor_release_sort (g_sorts, f0);
  btor_release_sort (g_sorts, f1);
  btor_release_sort (g_sorts, f2);

  finish_sort_test ();
}

void
test_tuple_sort (void)
{
  init_sort_test ();
  BtorSort *a, *b, *c, *d, *e[4], *t0, *t1;

  a = btor_bitvec_sort (g_sorts, 53);
  b = btor_bitvec_sort (g_sorts, 7);
  c = btor_bool_sort (g_sorts);
  d = btor_array_sort (g_sorts, b, a);

  e[0] = a;
  e[1] = b;
  e[2] = c;
  e[3] = d;

  t0 = btor_tuple_sort (g_sorts, e, 4);
  t1 = btor_tuple_sort (g_sorts, e, 4);
  assert (t0 == t1);
  btor_release_sort (g_sorts, t1);

  e[0] = d;
  e[1] = c;
  e[2] = b;
  e[3] = a;
  t1   = btor_tuple_sort (g_sorts, e, 4);
  assert (t1 != t0);

  btor_release_sort (g_sorts, t0);
  t0 = btor_tuple_sort (g_sorts, e, 3);
  assert (t0 != t1);

  btor_release_sort (g_sorts, a);
  btor_release_sort (g_sorts, b);
  btor_release_sort (g_sorts, c);
  btor_release_sort (g_sorts, d);
  btor_release_sort (g_sorts, t0);
  btor_release_sort (g_sorts, t1);

  finish_sort_test ();
}

void
run_sort_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (bool_sort);
  BTOR_RUN_TEST (bitvec_sort);
  BTOR_RUN_TEST (array_sort);
  BTOR_RUN_TEST (lst_sort);
  BTOR_RUN_TEST (fun_sort);
  BTOR_RUN_TEST (tuple_sort);
}

void
finish_sort_tests (void)
{
}

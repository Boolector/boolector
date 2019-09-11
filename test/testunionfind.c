/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testunionfind.h"
#include "btorcore.h"
#include "btorexp.h"
#include "testrunner.h"
#include "utils/btorunionfind.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *g_mm;
static Btor *g_btor;
static BtorSortId g_sort;

void
init_ufind_tests (void)
{
  g_btor = btor_new ();
  g_mm   = g_btor->mm;
  g_sort = btor_sort_bv (g_btor, 32);
}

static void
test_ufind_test1 (void)
{
  BtorUnionFind *ufind = btor_ufind_new (g_mm);

  BtorNode *x = btor_exp_var (g_btor, g_sort, "x");

  btor_ufind_add (ufind, x);

  assert (btor_ufind_get_repr (ufind, x) == x);

  btor_ufind_add (ufind, x);

  assert (btor_ufind_get_repr (ufind, x) == x);

  btor_node_release (g_btor, x);

  btor_ufind_delete (ufind);
}

static void
test_ufind_test2 (void)
{
  BtorUnionFind *ufind = btor_ufind_new (g_mm);

  BtorNode *x = btor_exp_var (g_btor, g_sort, "x");
  BtorNode *y = btor_exp_var (g_btor, g_sort, "y");

  btor_ufind_merge (ufind, x, y);
  assert (btor_ufind_get_repr (ufind, x) == btor_ufind_get_repr (ufind, y));
  assert (btor_ufind_is_equal (ufind, x, y));
  assert (btor_ufind_get_repr (ufind, y) == x);

  btor_node_release (g_btor, x);
  btor_node_release (g_btor, y);

  btor_ufind_delete (ufind);
}

static void
test_ufind_test3 (void)
{
  BtorUnionFind *ufind = btor_ufind_new (g_mm);

  BtorNode *x = btor_exp_var (g_btor, g_sort, "x");
  BtorNode *y = btor_exp_var (g_btor, g_sort, "y");
  BtorNode *z = btor_exp_var (g_btor, g_sort, "z");

  btor_ufind_merge (ufind, x, y);
  btor_ufind_merge (ufind, y, z);
  assert (btor_ufind_get_repr (ufind, x) == btor_ufind_get_repr (ufind, z));
  assert (btor_ufind_get_repr (ufind, z) == x);

  btor_node_release (g_btor, x);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, z);

  btor_ufind_delete (ufind);
}

static void
test_ufind_test4 (void)
{
  BtorUnionFind *ufind = btor_ufind_new (g_mm);

  BtorNode *w = btor_exp_var (g_btor, g_sort, "w");
  BtorNode *x = btor_exp_var (g_btor, g_sort, "x");
  BtorNode *y = btor_exp_var (g_btor, g_sort, "y");
  BtorNode *z = btor_exp_var (g_btor, g_sort, "z");

  btor_ufind_merge (ufind, w, x);
  btor_ufind_merge (ufind, y, z);
  assert (btor_ufind_get_repr (ufind, x) != btor_ufind_get_repr (ufind, y));

  btor_ufind_merge (ufind, x, z);

  assert (btor_ufind_get_repr (ufind, x) == btor_ufind_get_repr (ufind, y));
  assert (btor_ufind_get_repr (ufind, w) == btor_ufind_get_repr (ufind, z));

  btor_node_release (g_btor, w);
  btor_node_release (g_btor, x);
  btor_node_release (g_btor, y);
  btor_node_release (g_btor, z);

  btor_ufind_delete (ufind);
}

static void
test_ufind_test5 (void)
{
  BtorUnionFind *ufind = btor_ufind_new (g_mm);

  BtorNode *x     = btor_exp_var (g_btor, g_sort, "x");
  BtorNode *not_x = btor_exp_bv_not (g_btor, x);

  btor_ufind_add (ufind, x);
  btor_ufind_add (ufind, not_x);

  assert (btor_ufind_get_repr (ufind, x) == x);
  assert (btor_ufind_get_repr (ufind, not_x) == not_x);
  assert (!btor_ufind_is_equal (ufind, x, not_x));

  btor_ufind_merge (ufind, x, not_x);

  assert (btor_ufind_is_equal (ufind, x, not_x));

  btor_node_release (g_btor, x);
  btor_node_release (g_btor, not_x);

  btor_ufind_delete (ufind);
}

void
run_ufind_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (ufind_test1);
  BTOR_RUN_TEST (ufind_test2);
  BTOR_RUN_TEST (ufind_test3);
  BTOR_RUN_TEST (ufind_test4);
  BTOR_RUN_TEST (ufind_test5);
}

void
finish_ufind_tests (void)
{
  btor_sort_release (g_btor, g_sort);
  btor_delete (g_btor);
}

/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "btorexp.h"
}

class TestMap : public TestBtor
{
};

TEST_F (TestMap, new_delete)
{
  BtorNodeMap *map;
  map = btor_nodemap_new (d_btor);
  btor_nodemap_delete (map);
}

TEST_F (TestMap, map0)
{
  Btor *btor_a, *btor_b;
  BtorNode *s, *d, *m;
  BtorNodeMap *map;
  BtorSortId sort;

  btor_a = btor_new ();
  btor_b = btor_new ();

  sort = btor_sort_bv (btor_a, 32);
  s    = btor_exp_var (btor_a, sort, "s");
  btor_sort_release (btor_a, sort);

  sort = btor_sort_bv (btor_b, 32);
  d    = btor_exp_var (btor_b, sort, "d");
  btor_sort_release (btor_b, sort);

  map = btor_nodemap_new (d_btor);
  btor_nodemap_map (map, s, d);
  m = btor_nodemap_mapped (map, s);
  ASSERT_EQ (m, d);

  btor_node_release (btor_a, s);
  btor_node_release (btor_b, d);
  btor_nodemap_delete (map);
  btor_delete (btor_a);
  btor_delete (btor_b);
}

TEST_F (TestMap, map1)
{
  Btor *btor_a;
  BtorNode *s, *t, *a, *m;
  BtorSortId sort;
  BtorNodeMap *map;

  btor_a = btor_new ();
  sort   = btor_sort_bv (btor_a, 32);
  s      = btor_exp_var (btor_a, sort, "0");
  t      = btor_exp_var (btor_a, sort, "1");
  a      = btor_exp_bv_and (btor_a, s, t);
  map    = btor_nodemap_new (d_btor);
  btor_nodemap_map (map, s, a);
  m = btor_nodemap_mapped (map, s);
  ASSERT_EQ (m, a);

  btor_sort_release (btor_a, sort);
  btor_node_release (btor_a, t);
  btor_node_release (btor_a, s);
  btor_node_release (btor_a, a);
  btor_nodemap_delete (map);
  btor_delete (btor_a);
}

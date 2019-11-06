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
#include "utils/boolectornodemap.h"
}

class TestBoolectorNodeMap : public TestBoolector
{
 protected:
  static BoolectorNode *boolectornodemap1_mapper (Btor *btor,
                                                  void *state,
                                                  BoolectorNode *node)
  {
    const char *symbol;
    (void) state;
    if (!boolector_is_var (btor, node)) return 0;
    symbol = boolector_get_symbol (btor, node);
    assert (symbol);
    return boolector_unsigned_int (
        btor, atoi (symbol), boolector_get_sort (btor, node));
  }
};

TEST_F (TestBoolectorNodeMap, boolectornodemap0)
{
  BoolectorSort sort = boolector_bitvec_sort (d_btor, 32);
  BoolectorNode *a   = boolector_var (d_btor, sort, "a");
  BoolectorNode *b   = boolector_var (d_btor, sort, "b");
  BoolectorNode *s   = boolector_sub (d_btor, a, b);
  BoolectorNode *o   = boolector_one (d_btor, sort);
  BoolectorNode *t   = boolector_unsigned_int (d_btor, 2, sort);

  BoolectorNodeMap *map = boolector_nodemap_new (d_btor);
  BoolectorNode *d;
  boolector_nodemap_map (map, a, t);
  boolector_nodemap_map (map, b, o);
  d = boolector_nodemap_substitute_node (d_btor, map, s);
  (void) d;
  ASSERT_EQ (d, o);
  boolector_nodemap_delete (map);

  boolector_release (d_btor, a);
  boolector_release (d_btor, b);
  boolector_release (d_btor, o);
  boolector_release (d_btor, s);
  boolector_release (d_btor, t);
  boolector_release_sort (d_btor, sort);
}

TEST_F (TestBoolectorNodeMap, boolectornodemap1)
{
  BoolectorSort sort = boolector_bitvec_sort (d_btor, 8);
  BoolectorNode *a   = boolector_var (d_btor, sort, "11");
  BoolectorNode *b   = boolector_var (d_btor, sort, "22");
  BoolectorNode *c   = boolector_var (d_btor, sort, "33");
  BoolectorNode *s;

  BoolectorNode *sum = boolector_add (d_btor, a, b);
  s                  = boolector_add (d_btor, sum, c);
  boolector_release (d_btor, sum);

  BoolectorNodeMap *map = boolector_nodemap_new (d_btor);
  BoolectorNode *d, *g;
  d = boolector_nodemap_extended_substitute_node (
      d_btor, map, 0, boolectornodemap1_mapper, boolector_release, s);
  (void) d;
  g = boolector_unsigned_int (d_btor, 66, sort);
  ASSERT_EQ (d, g);
  boolector_release (d_btor, g);
  boolector_nodemap_delete (map);

  boolector_release (d_btor, a);
  boolector_release (d_btor, b);
  boolector_release (d_btor, c);
  boolector_release (d_btor, s);
  boolector_release_sort (d_btor, sort);
}

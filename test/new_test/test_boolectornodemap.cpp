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
    assert (btor == btor);
    if (!boolector_is_var (btor, node)) return 0;
    symbol = boolector_get_symbol (btor, node);
    assert (symbol);
    return boolector_unsigned_int (
        btor, atoi (symbol), boolector_get_sort (btor, node));
  }
};

TEST_F (TestBoolectorNodeMap, boolectornodemap0)
{
  BoolectorSort sort = boolector_bitvec_sort (btor, 32);
  BoolectorNode *a   = boolector_var (btor, sort, "a");
  BoolectorNode *b   = boolector_var (btor, sort, "b");
  BoolectorNode *s   = boolector_sub (btor, a, b);
  BoolectorNode *o   = boolector_one (btor, sort);
  BoolectorNode *t   = boolector_unsigned_int (btor, 2, sort);

  BoolectorNodeMap *map = boolector_nodemap_new (btor);
  BoolectorNode *d;
  boolector_nodemap_map (map, a, t);
  boolector_nodemap_map (map, b, o);
  d = boolector_nodemap_substitute_node (btor, map, s);
  (void) d;
  ASSERT_EQ (d, o);
  boolector_nodemap_delete (map);

  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, o);
  boolector_release (btor, s);
  boolector_release (btor, t);
  boolector_release_sort (btor, sort);
}

TEST_F (TestBoolectorNodeMap, boolectornodemap1)
{
  BoolectorSort sort = boolector_bitvec_sort (btor, 8);
  BoolectorNode *a   = boolector_var (btor, sort, "11");
  BoolectorNode *b   = boolector_var (btor, sort, "22");
  BoolectorNode *c   = boolector_var (btor, sort, "33");
  BoolectorNode *s;

  BoolectorNode *sum = boolector_add (btor, a, b);
  s                  = boolector_add (btor, sum, c);
  boolector_release (btor, sum);

  BoolectorNodeMap *map = boolector_nodemap_new (btor);
  BoolectorNode *d, *g;
  d = boolector_nodemap_extended_substitute_node (
      btor, map, 0, boolectornodemap1_mapper, boolector_release, s);
  (void) d;
  g = boolector_unsigned_int (btor, 66, sort);
  ASSERT_EQ (d, g);
  boolector_release (btor, g);
  boolector_nodemap_delete (map);

  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, s);
  boolector_release_sort (btor, sort);
}
